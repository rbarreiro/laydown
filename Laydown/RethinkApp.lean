import Laydown.BrowserGen
import Lean.Data.Json

open Lean
open Json

abbrev insertResTy := Ltype.record [("inserted", .nat)]

abbrev table (i : Ltype) (v : Ltype) := Ltype.record [
  ("insertI", i ⟶ v ⟶ .effect insertResTy)
]

abbrev serviceEnv : Env :=
  []

abbrev dbServiceEnv : Env :=
  [ ("uuid", .base (.effect .string))
  , ("now", .base (.effect .datetime))
  ]

def uuid [se : SubEnv dbServiceEnv e] : Lexp e (.effect .string) :=
  let p : HasVar dbServiceEnv "uuid" (.effect .string) := by repeat constructor
  Lexp.var "uuid" (se.adaptVar p)

def now [se : SubEnv dbServiceEnv e] : Lexp e (.effect .datetime) :=
  let p : HasVar dbServiceEnv "now" (.effect .datetime) := by repeat constructor
  Lexp.var "now" (se.adaptVar p)

abbrev Schema := List (String × Ltype × Ltype)

abbrev schemaEnv (x : Schema) : Fields :=
  x.map (λ (n, k, v) => (n, table k v))

inductive SchemaDef : Schema → Type where
  | new : String → (l : Schema) → SchemaDef l
deriving Repr

inductive AccessPolicy where
  | all
  | loggedOf
  | roles (list : List String)
deriving Repr, ToJson

structure ServiceTy where
  name : String
  args : Fields
  res : Ltype
  access : AccessPolicy
deriving Repr, ToJson


inductive ServiceDef : Schema → ServiceTy → Type where
  | service : (α : ServiceTy) →
                Lexp (toEnv α.args ++ toEnv (schemaEnv σ) ++ serviceEnv) (.effect α.res) →
                  ServiceDef σ α
  | dbService : (α : ServiceTy) →
                Lexp (toEnv α.args ++ toEnv (schemaEnv σ) ++ dbServiceEnv) (.effect α.res) →
                  ServiceDef σ α
deriving Repr, ToJson

abbrev roleHasAccess (role : Option String) (policy : AccessPolicy) : Bool :=
  match policy with
    | .all => true
    | .loggedOf => false
    | .roles roles =>
      match role with
        | .some r => r ∈ roles
        | .none => false


abbrev roleApi_ (role : Option String) (x : List ServiceTy) : Ltype :=
  let ty := (λ y => (y.name , Ltype.record y.args ⟶ .effect y.res))
  Ltype.record ((x.filter (λ z => roleHasAccess role z.access)).map ty)


inductive Server : List String → Schema → List ServiceTy → Type where
  | base : (roles : List String) → SchemaDef σ → Server roles σ []
  | addService : Server roles σ l → ServiceDef σ t → Server roles σ (t :: l)
deriving Repr

abbrev roleApi (role : Option String) (x : Server roles schema servs) : Ltype :=
  roleApi_ role servs

syntax (priority := high) "#server" "[" term,* "]" "[" term "]" "{" term,* "}" : term
macro_rules
  | `(#server[$r][$z]{}) => `(Server.base [$r] $z)
  | `(#server[$r][$z]{$x}) => `(Server.addService (Server.base [$r] $z) $x)
  | `(#server[$r][$z]{$xs:term,*, $x}) => `(Server.addService #server[$r][$z]{$xs,*} $x)

abbrev loginEnv : Env := [("login", .base (.record [("user", .string), ("password", .string)] ⟶ .effect unit))]

abbrev login : Ltype := .sum [
  ("guest", unit),
  ("user", .record [("user", .string), ("password", .string)])
]


abbrev serverConnection (roles : List String) (services : List ServiceTy) : Env :=
  let rolesServs := roles.map (λ x => (x, roleApi_ (some x) services))
  let servs := ("guest", roleApi_ none services) :: rolesServs
  [("connect", .base (login ⟶ .effect (.sum servs)))]

inductive RethinkApp : Type where
  | mk : Server r σ γ → Lexp (serverConnection r γ ++ ui) (.effect .ui) → RethinkApp

macro "#rapp" "[" s:term "]" "{" n:term "}" : term => `(RethinkApp.mk $s $n)


structure RethinkGeneratedApp where
  server : String
  client : String
  migrations : List String
deriving Repr


def getServerSchema (server : Server roles sch srvs) : SchemaDef sch :=
  match server with
    | .addService rest service =>
      getServerSchema rest
    | .base roles sch =>
      sch

abbrev migrationEnv : Env :=
  [ ("tableCreate", .base (.string ⟶ .string ⟶ .effect unit))
  ]


def genStartMigration  (name : String)  (sch : Schema) : Lexp migrationEnv (.effect unit) :=
  match sch with
    | [] =>
      [laydown| return ()]
    | (n, _, _) :: xs =>
      [laydown|
        do {
          tableCreate !(Lexp.litStr ("app_" ++ name)) !(Lexp.litStr n),
          !(genStartMigration name xs)
        }
      ]


def genMigrations_ (schDef : SchemaDef sch) : List String :=
  match schDef with
    | .new name sch =>
      [genStartMigration name sch |> toJson |>.pretty]

def genMigrations (server : Server roles sch srvs) : List String :=
  genMigrations_ (getServerSchema server)

def genServices (server : Server roles sch srvs) : List Json :=
  match server with
    | .addService rest service =>
      genServices rest ++ [toJson service]
    | .base _ _ =>
      []

def genApp (app : RethinkApp) : RethinkGeneratedApp :=
  match app with
    | .mk server page =>
        let migs := genMigrations server
        let client := genBrowser page
        { server := toJson (genServices server) |>.pretty
        , client := client
        , migrations := migs
        }


def escapeforRun (s : String) : String :=
  s.replace "\\\"" "\\\\\""

def appName (app : RethinkApp) : String :=
  match app with
    | .mk server _ =>
      match getServerSchema server with
        | .new name _ => name

def deployApp (host : String) (port : Nat) (app : RethinkApp) : IO Unit :=
  do
    let a := genApp app
    let name_ := escapeString (appName app) |> escapeforRun
    let server_ := escapeString a.server |> escapeforRun
    let client_ := escapeString a.client |> escapeforRun
    let migrations_ := "[" ++ String.intercalate "," (a.migrations.map (λ x => escapeString x |> escapeforRun)) ++ "]"
    let payload := "{" ++
                    s!"\"id\" : {name_}, \"server\" : {server_},\"page\" : {client_}, \"migrations\" : {migrations_}" ++
                    "}"
    let url := s!"http://{host}:{toString port}/upsertapp"
    let output ← IO.Process.run {
      cmd := "curl.exe",
      args:= #[ "-X", "POST"
              , "-H", "accept: application/json"
              , "-H", "Content-Type: application/json"
              ,"-d", payload
              , url
              ]
    }
    IO.println output
