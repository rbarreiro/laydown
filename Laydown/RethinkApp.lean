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
  | roles (list : List String)
deriving Repr, ToJson

structure ServiceTy where
  name : String
  args : Fields
  res : Ltype
  roles : AccessPolicy
deriving Repr, ToJson


inductive ServiceDef : Schema → ServiceTy → Type where
  | service : (α : ServiceTy) →
                Lexp (toEnv α.args ++ toEnv (schemaEnv σ) ++ serviceEnv) (.effect α.res) →
                  ServiceDef σ α
  | dbService : (α : ServiceTy) →
                Lexp (toEnv α.args ++ toEnv (schemaEnv σ) ++ dbServiceEnv) (.effect α.res) →
                  ServiceDef σ α
deriving Repr, ToJson

abbrev servicesToEnv (x : List ServiceTy) : Env :=
  List.map (λ y => (y.name , .base (Ltype.record y.args ⟶ y.res))) x

inductive Server : Schema → List ServiceTy → Type where
  | base : SchemaDef σ → Server σ []
  | addService : Server σ l → ServiceDef σ t → Server σ (t :: l)
deriving Repr

syntax (priority := high) "#server" "[" term "]" "{" term,* "}" : term
macro_rules
  | `(#server[$z]{}) => `(Server.base $z)
  | `(#server[$z]{$x}) => `(Server.addService (Server.base $z) $x)
  | `(#server[$z]{$xs:term,*, $x}) => `(Server.addService #server[$z]{$xs,*} $x)

inductive RethinkApp where
  | mk : Server σ γ → Lexp (servicesToEnv γ ++ ui) (.effect .ui) → RethinkApp

macro "#rapp" "[" s:term "]" "{" n:term "}" : term => `(RethinkApp.mk $s $n)


structure RethinkGeneratedApp where
  server : String
  client : String
  migrations : List String
deriving Repr


def getServerSchema (server : Server sch srvs) : SchemaDef sch :=
  match server with
    | .addService rest service =>
      getServerSchema rest
    | .base sch =>
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
          tableCreate !(Lexp.litStr ("app_" ++ n)) !(Lexp.litStr n),
          !(genStartMigration name xs)
        }
      ]


def genMigrations_ (schDef : SchemaDef sch) : List String :=
  match schDef with
    | .new name sch =>
      [genStartMigration name sch |> toJson |>.pretty]

def genMigrations (server : Server sch srvs) : List String :=
  genMigrations_ (getServerSchema server)

def genServices (server : Server sch srvs) : List Json :=
  match server with
    | .addService rest service =>
      genServices rest ++ [toJson service]
    | .base _ =>
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
