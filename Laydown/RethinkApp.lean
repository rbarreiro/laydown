import Laydown.BrowserGen
import Lean.Data.Json

open Lean
open Json

inductive HasKey : List (String × α) → String → Type where
  | here : HasKey (⟨name, t⟩ :: r) name
  | there : HasKey s name → HasKey (h :: s) name
deriving Repr

def getValue (l : List (String × α)) (p : HasKey l name) : α :=
  match l with
    | ((_, v) :: xs) =>
      match p with
        | .here => v
        | .there p => getValue xs p

abbrev idValue (i : Ltype) (v : Ltype) := Ltype.record [
  ("id", i),
  ("value", v)
]

abbrev insertResTy := Ltype.record [("inserted", .nat)]

abbrev table (i : Ltype) (v : Ltype) := Ltype.record [
  ("insertI", i ⟶ v ⟶ .effect insertResTy),
  ("between", .interval i ⟶ .stream (idValue i v)),
  ("items", .stream (idValue i v))
]

abbrev serviceEnv : Env :=
  []

abbrev dbServiceEnv : Env :=
  [ ("uuid", .base (.effect .string))
  , ("now", .base (.effect .datetime))
  , ("streamChanges", .parametric (λ α => .stream α ⟶ .stream (changes α)))
  , ("setDim1_2", .parametric2 (λ α β => α ⟶ .interval (.tuple [α, β])))
  ]

def uuid [se : SubEnv dbServiceEnv e] : Lexp e (.effect .string) :=
  let p : HasVar dbServiceEnv "uuid" (.effect .string) := by repeat constructor
  Lexp.var "uuid" (se.adaptVar p)

def now [se : SubEnv dbServiceEnv e] : Lexp e (.effect .datetime) :=
  let p : HasVar dbServiceEnv "now" (.effect .datetime) := by repeat constructor
  Lexp.var "now" (se.adaptVar p)

def streamChanges [se : SubEnv dbServiceEnv e] : Lexp e (.stream α ⟶ .stream (changes α)) :=
  let p : HasGenVar dbServiceEnv "streamChanges" (.parametric (λ α => .stream α ⟶ .stream (changes α))) := by repeat constructor
  let w : Lexp e (.stream α ⟶ .stream (changes α)) := Lexp.parametricVar "streamChanges" α (se.adaptVar p)
  w

def setDim1_2 [se : SubEnv dbServiceEnv e] : Lexp e  (α ⟶ .interval (.tuple [α, β])) :=
  let p : HasGenVar dbServiceEnv "setDim1_2" (.parametric2 (λ α β => α ⟶ .interval (.tuple [α, β]))) := by repeat constructor
  let w : Lexp e  (α ⟶ .interval (.tuple [α, β])) := Lexp.parametric2Var "setDim1_2" α β (se.adaptVar p)
  w

abbrev Schema := List (String × Ltype × Ltype)

inductive IsDataSchema : Schema → Type where
  | base : IsData key  → IsData value → IsDataSchema [(name, key, value)]
  | cons : IsDataSchema xs → IsData key → IsData value → IsDataSchema ((name, key, value) :: xs)
deriving Repr

abbrev schemaEnv (x : Schema) : Fields :=
  x.map (λ (n, k, v) => (n, table k v))

inductive SchemaDef : Schema → Type where
  | new : String → (l : Schema) → IsDataSchema l → SchemaDef l
deriving Repr



abbrev idValueType_ (_ : SchemaDef schema) (tbl : String) (p : HasKey schema tbl) : Ltype :=
  let (i, v) := getValue schema p
  idValue i v

macro "idValueType" "(" sch:term "," tbl:term  ")": term => `(idValueType_ $sch $tbl (by repeat constructor))

inductive AccessPolicy where
  | all
  | roles (list : List String)
deriving Repr, ToJson

inductive ServiceKind where
  | rpc
  | stream
deriving Repr, ToJson

structure ServiceTy where
  name : String
  args : Fields
  res : Ltype
  access : AccessPolicy
  kind : ServiceKind
deriving Repr, ToJson

abbrev serviceDefTy (t : ServiceTy) : Ltype :=
  match t.kind with
    | .rpc => .effect t.res
    | .stream => .effect (.stream t.res)

inductive ServiceDef : Schema → ServiceTy → Type where
  | dbService : (α : ServiceTy) →
                Lexp (toEnv α.args ++ toEnv (schemaEnv σ) ++ dbServiceEnv) (serviceDefTy α) →
                  IsData α.res → IsData (Ltype.record α.args) →
                  ServiceDef σ α
deriving Repr

def serviceDefToJson (s : ServiceDef schema ty) : Json :=
  match s with
    | .dbService _ x _ _ => toJson [toJson "dbService", toJson ty, toJson x]

instance : ToJson (ServiceDef schema ty) where
  toJson := serviceDefToJson


abbrev roleHasAccess (role : String) (policy : AccessPolicy) : Bool :=
  match policy with
    | .all => true
    | .roles roles => role ∈ roles


inductive Server : List String → Schema → List ServiceTy → Type where
  | base : (roles : List String) → SchemaDef σ → Server roles σ []
  | addService : Server roles σ l → ServiceDef σ t → Server roles σ (t :: l)
deriving Repr

abbrev serviceSig (y : ServiceTy) :=
  match y.kind with
    | .rpc => (y.name , Ltype.record y.args ⟶ .effect y.res)
    | .stream =>  (y.name , Ltype.record y.args ⟶ .effect (.stream y.res))

abbrev roleApi_ (role : String) (x : List ServiceTy) : Ltype :=
  Ltype.record ((x.filter (λ z => roleHasAccess role z.access)).map serviceSig)

abbrev roleApi (role : String) (_ : Server roles schema servs) : Ltype :=
  roleApi_ role servs

abbrev serviceGroup (names : List String) (_ : Server roles schema services) : Ltype :=
  .record (SubrecordFields names (services.map serviceSig))

macro "mkSchema" "[" n:term "]" i:term : term =>
  `(SchemaDef.new $n $i (by repeat constructor))

macro "dbService" ":" t:term ":=" x:term : term =>
  `(ServiceDef.dbService $t $x (by repeat constructor) (by repeat constructor))

syntax (priority := high) "#server" "[" term,* "]" "[" term "]" "{" term,* "}" : term
macro_rules
  | `(#server[$r,*][$z]{}) => `(Server.base [$r,*] $z)
  | `(#server[$r,*][$z]{$x}) => `(Server.addService (Server.base [$r,*] $z) $x)
  | `(#server[$r,*][$z]{$xs:term,*, $x}) => `(Server.addService #server[$r,*][$z]{$xs,*} $x)


abbrev login : Ltype := .sum [
  ("guest", unit),
  ("user", .record [("user", .string), ("password", .string)])
]


abbrev serverConnection (roles : List String) (services : List ServiceTy) : Env :=
  let rolesServs := roles.map (λ x => (x, roleApi_ x services))
  let servs := ("guest", roleApi_ "guest" services) :: rolesServs
  [("connect", .base (login ⟶ (.sum servs ⟶ .effect unit) ⟶ .effect unit))]

inductive RethinkApp : Type where
  | mk : Server r σ γ → Lexp (serverConnection r γ ++ ui) (.effect .ui) → RethinkApp

macro "#rapp" "[" s:term "]" "{" n:term "}" : term => `(RethinkApp.mk $s $n)


structure RethinkGeneratedApp where
  server : String
  client : String
  migrations : List String
  tables : String
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
      [laydown| !pure ()]
    | (n, _, _) :: xs =>
      [laydown|
        do {
          tableCreate !(Lexp.litStr ("app_" ++ name)) !(Lexp.litStr n),
          !(genStartMigration name xs)
        }
      ]


def genMigrations_ (schDef : SchemaDef sch) : List String :=
  match schDef with
    | .new name sch _ =>
      [genStartMigration name sch |> toJson |>.pretty]

def genMigrations (server : Server roles sch srvs) : List String :=
  genMigrations_ (getServerSchema server)

def genServices (server : Server roles sch srvs) : List Json :=
  match server with
    | .addService rest service =>
      genServices rest ++ [toJson service]
    | .base _ _ =>
      []


def appName (app : RethinkApp) : String :=
  match app with
    | .mk server _ =>
      match getServerSchema server with
        | .new name _ _ => name

def genService (x : ServiceTy) : String :=
let i := "const i = '' + (lastReqId++)"
let msg := "const msg = JSON.stringify({" ++
      s!"service: {escapeString x.name}, reqId:i, arg: arg" ++
      "})"
let rpcSetCallback := "message_call_backs[i] = x => {r(x);delete message_call_backs[i]};"
let streamSetCallback := "message_call_backs[i] = x => {cb(x)};"
match x.kind with
  | .rpc =>
    x.name ++ ": arg => r => {" ++
          s!"{i};{msg};{rpcSetCallback};ws.send(msg)" ++
    "}"
  | .stream =>
    x.name ++ ": arg => r => {" ++
        "r(cb => {" ++ s!"{i};{msg};{streamSetCallback};ws.send(msg);" ++ "})" ++
      "}"

def genClientServicesRole (role : String) (services : List ServiceTy) : String :=
  let filtered := services.filter (λ x => roleHasAccess role x.access)
  let defs := filtered.map genService
  "Immutable.Map({" ++ String.intercalate "," defs ++ "})"

def genClientServices_ (_ : Server roles sch srvs) : String :=
  let roles_ := "guest" :: roles
  "Immutable.Map({" ++ String.intercalate "," (roles_.map (λ r => s!"{r}: {genClientServicesRole r srvs}")) ++ "})"

def genClientServices : (app : RethinkApp) → String
  | .mk server _ => genClientServices_ server


def genServerApi (app : RethinkApp) : String :=
  "const connect = login => cb => r => {\n
    const ws = new WebSocket('/appcom/"++ appName app ++"');
    const message_call_backs = {};
    let lastReqId = 0;
    let role = null;
    const servs = "++ genClientServices app ++"
    ws.onmessage = event => {
      const data = JSON.parse(event.data);
      if(role === null){
        role = data.role;
        const api = servs.get(role);
        cb(Immutable.Map().set(role, api))(x => x);
      }else{
        const i = data.reqId;
        message_call_backs[i](Immutable.fromJS(data.result));
      }
    }
    ws.onopen = event =>{
      ws.send(JSON.stringify(login));
    }
    r(x=>x)
  }
  "

def genTables (_ : Server roles sch srvs) : String :=
  toJson sch |> pretty

def genApp (app : RethinkApp) : RethinkGeneratedApp :=
  match app with
    | .mk server page =>
        let migs := genMigrations server
        let client := browserTemplate (genServerApi app) (jsGen page)
        { server := (genServices server) |> toJson |> pretty
        , client := client
        , migrations := migs
        , tables := genTables server
        }


def escapeforRun (s : String) : String :=
  s.replace "\\\"" "\\\\\""

def deployApp (host : String) (port : Nat) (app : RethinkApp) : IO Unit :=
  do
    let a := genApp app
    let name_ := escapeString (appName app) |> escapeforRun
    let server_ := escapeString a.server |> escapeforRun
    let tables_ := escapeString a.tables |> escapeforRun
    let client_ := escapeString a.client |> escapeforRun
    let migrations_ := "[" ++ String.intercalate "," (a.migrations.map (λ x => escapeString x |> escapeforRun)) ++ "]"
    let payload := "{" ++
                    s!"\"id\" : {name_}, \"server\" : {server_},\"page\" : {client_}, \"migrations\" : {migrations_}, \"tables\": {tables_}" ++
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
