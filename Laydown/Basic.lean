
import Lean.Data.Json

open Lean
open Json

inductive Ltype where
  | int
  | bool
  | nat
  | datetime
  | float
  | string
  | signal (α : Ltype)
  | stream (α : Ltype)
  | effect (α : Ltype)
  | func : Ltype → Ltype → Ltype
  | ui
  | record (fs : List (String × Ltype))
  | sum (fs : List (String × Ltype))
  | list (α : Ltype)
  | tuple (fs : List Ltype)
  | interval (α : Ltype)
deriving Repr, ToJson

infixr:10   " ⟶ " => Ltype.func

abbrev unit := Ltype.tuple []

def option (α : Ltype) : Ltype := .sum [("some", α), ("none", unit)]

abbrev Fields := List (String × Ltype)

inductive HasField : List (String × Ltype) → String -> Ltype → Type where
  | here : HasField (⟨name, t⟩ :: r) name t
  | there : HasField s name t → HasField (h :: s) name t
deriving Repr

class HasFieldClass (fs : Fields) (n : String) (t : Ltype) where
  hasField : HasField fs n t

instance : HasFieldClass ((n, t):: rs) n t where
  hasField := HasField.here

instance [i : HasFieldClass fs n t] : HasFieldClass (h :: fs) n t where
  hasField := HasField.there i.hasField

inductive GenType where
  | base : Ltype → GenType
  | parametric : (g: Ltype → Ltype) → GenType
  | parametric2 : (g: Ltype → Ltype → Ltype) → GenType

abbrev Env := List (String × GenType)

inductive HasGenVar : Env → String -> GenType → Type where
  | here : HasGenVar (⟨name, t⟩ :: r) name t
  | there : HasGenVar s name t → HasGenVar (h :: s) name t
deriving Repr

abbrev HasVar e n α := HasGenVar e n (GenType.base α)

abbrev toEnv (fs : Fields) : Env :=
  fs.map (λ (n, t) => (n, GenType.base t))

abbrev SubrecordFields (names : List String) (fs : Fields) : Fields :=
  fs.filter (λ (n, _) => n ∈ names)

inductive Lexp : Env → Ltype → Type where
  | litStr : (s : String) → Lexp e Ltype.string
  | litInt : (i : Int) → Lexp e Ltype.int
  | litBool : (b : Bool) → Lexp e Ltype.bool
  | litFloat : (f : Float) → Lexp e Ltype.float
  | var : (n : String) → (p : HasVar e n α) → Lexp e α
  | parametricVar : (n : String) → (α : Ltype) → (p : HasGenVar e n (GenType.parametric g)) → Lexp e (g α)
  | parametric2Var : (n : String) → (α : Ltype) → (β : Ltype) →
                        (p : HasGenVar e n (GenType.parametric2 g)) → Lexp e (g α β)
  | app : Lexp e (α ⟶ β) → Lexp e α → Lexp e β
  | lambda : (n : String) → Lexp ((n, .base α) :: e) β → Lexp e (α ⟶ β)
  | lambdaConst : Lexp e β → Lexp e (α ⟶ β)
  | llet : (n : String) → (v : Lexp e α) → (body : Lexp ((n, .base α) :: e) β) -> Lexp e β
  | mk : (n : String) → Lexp e α → (p : HasField ts n α) → Lexp e (Ltype.sum ts)
  | pureEffect : Lexp e (α ⟶ Ltype.effect α)
  | bindEffect : Lexp e (Ltype.effect α ⟶ (α ⟶ Ltype.effect β) ⟶ Ltype.effect β)
  | seqEffect : Lexp e (Ltype.effect unit ⟶ Ltype.effect β ⟶ Ltype.effect β)
  | intToString : Lexp e (Ltype.int ⟶ Ltype.string)
  | floatToString : Lexp e (Ltype.float ⟶ Ltype.string)
  | boolToString : Lexp e (Ltype.bool ⟶ Ltype.string)
  | recordGet : (n : String) → Lexp e (Ltype.record ts) → HasField ts n α → Lexp e α
  | listnil : Lexp e (.list α)
  | listcons : Lexp e (α ⟶ .list α ⟶ .list α)
  | intAdd : Lexp e (Ltype.int ⟶ Ltype.int ⟶ Ltype.int)
  | floatAdd : Lexp e (Ltype.float ⟶ Ltype.float ⟶ Ltype.float)
  | boolAnd : Lexp e (Ltype.bool ⟶ Ltype.bool ⟶ Ltype.bool)
  | boolOr : Lexp e (Ltype.bool ⟶ Ltype.bool ⟶ Ltype.bool)
  | boolNot : Lexp e (Ltype.bool ⟶ Ltype.bool)
  | boolEq : Lexp e (α ⟶ α ⟶ Ltype.bool)
  | switchbase : (n : String) → (v : String) → (Lexp ((v, GenType.base α) :: e) β) →
                    Lexp e (Ltype.sum [(n, α)] ⟶ β)
  | switchcons : (n : String) → (v : String) → (Lexp ((v, GenType.base α) :: e) β) →
                    Lexp e (Ltype.sum ts ⟶ β) → Lexp e (Ltype.sum ((n, α)::ts) ⟶ β)
  | tupleBase : Lexp e (.tuple [])
  | tupleCons : Lexp e (α ⟶ .tuple ts ⟶ .tuple (α :: ts))
  | recordnil : Lexp e (Ltype.record [])
  | recordcons : (n : String) → Lexp e α → Lexp e (Ltype.record ts) → Lexp e (Ltype.record ((n, α) :: ts))
  | subrecord : (names : List String) → Lexp e (Ltype.record ts) → Lexp e (Ltype.record (SubrecordFields names ts))
  | listMap : Lexp e ((α ⟶ β) ⟶ .list α ⟶ .list β)
deriving Repr

def lexpToJson : Lexp e α → Json
  | Lexp.litStr s => toJson [toJson "litStr", toJson s]
  | Lexp.litInt i => toJson [toJson "litInt", toJson i]
  | Lexp.litBool b => toJson [toJson "litBool", toJson b]
  | Lexp.litFloat f => toJson [toJson "litFloat", toJson f]
  | Lexp.var n _ => toJson [toJson "var", toJson n]
  | Lexp.parametricVar n _ _ => toJson [toJson "parametricVar", toJson n]
  | Lexp.parametric2Var n _ _ _ => toJson [toJson "parametric2Var", toJson n]
  | Lexp.app f a => toJson [toJson "app", lexpToJson f, lexpToJson a]
  | Lexp.lambda n b => toJson [toJson "lambda", toJson n, lexpToJson b]
  | Lexp.lambdaConst b => toJson [toJson "lambdaConst", lexpToJson b]
  | Lexp.llet n v b => toJson [toJson "llet", toJson n, lexpToJson v, lexpToJson b]
  | Lexp.mk n v _ => toJson [toJson "mk", toJson n, lexpToJson v]
  | Lexp.pureEffect => toJson [toJson "pureEffect"]
  | Lexp.bindEffect => toJson [toJson "bindEffect"]
  | Lexp.seqEffect => toJson [toJson "seqEffect"]
  | Lexp.intToString => toJson [toJson "intToString"]
  | Lexp.floatToString => toJson [toJson "floatToString"]
  | Lexp.boolToString => toJson [toJson "boolToString"]
  | Lexp.recordGet n r _ => toJson [toJson "recordGet", toJson n, lexpToJson r]
  | Lexp.listnil => toJson [toJson "listnil"]
  | Lexp.listcons => toJson [toJson "listcons"]
  | Lexp.intAdd => toJson [toJson "intAdd"]
  | Lexp.floatAdd => toJson [toJson "floatAdd"]
  | Lexp.boolAnd => toJson [toJson "boolAnd"]
  | Lexp.boolOr => toJson [toJson "boolOr"]
  | Lexp.boolNot => toJson [toJson "boolNot"]
  | Lexp.boolEq => toJson [toJson "boolEq"]
  | Lexp.switchbase n v b => toJson [toJson "switchbase", toJson n, toJson v, lexpToJson b]
  | Lexp.switchcons n v b c => toJson [toJson "switchcons", toJson n, toJson v, lexpToJson b, lexpToJson c]
  | Lexp.tupleBase => toJson [toJson "tupleBase"]
  | Lexp.tupleCons => toJson [toJson "tupleCons"]
  | Lexp.recordnil => toJson [toJson "recordnil"]
  | Lexp.recordcons n v r => toJson [toJson "recordcons", toJson n, lexpToJson v, lexpToJson r]
  | Lexp.subrecord names r => toJson [toJson "subrecord", toJson names, lexpToJson r]
  | Lexp.listMap => toJson [toJson "listMap"]

instance : ToJson (Lexp e α) where
  toJson := lexpToJson

class Has (f : String) (x : Ltype) (t : Ltype) where
  get : Lexp e (x ⟶ t)

class LHAdd (α : Ltype) (β : Ltype) (γ : Ltype) where
  hadd : Lexp e (α ⟶ β ⟶ γ)

instance : LHAdd Ltype.int Ltype.int Ltype.int where
  hadd := .intAdd

instance : LHAdd Ltype.float Ltype.float Ltype.float where
  hadd := .floatAdd

class LToString (α : Ltype) where
  toString : Lexp e (α ⟶ .string)

abbrev toString := @LToString.toString

instance : LToString Ltype.int where
  toString := .intToString

instance : LToString Ltype.float where
  toString := .floatToString

instance : LToString Ltype.bool where
  toString := .boolToString

class LFunctor (f : Ltype → Ltype) where
  map : Lexp e ((α ⟶  β) ⟶ f α ⟶ f β)

instance : LFunctor (.list) where
  map := Lexp.listMap

def the (α : Ltype) : Lexp e (α ⟶ α) := Lexp.lambda "x" (Lexp.var "x" (.here))

declare_syntax_cat laydown
declare_syntax_cat inst_do
declare_syntax_cat switch_branch
declare_syntax_cat tuple_item
declare_syntax_cat key_value

syntax "[identList|" ident,* "]" : term
macro_rules
  | `([identList| ]) => `([])
  | `([identList| $x:ident]) => `([$(Lean.quote (toString x.getId))])
  | `([identList| $x:ident, $xs:ident,* ]) => `($(Lean.quote (toString x.getId)) :: [identList| $xs,*])

syntax "[laydown| " laydown "]" : term
syntax str : laydown
syntax num : laydown
syntax laydown "#" ident : laydown
syntax laydown "#" "(" ident,* ")" : laydown
syntax ident : laydown
syntax:100 laydown:100 laydown:101 : laydown
syntax "!" ident : laydown
syntax "!" "(" term ")" : laydown
syntax laydown : inst_do
syntax "let" ident ":=" laydown : inst_do
syntax "let" ident ":" term ":=" laydown : inst_do
syntax "let" ident "←" laydown : inst_do
syntax "let" "_" "←" laydown : inst_do
syntax "let" ident ":" term "←" laydown : inst_do
syntax "do" "{" inst_do,+ "}" : laydown
syntax "return" laydown : laydown
syntax "(" laydown ")" : laydown
syntax:10 "λ" ident+ "=>" laydown : laydown
syntax "!sorry" : laydown
syntax:60 laydown:60 "+" laydown:61 : laydown
syntax "Mk" "(" ident "," laydown ")" : laydown
syntax "Mk" "(" ident ")" : laydown
syntax "Mk" "(" ident "," ident ")" "=>" laydown : switch_branch
syntax "Mk" "(" ident ")" "=>" laydown : switch_branch
syntax "match" "{" switch_branch,+  "}" : laydown
syntax "match" laydown "with" "{" switch_branch,* "}" : laydown
syntax laydown "," : tuple_item
syntax "(" tuple_item* ")" : laydown
syntax "(" tuple_item* laydown "," laydown ")" : laydown
syntax "[" laydown,* "]" : laydown
syntax "{" key_value,* "}" : laydown
syntax ident ":=" laydown : key_value
syntax laydown "<$>" laydown : laydown



macro_rules
  | `([laydown| !sorry]) => `(sorry)
  | `([laydown|  $s:str]) => `(Lexp.litStr $s)
  | `([laydown| return $x:laydown]) => `(Lexp.app Lexp.pureEffect [laydown| $x])
  | `([laydown| $x:num]) => `(Lexp.litInt $x)
  | `([laydown| $x:ident]) => `(Lexp.var $(Lean.quote (toString x.getId)) (by repeat constructor))
  | `([laydown| $f:laydown $a:laydown]) => `(Lexp.app [laydown| $f] [laydown| $a])
  | `([laydown| do {$x:laydown, $xs:inst_do,* }]) => `(
          Lexp.app
            (Lexp.app
              Lexp.seqEffect
              [laydown| $x]
            )
            [laydown| do { $xs,* }]

        )
  | `([laydown| do {$x:laydown}]) => `([laydown| $x])
  | `([laydown| do { let $n:ident ← $v:laydown, $rest:inst_do,* }]) => `(
        Lexp.app
          (Lexp.app
            Lexp.bindEffect
            [laydown| $v]
          )
            (Lexp.lambda $(Lean.quote (toString n.getId)) [laydown| do { $rest,* }])

      )
  | `([laydown| do { let _ ← $v:laydown, $rest:inst_do,* }]) => `(
        Lexp.app
          (Lexp.app
            Lexp.bindEffect
            [laydown| $v]
          )
            (Lexp.lambdaConst [laydown| do { $rest,* }])

      )
  | `([laydown| do { let $n:ident : $t:term ← $v:laydown, $rest:inst_do,* }]) => `(
        Lexp.app
          (Lexp.app
            Lexp.bindEffect
            [laydown| !(the (Ltype.effect $t)) $v]
          )
            (Lexp.lambda $(Lean.quote (toString n.getId)) [laydown| do { $rest,* }])

      )
  | `([laydown| do { let $n:ident := $v:laydown, $rest:inst_do,* }]) => `(
        Lexp.llet $(Lean.quote (toString n.getId)) [laydown| $v] [laydown| do { $rest,* }]
      )
  | `([laydown| do { let $n:ident : $t := $v:laydown, $rest:inst_do,* }]) => `(
        Lexp.llet $(Lean.quote (toString n.getId)) [laydown| !(the $t) $v] [laydown| do { $rest,* }]
      )
  | `([laydown| !$n:ident]) => `($n)
  | `([laydown| !($t:term)]) => `($t)
  | `([laydown| ($t:laydown)]) => `([laydown| $t])
  | `([laydown| λ $n:ident => $body:laydown]) => `(
        Lexp.lambda $(Lean.quote (toString n.getId)) [laydown| $body]
      )
  | `([laydown| λ $n:ident $r:ident* => $body:laydown]) => `(
        Lexp.lambda $(Lean.quote (toString n.getId)) [laydown| λ $r* => $body]
      )
  | `([laydown| $x:laydown#$f:ident]) => `(
        Lexp.recordGet $(Lean.quote (toString f.getId)) [laydown| $x] (by repeat constructor)
      )
  | `([laydown| $x:laydown#($fs:ident,*)]) => `(
        Lexp.subrecord [identList| $fs,* ] [laydown| $x]
      )
  | `([laydown| $x + $y]) => `([laydown| !LHAdd.hadd $x $y])
  | `([laydown| Mk($n, $v)]) => `(Lexp.mk $(Lean.quote (toString n.getId)) [laydown| $v] (by repeat constructor))
  | `([laydown| match { Mk($n, $v) => $b }]) => `(
        Lexp.switchbase
          $(Lean.quote (toString n.getId))
          $(Lean.quote (toString v.getId))
          [laydown| $b]
     )
  | `([laydown| match { Mk($n, $v) => $b, $bs:switch_branch,* }]) => `(
        Lexp.switchcons
          $(Lean.quote (toString n.getId))
          $(Lean.quote (toString v.getId))
          [laydown| $b]
          [laydown| match { $bs,* }]
      )
  | `([laydown| match $x with { $bs:switch_branch,* }]) => `(
        [laydown| ( match { $bs,* }) $x]
      )
  | `([laydown| Mk($n)]) => `(Lexp.mk $(Lean.quote (toString n.getId)) .tupleBase (by repeat constructor))
  | `([laydown| match { Mk($n) => $b }]) => `(
        Lexp.switchbase
          $(Lean.quote (toString n.getId))
          "_"
          [laydown| $b]
     )
  | `([laydown| match { Mk($n) => $b, $bs:switch_branch,* }]) => `(
        Lexp.switchcons
          $(Lean.quote (toString n.getId))
          "_"
          [laydown| $b]
          [laydown| match { $bs,* }]
      )
  | `([laydown| ()]) => `(Lexp.tupleBase)
  | `([laydown| ($x:laydown , $xs:tuple_item*)]) => `(
        Lexp.app (Lexp.app Lexp.tupleCons [laydown| $x])  [laydown| ($xs*)]
      )
  | `([laydown| []]) =>
      `(Lexp.listnil)
  | `([laydown| [$x:laydown]]) =>
      `(
        Lexp.app (Lexp.app Lexp.listcons [laydown| $x]) [laydown| [] ]
      )
  | `([laydown| [$x:laydown, $xs:laydown,*]]) => `(
        Lexp.app Lexp.listcons [laydown| $x] [laydown| [ $xs,* ]]
      )
  | `([laydown| {}]) => `(Lexp.recordnil)
  | `([laydown| { $n:ident := $v:laydown }]) => `(
        Lexp.recordcons
          $(Lean.quote (toString n.getId))
          [laydown| $v]
          [laydown| {} ]
    )
  | `([laydown| { $n:ident := $v:laydown, $rest:key_value,* }]) => `(
        Lexp.recordcons
          $(Lean.quote (toString n.getId))
          [laydown| $v]
          [laydown| { $rest,* }]
      )
  | `([laydown| $f <$> $xs]) =>
      `([laydown| !LFunctor.map $f $xs])

def fromOption : Lexp e (α ⟶ option α ⟶ α) :=
  [laydown|
    λ defVal => match {
      Mk(some, v) => v,
      Mk(none) => defVal
    }
  ]

instance [c : HasFieldClass fs n α] : Has n (Ltype.record fs) α where
  get := Lexp.lambda "x" (Lexp.recordGet n (Lexp.var "x" (.here)) c.hasField)

class SubEnv (a : Env) (b : Env) where
  adaptVar : HasGenVar a n α → HasGenVar b n α

instance : SubEnv e e where
  adaptVar := id

instance [s : SubEnv a b] : SubEnv a (h :: b) where
  adaptVar x := HasGenVar.there (s.adaptVar x)

def adaptVarAppend (p : HasGenVar a n α) : HasGenVar (more ++ a) n α :=
  match more with
   | [] => p
   | _ :: rest => HasGenVar.there (@adaptVarAppend a n α rest p)

instance [s : SubEnv a b] : SubEnv a (more ++ b) where
  adaptVar x := adaptVarAppend (s.adaptVar x)
