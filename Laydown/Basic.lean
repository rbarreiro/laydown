
inductive Ltype where
  | unit
  | int
  | bool
  | float
  | string
  | signal (α : Ltype)
  | effect (α : Ltype)
  | func : Ltype → Ltype → Ltype
  | ui
  | record (fs : List (String × Ltype))
  | sum (fs : List (String × Ltype))
  | list (α : Ltype)
deriving Repr

infixr:10   " ⟶ " => Ltype.func

abbrev Fields := List (String × Ltype)

inductive HasField : List (String × Ltype) → String -> Ltype → Type where
  | here : HasField (⟨name, t⟩ :: r) name t
  | there : HasField s name t → HasField (h :: s) name t
deriving Repr

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

inductive Lexp : Env → Ltype → Type where
  | litStr : (s : String) → Lexp e Ltype.string
  | litInt : (n : Int) → Lexp e Ltype.int
  | litBool : (b : Bool) → Lexp e Ltype.bool
  | litFloat : (f : Float) → Lexp e Ltype.float
  | litUnit : Lexp e Ltype.unit
  | var : (n : String) → (p : HasVar e n α) → Lexp e α
  | parametricVar : (n : String) → (α : Ltype) → (p : HasGenVar e n (GenType.parametric g)) → Lexp e (g α)
  | parametric2Var : (n : String) → (α : Ltype) → (β : Ltype) → (p : HasGenVar e n (GenType.parametric2 g)) → Lexp e (g α β)
  | app : Lexp e (α ⟶ β) → Lexp e α → Lexp e β
  | lambda : (n : String) → Lexp ((n, .base α) :: e) β → Lexp e (α ⟶ β)
  | llet : (n : String) → (v : Lexp e α) → (body : Lexp ((n, .base α) :: e) β) -> Lexp e β
  | pureEffect : Lexp e (α ⟶ Ltype.effect α)
  | bindEffect : Lexp e (Ltype.effect α ⟶ (α ⟶ Ltype.effect β) ⟶ Ltype.effect β)
  | seqEffect : Lexp e (Ltype.effect α ⟶ Ltype.effect β ⟶ Ltype.effect β)
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

declare_syntax_cat laydown
declare_syntax_cat inst_do


syntax str : laydown
syntax num : laydown
syntax laydown "#" ident : laydown
syntax ident : laydown
syntax:100 laydown:100 laydown:101 : laydown
syntax "!" ident : laydown
syntax "!" "(" term ")" : laydown
syntax laydown : inst_do
syntax "let" ident ":=" laydown : inst_do
syntax "let" ident "←" laydown : inst_do
syntax "do" "{" inst_do,+ "}" : laydown
syntax "return" laydown : laydown
syntax "[laydown| " laydown "]" : term
syntax "(" laydown ")" : laydown
syntax:10 "λ" ident+ "=>" laydown : laydown
syntax "!sorry" : laydown
syntax:60 laydown:60 "+" laydown:61 : laydown

macro_rules
  | `([laydown| !sorry]) => `(sorry)
  | `([laydown|  $s:str]) => `(Lexp.litStr $s)
  | `([laydown| return $x:laydown]) => `(Lexp.app Lexp.pureEffect [laydown| $x])
  | `([laydown| $x:num]) => `(Lexp.litInt $x)
  | `([laydown| $x:ident]) => `(Lexp.var $(Lean.quote (toString x.getId)) (by repeat constructor))
  | `([laydown| $f:laydown $a:laydown]) => `(Lexp.app [laydown| $f] [laydown| $a])
  | `([laydown| do {$x:laydown, $xs:inst_do,* }]) => `(
          Lexp.app
            Lexp.seqEffect
            ( [laydown| $x]
              [laydown| do { $xs,* }]
            )
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
  | `([laydown| do { let $n:ident := $v:laydown, $rest:inst_do,* }]) => `(
        Lexp.llet $(Lean.quote (toString n.getId)) [laydown| $v] [laydown| do { $rest,* }]
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
  | `([laydown| $x + $y]) => `([laydown| !LHAdd.hadd $x $y])


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
