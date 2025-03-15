
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
  | app : Lexp e (α ⟶ β) → Lexp e α → Lexp e β
  | lambda : (n : String) → Lexp ((n, .base α) :: e) β → Lexp e (α ⟶ β)
  | llet : (n : String) → (v : Lexp e α) → (body : Lexp ((n, .base α) :: e) β) -> Lexp e β
  | pureEffect : Lexp e (α ⟶ Ltype.effect α)
  | bindEffect : Lexp e (Ltype.effect α ⟶ (α ⟶ Ltype.effect β) ⟶ Ltype.effect β)
  | seqEffect : Lexp e (Ltype.effect α ⟶ Ltype.effect β ⟶ Ltype.effect β)


declare_syntax_cat laydown

syntax str : laydown
syntax num : laydown
syntax ident : laydown
syntax laydown laydown : laydown
syntax "!" ident : laydown
syntax "!" "(" term ")" : laydown
syntax "do" "{" "let" ident "←" laydown "," laydown,+ "}" : laydown
syntax "do" "{" "let" ident ":=" laydown "," laydown,+ "}" : laydown
syntax "do" "{" laydown,+ "}" : laydown
syntax "return" laydown : laydown
syntax "[laydown| " laydown "]" : term

macro_rules
  | `([laydown|  $s:str]) => `(Lexp.litStr $s)
  | `([laydown| return $x:laydown]) => `(Lexp.app Lexp.pureEffect [laydown| $x])
  | `([laydown| $x:num]) => `(Lexp.litInt $x)
  | `([laydown| $x:ident]) => `(Lexp.var $x (by repeat constructor))
  | `([laydown| $f:laydown $a:laydown]) => `(Lexp.app [laydown| $f] [laydown| $a])
  | `([laydown| do {$x:laydown, $xs:laydown,* }]) => `(
          Lexp.app
            Lexp.seqEffect
            ( [laydown| $x]
              [laydown| do { $xs,* }]
            )
        )
  | `([laydown| do {$x:laydown}]) => `([laydown| $x])
  | `([laydown| do { let $n:ident ← $v:laydown, $body:laydown }]) => `(
        Lexp.app
          (Lexp.app
            Lexp.bindEffect
            [laydown| $v]
          )
          (Lexp.lambda $(Lean.quote (toString n.getId)) [laydown| $body])

      )
  | `([laydown| do { let $n:ident := $v:laydown, $body:laydown }]) => `(
        Lexp.llet $(Lean.quote (toString n.getId)) [laydown| $v] [laydown| $body]
      )
  | `([laydown| ! $n:ident]) => `($n)
  | `([laydown| !($t:term)]) => `($t)


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
