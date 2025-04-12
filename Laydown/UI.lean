import Laydown.Basic

abbrev changes (α : Ltype) : Ltype := .sum [
  ("added", α),
  ("removed", α),
  ("updated", .record [("new", α),("old", α)]),
]

abbrev signalAndSetter (α : Ltype) : Ltype := .record [
    ("set", α ⟶ .effect unit),
    ("update", (α ⟶ α) ⟶ .effect unit),
    ("signal", .signal α),
    ("get", .effect α)
]

abbrev createSignalTy := λ α =>
  α ⟶ .effect (signalAndSetter α)


abbrev formSubmitContext : Ltype := .record [
  ("reset", .effect unit)
]

abbrev ui : Env := [
  ("button", .base (.effect .ui ⟶ .effect unit ⟶ .effect .ui)),
  ("text", .base (.string ⟶ .effect .ui)),
  ("signalUI", .base (.signal (.effect .ui) ⟶ .effect .ui)),
  ("signalListUI", .parametric ( λ α => (.signal (.list α)) ⟶ (α ⟶ .effect .ui) ⟶ .effect .ui)),
  ("concat", .base (.effect .ui ⟶ .effect .ui ⟶ .effect .ui)),
  ("displayList", .base (.list (.effect .ui) ⟶ .effect .ui)),
  ("createSignal", .parametric createSignalTy),
  ("mapSignal", .parametric2 (λ α β => ((α ⟶ β) ⟶ .signal α ⟶ .signal β))),
  ("pureSignal", .parametric (λ α => α ⟶ .signal α)),
  ("seqSignal", .parametric2 (λ α β => .signal (α ⟶ β) ⟶  (unit ⟶ .signal α) ⟶ .signal β)),
  ("subscribeSignal", .parametric (λ α => .signal α ⟶ (α ⟶ .effect unit) ⟶ .effect unit)),
  ("currentValue", .parametric (λ α => .signal α ⟶ .effect α)),
  ("br", .base (.effect .ui)),
  ("textInput", .base (.string ⟶ (.string ⟶ .effect unit) ⟶ .effect .ui)),
  ("passwordInput", .base (.string ⟶ (.string ⟶ .effect unit) ⟶ .effect .ui)),
  ("streamChangesUI", .parametric2 (λ α β => .stream (changes α) ⟶ (α ⟶ .effect .ui) ⟶ (α ⟶ β) ⟶ .effect .ui)),
  ("form", .base ((formSubmitContext ⟶ .effect unit) ⟶ .effect .ui ⟶ .effect .ui)),
  ("withLabel", .base (.effect .ui ⟶ .effect .ui ⟶ .effect .ui)),
  ("consoleLog", .parametric (λ α => α ⟶ .effect unit)),
  ("submitButton", .base (.effect .ui ⟶ .effect .ui))
]


def button [se : SubEnv ui e] : Lexp e (.effect .ui ⟶ .effect unit ⟶ .effect .ui) :=
  let p : HasVar ui "button" (.effect .ui ⟶ .effect unit ⟶.effect .ui) := by repeat constructor
  Lexp.var "button" (se.adaptVar p)

def text [se : SubEnv ui e] : Lexp e (.string ⟶ .effect .ui) :=
  let p : HasVar ui "text" (.string ⟶ .effect .ui) := by repeat constructor
  Lexp.var "text" (se.adaptVar p)

def signalUI [se : SubEnv ui e] : Lexp e (.signal (.effect .ui) ⟶ .effect .ui) :=
  let p : HasVar ui "signalUI" (.signal (.effect .ui) ⟶ .effect .ui) := by repeat constructor
  Lexp.var "signalUI" (se.adaptVar p)

def signalListUI [se : SubEnv ui e] :
  Lexp e (.signal (.list α) ⟶ (α ⟶ .effect .ui) ⟶ .effect .ui) :=
  let p : HasGenVar ui "signalListUI"
    (.parametric (λ α => (.signal (.list α)) ⟶ (α ⟶ .effect .ui) ⟶ .effect .ui)) :=
            by repeat constructor
  Lexp.parametricVar "signalListUI" α (se.adaptVar p)

def concat [se : SubEnv ui e] : Lexp e (.effect .ui ⟶ .effect .ui ⟶ .effect .ui) :=
  let p : HasVar ui "concat" (.effect .ui ⟶ .effect .ui ⟶ .effect .ui) := by repeat constructor
  Lexp.var "concat" (se.adaptVar p)

def createSignal [se : SubEnv ui e] :
  Lexp e (createSignalTy α) :=
    let p : HasGenVar ui "createSignal"
      (.parametric createSignalTy) :=
            by repeat constructor
  Lexp.parametricVar "createSignal" α (se.adaptVar p)

def mapSignal [se : SubEnv ui e] : Lexp e ((α ⟶ β) ⟶ .signal α ⟶ .signal β) :=
  let p : HasGenVar ui "mapSignal"
    (.parametric2 (λ α β => ((α ⟶ β) ⟶ .signal α ⟶ .signal β))) :=
            by repeat constructor
  Lexp.parametric2Var "mapSignal" α  β (se.adaptVar p)

def pureSignal [se : SubEnv ui e] : Lexp e (α ⟶ .signal α) :=
  let p : HasGenVar ui "pureSignal"
    (.parametric (λ α => α ⟶ .signal α)) :=
            by repeat constructor
  Lexp.parametricVar "pureSignal" α (se.adaptVar p)

def seqSignal [se : SubEnv ui e] :
  Lexp e (.signal (α ⟶ β) ⟶ (unit ⟶ .signal α) ⟶ .signal β) :=
  let p : HasGenVar ui "seqSignal"
    (.parametric2 (λ α β => .signal (α ⟶ β) ⟶ (unit ⟶ .signal α) ⟶ .signal β)) :=
            by repeat constructor
  Lexp.parametric2Var "seqSignal" α β (se.adaptVar p)

def subscribeSignal [se : SubEnv ui e] :
  Lexp e (.signal α ⟶ (α ⟶ .effect unit) ⟶ .effect unit) :=
  let p : HasGenVar ui "subscribeSignal"
    (.parametric (λ α => .signal α ⟶ (α ⟶ .effect unit) ⟶ .effect unit)) :=
            by repeat constructor
  Lexp.parametricVar "subscribeSignal" α (se.adaptVar p)

def currentValue [se : SubEnv ui e] :
  Lexp e (.signal α ⟶ .effect α) :=
  let p : HasGenVar ui "currentValue"
    (.parametric (λ α => .signal α ⟶ .effect α)) :=
            by repeat constructor
  Lexp.parametricVar "currentValue" α (se.adaptVar p)

def displayList [se : SubEnv ui e] :
  Lexp e (.list (.effect .ui) ⟶ .effect .ui) :=
  let p : HasVar ui "displayList" (.list (.effect .ui) ⟶ .effect .ui) := by repeat constructor
  Lexp.var "displayList" (se.adaptVar p)

def br [se : SubEnv ui e] : Lexp e (.effect .ui) :=
  let p : HasVar ui "br" (.effect .ui) := by repeat constructor
  Lexp.var "br" (se.adaptVar p)

def textInput [se : SubEnv ui e] : Lexp e (.string ⟶ (.string ⟶ .effect unit) ⟶ .effect .ui) :=
  let p : HasVar ui "textInput" (.string ⟶ (.string ⟶ .effect unit) ⟶ .effect .ui) := by repeat constructor
  Lexp.var "textInput" (se.adaptVar p)

def passwordInput [se : SubEnv ui e] : Lexp e (.string ⟶ (.string ⟶ .effect unit) ⟶ .effect .ui) :=
  let p : HasVar ui "passwordInput" (.string ⟶ (.string ⟶ .effect unit) ⟶ .effect .ui) := by repeat constructor
  Lexp.var "passwordInput" (se.adaptVar p)

def streamChangesUI [se : SubEnv ui e] :
  Lexp e (.stream (changes α) ⟶ (α ⟶ .effect .ui) ⟶ (α ⟶  β) ⟶ .effect .ui) :=
  let p : HasGenVar ui "streamChangesUI"
    (.parametric2 (λ α β => .stream (changes α) ⟶ (α ⟶ .effect .ui) ⟶ (α ⟶ β) ⟶ .effect .ui)) :=
            by repeat constructor
  Lexp.parametric2Var "streamChangesUI" α β (se.adaptVar p)

def form [se : SubEnv ui e] :
  Lexp e ((formSubmitContext ⟶ .effect unit) ⟶ .effect .ui ⟶ .effect .ui) :=
  let p : HasVar ui "form" ((formSubmitContext ⟶ .effect unit) ⟶ .effect .ui ⟶ .effect .ui) := by repeat constructor
  Lexp.var "form" (se.adaptVar p)

def withLabel [se : SubEnv ui e] :
  Lexp e (.effect .ui ⟶ .effect .ui ⟶ .effect .ui) :=
  let p : HasVar ui "withLabel" (.effect .ui ⟶ .effect .ui ⟶ .effect .ui) := by repeat constructor
  Lexp.var "withLabel" (se.adaptVar p)

def consoleLog [se : SubEnv ui e] :
  Lexp e (α ⟶ .effect unit) :=
  let p : HasGenVar ui "consoleLog" (.parametric (λ α => α ⟶ .effect unit)) := by repeat constructor
  Lexp.parametricVar "consoleLog" α (se.adaptVar p)

def submitButton [se : SubEnv ui e] :
  Lexp e (.effect .ui ⟶ .effect .ui) :=
  let p : HasVar ui "submitButton" (.effect .ui ⟶ .effect .ui) := by repeat constructor
  Lexp.var "submitButton" (se.adaptVar p)

class LDisplay (α : Ltype) where
  display [SubEnv ui e] : Lexp e (α ⟶ .effect .ui)

class LListDisplay (l : Ltype → Ltype) where
  listDisplay [SubEnv ui e] : Lexp e (l α ⟶ (α ⟶ .effect .ui) ⟶ .effect .ui)

instance [e : LDisplay α] : LDisplay (.signal α) where
  display := [laydown| λ x => !signalUI (!mapSignal !e.display x)]

instance : LDisplay (.effect .ui) where
  display := [laydown| λ x => x]

instance : LDisplay Ltype.string where
  display := text

instance : LDisplay .int where
  display := [laydown| λ x => !LDisplay.display (!toString x)]

instance : LListDisplay .list where
  listDisplay :=
    [laydown| λ xs render =>
      !displayList (render <$> xs)
    ]

instance : LListDisplay (.signal ∘ .list) where
  listDisplay :=
    [laydown| λ xs render =>
      !signalListUI xs (λ x => render x)
    ]

declare_syntax_cat ui

syntax "[ui| " ui "]" : laydown
syntax ":" : ui
syntax "..." : ui
syntax "___(" laydown ")" : ui
syntax "__" laydown "__(" laydown ")" : ui
syntax "*___(" laydown ")" : ui
syntax "*__" laydown "__(" laydown ")" : ui
syntax ident : ui
syntax ui ui : ui
syntax "{ " laydown " }" : ui
syntax  "{{for " ident "in" laydown "}"  ui "}": ui
syntax  "{{forChanges " ident "in" laydown "order" "by" laydown "}"  ui "}": ui
syntax  "{{forChanges " ident "in" laydown "}"  ui "}": ui
syntax "<br>" : ui
syntax "b[" ui "](" laydown ")" : ui
syntax ui "::" ui : ui


macro_rules
  | `([laydown| [ui| :]]) =>
      `(Lexp.app text (Lexp.litStr ": "))
  | `([laydown| [ui| ...]]) =>
      `(Lexp.app text (Lexp.litStr "..."))
  | `([laydown| [ui| ___($c) ]]) =>
      `([laydown| !textInput "" $c])
  | `([laydown| [ui| __ $v __($c) ]]) =>
      `([laydown| !textInput $v $c])
  | `([laydown| [ui| *___($c) ]]) =>
      `([laydown| !passwordInput "" $c])
  | `([laydown| [ui| *__ $v __($c) ]]) =>
      `([laydown| !passwordInput $v $c])
  | `([laydown| [ui| $txt:ident ]]) =>
      `( Lexp.app
          text
          (Lexp.litStr ($(Lean.quote (toString txt.getId)) ++ " "))
      )
  | `([laydown| [ui| $x:ui $y:ui ]]) =>
      `(
        Lexp.app
          (Lexp.app
            concat
            [laydown| [ui| $x ]]
          )
          [laydown| [ui| $y ]]
      )
  | `([laydown| [ui| <br> ]]) =>
      `([laydown| !br])
  | `([laydown| [ui| { $x:laydown }]]) =>
      `([laydown| !LDisplay.display $x])
  | `([laydown| [ui| {{for $i in $xs} $render }]]) =>
      `([laydown| !LListDisplay.listDisplay $xs (λ $i => [ui|$render])])
  | `([laydown| [ui| {{forChanges $i in $xs} $render }]]) =>
      `([laydown| !streamChangesUI $xs (λ $i => [ui|$render]) (λ $i => ())])
  | `([laydown| [ui| {{forChanges $i in $xs order by $orderby} $render }]]) =>
      `([laydown| !streamChangesUI $xs (λ $i => [ui|$render]) (λ $i => $orderby)])
  | `([laydown| [ui| b[$b]($c) ]]) =>
      `([laydown| !button [ui|$b] $c])
  | `([laydown| [ui| $x :: $y ]]) =>
      `([laydown| !withLabel [ui|$x] [ui|$y]])

instance [SubEnv ui e] : LFunctor e .signal where
  map := [laydown| λ f x =>  !mapSignal f x]

instance [SubEnv ui e] : LApplicative e .signal where
  pure := pureSignal
  seq := seqSignal

abbrev render : Ltype := .effect .ui ⟶ .effect unit

abbrev flux (α : Ltype) : Ltype :=
  (α ⟶ render ⟶ .effect unit) ⟶ render ⟶ .effect unit

instance [SubEnv ui e] : LFunctor e flux where
  map := [laydown| λ f x =>
    λ cb render => x (λ z r => cb (f z) r) render
  ]

instance [SubEnv ui e] : LApplicative e flux where
  pure := [laydown| λ x => λ cb render => cb x render]
  seq := [laydown| λ appf x =>
    λ cb render => appf (λ f' r => x () (λ x' r => cb (f' x') r) r) render
  ]

instance [SubEnv ui e] : LMonad e flux where
  bind := [laydown| λ x mff =>
    λ cb render => x (λ x' r => mff x' cb render) render
  ]

def lift [SubEnv ui e]: Lexp e (.effect α ⟶ flux α) :=
  [laydown| λ x => λ cb render => do {
    let r ← x,
    cb r render
  }]

def startFlux [SubEnv ui e] : Lexp e (render ⟶ flux empty ⟶ .effect unit) :=
  [laydown| λ r x =>
    x (λ x y => !pure ()) r
  ]

def terminal [SubEnv ui e] : Lexp e (.effect .ui ⟶ flux empty) :=
  [laydown| λ x =>
    λ cb render => render x
  ]
