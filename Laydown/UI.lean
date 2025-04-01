import Laydown.Basic

abbrev changes (α : Ltype) : Ltype := .record [
    ("old_val", option α),
    ("new_val", option α)
]

abbrev createSignalTy := λ α =>
  α ⟶ .effect (.record [
    ("set", α ⟶ .effect unit),
    ("update", (α ⟶ α) ⟶ .effect unit),
    ("signal", .signal α),
    ("get", .effect α)
  ])


abbrev ui : Env := [
  ("button", .base (.effect .ui ⟶ .effect unit ⟶ .effect .ui)),
  ("text", .base (.string ⟶ .effect .ui)),
  ("signalUI", .base (.signal (.effect .ui) ⟶ .effect .ui)),
  ("signalListUI", .parametric ( λ α => (.signal (.list α)) ⟶ (α ⟶ .effect .ui) ⟶ .effect .ui)),
  ("concat", .base (.effect .ui ⟶ .effect .ui ⟶ .effect .ui)),
  ("displayList", .base (.list (.effect .ui) ⟶ .effect .ui)),
  ("createSignal", .parametric createSignalTy),
  ("mapSignal", .parametric2 (λ α β => ((α ⟶ β) ⟶ .signal α ⟶ .signal β))),
  ("currentValue", .parametric (λ α => .signal α ⟶ .effect α)),
  ("br", .base (.effect .ui)),
  ("textInput", .base ((.string ⟶ .effect unit) ⟶ .effect .ui)),
  ("streamChangesUI", .parametric (λ α => .stream (changes α) ⟶ (α ⟶ .effect .ui) ⟶ .effect .ui))
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
  let w : Lexp e (.signal (.list α) ⟶ (α ⟶ .effect .ui) ⟶ .effect .ui) :=
            Lexp.parametricVar "signalListUI" α (se.adaptVar p)
  w

def concat [se : SubEnv ui e] : Lexp e (.effect .ui ⟶ .effect .ui ⟶ .effect .ui) :=
  let p : HasVar ui "concat" (.effect .ui ⟶ .effect .ui ⟶ .effect .ui) := by repeat constructor
  Lexp.var "concat" (se.adaptVar p)

def createSignal [se : SubEnv ui e] :
  Lexp e (createSignalTy α) :=
    let p : HasGenVar ui "createSignal"
      (.parametric createSignalTy) :=
            by repeat constructor
  let w : Lexp e (createSignalTy α) :=
            Lexp.parametricVar "createSignal" α (se.adaptVar p)
  w

def mapSignal [se : SubEnv ui e] : Lexp e ((α ⟶ β) ⟶ .signal α ⟶ .signal β) :=
  let p : HasGenVar ui "mapSignal"
    (.parametric2 (λ α β => ((α ⟶ β) ⟶ .signal α ⟶ .signal β))) :=
            by repeat constructor
  let w : Lexp e ((α ⟶ β) ⟶ .signal α ⟶ .signal β) :=
            Lexp.parametric2Var "mapSignal" α  β (se.adaptVar p)
  w

def currentValue [se : SubEnv ui e] :
  Lexp e (.signal α ⟶ .effect α) :=
  let p : HasGenVar ui "currentValue"
    (.parametric (λ α => .signal α ⟶ .effect α)) :=
            by repeat constructor
  let w : Lexp e (.signal α ⟶ .effect α) :=
            Lexp.parametricVar "currentValue" α (se.adaptVar p)
  w

def displayList [se : SubEnv ui e] :
  Lexp e (.list (.effect .ui) ⟶ .effect .ui) :=
  let p : HasVar ui "displayList" (.list (.effect .ui) ⟶ .effect .ui) := by repeat constructor
  Lexp.var "displayList" (se.adaptVar p)

def br [se : SubEnv ui e] : Lexp e (.effect .ui) :=
  let p : HasVar ui "br" (.effect .ui) := by repeat constructor
  Lexp.var "br" (se.adaptVar p)

def textInput [se : SubEnv ui e] : Lexp e ((.string ⟶ .effect unit) ⟶ .effect .ui) :=
  let p : HasVar ui "textInput" ((.string ⟶ .effect unit) ⟶ .effect .ui) := by repeat constructor
  Lexp.var "textInput" (se.adaptVar p)

def streamChangesUI [se : SubEnv ui e] :
  Lexp e (.stream (changes α) ⟶ (α ⟶ .effect .ui) ⟶ .effect .ui) :=
  let p : HasGenVar ui "streamChangesUI"
    (.parametric (λ α => .stream (changes α) ⟶ (α ⟶ .effect .ui) ⟶ .effect .ui)) :=
            by repeat constructor
  let w : Lexp e (.stream (changes α) ⟶ (α ⟶ .effect .ui) ⟶ .effect .ui) :=
            Lexp.parametricVar "streamChangesUI" α (se.adaptVar p)
  w

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

syntax ":" : ui
syntax "___(" laydown ")" : ui
syntax ident : ui
syntax ui ui : ui
syntax "{ " laydown " }" : ui
syntax  "{{for " ident "in" laydown "}"  ui "}": ui
syntax  "{{forChanges " ident "in" laydown "}"  ui "}": ui
syntax "<br>" : ui
syntax "b[" ui "](" laydown ")" : ui
syntax "[ui| " ui "]" : laydown


macro_rules
  | `([laydown| [ui| :]]) =>
      `(Lexp.app text (Lexp.litStr ": "))
  | `([laydown| [ui| ___($c) ]]) =>
      `([laydown| !textInput $c])
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
      `([laydown| !streamChangesUI $xs (λ $i => [ui|$render])])
  | `([laydown| [ui| b[$b]($c) ]]) =>
      `([laydown| !button [ui|$b] $c])
