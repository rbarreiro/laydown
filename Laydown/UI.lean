import Laydown.Basic

abbrev createSignalTy := λ α =>
  α ⟶ .effect (.record [
    ("set", α ⟶ .effect unit),
    ("update", (α ⟶ α) ⟶ .effect unit),
    ("signal", .signal α)
  ])


abbrev ui : Env := [
  ("button", .base (.effect .ui ⟶ .effect unit ⟶ .effect .ui)),
  ("text", .base (.string ⟶ .effect .ui)),
  ("signalText", .base (.signal .string ⟶ .effect .ui)),
  ("concat", .base (.effect .ui ⟶ .effect .ui ⟶ .effect .ui)),
  ("createSignal", .parametric createSignalTy),
  ("mapSignal", .parametric2 (λ α β => ((α ⟶ β) ⟶ .signal α ⟶ .signal β))),
  ("currentValue", .parametric (λ α => .signal α ⟶ .effect α)),
  ("br", .base (.effect .ui))
]


def button [se : SubEnv ui e] : Lexp e (.effect .ui ⟶ .effect unit ⟶ .effect .ui) :=
  let p : HasVar ui "button" (.effect .ui ⟶ .effect unit ⟶.effect .ui) := by repeat constructor
  Lexp.var "button" (se.adaptVar p)

def text [se : SubEnv ui e] : Lexp e (.string ⟶ .effect .ui) :=
  let p : HasVar ui "text" (.string ⟶ .effect .ui) := by repeat constructor
  Lexp.var "text" (se.adaptVar p)

def signalText [se : SubEnv ui e] : Lexp e (.signal .string ⟶ .effect .ui) :=
  let p : HasVar ui "signalText" (.signal .string ⟶ .effect .ui) := by repeat constructor
  Lexp.var "signalText" (se.adaptVar p)

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

def br [se : SubEnv ui e] : Lexp e (.effect .ui) :=
  let p : HasVar ui "br" (.effect .ui) := by repeat constructor
  Lexp.var "br" (se.adaptVar p)

class LDisplay (α : Ltype) where
  display [SubEnv ui e] : Lexp e (α ⟶ .effect .ui)

instance : LDisplay Ltype.string where
  display := text

instance : LDisplay (.signal .string) where
  display := signalText

instance : LDisplay (.signal .int) where
  display := [laydown| λ x => !LDisplay.display ((!mapSignal !toString) x)]

declare_syntax_cat ui

syntax ":" : ui
syntax ident : ui
syntax ui ui : ui
syntax "{ " laydown " }" : ui
syntax "<br>" : ui
syntax "b[" ui "]" "(" laydown ")" : ui
syntax "[ui| " ui "]" : laydown


macro_rules
  | `([laydown| [ui| :]]) => `(Lexp.app text (Lexp.litStr ": "))
  | `([laydown| [ui| $txt:ident ]]) => `( Lexp.app
                                              text
                                              (Lexp.litStr ($(Lean.quote (toString txt.getId)) ++ " "))
     )
  | `([laydown| [ui| $x:ui $y:ui ]]) => `(
        Lexp.app
          (Lexp.app
            concat
            [laydown| [ui| $x ]]
          )
          [laydown| [ui| $y ]]
      )
  | `([laydown| [ui| <br> ]]) => `([laydown| !br])
  | `([laydown| [ui| { $x:laydown }]]) => `([laydown| !LDisplay.display $x])
  | `([laydown| [ui| b[$b]($c) ]]) => `([laydown| !button [ui|$b] $c])
