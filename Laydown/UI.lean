import Laydown.Basic

abbrev ui : Env := [
  ("button", .base (.string ⟶ .effect .unit ⟶ .effect .ui)),
  ("text", .base (.string ⟶ .effect .ui)),
  ("signalText", .base (.signal .string ⟶ .effect .ui)),
  ("concat", .base (.effect .ui ⟶ .effect .ui ⟶ .effect .ui)),
  ("createSignal", .parametric (λ α => α ⟶ .effect (.record [("set", α ⟶ .effect .unit), ("value", .signal α)])))
]


def button [se : SubEnv ui e] : Lexp e (.string ⟶ .effect .unit ⟶ .effect .ui) :=
  let p : HasVar ui "button" (.string ⟶ .effect .unit ⟶.effect .ui) := by repeat constructor
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
  Lexp e (α ⟶ .effect (.record [("set", α ⟶ .effect .unit), ("value", .signal α)])) :=
  let p : HasGenVar ui "createSignal"
    (.parametric (λ α => α ⟶ .effect (.record [("set", α ⟶ .effect .unit), ("value", .signal α)]))) :=
            by repeat constructor
  let w : Lexp e (α ⟶ .effect (.record [("set", α ⟶ .effect .unit), ("value", .signal α)])) :=
            Lexp.parametricVar "createSignal" α (se.adaptVar p)
  w


class LDisplay (α : Ltype) where
  display [SubEnv ui e] : Lexp e (α ⟶ .effect .ui)

instance : LDisplay Ltype.string where
  display := text

instance : LDisplay (.signal .string) where
  display := signalText

declare_syntax_cat ui

syntax ident : ui
syntax ui ui : ui
syntax "{ " laydown " }" : ui
syntax "[ui| " ui "]" : laydown


macro_rules
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
  | `([laydown| [ui| { $x:laydown }]]) => `([laydown| !display $x])
