import Laydown.UI

abbrev formElement (α : Ltype) : Ltype :=
  option α ⟶ .signal .bool ⟶ (option α ⟶ .effect unit) ⟶ .effect .ui

def stringForm [se : SubEnv ui e] : Lexp e (formElement .string) :=
  [laydown|
    λ init isSubmited onchange =>
      [ui|
        _ !fromOption "" init _(λ x => onchange Mk(some, x))
      ]
  ]

def toForm [se : SubEnv ui e] : Lexp e (
    option α ⟶ formElement α ⟶ (formSubmitContext ⟶ option α ⟶ .effect unit) ⟶ .effect .ui
  ) :=
  [laydown|
    λ init frmElem onsubmit => do {
      let isSubmited ← !createSignal False,
      let currentValue ← !createSignal init,
      let fe := frmElem init isSubmited~signal currentValue~set,
      !form (λ c => do{let v ← currentValue~get, isSubmited~set True, onsubmit c v}) fe
    }
  ]

def toFormR [se : SubEnv ui e] : Lexp e (
    option α ⟶ formElement α ⟶ (option α ⟶ .effect unit) ⟶ .effect .ui
  ) :=
  [laydown|
    λ init frmElem onsubmit => !toForm init frmElem (λ c v => do {c~reset,onsubmit v})
  ]


declare_syntax_cat ui_form

syntax "___" : ui_form
syntax "[form|" laydown "|" ui_form "]" : ui
syntax "[formR|" laydown "|" ui_form "]" : ui
syntax "[formElement| " ui_form "]" : ui


macro_rules
  | `([laydown| [ui| [formElement| ___ ] ]]) =>
      `(stringForm)
  | `([laydown| [ui| [form| $s | $x] ]]) =>
      `([laydown| !toForm !none [ui| [formElement| $x ]] (λ c v => $s v) ])
  | `([laydown| [ui| [formR| $s | $x] ]]) =>
      `([laydown| !toFormR !none [ui| [formElement| $x ]] $s ])
