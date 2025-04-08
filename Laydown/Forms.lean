import Laydown.UI

abbrev formElement (α : Ltype) : Ltype :=
  option α ⟶ .signal .bool ⟶ (option α ⟶ .effect unit) ⟶ .effect .ui

def stringForm [se : SubEnv ui e] : Lexp e (formElement .string) :=
  [laydown|
    λ init isSubmited onchange =>
      [ui|
        __ !fromOption "" init __(λ x => onchange Mk(some, x))
      ]
  ]

def keyvalForm [se : SubEnv ui e] (name : String)
: Lexp e (formElement α ⟶  formElement (.record [(name, α)])) :=
  [laydown|
    λ frm init isSubmited onchange =>
      let newInit : option α :=  !(mkRecordGet name HasField.here) <$> init in
      let z := frm newInit isSubmited (λ x => onchange (!(mkSingletonRec name) <$> x)) in
      [ui|
        {!(Lexp.litStr name)} :: z
      ]
  ]

def recordFormCons [se : SubEnv ui e]
    (name : String)
     :  Lexp e (formElement α ⟶ formElement (.record xs) ⟶ formElement (.record ((name, α) :: xs))) :=
  [laydown|
    λ frmTop frmRest init isSubmited onchange =>
      do{
        let newInitTop : option α :=  !(mkRecordGet name HasField.here) <$> init,
        let newInitRest : option (.record xs) :=  (λ x => !(Lexp.recorduncons name (Lexp.var "x" HasGenVar.here)) ) <$> init,
        let topSig ← !createSignal newInitTop,
        let restSig ← !createSignal newInitRest,
        let z := frmTop newInitTop isSubmited topSig~set,
        let r := frmRest newInitRest isSubmited restSig~set,
        --todo sigsubscribe
        [ui|
          {!(Lexp.litStr name)} :: z
          frmRest
        ]
      }
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


declare_syntax_cat ui_form_keyval
declare_syntax_cat ui_form

syntax "[ui_form_keyvals| " ui_form_keyval* "]" : laydown

syntax str "::" ui_form : ui_form_keyval
syntax ui_form_keyval+ : ui_form
syntax "___" : ui_form
syntax "[form|" laydown "|" ui_form "]" : ui
syntax "[formR|" laydown "|" ui_form "]" : ui
syntax "[formElement| " ui_form "]" : ui

macro_rules
  | `([laydown| [ui_form_keyvals| $s:str :: $f:ui_form]]) =>
      `([laydown| !(keyvalForm $s) [ui| [formElement| $f]]])
  | `([laydown| [ui_form_keyvals| $s:str :: $f:ui_form $xs:ui_form_keyval*]]) =>
      `([laydown| !(recordFormCons $s) [ui| [formElement| $f]]] [laydown| [ui_form_keyvals| $xs*]])


macro_rules
  | `([laydown| [ui| [formElement| ___ ] ]]) =>
      `(stringForm)
  | `([laydown| [ui| [formElement|  $xs:ui_form_keyval*]]]) =>
      `([laydown|[ui_form_keyvals| $xs*]])
  | `([laydown| [ui| [form| $s | $x] ]]) =>
      `([laydown| !toForm !none [ui| [formElement| $x ]] (λ c v => $s v) ])
  | `([laydown| [ui| [formR| $s | $x] ]]) =>
      `([laydown| !toFormR !none [ui| [formElement| $x ]] $s ])
