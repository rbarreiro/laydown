import Laydown.Basic

def jsRuntime : String :=
  "
    const createSignal = init => () => {
      let currentValue = init;
      let callbacks = {};
      return Immutable.Map({
        set : (newVal) => {
          curruntValue = newVal;
          Object.values(callbacks).forEach(cb => cb(signal));
        },
        value : {
          subscribe : (cb) => {
            const i = crypto.randomUUID();
            callbacks[i] = cb;
            cb(currentValue);
            return i;
          },
          unsubsribe : (i) => {
            delete callbacks[i];
          },
          get : () => currentValue
        }
      });
    }

    const pureEffect = (a) => () => a;
    const bindEffect = (a) => (f) => f(a());
    const seqEffect = (a) => (b) => () => {
      a();
      b();
    }
  "

def escapeString (s : String) : String :=
  let f := λ s c => match c with
                      | '\\' => s ++ "\\\\"
                      | '\n' => s ++ "\\n"
                      | '"' => s ++ "\\\""
                      | o => s ++ o.toString;
   "\"" ++ String.foldl f "" s ++ "\""

def jsGen : Lexp e α → String
  | Lexp.litStr s => escapeString s
  | Lexp.litInt n => toString n
  | Lexp.litBool b => toString b
  | Lexp.litFloat f => toString f
  | Lexp.litUnit => "()"
  | Lexp.var n _ => n
  | Lexp.parametricVar n _ _ => n
  | Lexp.app f a =>  jsGen f ++ "(" ++ jsGen a ++ ")"
  | Lexp.lambda n b =>  "((" ++ n ++ ") => " ++ jsGen b ++ ")"
  | Lexp.llet n v b =>  "((" ++ n ++ " => " ++ jsGen b ++ ")(" ++ jsGen v ++ "))"
  | Lexp.pureEffect => "pureEffect"
  | Lexp.bindEffect => "bindEffect"
  | Lexp.seqEffect => "seqEffect"
