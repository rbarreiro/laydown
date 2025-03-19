import Laydown.Basic

def jsRuntime : String :=
  "

    const pureEffect = (a) => () => a;
    const bindEffect = (a) => (f) => f(a());
    const seqEffect = (a) => (b) => () => {
      a();
      b();
    }

    const intToString = (a) => a.toString();
    const floatToString = (a) => a.toString();
    const boolToString = (a) => a.toString();

    const listcons = (a) => (b) => b.unshift(a);
    const add = (a) => (b) => a + b;
    const and = (a) => (b) => a && b;
    const or = (a) => (b) => a || b;
    const not = (a) => !a;
    const eq = (a) => (b) => a === b;
    const tupleCons = (a) => (b) => b.unshift(a);
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
  | Lexp.var n _ => n
  | Lexp.parametricVar n _ _ => n
  | Lexp.parametric2Var n _ _ _ => n
  | Lexp.app f a =>  jsGen f ++ "(" ++ jsGen a ++ ")"
  | Lexp.lambda n b =>  "(" ++ n ++ " => " ++ jsGen b ++ ")"
  | Lexp.llet n v b =>  "((" ++ n ++ " => " ++ jsGen b ++ ")(" ++ jsGen v ++ "))"
  | Lexp.pureEffect => "pureEffect"
  | Lexp.bindEffect => "bindEffect"
  | Lexp.seqEffect => "seqEffect"
  | Lexp.intToString => "intToString"
  | Lexp.floatToString => "floatToString"
  | Lexp.boolToString => "boolToString"
  | Lexp.recordGet n r _ => jsGen r ++ ".get(" ++ escapeString n ++ ")"
  | Lexp.listnil => "Immutable.List()"
  | Lexp.listcons => "listcons"
  | Lexp.intAdd => "add"
  | Lexp.floatAdd => "add"
  | Lexp.boolAnd => "and"
  | Lexp.boolOr => "or"
  | Lexp.boolNot => "not"
  | Lexp.boolEq => "eq"
  | Lexp.mk n v _ => "{" ++ n ++ ": " ++ jsGen v ++ "}"
  | Lexp.switchbase n v b => s!"(x => ({v} => {jsGen b})(x[{n}]))"
  | Lexp.switchcons n v b c => s!"(x => x.hasOwnProperty({n}) ? ({v} => {jsGen b})(x[{n}]) : {jsGen c}(x))"
  | Lexp.tupleBase => "Immutable.List()"
  | Lexp.tupleCons => "tupleCons"
  | Lexp.recordnil => "Immutable.Map()"
  | Lexp.recordcons n v r => s!"{jsGen r}.set({escapeString n}, {jsGen v})"
