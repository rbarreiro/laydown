import Laydown.Basic

def jsRuntime : String :=
  "

    const pureEffect = a => r => r(a);
    const bindEffect = a => f => r => a(a_ => f(a_)(r));
    const seqEffect = f => x => r => f(f_ => x()(x_ => r(f_(x_))));
    const joinEffects = xs => r => {
      xs.first()(x_ => joinEffects(xs.rest())(rest_ => r(rest_.unshift(x_))));
    }

    const intToString = a => a.toString();
    const floatToString = a => a.toString();
    const boolToString = a => a.toString();

    const listcons = a => b => b.unshift(a);
    const add = a => b => a + b;
    const and = a => b => a && b;
    const or = a => (b) => a || b;
    const not = a => !a;
    const eq = a => b => a === b;
    const tupleCons = a => b => b.unshift(a);
    const listMap = f => xs => xs.map(f);

    let ctxt = Immutable.Map();
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
  | Lexp.var n _ =>s!"ctxt.get({escapeString n})"
  | Lexp.parametricVar n _ _ => s!"ctxt.get({escapeString n})"
  | Lexp.parametric2Var n _ _ _ => s!"ctxt.get({escapeString n})"
  | Lexp.app f a =>  jsGen f ++ "(" ++ jsGen a ++ ")"
  | Lexp.lambda n b => s!"(arg => (ctxt => {jsGen b})(ctxt.set({escapeString n}, arg)))"
  | Lexp.lambdaConst b =>  "(() => " ++ jsGen b ++ ")"
  | Lexp.llet n v b =>  s!"(ctxt => {jsGen b})(ctxt.set({escapeString n}, {jsGen v}))"
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
  | Lexp.mk n v _ => "(Immutable.Map().set(" ++ escapeString n ++ ", " ++ jsGen v ++ "))"
  | Lexp.switchbase n v b =>
    let n_ := escapeString n
    let v_ := escapeString v
    s!"(x => (  ctxt => {jsGen b})( ctxt.set({v_}, x.get({n_}))  ))"
  | Lexp.switchcons n v b c =>
      let n_ := escapeString n
      let v_ := escapeString v
      s!"(x => x.has({n_}) ? (ctxt => {jsGen b})(ctxt.set({v_}, x.get({n_}))) : {jsGen c}(x))"
  | Lexp.tupleBase => "Immutable.List()"
  | Lexp.tupleCons => "tupleCons"
  | Lexp.recordnil => "Immutable.Map()"
  | Lexp.recordcons n v r => s!"({jsGen r}.set({escapeString n}, {jsGen v}))"
  | Lexp.subrecord names r =>
      let names_ := String.intercalate "," (names.map escapeString)
      s!"{jsGen r}.filter((v,k) => [{names_}].includes(k))"
  | Lexp.listMap => "listMap"
  | Lexp.recorduncons n r =>
      s!"{jsGen r}.delete({escapeString n})"
