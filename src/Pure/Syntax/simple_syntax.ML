(*  Title:      Pure/Syntax/simple_syntax.ML
    ID:         $Id$
    Author:     Makarius

Simple syntax for types and terms --- for bootstrapping Pure.
*)

signature SIMPLE_SYNTAX =
sig
  val read_typ: string -> typ
  val read_term: string -> term
  val read_prop: string -> term
end;

structure SimpleSyntax: SIMPLE_SYNTAX =
struct

(* scanning tokens *)

local

val eof = Lexicon.EndToken;
fun is_eof tk = tk = Lexicon.EndToken;

val stopper = (eof, is_eof);
val not_eof = not o is_eof;

val lexicon = Scan.make_lexicon
  (map Symbol.explode ["!!", "%", "(", ")", ".", "::", "==", "==>", "=?=", "=>", "CONST"]);

in

fun read scan s =
  (case
      Symbol.explode s |>
      Lexicon.tokenize lexicon false |> filter not_eof |>
      Scan.read stopper scan of
    SOME x => x
  | NONE => error ("Bad input: " ^ quote s));

end;


(* basic scanners *)

fun $$ s = Scan.some (fn Lexicon.Token s' => if s = s' then SOME s else NONE | _ => NONE);
fun enum1 s scan = scan -- Scan.repeat ($$ s |-- scan) >> op ::;
fun enum2 s scan = scan -- Scan.repeat1 ($$ s |-- scan) >> op ::;

val tfree = Scan.some (fn Lexicon.TFreeSy s => SOME s | _ => NONE);
val ident = Scan.some (fn Lexicon.IdentSy s => SOME s | _ => NONE);
val long_ident = Scan.some (fn Lexicon.LongIdentSy s => SOME s | _ => NONE);
val const = long_ident || ident;


(* types *)

(*
  typ  = typ1 => ... => typ1
       | typ1
  typ1 = typ2 const ... const
       | typ2
  typ2 = tfree
       | const
       | ( typ )
*)

fun typ x =
 (enum1 "=>" typ1 >> (op ---> o split_last)) x
and typ1 x =
 (typ2 -- Scan.repeat const >> (fn (T, cs) => fold (fn c => fn U => Type (c, [U])) cs T)) x
and typ2 x =
 (tfree >> (fn a => TFree (a, [])) ||
  const >> (fn c => Type (c, [])) ||
  $$ "(" |-- typ --| $$ ")") x;

val read_typ = read typ;


(* terms *)

(*
  term  = !!ident :: typ. term
        | term1
  term1 = term2 ==> ... ==> term2
        | term2
  term2 = term3 == term2
        | term3 =?= term2
        | term3
  term3 = ident :: typ
        | CONST const :: typ
        | %ident :: typ. term3
        | term4
  term4 = term5 ... term5
        | term5
  term5 = ident
        | CONST const
        | ( term )
*)

local

val constraint = $$ "::" |-- typ;
val var = ident -- constraint;
val bind = var --| $$ ".";

in

fun term env T x =
 ($$ "!!" |-- bind :|-- (fn v =>
   term (v :: env) propT >> (fn B => Term.all (#2 v) $ lambda (Free v) B)) ||
  term1 env T) x
and term1 env T x =
 (enum2 "==>" (term2 env propT) >> foldr1 (fn (A, B) => Term.implies $ A $ B) ||
  term2 env T) x
and term2 env T x =
 (equal env "==" || equal env "=?=" || term3 env T) x
and equal env eq x =
 (term3 env dummyT -- ($$ eq |-- term2 env dummyT) >> (fn (t, u) =>
   Const (eq, Term.fastype_of t --> Term.fastype_of u --> propT) $ t $ u)) x
and term3 env T x =
 (var >> Free ||
  $$ "CONST" |-- const -- constraint >> Const ||
  $$ "%" |-- bind :|-- (fn v => term3 (v :: env) dummyT >> lambda (Free v)) ||
  term4 env T) x
and term4 env T x =
 (term5 env dummyT -- Scan.repeat1 (term5 env dummyT) >> Term.list_comb ||
  term5 env T) x
and term5 env T x =
 (ident >> (fn a => Free (a, the_default T (AList.lookup (op =) env a))) ||
  $$ "CONST" |-- const >> (fn c => Const (c, T)) ||
  $$ "(" |-- term env T --| $$ ")") x;

val read_term = read (term [] dummyT);
val read_prop = read (term [] propT);

end;

end;

