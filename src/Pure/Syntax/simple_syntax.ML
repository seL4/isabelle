(*  Title:      Pure/Syntax/simple_syntax.ML
    Author:     Makarius

Simple syntax for types and terms --- for bootstrapping Pure.
*)

signature SIMPLE_SYNTAX =
sig
  val read_typ: string -> typ
  val read_term: string -> term
  val read_prop: string -> term
end;

structure Simple_Syntax: SIMPLE_SYNTAX =
struct

(* scanning tokens *)

val lexicon = Scan.make_lexicon
  (map Symbol.explode ["\<And>", "\<lambda>", "(", ")", ".", "::", "\<equiv>", "\<Longrightarrow>", "\<Rightarrow>", "&&&", "CONST"]);

fun read scan s =
  (case
      Symbol_Pos.explode0 s |>
      Lexicon.tokenize lexicon {raw = false} |>
      filter Lexicon.is_proper |>
      Scan.read Lexicon.stopper scan of
    SOME x => x
  | NONE => error ("Malformed input: " ^ quote s));


(* basic scanners *)

fun $$ s =
  Scan.some (fn tok =>
    if Lexicon.is_literal tok andalso s = Lexicon.str_of_token tok then SOME s else NONE);

fun enum1 s scan = scan ::: Scan.repeat ($$ s |-- scan);
fun enum2 s scan = scan ::: Scan.repeat1 ($$ s |-- scan);

fun kind k =
  Scan.some (fn tok =>
    if Lexicon.kind_of_token tok = k then SOME (Lexicon.str_of_token tok) else NONE);

val tfree = kind Lexicon.Type_Ident;
val ident = kind Lexicon.Ident;
val var = kind Lexicon.Var >> (Lexicon.read_indexname o unprefix "?");
val long_ident = kind Lexicon.Long_Ident;

val const = long_ident || ident;


(* types *)

(*
  typ  = typ1 \<Rightarrow> ... \<Rightarrow> typ1
       | typ1
  typ1 = typ2 const ... const
       | typ2
  typ2 = tfree
       | const
       | ( typ )
*)

fun typ x =
 (enum1 "\<Rightarrow>" typ1 >> (op ---> o split_last)) x
and typ1 x =
 (typ2 -- Scan.repeat const >> (fn (T, cs) => fold (fn c => fn U => Type (c, [U])) cs T)) x
and typ2 x =
 (tfree >> (fn a => TFree (a, [])) ||
  const >> (fn c => Type (c, [])) ||
  $$ "(" |-- typ --| $$ ")") x;

val read_typ = read typ;


(* terms *)

(*
  term  = \<And>ident :: typ. term
        | term1
  term1 = term2 \<Longrightarrow> ... \<Longrightarrow> term2
        | term2
  term2 = term3 \<equiv> term2
        | term3 &&& term2
        | term3
  term3 = ident :: typ
        | var :: typ
        | CONST const :: typ
        | \<lambda>ident :: typ. term3
        | term4
  term4 = term5 ... term5
        | term5
  term5 = ident
        | var
        | CONST const
        | ( term )
*)

local

val constraint = $$ "::" |-- typ;
val idt = ident -- constraint;
val bind = idt --| $$ ".";

fun term env T x =
 ($$ "\<And>" |-- bind :|-- (fn v => term (v :: env) propT >> (Logic.all (Free v))) ||
  term1 env T) x
and term1 env T x =
 (enum2 "\<Longrightarrow>" (term2 env propT) >> foldr1 Logic.mk_implies ||
  term2 env T) x
and term2 env T x =
 (equal env ||
  term3 env propT -- ($$ "&&&" |-- term2 env propT) >> Logic.mk_conjunction ||
  term3 env T) x
and equal env x =
 (term3 env dummyT -- ($$ "\<equiv>" |-- term2 env dummyT) >> (fn (t, u) =>
   Const ("Pure.eq", Term.fastype_of t --> Term.fastype_of u --> propT) $ t $ u)) x
and term3 env T x =
 (idt >> Free ||
  var -- constraint >> Var ||
  $$ "CONST" |-- const -- constraint >> Const ||
  $$ "\<lambda>" |-- bind :|-- (fn v => term3 (v :: env) dummyT >> lambda (Free v)) ||
  term4 env T) x
and term4 env T x =
 (term5 env dummyT -- Scan.repeat1 (term5 env dummyT) >> Term.list_comb ||
  term5 env T) x
and term5 env T x =
 (ident >> (fn a => Free (a, the_default T (AList.lookup (op =) env a))) ||
  var >> (fn xi => Var (xi, T)) ||
  $$ "CONST" |-- const >> (fn c => Const (c, T)) ||
  $$ "(" |-- term env T --| $$ ")") x;

fun read_tm T s =
  let
    val t = read (term [] T) s
      handle ERROR msg => cat_error ("Malformed input " ^ quote s) msg;
  in
    if can (Term.map_types Term.no_dummyT) t then t
    else error ("Unspecified types in input: " ^ quote s)
  end;

in

val read_term = read_tm dummyT;
val read_prop = read_tm propT;

end;

end;

