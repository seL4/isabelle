structure Nat2 =
struct

local
 val parse_ast_translation = []
 val parse_preproc = None
 val parse_postproc = None
 val parse_translation = []
 val print_translation = []
 val print_preproc = None
 val print_postproc = None
 val print_ast_translation = []
in

(**** begin of user section ****)

(**** end of user section ****)

val thy = extend_theory (FOL.thy)
 "Nat2"
 ([],
  [],
  [(["nat"], 0)],
  [(["nat"], ([], "term"))],
  [(["succ", "pred"], "nat => nat")],
  Some (NewSext {
   mixfix =
    [Delimfix("0", "nat", "0"),
     Infixr("+", "[nat,nat] => nat", 90),
     Infixr("<", "[nat,nat] => o", 70),
     Infixr("<=", "[nat,nat] => o", 70)],
   xrules =
    [],
   parse_ast_translation = parse_ast_translation,
   parse_preproc = parse_preproc,
   parse_postproc = parse_postproc,
   parse_translation = parse_translation,
   print_translation = print_translation,
   print_preproc = print_preproc,
   print_postproc = print_postproc,
   print_ast_translation = print_ast_translation}))
 [("pred_0", "pred(0) = 0"),
  ("pred_succ", "pred(succ(m)) = m"),
  ("plus_0", "0+n = n"),
  ("plus_succ", "succ(m)+n = succ(m+n)"),
  ("nat_distinct1", "~ 0=succ(n)"),
  ("nat_distinct2", "~ succ(m)=0"),
  ("succ_inject", "succ(m)=succ(n) <-> m=n"),
  ("leq_0", "0 <= n"),
  ("leq_succ_succ", "succ(m)<=succ(n) <-> m<=n"),
  ("leq_succ_0", "~ succ(m) <= 0"),
  ("lt_0_succ", "0 < succ(n)"),
  ("lt_succ_succ", "succ(m)<succ(n) <-> m<n"),
  ("lt_0", "~ m < 0"),
  ("nat_ind", "[| P(0); ALL n. P(n)-->P(succ(n)) |] ==> All(P)")]

val ax = get_axiom thy

val pred_0 = ax "pred_0"
val pred_succ = ax "pred_succ"
val plus_0 = ax "plus_0"
val plus_succ = ax "plus_succ"
val nat_distinct1 = ax "nat_distinct1"
val nat_distinct2 = ax "nat_distinct2"
val succ_inject = ax "succ_inject"
val leq_0 = ax "leq_0"
val leq_succ_succ = ax "leq_succ_succ"
val leq_succ_0 = ax "leq_succ_0"
val lt_0_succ = ax "lt_0_succ"
val lt_succ_succ = ax "lt_succ_succ"
val lt_0 = ax "lt_0"
val nat_ind = ax "nat_ind"


end
end
