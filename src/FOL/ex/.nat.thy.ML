structure Nat =
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
 "Nat"
 ([],
  [],
  [(["nat"], 0)],
  [(["nat"], ([], "term"))],
  [(["Suc"], "nat=>nat"),
   (["rec"], "[nat, 'a, [nat,'a]=>'a] => 'a")],
  Some (NewSext {
   mixfix =
    [Delimfix("0", "nat", "0"),
     Infixl("+", "[nat, nat] => nat", 60)],
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
 [("induct", "[| P(0);  !!x. P(x) ==> P(Suc(x)) |]  ==> P(n)"),
  ("Suc_inject", "Suc(m)=Suc(n) ==> m=n"),
  ("Suc_neq_0", "Suc(m)=0      ==> R"),
  ("rec_0", "rec(0,a,f) = a"),
  ("rec_Suc", "rec(Suc(m), a, f) = f(m, rec(m,a,f))"),
  ("add_def", "m+n == rec(m, n, %x y. Suc(y))")]

val ax = get_axiom thy

val induct = ax "induct"
val Suc_inject = ax "Suc_inject"
val Suc_neq_0 = ax "Suc_neq_0"
val rec_0 = ax "rec_0"
val rec_Suc = ax "rec_Suc"
val add_def = ax "add_def"


end
end
