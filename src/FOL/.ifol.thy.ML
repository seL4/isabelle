structure IFOL =
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

val thy = extend_theory (Pure.thy)
 "IFOL"
 ([("term", ["logic"])],
  ["term"],
  [(["o"], 0)],
  [(["o"], ([], "logic"))],
  [(["True", "False"], "o")],
  Some (NewSext {
   mixfix =
    [Mixfix("(_)", "o => prop", "Trueprop", [0], 5),
     Infixl("=", "['a,'a] => o", 50),
     Mixfix("~ _", "o => o", "Not", [40], 40),
     Infixr("&", "[o,o] => o", 35),
     Infixr("|", "[o,o] => o", 30),
     Infixr("-->", "[o,o] => o", 25),
     Infixr("<->", "[o,o] => o", 25),
     Binder("ALL ", "('a => o) => o", "All", 0, 10),
     Binder("EX ", "('a => o) => o", "Ex", 0, 10),
     Binder("EX! ", "('a => o) => o", "Ex1", 0, 10)],
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
 [("refl", "a=a"),
  ("subst", "[| a=b;  P(a) |] ==> P(b)"),
  ("conjI", "[| P;  Q |] ==> P&Q"),
  ("conjunct1", "P&Q ==> P"),
  ("conjunct2", "P&Q ==> Q"),
  ("disjI1", "P ==> P|Q"),
  ("disjI2", "Q ==> P|Q"),
  ("disjE", "[| P|Q;  P ==> R;  Q ==> R |] ==> R"),
  ("impI", "(P ==> Q) ==> P-->Q"),
  ("mp", "[| P-->Q;  P |] ==> Q"),
  ("FalseE", "False ==> P"),
  ("True_def", "True == False-->False"),
  ("not_def", "~P == P-->False"),
  ("iff_def", "P<->Q == (P-->Q) & (Q-->P)"),
  ("ex1_def", "EX! x. P(x) == EX x. P(x) & (ALL y. P(y) --> y=x)"),
  ("allI", "(!!x. P(x)) ==> (ALL x.P(x))"),
  ("spec", "(ALL x.P(x)) ==> P(x)"),
  ("exI", "P(x) ==> (EX x.P(x))"),
  ("exE", "[| EX x.P(x);  !!x. P(x) ==> R |] ==> R"),
  ("eq_reflection", "(x=y)   ==> (x==y)"),
  ("iff_reflection", "(P<->Q) ==> (P==Q)")]

val ax = get_axiom thy

val refl = ax "refl"
val subst = ax "subst"
val conjI = ax "conjI"
val conjunct1 = ax "conjunct1"
val conjunct2 = ax "conjunct2"
val disjI1 = ax "disjI1"
val disjI2 = ax "disjI2"
val disjE = ax "disjE"
val impI = ax "impI"
val mp = ax "mp"
val FalseE = ax "FalseE"
val True_def = ax "True_def"
val not_def = ax "not_def"
val iff_def = ax "iff_def"
val ex1_def = ax "ex1_def"
val allI = ax "allI"
val spec = ax "spec"
val exI = ax "exI"
val exE = ax "exE"
val eq_reflection = ax "eq_reflection"
val iff_reflection = ax "iff_reflection"


end
end
