structure FOL =
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

val thy = extend_theory (IFOL.thy)
 "FOL"
 ([],
  [],
  [],
  [],
  [],
  None)
 [("classical", "(~P ==> P) ==> P")]

val ax = get_axiom thy

val classical = ax "classical"


end
end
