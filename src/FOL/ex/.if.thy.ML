structure If =
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
 "If"
 ([],
  [],
  [],
  [],
  [(["if"], "[o,o,o]=>o")],
  None)
 [("if_def", "if(P,Q,R) == P&Q | ~P&R")]

val ax = get_axiom thy

val if_def = ax "if_def"


end
end
