(*  Title:      Pure/Isar/auto_bind.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Automatic bindings of Isar text elements.
*)

signature AUTO_BIND =
sig
  val rule_contextN: string
  val thesisN: string
  val thisN: string
  val goal: theory -> term list -> (indexname * term option) list
  val cases: theory -> term list -> (string * RuleCases.T option) list
  val facts: theory -> term list -> (indexname * term option) list
  val no_facts: (indexname * term option) list
end;

structure AutoBind: AUTO_BIND =
struct

(** bindings **)

val rule_contextN = "rule_context";
val thesisN = "thesis";
val thisN = "this";

fun strip_judgment thy = ObjectLogic.drop_judgment thy o Logic.strip_assums_concl;

fun statement_binds thy name prop =
  [((name, 0), SOME (Term.list_abs (Logic.strip_params prop, strip_judgment thy prop)))];


(* goal *)

fun goal thy [prop] = statement_binds thy thesisN prop
  | goal _ _ = [((thesisN, 0), NONE)];

fun cases _ [] = [(rule_contextN, NONE)]
  | cases thy props = RuleCases.simple (thy, Logic.mk_conjunction_list props) rule_contextN;


(* facts *)

fun get_arg thy prop =
  (case strip_judgment thy prop of
    _ $ t => SOME (Term.list_abs (Logic.strip_params prop, t))
  | _ => NONE);

fun facts _ [] = []
  | facts thy props =
      let val prop = Library.last_elem props
      in [(Syntax.dddot_indexname, get_arg thy prop)] @ statement_binds thy thisN prop end;

val no_facts = [(Syntax.dddot_indexname, NONE), ((thisN, 0), NONE)];

end;
