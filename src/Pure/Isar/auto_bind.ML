(*  Title:      Pure/Isar/auto_bind.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Logic specific patterns and automatic term bindings.

Note: the current implementation is not quite 'generic', but works
fine with common object-logics (HOL, FOL, ZF etc.).
*)

signature AUTO_BIND =
sig
  val goal: Sign.sg -> term list -> (indexname * term option) list
  val facts: Sign.sg -> term list -> (indexname * term option) list
  val thesisN: string
end;

structure AutoBind: AUTO_BIND =
struct

(** bindings **)

val thesisN = "thesis";
val thisN = "this";

fun strip_judgment sg = ObjectLogic.drop_judgment sg o Logic.strip_assums_concl;

fun statement_binds sg name prop =
  [((name, 0), Some (Term.list_abs (Logic.strip_params prop, strip_judgment sg prop)))];


(* goal *)

fun goal sg props = statement_binds sg thesisN (Library.last_elem props);


(* facts *)

fun get_arg sg prop =
  (case strip_judgment sg prop of
    _ $ t => Some (Term.list_abs (Logic.strip_params prop, t))
  | _ => None);

fun facts _ [] = []
  | facts sg props =
      let val prop = Library.last_elem props
      in [(Syntax.dddot_indexname, get_arg sg prop)] @ statement_binds sg thisN prop end;


end;
