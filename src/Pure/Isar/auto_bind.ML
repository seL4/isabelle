(*  Title:      Pure/Isar/auto_bind.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Automatic term bindings -- logic specific patterns.

Note: the current implementation is not quite 'generic', but works
fine with the more common object-logics (HOL, FOL, ZF etc.).
*)

signature AUTO_BIND =
sig
  val goal: term -> (indexname * term option) list
  val facts: string -> term list -> (indexname * term option) list
  val atomic_thesis: term -> (string * term) * term
  val add_judgment: bstring * string * mixfix -> theory -> theory
  val add_judgment_i: bstring * typ * mixfix -> theory -> theory
end;

structure AutoBind: AUTO_BIND =
struct

val thesisN = "thesis";
val thisN = "this";


(** bindings **)

(* goal *)

fun statement_binds (name, prop) =
  let
    val concl = Logic.strip_assums_concl prop;
    val parms = Logic.strip_params prop;
    fun list_abs tm = foldr (fn ((x, T), t) => Abs (x, T, t)) (parms, tm);

    val env = [(name ^ "_prop", Some prop), (name ^ "_concl", Some (list_abs concl)),
      (name, case concl of Const ("Trueprop", _) $ t => Some (list_abs t) | _ => None)];
  in map (fn (s, t) => ((s, 0), t)) env end;

fun goal prop = statement_binds (thesisN, prop);


(* facts *)

fun dddot_bind prop =
  [(Syntax.dddot_indexname,
      case Logic.strip_imp_concl prop of Const ("Trueprop", _) $ (_ $ t) => Some t | _ => None)];

fun facts _ [] = []
  | facts name props =
      let val prop = Library.last_elem props
      in dddot_bind prop @ statement_binds (thisN, prop) end;


(* atomic_thesis *)

fun mk_free t = Free (thesisN, Term.fastype_of t);

fun atomic_thesis ((c as Const ("Trueprop", _)) $ t) = ((thesisN, t), c $ mk_free t)
  | atomic_thesis t = ((thesisN, t), mk_free t);


(** judgment **)

fun gen_add_judgment add args = PureThy.local_path o add [args] o PureThy.global_path;

val add_judgment = gen_add_judgment Theory.add_consts;
val add_judgment_i = gen_add_judgment Theory.add_consts_i;


end;
