(*  Title:      Pure/Isar/auto_bind.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Automatic term bindings -- logic specific patterns.

The implementation below works fine with the more common
object-logics, such as HOL, ZF.
*)

signature AUTO_BIND =
sig
  val goal: term -> (indexname * term option) list
  val facts: string -> term list -> (indexname * term option) list
  val atomic_thesis: term -> (string * term) * term
end;

structure AutoBind: AUTO_BIND =
struct

val thesisN = "thesis";
val thisN = "this";


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
      

end;
