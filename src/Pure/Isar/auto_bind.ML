(*  Title:      Pure/Isar/auto_bind.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Automatic term bindings -- logic specific patterns.
*)

signature AUTO_BIND =
sig
  val goal: term -> (indexname * term option) list
  val facts: string -> term list -> (indexname * term option) list
end;

structure AutoBind: AUTO_BIND =
struct


(* goals *)

fun statement_binds (name, prop) =
  let
    val concl = Logic.strip_assums_concl prop;
    val parms = Logic.strip_params prop;
    fun list_abs tm = foldr (fn ((x, T), t) => Abs (x, T, t)) (parms, tm);

    val env = [(name ^ "_prop", Some prop), (name ^ "_concl", Some (list_abs concl)),
      (name, case concl of Const ("Trueprop", _) $ t => Some (list_abs t) | _ => None)];
  in map (fn (s, t) => ((s, 0), t)) env end;

fun goal prop = statement_binds ("thesis", prop);


(* facts *)

fun dddot_bind prop =
  [(Syntax.dddot_indexname,
      case Logic.strip_imp_concl prop of Const ("Trueprop", _) $ (_ $ t) => Some t | _ => None)];

fun facts _ [] = []
  | facts name props =
      let val prop = Library.last_elem props
      in dddot_bind prop @ statement_binds ("this", prop) end;
      

end;
