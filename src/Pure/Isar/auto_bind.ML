(*  Title:      Pure/Isar/auto_bind.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Automatic term bindings -- logic specific patterns.
*)

signature AUTO_BIND =
sig
  val goal: term -> (indexname * term) list
  val facts: string -> term list -> (indexname * term) list
end;

structure AutoBind: AUTO_BIND =
struct


(* goals *)

fun statement_binds (name, prop) =
  let
    val concl = Logic.strip_imp_concl prop;
    val env = [(name ^ "_prop", prop), (name ^ "_concl", concl)] @
      (case concl of Const ("Trueprop", _) $ t => [(name, t)] | _ => []);
  in map (fn (s, t) => ((Syntax.binding s, 0), t)) env end;

fun goal prop = statement_binds ("thesis", prop);


(* facts *)

fun dddot_bind prop =
  (case Logic.strip_imp_concl prop of
    Const ("Trueprop", _) $ (_ $ t) => [(Syntax.dddot_indexname, t)]
  | _ => []);

fun facts _ [] = []
  | facts name [prop] = statement_binds (name, prop) @ dddot_bind prop
  | facts name props =
      flat (map statement_binds
        (map2 (fn (i, t) => (name ^ string_of_int i, t)) (1 upto length props, props))) @
      dddot_bind (Library.last_elem props);
      

end;
