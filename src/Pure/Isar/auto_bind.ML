(*  Title:      Pure/Isar/auto_bind.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Automatic term bindings -- logic specific patterns.

TODO:
  - logic specific theory data instead of hardwired operations (!!);
*)

signature AUTO_BIND =
sig
  val goal: term -> (indexname * term) list
  val facts: term list -> (indexname * term) list
end;

structure AutoBind: AUTO_BIND =
struct

val thesisN = "thesis";
fun thesis_name sfx = (Syntax.binding (thesisN ^ sfx), 0);

fun goal prop =
  let val concl = Logic.strip_imp_concl prop in
    [(thesis_name "_prop", prop), (thesis_name "_concl", concl)] @
      (case concl of Const ("Trueprop", _) $ t => [(thesis_name "", t)] | _ => [])
  end;

fun facts [] = []
  | facts props =
      (case Logic.strip_imp_concl (Library.last_elem props) of
        Const ("Trueprop", _) $ (_ $ t) => [(Syntax.dddot_indexname, t)]
      | _ => []);


end;
