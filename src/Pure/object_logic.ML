(*  Title:      Pure/object_logic.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Object logic specific operations.

TODO:
  - theory data instead of hardwired operations (!!);
*)

signature OBJECT_LOGIC =
sig
  val dest_statement: string * term -> (string * term) list
  val dest_main_statement: term -> term
  val setup: (theory -> theory) list
end;

structure ObjectLogic: OBJECT_LOGIC =
struct


fun dest_statement (name, prop) =
  let val concl = Logic.strip_imp_concl prop in
    [(name ^ "_prop", prop), (name ^ "_concl", concl)] @
      (case concl of Const ("Trueprop", _) $ t => [(name, t)] | _ => [])
  end;

fun dest_main_statement t =
  (case Logic.strip_imp_concl t of
    _ $ t => t
  | _ => raise TERM ("dest_main", [t]));


(* FIXME *)
val setup = [];

end;
