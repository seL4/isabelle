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
  val setup: (theory -> theory) list
end;

structure ObjectLogic: OBJECT_LOGIC =
struct


fun dest_statement (name, prop) =
  let val concl = Logic.strip_imp_concl prop in
    [(name ^ "_prop", prop), (name ^ "_concl", concl)] @
      (case concl of Const ("Trueprop", _) $ t => [(name, t)] | _ => [])
  end;


(* FIXME *)
val setup = [];

end;
