(* Author: Pascal Stoop, ETH Zurich
   Author: Andreas Lochbihler, Digital Asset *)

structure Termify_Lazy =
struct

fun termify_lazy
  (_: string -> typ -> term) (_: term -> term -> term)  (_: string -> typ -> term -> term)
  (_: typ) (_: typ -> typ -> typ) (_: typ -> typ)
  (term_of: 'a -> term) (T: typ) (x: 'a Lazy.lazy) (_: term) =
  Const ("Code_Lazy.delay", (HOLogic.unitT --> T) --> Type ("Code_Lazy.lazy", [T])) $
  (case Lazy.peek x of
    SOME (Exn.Res x) => absdummy HOLogic.unitT (term_of x)
  | _ => Const ("Pure.dummy_pattern", HOLogic.unitT --> T));

end
