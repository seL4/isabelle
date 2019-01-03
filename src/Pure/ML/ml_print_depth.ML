(*  Title:      Pure/ML/ml_print_depth.ML
    Author:     Makarius

Print depth for ML toplevel pp: context option with global default.
*)

signature ML_PRINT_DEPTH =
sig
  val set_print_depth: int -> unit
  val print_depth: int Config.T
  val get_print_depth: unit -> int
end;

structure ML_Print_Depth: ML_PRINT_DEPTH =
struct

val set_print_depth = ML_Print_Depth.set_print_depth;

val print_depth =
  Config.declare_int ("ML_print_depth", \<^here>) (fn _ => ML_Print_Depth.get_print_depth ());

fun get_print_depth () =
  (case Context.get_generic_context () of
    NONE => ML_Print_Depth.get_print_depth ()
  | SOME context => Config.get_generic context print_depth);

end;
