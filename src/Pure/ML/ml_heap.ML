(*  Title:      Pure/ML/ml_heap.ML
    Author:     Makarius

ML heap operations.
*)

signature ML_HEAP =
sig
  val share_common_data: unit -> unit
  val save_state: string -> unit
end;

structure ML_Heap: ML_HEAP =
struct
  fun share_common_data () = PolyML.shareCommonData PolyML.rootFunction;
  val save_state = PolyML.SaveState.saveState o ML_System.platform_path;
end;
