(*  Title:      Pure/ML/ml_heap.ML
    Author:     Makarius

ML heap operations.
*)

signature ML_HEAP =
sig
  val share_common_data: unit -> unit
end;

structure ML_Heap: ML_HEAP =
struct
  fun share_common_data () = PolyML.shareCommonData PolyML.rootFunction;
end;
