(*  Title:      Pure/ML-Systems/ml_stack_polyml-5.6.ML

Maximum stack size (in words) for ML threads -- Poly/ML 5.6, or later.
*)

signature ML_STACK =
sig
  val limit: int option -> Thread.threadAttribute list
end;

structure ML_Stack: ML_STACK =
struct

fun limit m = [Thread.MaximumMLStack m];

end;
