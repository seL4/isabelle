(*  Title:      Pure/RAW/ml_stack_dummy.ML

Maximum stack size (in words) for ML threads -- dummy version.
*)

signature ML_STACK =
sig
  val limit: int option -> Thread.threadAttribute list
end;

structure ML_Stack: ML_STACK =
struct

fun limit (_: int option) : Thread.threadAttribute list = [];

end;
