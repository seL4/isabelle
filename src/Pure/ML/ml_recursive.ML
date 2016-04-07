(*  Title:      Pure/ML/ml_recursive.ML
    Author:     Makarius

ML name space for recursive compiler invocation.
*)

signature ML_RECURSIVE =
sig
  val get: unit -> PolyML.NameSpace.nameSpace option
  val recursive: PolyML.NameSpace.nameSpace -> (unit -> 'a) -> 'a
end;

structure ML_Recursive: ML_RECURSIVE =
struct

val var = Thread_Data.var () : PolyML.NameSpace.nameSpace Thread_Data.var;

fun get () = Thread_Data.get var;
fun recursive space e = Thread_Data.setmp var (SOME space) e ();

end;
