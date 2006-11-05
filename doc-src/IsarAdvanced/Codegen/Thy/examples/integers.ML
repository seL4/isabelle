structure ROOT = 
struct

structure Codegen = 
struct

fun double_inc a =
  IntInf.+ ((IntInf.* ((2 : IntInf.int), a)), (1 : IntInf.int));

end; (*struct Codegen*)

end; (*struct ROOT*)
