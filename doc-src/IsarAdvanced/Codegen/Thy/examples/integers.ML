structure ROOT = 
struct

structure Codegen = 
struct

fun double_inc k =
  IntInf.+ ((IntInf.* ((2 : IntInf.int), k)), (1 : IntInf.int));

end; (*struct Codegen*)

end; (*struct ROOT*)
