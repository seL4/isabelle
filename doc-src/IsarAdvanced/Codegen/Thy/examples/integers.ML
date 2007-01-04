structure ROOT = 
struct

structure Codegen = 
struct

val double_inc : IntInf.int -> IntInf.int =
  (fn k => IntInf.+ ((IntInf.* ((2 : IntInf.int), k)), (1 : IntInf.int)));

end; (*struct Codegen*)

end; (*struct ROOT*)
