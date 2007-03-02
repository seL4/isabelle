structure ROOT = 
struct

structure Orderings = 
struct

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
fun less_eq (A_:'a ord) = #less_eq A_;
fun less (A_:'a ord) = #less A_;

end; (*struct Orderings*)

structure Code_Generator = 
struct

type 'a eq = {op_eq : 'a -> 'a -> bool};
fun op_eq (A_:'a eq) = #op_eq A_;

end; (*struct Code_Generator*)

structure Codegen = 
struct

fun less_eq_prod (A1_, A2_) B_ (x1, y1) (x2, y2) =
  Orderings.less A2_ x1 x2 orelse
    Code_Generator.op_eq A1_ x1 x2 andalso Orderings.less_eq B_ y1 y2;

end; (*struct Codegen*)

end; (*struct ROOT*)
