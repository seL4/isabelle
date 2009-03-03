structure HOL = 
struct

type 'a eq = {eq : 'a -> 'a -> bool};
fun eq (A_:'a eq) = #eq A_;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
fun less_eq (A_:'a ord) = #less_eq A_;
fun less (A_:'a ord) = #less A_;

end; (*struct HOL*)

structure Codegen = 
struct

fun less_eq (A1_, A2_) B_ (x1, y1) (x2, y2) =
  HOL.less A2_ x1 x2 orelse HOL.eq A1_ x1 x2 andalso HOL.less_eq B_ y1 y2;

end; (*struct Codegen*)
