structure ROOT = 
struct

structure Code_Generator = 
struct

type 'a eq = {eq_ : 'a -> 'a -> bool};
fun eq (A_:'a eq) = #eq_ A_;

end; (*struct Code_Generator*)

structure Product_Type = 
struct

fun eq_prod (A_:'a Code_Generator.eq) (B_:'b Code_Generator.eq) (x1, y1)
  (x2, y2) = Code_Generator.eq A_ x1 x2 andalso Code_Generator.eq B_ y1 y2;

end; (*struct Product_Type*)

structure Orderings = 
struct

type 'a ord = {less_eq_ : 'a -> 'a -> bool, less_ : 'a -> 'a -> bool};
fun less_eq (A_:'a ord) = #less_eq_ A_;
fun less (A_:'a ord) = #less_ A_;

end; (*struct Orderings*)

structure Codegen = 
struct

fun less_prod (B_:'b Code_Generator.eq * 'b Orderings.ord)
  (C_:'c Code_Generator.eq * 'c Orderings.ord) p1 p2 =
  let
    val (x1a, y1a) = p1;
    val (x2a, y2a) = p2;
  in
    Orderings.less (#2 B_) x1a x2a orelse
      Code_Generator.eq (#1 B_) x1a x2a andalso
        Orderings.less (#2 C_) y1a y2a
  end;

fun less_eq_prod (B_:'b Code_Generator.eq * 'b Orderings.ord)
  (C_:'c Code_Generator.eq * 'c Orderings.ord) p1 p2 =
  less_prod ((#1 B_), (#2 B_)) ((#1 C_), (#2 C_)) p1 p2 orelse
    Product_Type.eq_prod (#1 B_) (#1 C_) p1 p2;

end; (*struct Codegen*)

end; (*struct ROOT*)
