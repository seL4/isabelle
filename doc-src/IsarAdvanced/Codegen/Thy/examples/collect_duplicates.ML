structure ROOT = 
struct

structure Code_Generator = 
struct

type 'a eq = {eq_ : 'a -> 'a -> bool};
fun eq (A_:'a eq) = #eq_ A_;

end; (*struct Code_Generator*)

structure HOL = 
struct

fun op_eq (A_:'a Code_Generator.eq) a b = Code_Generator.eq A_ a b;

end; (*struct HOL*)

structure List = 
struct

fun memberl (A_1_:'a_1 Code_Generator.eq) x (y :: ys) =
  HOL.op_eq A_1_ x y orelse memberl A_1_ x ys
  | memberl (A_1_:'a_1 Code_Generator.eq) x [] = false;

end; (*struct List*)

structure Codegen = 
struct

fun collect_duplicates (A_:'a Code_Generator.eq) xs ys (z :: zs) =
  (if List.memberl A_ z xs
    then (if List.memberl A_ z ys then collect_duplicates A_ xs ys zs
           else collect_duplicates A_ xs (z :: ys) zs)
    else collect_duplicates A_ (z :: xs) (z :: ys) zs)
  | collect_duplicates (A_:'a Code_Generator.eq) y ys [] = y;

end; (*struct Codegen*)

end; (*struct ROOT*)
