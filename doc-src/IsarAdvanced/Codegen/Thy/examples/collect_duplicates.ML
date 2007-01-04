structure ROOT = 
struct

structure Code_Generator = 
struct

type 'a eq = {op_eq_ : 'a -> 'a -> bool};
fun op_eq (A_:'a eq) = #op_eq_ A_;

end; (*struct Code_Generator*)

structure List = 
struct

fun memberl (A_:'a Code_Generator.eq) x (y :: ys) =
  (Code_Generator.op_eq A_ x y orelse memberl A_ x ys)
  | memberl (A_:'a Code_Generator.eq) x [] = false;

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
