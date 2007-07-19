structure HOL = 
struct

type 'a eq = {eq : 'a -> 'a -> bool};
fun eq (A_:'a eq) = #eq A_;

end; (*struct HOL*)

structure List = 
struct

fun member A_ x (y :: ys) = HOL.eq A_ x y orelse member A_ x ys
  | member A_ x [] = false;

end; (*struct List*)

structure Codegen = 
struct

fun collect_duplicates B_ xs ys (z :: zs) =
  (if List.member B_ z xs
    then (if List.member B_ z ys then collect_duplicates B_ xs ys zs
           else collect_duplicates B_ xs (z :: ys) zs)
    else collect_duplicates B_ (z :: xs) (z :: ys) zs)
  | collect_duplicates B_ xs ys [] = xs;

end; (*struct Codegen*)
