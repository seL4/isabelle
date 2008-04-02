structure HOL = 
struct

type 'a eq = {eq : 'a -> 'a -> bool};
fun eq (A_:'a eq) = #eq A_;

fun eqop A_ a = eq A_ a;

end; (*struct HOL*)

structure List = 
struct

fun member A_ x (y :: ys) =
  (if HOL.eqop A_ y x then true else member A_ x ys)
  | member A_ x [] = false;

end; (*struct List*)

structure Codegen = 
struct

fun collect_duplicates A_ xs ys (z :: zs) =
  (if List.member A_ z xs
    then (if List.member A_ z ys then collect_duplicates A_ xs ys zs
           else collect_duplicates A_ xs (z :: ys) zs)
    else collect_duplicates A_ (z :: xs) (z :: ys) zs)
  | collect_duplicates A_ xs ys [] = xs;

end; (*struct Codegen*)
