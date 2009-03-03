structure Example = 
struct

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun rev xs = foldl (fn xsa => fn x => x :: xsa) [] xs;

fun list_case f1 f2 (a :: lista) = f2 a lista
  | list_case f1 f2 [] = f1;

datatype 'a queue = AQueue of 'a list * 'a list;

val empty : 'a queue = AQueue ([], [])

fun dequeue (AQueue ([], [])) = (NONE, AQueue ([], []))
  | dequeue (AQueue (xs, y :: ys)) = (SOME y, AQueue (xs, ys))
  | dequeue (AQueue (v :: va, [])) =
    let
      val y :: ys = rev (v :: va);
    in
      (SOME y, AQueue ([], ys))
    end;

fun enqueue x (AQueue (xs, ys)) = AQueue (x :: xs, ys);

end; (*struct Example*)
