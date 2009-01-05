structure Example = 
struct

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun rev xs = foldl (fn xsa => fn x => x :: xsa) [] xs;

fun list_case f1 f2 (a :: lista) = f2 a lista
  | list_case f1 f2 [] = f1;

datatype 'a queue = Queue of 'a list * 'a list;

val empty : 'a queue = Queue ([], [])

fun dequeue (Queue ([], [])) = (NONE, Queue ([], []))
  | dequeue (Queue (xs, y :: ys)) = (SOME y, Queue (xs, ys))
  | dequeue (Queue (v :: va, [])) =
    let
      val y :: ys = rev (v :: va);
    in
      (SOME y, Queue ([], ys))
    end;

fun enqueue x (Queue (xs, ys)) = Queue (x :: xs, ys);

end; (*struct Example*)
