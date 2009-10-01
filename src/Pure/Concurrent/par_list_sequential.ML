(*  Title:      Pure/Concurrent/par_list_sequential.ML
    Author:     Makarius

Dummy version of parallel list combinators -- plain sequential evaluation.
*)

structure Par_List: PAR_LIST =
struct

val map = map;
val get_some = get_first;
val find_some = find_first;
val exists = exists;
val forall = forall;

end;
