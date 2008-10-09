(*  Title:      Pure/Concurrent/par_list_dummy.ML
    ID:         $Id$
    Author:     Makarius

Dummy version of parallel list combinators -- plain sequential evaluation.
*)

structure ParList: PAR_LIST =
struct

val map = map;
val get_some = get_first;
val find_some = find_first;
val exists = exists;
val forall = forall;

end;
