(*  Title:      Pure/Concurrent/par_list.ML
    Author:     Makarius

Parallel list combinators.

Notes:

  * These combinators only make sense if the operator (function or
    predicate) applied to the list of operands takes considerable
    time.  The overhead of scheduling is significantly higher than
    just traversing the list of operands sequentially.

  * The order of operator application is non-deterministic.  Watch out
    for operators that have side-effects or raise exceptions!
*)

signature PAR_LIST =
sig
  val map: ('a -> 'b) -> 'a list -> 'b list
  val get_some: ('a -> 'b option) -> 'a list -> 'b option
  val find_some: ('a -> bool) -> 'a list -> 'a option
  val exists: ('a -> bool) -> 'a list -> bool
  val forall: ('a -> bool) -> 'a list -> bool
end;

structure Par_List: PAR_LIST =
struct

fun raw_map f xs =
  if Future.enabled () then
    let val group = Task_Queue.new_group ()
    in Future.join_results (map (fn x => Future.fork_group group (fn () => f x)) xs) end
  else map (Exn.capture f) xs;

fun map f xs = Exn.release_first (raw_map f xs);

fun get_some f xs =
  let
    exception FOUND of 'b option;
    fun found (Exn.Exn (FOUND some)) = some
      | found _ = NONE;
    val results = raw_map (fn x => (case f x of NONE => () | some => raise FOUND some)) xs;
  in
    (case get_first found results of
      SOME y => SOME y
    | NONE => (Exn.release_first results; NONE))
  end;

fun find_some P = get_some (fn x => if P x then SOME x else NONE);

fun exists P = is_some o get_some (fn x => if P x then SOME () else NONE);
fun forall P = not o exists (not o P);

end;
