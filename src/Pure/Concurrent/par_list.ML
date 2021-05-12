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
  val map': {name: string, sequential: bool} -> ('a -> 'b) -> 'a list -> 'b list
  val map_independent: ('a -> 'b) -> 'a list -> 'b list
  val map: ('a -> 'b) -> 'a list -> 'b list
  val get_some: ('a -> 'b option) -> 'a list -> 'b option
  val find_some: ('a -> bool) -> 'a list -> 'a option
  val exists: ('a -> bool) -> 'a list -> bool
  val forall: ('a -> bool) -> 'a list -> bool
end;

structure Par_List: PAR_LIST =
struct

fun managed_results {name, sequential} f xs =
  if sequential orelse not (Future.relevant xs) then map (Exn.capture f) xs
  else
    Future.forked_results
     {name = if name = "" then "Par_List.map" else name, deps = []}
     (map (fn x => fn () => f x) xs);

fun map' params f xs = Par_Exn.release_first (managed_results params f xs);
fun map f = map' {name = "", sequential = false} f;
fun map_independent f = map (Exn.interruptible_capture f) #> Par_Exn.release_all;

fun get_some f xs =
  let
    exception FOUND of 'b;
    val results =
      managed_results {name = "Par_List.get_some", sequential = false}
        (fn x => (case f x of NONE => () | SOME y => raise FOUND y)) xs;
  in
    (case get_first (fn Exn.Exn (FOUND res) => SOME res | _ => NONE) results of
      NONE => (Par_Exn.release_first results; NONE)
    | some => some)
  end;

fun find_some P = get_some (fn x => if P x then SOME x else NONE);

fun exists P = is_some o find_some P;
fun forall P = not o exists (not o P);

end;
