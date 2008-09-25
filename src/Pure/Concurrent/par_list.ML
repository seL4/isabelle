(*  Title:      Pure/Concurrent/par_list.ML
    ID:         $Id$
    Author:     Makarius

Parallel list combinators.

Notes:

  * These combinators only make sense if the operator (function or
    predicate) applied to the list of operands takes considerable
    time.  The overhead of scheduling is significantly higher than
    just traversing the list of operands sequentially.

  * The order of operator application is non-determined.  Watch out
    for operators that have side-effects or raise exceptions!
*)

signature PAR_LIST =
sig
  val release_results: 'a Exn.result list -> 'a list
  val map: ('a -> 'b) -> 'a list -> 'b list
  val get_some: ('a -> 'b option) -> 'a list -> 'b option
  val find_some: ('a -> bool) -> 'a list -> 'a option
  val exists: ('a -> bool) -> 'a list -> bool
  val forall: ('a -> bool) -> 'a list -> bool
end;

structure ParList: PAR_LIST =
struct

(* release results *)

fun proper_exn (Exn.Result _) = NONE
  | proper_exn (Exn.Exn Interrupt) = NONE
  | proper_exn (Exn.Exn exn) = SOME exn;

fun release_results results =
  (case get_first proper_exn results of
    SOME exn => raise exn
  | NONE => List.map Exn.release results);


(* map *)

fun raw_map f xs =
  let val group = TaskQueue.new_group () in
    Future.join_results (List.map (fn x => Future.future (SOME group) [] true (fn () => f x)) xs)
  end;

fun map f xs = release_results (raw_map f xs);


(* get_some etc. *)

fun get_some f xs =
  let
    exception FOUND of 'b option;
    fun found (Exn.Exn (FOUND some)) = some
      | found _ = NONE;
    val results = raw_map (fn x => (case f x of NONE => () | some => raise FOUND some)) xs;
  in
    (case get_first found results of
      SOME y => SOME y
    | NONE =>
        (case get_first proper_exn results of
          SOME exn => raise exn
        | NONE =>
            (case get_first Exn.get_exn results of
              SOME exn => raise exn
            | NONE => NONE)))
  end;

fun find_some P = get_some (fn x => if P x then SOME x else NONE);

fun exists P = is_some o get_some (fn x => if P x then SOME () else NONE);
fun forall P = not o exists (not o P);

end;
