(*  Title:      Pure/General/history.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Histories of values, with undo and redo, and optional limit.
*)

signature HISTORY =
sig
  type 'a T
  val init: int option -> 'a -> 'a T
  val is_initial: 'a T -> bool
  val current: 'a T -> 'a
  val clear: int -> 'a T -> 'a T
  val undo: 'a T -> 'a T
  val redo: 'a T -> 'a T
  val apply_copy: ('a -> 'a) -> ('a -> 'a) -> 'a T -> 'a T
  val apply: ('a -> 'a) -> 'a T -> 'a T
  val map: ('a -> 'a) -> 'a T -> 'a T
end;

structure History: HISTORY =
struct


(* datatype history *)

datatype 'a T =
  History of 'a * (int option * int * 'a list * 'a list);

fun init lim x = History (x, (lim, 0, [], []));

fun is_initial (History (_, (_, len, _, _))) = len = 0;

fun current (History (x, _)) = x;

fun clear n (History (x, (lim, len, undo_list, redo_list))) =
  History (x, (lim, Int.max (0, len - n), drop (n, undo_list), redo_list));

fun undo (History (_, (_, _, [], _))) = error "No further undo information"
  | undo (History (x, (lim, len, u :: undo_list, redo_list))) =
      History (u, (lim, len - 1, undo_list, x :: redo_list));

fun redo (History (_, (_, _, _, []))) = error "No further redo information"
  | redo (History (x, (lim, len, undo_list, r :: redo_list))) =
      History (r, (lim, len + 1, x :: undo_list, redo_list));

fun push None _ x xs = x :: xs
  | push (Some 0) _ _ _ = []
  | push (Some n) len x xs = if len < n then x :: xs else take (n, x :: xs);

fun apply_copy cp f (History (x, (lim, len, undo_list, _))) =
  let val x' = cp x
  in History (f x, (lim, len + 1, push lim len x' undo_list, [])) end;

fun apply f = apply_copy I f;

fun map f (History (x, hist)) = History (f x, hist);


end;
