(*  Title:      Pure/General/history.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Histories of values, with undo and redo.
*)

signature HISTORY =
sig
  type 'a T
  val init: 'a -> 'a T
  val current: 'a T -> 'a
  val clear: 'a T -> 'a T
  val undo: 'a T -> 'a T
  val redo: 'a T -> 'a T
  val apply: ('a -> 'a) -> 'a T -> 'a T
end;

structure History: HISTORY =
struct


(* datatype history *)

datatype 'a T =
  History of 'a * 'a list * 'a list;

fun init x = History (x, [], []);

fun current (History (x, _, _)) = x;

fun clear (History (x, _, _)) = History (x, [], []);

fun undo (History (_, [], _)) = error "No further undo information"
  | undo (History (x, u :: undo_list, redo_list)) = History (u, undo_list, x :: redo_list);

fun redo (History (_, _, [])) = error "No further redo information"
  | redo (History (x, undo_list, r :: redo_list)) = History (r, x :: undo_list, redo_list);

fun apply f (History (x, undo_list, _)) =
  History (f x, x :: undo_list, []);


end;
