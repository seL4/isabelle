(*  Title:      Pure/Concurrent/par_exn.ML
    Author:     Makarius

Parallel exceptions as flattened results from acyclic graph of
evaluations.  Interrupt counts as neutral element.
*)

signature PAR_EXN =
sig
  val serial: exn -> serial * exn
  val make: exn list -> exn
  val dest: exn -> exn list option
  val release_all: 'a Exn.result list -> 'a list
  val release_first: 'a Exn.result list -> 'a list
end;

structure Par_Exn =
struct

(* identification via serial numbers *)

fun serial exn =
  (case get_exn_serial exn of
    SOME i => (i, exn)
  | NONE => let val i = Library.serial () in (i, set_exn_serial i exn) end);

val exn_ord = rev_order o int_ord o pairself (the o get_exn_serial);


(* parallel exceptions *)

exception Par_Exn of exn list;
  (*non-empty list with unique identified elements sorted by exn_ord;
    no occurrences of Par_Exn or Exn.Interrupt*)

fun par_exns (Par_Exn exns) = exns
  | par_exns exn = if Exn.is_interrupt exn then [] else [#2 (serial exn)];

fun make exns =
  (case Balanced_Tree.make (Ord_List.merge exn_ord) ([] :: map par_exns exns) of
    [] => Exn.Interrupt
  | es => Par_Exn es);

fun dest (Par_Exn exns) = SOME exns
  | dest _ = NONE;


(* parallel results *)

fun all_res results = forall (fn Exn.Res _ => true | _ => false) results;

fun release_all results =
  if all_res results then map Exn.release results
  else raise make (map_filter Exn.get_exn results);

fun release_first results =
  if all_res results then map Exn.release results
  else
    (case get_first
        (fn res => if Exn.is_interrupt_exn res then NONE else Exn.get_exn res) results of
      NONE => Exn.interrupt ()
    | SOME exn => reraise exn);

end;

