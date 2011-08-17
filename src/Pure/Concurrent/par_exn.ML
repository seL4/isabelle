(*  Title:      Pure/Concurrent/par_exn.ML
    Author:     Makarius

Parallel exceptions as flattened results from acyclic graph of
evaluations.  Interrupt counts as neutral element.
*)

signature PAR_EXN =
sig
  val make: exn list -> exn
  val dest: exn -> (serial * exn) list option
  val release_all: 'a Exn.result list -> 'a list
  val release_first: 'a Exn.result list -> 'a list
end;

structure Par_Exn =
struct

(* parallel exceptions *)

exception Par_Exn of (serial * exn) Ord_List.T;

fun exn_ord ((i, _), (j, _)) = int_ord (j, i);

fun par_exns (Par_Exn exns) = SOME exns
  | par_exns exn = if Exn.is_interrupt exn then NONE else SOME [(serial (), exn)];

fun make exns =
  (case map_filter par_exns exns of
    [] => Exn.Interrupt
  | e :: es => Par_Exn (Library.foldl (Ord_List.merge exn_ord) (e, es)));

fun dest (Par_Exn exns) = SOME (rev exns)
  | dest _ = NONE;


(* parallel results *)

fun all_res results = forall (fn Exn.Res _ => true | _ => false) results;

fun release_all results =
  if all_res results then map Exn.release results
  else raise make (map_filter Exn.get_exn results);

fun release_first results = release_all results
  handle Par_Exn ((serial, exn) :: _) => reraise exn;  (* FIXME preserve serial in location (?!?) *)

end;

