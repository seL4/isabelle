(*  Title:      Pure/Isar/proof_history.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Histories of proof states, with undo / redo and prev / back.
*)

signature PROOF_HISTORY =
sig
  type T
  exception FAIL of string
  val position: T -> int
  val init: int option -> Proof.state -> T
  val is_initial: T -> bool
  val current: T -> Proof.state
  val clear: T -> T
  val undo: T -> T
  val redo: T -> T
  val back: bool -> T -> T
  val applys: (Proof.state -> Proof.state Seq.seq) -> T -> T
  val apply: (Proof.state -> Proof.state) -> T -> T
end;

structure ProofHistory: PROOF_HISTORY =
struct


(* datatype proof history *)

type node =
  Proof.state *			(*first result*)
  Proof.state Seq.seq; 		(*alternative results*)

type proof = node * node list;

datatype T = ProofHistory of proof History.T;

exception FAIL of string;

fun app f (ProofHistory x) = ProofHistory (f x);
fun hist_app f = app (History.apply f);

fun position (ProofHistory prf) = length (snd (History.current prf));


(* generic history operations *)

fun init lim st = ProofHistory (History.init lim ((st, Seq.empty), []));
fun is_initial (ProofHistory prf) = History.is_initial prf;
fun current (ProofHistory prf) = fst (fst (History.current prf));
val clear = app History.clear;
val undo = app History.undo;
val redo = app History.redo;


(* backtrack *)

fun back_fun recur ((_, stq), nodes) =
  (case Seq.pull stq of
    None =>
      if recur andalso not (null nodes) then
        (writeln "back: trying previous proof state ..."; back_fun recur (hd nodes, tl nodes))
      else raise FAIL "back: no alternatives"
  | Some result => (result, nodes));

val back = hist_app o back_fun;


(* apply transformer *)

fun applys f = hist_app (fn (node as (st, _), nodes) =>
  (case Seq.pull (f st) of
    None => raise FAIL "empty result sequence -- proof command failed"
  | Some results => (results, node :: nodes)));

fun apply f = applys (Seq.single o f);


end;
