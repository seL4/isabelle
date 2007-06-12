(*  Title:      Pure/Isar/proof_history.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Histories of proof states, with undo / redo and backtracking.
*)

signature PROOF_HISTORY =
sig
  type T
  val position: T -> int
  val init: int option -> Proof.state -> T
  val is_initial: T -> bool
  val map_current: (Proof.state -> Proof.state) -> T -> T
  val current: T -> Proof.state
  val previous: T -> Proof.state option
  val clear: int -> T -> T
  val undo: T -> T
  val redo: T -> T
  val back: T -> T
  val applys: (Proof.state -> Proof.state Seq.seq) -> T -> T
  val apply: (Proof.state -> Proof.state) -> T -> T
end;

structure ProofHistory: PROOF_HISTORY =
struct


(* datatype proof history *)

type node =
  Proof.state *                 (*first result*)
  Proof.state Seq.seq;          (*alternative results*)

type proof = node * int;        (*proof node, proof position*)

datatype T = ProofHistory of proof History.T;

fun app f (ProofHistory x) = ProofHistory (f x);
fun hist_app f = app (History.apply f);
fun hist_map f = app (History.map_current f);

fun position (ProofHistory prf) = snd (History.current prf);


(* generic history operations *)

fun init lim st = ProofHistory (History.init lim ((st, Seq.empty), 0));
fun is_initial (ProofHistory prf) = History.is_initial prf;
fun map_current f = hist_map (apfst (apfst f));
fun current (ProofHistory prf) = fst (fst (History.current prf));
fun previous (ProofHistory prf) = Option.map (fst o fst) (History.previous prf);
val clear = app o History.clear;
val undo = app History.undo;
val redo = app History.redo;


(* backtracking *)

val back = hist_app (fn ((_, stq), position) =>
  (case Seq.pull stq of
    NONE => error "back: no alternatives"
  | SOME result => (result, position)));


(* apply transformer *)

fun applys f = hist_app (fn (node as (st, _), position) =>
  (case Seq.pull (f st) of
    NONE => error "empty result sequence -- proof command failed"
  | SOME results => (results, position + 1)));

fun apply f = applys (Seq.single o f);


end;
