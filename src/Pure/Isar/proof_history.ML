(*  Title:      Pure/Isar/proof_history.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Histories of proof states, with undo / redo and prev / back.
*)

signature PROOF_HISTORY =
sig
  type T
  exception FAIL of string
  val init: Proof.state -> T
  val current: T -> Proof.state
  val clear: T -> T
  val undo: T -> T
  val redo: T -> T
  val undos: int -> T -> T
  val redos: int -> T -> T
  val position: T -> int
  val nesting: T -> int
  val prev: T -> T
  val up: T -> T
  val top: T -> T
  val back: T -> T
  val applys: (Proof.state -> Proof.state Seq.seq) -> T -> T
  val applys_open: (Proof.state -> Proof.state Seq.seq) -> T -> T
  val applys_close: (Proof.state -> Proof.state Seq.seq) -> T -> T
  val apply: (Proof.state -> Proof.state) -> T -> T
  val apply_open: (Proof.state -> Proof.state) -> T -> T
  val apply_close: (Proof.state -> Proof.state) -> T -> T
  val apply_cond_open: bool -> (Proof.state -> Proof.state) -> T -> T
end;

structure ProofHistory: PROOF_HISTORY =
struct


(* datatype proof history *)

type node =
 (Proof.state *			(*first result*)
  Proof.state Seq.seq) *	(*alternative results*)
  int;				(*nest level*)

type proof = node * node list;

datatype T = ProofHistory of proof History.T;

exception FAIL of string;

fun app f (ProofHistory x) = ProofHistory (f x);
fun hist_app f = app (History.apply f);


(* generic history operations *)

fun init st = ProofHistory (History.init (((st, Seq.empty), 0), []));
fun current (ProofHistory prf) = fst (fst (fst (History.current prf)));
val clear = app History.clear;
val undo = app History.undo;
val redo = app History.redo;

fun undos n = funpow n undo;
fun redos n = funpow n redo;


(* navigate *)

fun position (ProofHistory prf) = length (snd (History.current prf));
fun nesting (ProofHistory prf) = snd (fst (History.current prf));

fun prev_until msg _ (_, []) = raise FAIL msg
  | prev_until msg pred (_, node :: nodes) =
      if pred node then (node, nodes)
      else prev_until msg pred (node, nodes);

val prev = hist_app (prev_until "no previous proof state" (K true));
fun up prf = hist_app (prev_until "no upper proof state" (fn (_, m) => m < nesting prf)) prf;
val top = hist_app (fn (node, nodes) => (last_elem (node :: nodes), []));


(* backtrack *)

fun back_fun (((_, stq), n), nodes) =
  (case Seq.pull stq of
    None =>
      (case nodes of
        [] => raise FAIL "back: no alternatives"
      | nd :: nds => (writeln "back: trying previous proof state ..."; back_fun (nd, nds)))
  | Some result => ((result, n), nodes));

val back = hist_app back_fun;


(* apply transformer *)

fun gen_apply d f (node as ((st, _), n): node, nodes) =
  (case Seq.pull (f st) of
    None => raise FAIL "empty result sequence -- command failed"
  | Some results => ((results, n + d), node :: nodes));

val applys = hist_app o gen_apply 0;
val applys_open = hist_app o gen_apply 1;
val applys_close = hist_app o gen_apply ~1;

fun apply f = applys (Seq.single o f);
fun apply_open f = applys_open (Seq.single o f);
fun apply_close f = applys_close (Seq.single o f);
fun apply_cond_open do_open f = if do_open then apply_open f else apply f;

end;
