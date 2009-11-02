(*  Title:      Pure/context_position.ML
    Author:     Makarius

Context position visibility flag.
*)

signature CONTEXT_POSITION =
sig
  val is_visible: Proof.context -> bool
  val set_visible: bool -> Proof.context -> Proof.context
  val restore_visible: Proof.context -> Proof.context -> Proof.context
  val report_visible: Proof.context -> Markup.T -> Position.T -> unit
end;

structure Context_Position: CONTEXT_POSITION =
struct

structure Data = ProofDataFun
(
  type T = bool;
  fun init _ = true;
);

val is_visible = Data.get;
val set_visible = Data.put;
val restore_visible = set_visible o is_visible;

fun report_visible ctxt markup pos =
  if is_visible ctxt then Position.report markup pos else ();

end;
