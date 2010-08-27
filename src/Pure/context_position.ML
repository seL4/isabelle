(*  Title:      Pure/context_position.ML
    Author:     Makarius

Context position visibility flag.
*)

signature CONTEXT_POSITION =
sig
  val is_visible: Proof.context -> bool
  val set_visible: bool -> Proof.context -> Proof.context
  val restore_visible: Proof.context -> Proof.context -> Proof.context
  val if_visible: Proof.context -> ('a -> unit) -> 'a -> unit
  val report_text: Proof.context -> Markup.T -> Position.T -> string -> unit
  val report: Proof.context -> Markup.T -> Position.T -> unit
end;

structure Context_Position: CONTEXT_POSITION =
struct

structure Data = Proof_Data
(
  type T = bool;
  fun init _ = true;
);

val is_visible = Data.get;
val set_visible = Data.put;
val restore_visible = set_visible o is_visible;

fun if_visible ctxt f x = if is_visible ctxt then f x else ();

fun report_text ctxt markup pos txt =
  if is_visible ctxt then Position.report_text markup pos txt else ();

fun report ctxt markup pos = report_text ctxt markup pos "";

end;
