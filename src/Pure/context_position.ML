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
  val is_visible_proof: Context.generic -> bool
  val if_visible_proof: Context.generic -> ('a -> unit) -> 'a -> unit
  val reported_text: Proof.context -> Position.T -> Markup.T -> string -> string
  val report_text: Proof.context -> Position.T -> Markup.T -> string -> unit
  val report: Proof.context -> Position.T -> Markup.T -> unit
  val reports: Proof.context -> Position.report list -> unit
end;

structure Context_Position: CONTEXT_POSITION =
struct

val visible = Config.bool (Config.declare "Context_Position.visible" (K (Config.Bool true)));
fun is_visible ctxt = Config.get ctxt visible;
val set_visible = Config.put visible;
val restore_visible = set_visible o is_visible;

fun if_visible ctxt f x = if is_visible ctxt then f x else ();

fun is_visible_proof (Context.Proof ctxt) = is_visible ctxt
  | is_visible_proof _ = false;

fun if_visible_proof context f x = if is_visible_proof context then f x else ();

fun reported_text ctxt pos markup txt =
  if is_visible ctxt then Position.reported_text pos markup txt else "";

fun report_text ctxt pos markup txt = Output.report (reported_text ctxt pos markup txt);
fun report ctxt pos markup = report_text ctxt pos markup "";

fun reports ctxt reps = if is_visible ctxt then Position.reports reps else ();

end;
