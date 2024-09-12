(*  Title:      Pure/context_position.ML
    Author:     Makarius

Context position visibility flag.
*)

signature CONTEXT_POSITION =
sig
  val is_visible_generic: Context.generic -> bool
  val is_visible: Proof.context -> bool
  val is_visible_global: theory -> bool
  val set_visible_generic: bool -> Context.generic -> Context.generic
  val set_visible: bool -> Proof.context -> Proof.context
  val set_visible_global: bool -> theory -> theory
  val is_really_visible: Proof.context -> bool
  val not_really: Proof.context -> Proof.context
  val restore_visible_generic: Context.generic -> Context.generic -> Context.generic
  val restore_visible: Proof.context -> Proof.context -> Proof.context
  val restore_visible_global: theory -> theory -> theory
  val reports_enabled0: unit -> bool
  val reports_enabled_generic: Context.generic -> bool
  val reports_enabled: Proof.context -> bool
  val reports_enabled_global: theory -> bool
  val is_reported_generic: Context.generic -> Position.T -> bool
  val is_reported: Proof.context -> Position.T -> bool
  val is_reported_global: theory -> Position.T -> bool
  val report_generic: Context.generic -> Position.T -> Markup.T -> unit
  val reported_text: Proof.context -> Position.T -> Markup.T -> string -> string
  val report_text: Proof.context -> Position.T -> Markup.T -> string -> unit
  val report: Proof.context -> Position.T -> Markup.T -> unit
  val reports_text: Proof.context -> Position.report_text list -> unit
  val reports_generic: Context.generic -> Position.report list -> unit
  val reports: Proof.context -> Position.report list -> unit
  val reports_global: theory -> Position.report list -> unit
end;

structure Context_Position: CONTEXT_POSITION =
struct

(* visible context *)

val really = Config.declare_bool ("really", Position.none) (K true);
val visible = Config.declare_bool ("visible", Position.none) (K true);

val is_visible_generic = Config.apply_generic visible;
val is_visible = Config.apply visible;
val is_visible_global = Config.apply_global visible;

val set_visible_generic = Config.put_generic visible;
val set_visible = Config.put visible;
val set_visible_global = Config.put_global visible;

val is_really = Config.apply really;
fun is_really_visible ctxt = is_really ctxt andalso is_visible ctxt;
val not_really = Config.put really false;

fun restore_visible_generic context =
  Config.restore_generic really context #>
  Config.restore_generic visible context;

val restore_visible = Context.proof_map o restore_visible_generic o Context.Proof;
val restore_visible_global = Context.theory_map o restore_visible_generic o Context.Theory;


(* PIDE reports *)

fun reports_enabled0 () = Options.default_bool "pide_reports" andalso Print_Mode.PIDE_enabled ();
fun reports_enabled_generic context = reports_enabled0 () andalso is_visible_generic context;
val reports_enabled = reports_enabled_generic o Context.Proof;
val reports_enabled_global = reports_enabled_generic o Context.Theory;

fun is_reported_generic context pos =
  reports_enabled_generic context andalso Position.is_reported pos;

val is_reported = is_reported_generic o Context.Proof;
val is_reported_global = is_reported_generic o Context.Theory;

fun report_generic context pos markup =
  if is_reported_generic context pos then
    Output.report [Position.reported_text pos markup ""]
  else ();

fun reported_text ctxt pos markup txt =
  if is_reported ctxt pos then Position.reported_text pos markup txt else "";

fun report_text ctxt pos markup txt = Output.report [reported_text ctxt pos markup txt];
fun report ctxt pos markup = report_text ctxt pos markup "";

fun reports_text ctxt reps =
  if reports_enabled ctxt then Position.reports_text reps else ();

fun reports_generic context reps =
  if reports_enabled_generic context then Position.reports reps else ();

val reports = reports_generic o Context.Proof;
val reports_global = reports_generic o Context.Theory;

end;
