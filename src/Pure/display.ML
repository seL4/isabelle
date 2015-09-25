(*  Title:      Pure/display.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Makarius

Printing of theorems, results etc.
*)

signature BASIC_DISPLAY =
sig
  val show_consts: bool Config.T
  val show_hyps_raw: Config.raw
  val show_hyps: bool Config.T
  val show_tags_raw: Config.raw
  val show_tags: bool Config.T
end;

signature DISPLAY =
sig
  include BASIC_DISPLAY
  val pretty_thm_raw: Proof.context -> {quote: bool, show_hyps: bool} -> thm -> Pretty.T
  val pretty_thm: Proof.context -> thm -> Pretty.T
  val pretty_thm_item: Proof.context -> thm -> Pretty.T
  val pretty_thm_global: theory -> thm -> Pretty.T
  val string_of_thm: Proof.context -> thm -> string
  val string_of_thm_global: theory -> thm -> string
end;

structure Display: DISPLAY =
struct

(** options **)

val show_consts = Goal_Display.show_consts;

val show_hyps_raw = Config.declare ("show_hyps", @{here}) (fn _ => Config.Bool false);
val show_hyps = Config.bool show_hyps_raw;

val show_tags_raw = Config.declare ("show_tags", @{here}) (fn _ => Config.Bool false);
val show_tags = Config.bool show_tags_raw;



(** print thm **)

fun pretty_tag (name, arg) = Pretty.strs [name, quote arg];
val pretty_tags = Pretty.list "[" "]" o map pretty_tag;

fun pretty_thm_raw ctxt {quote, show_hyps = show_hyps'} raw_th =
  let
    val show_tags = Config.get ctxt show_tags;
    val show_hyps = Config.get ctxt show_hyps;

    val th = raw_th
      |> perhaps (try (Thm.transfer (Proof_Context.theory_of ctxt)))
      |> perhaps (try Thm.strip_shyps);

    val hyps = if show_hyps then Thm.hyps_of th else Thm.undeclared_hyps (Context.Proof ctxt) th;
    val extra_shyps = Thm.extra_shyps th;
    val tags = Thm.get_tags th;
    val tpairs = Thm.tpairs_of th;

    val q = if quote then Pretty.quote else I;
    val prt_term = q o Syntax.pretty_term ctxt;


    val hlen = length extra_shyps + length hyps + length tpairs;
    val hsymbs =
      if hlen = 0 then []
      else if show_hyps orelse show_hyps' then
        [Pretty.brk 2, Pretty.list "[" "]"
          (map (q o Goal_Display.pretty_flexpair ctxt) tpairs @ map prt_term hyps @
           map (Syntax.pretty_sort ctxt) extra_shyps)]
      else [Pretty.brk 2, Pretty.str ("[" ^ replicate_string hlen "." ^ "]")];
    val tsymbs =
      if null tags orelse not show_tags then []
      else [Pretty.brk 1, pretty_tags tags];
  in Pretty.block (prt_term (Thm.prop_of th) :: (hsymbs @ tsymbs)) end;

fun pretty_thm ctxt = pretty_thm_raw ctxt {quote = false, show_hyps = true};
fun pretty_thm_item ctxt th = Pretty.item [pretty_thm ctxt th];

fun pretty_thm_global thy =
  pretty_thm_raw (Syntax.init_pretty_global thy) {quote = false, show_hyps = false};

val string_of_thm = Pretty.string_of oo pretty_thm;
val string_of_thm_global = Pretty.string_of oo pretty_thm_global;

end;

structure Basic_Display: BASIC_DISPLAY = Display;
open Basic_Display;
