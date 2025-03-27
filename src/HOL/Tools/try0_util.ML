(* Title:      HOL/Tools/try0_hol.ML
   Author:     Jasmin Blanchette, LMU Muenchen
   Author:     Martin Desharnais, LMU Muenchen
   Author:     Fabian Huch, TU Muenchen

General-purpose functions used by Try0.
*)

signature TRY0_UTIL =
sig
  val silence_methods : bool -> Proof.context -> Proof.context
  val string_of_xref : Try0.xref -> string
  val apply_raw_named_method : string -> bool -> (Try0.modifier * string) list ->
    Time.time option -> Try0.tagged_xref list -> Proof.state -> Try0.result option
end

structure Try0_Util : TRY0_UTIL = struct

(* Makes reconstructor tools as silent as possible. The "set_visible" calls suppresses "Unification
   bound exceeded" warnings and the like. *)
fun silence_methods debug =
  Config.put Metis_Tactic.verbose debug
  #> not debug ? (fn ctxt =>
      ctxt
      |> Simplifier_Trace.disable
      |> Context_Position.set_visible false
      |> Config.put Unify.unify_trace false
      |> Config.put Argo_Tactic.trace "none")

fun string_of_xref ((xref, args) : Try0.xref) =
  (case xref of
    Facts.Fact literal => literal |> Symbol_Pos.explode0 |> Symbol_Pos.implode |> cartouche
  | _ =>
      Facts.string_of_ref xref) ^ implode
        (map (enclose "[" "]" o Pretty.unformatted_string_of o Token.pretty_src \<^context>) args)

local

fun add_attr_text (tagged : Try0.tagged_xref list) (tag, src) s =
  let
    val fs = tagged
      |> map_filter (fn (xref, tags) =>
        if member (op =) tags tag then
          SOME (string_of_xref xref)
        else
          NONE)
  in if null fs then s else s ^ " " ^ (if src = "" then "" else src ^ ": ") ^ implode_space fs end

fun attrs_text tags (tagged : Try0.tagged_xref list) =
  "" |> fold (add_attr_text tagged) tags

fun parse_method ctxt s =
  enclose "(" ")" s
  |> Token.explode (Thy_Header.get_keywords' ctxt) Position.start
  |> filter Token.is_proper
  |> Scan.read Token.stopper Method.parse
  |> (fn SOME (Method.Source src, _) => src | _ => raise Fail "expected Source")

fun run_tac timeout_opt tac st =
  let val with_timeout =
    (case timeout_opt of SOME timeout => Timeout.apply_physical timeout | NONE => I)
  in with_timeout (Seq.pull o tac) st |> Option.map fst end

val num_goals = Thm.nprems_of o #goal o Proof.goal

fun apply_recursive recurse elapsed0 timeout_opt apply st =
  (case Timing.timing (Option.join o try (run_tac timeout_opt apply)) st of
    ({elapsed, ...}, SOME st') =>
      if recurse andalso num_goals st' > 0 andalso num_goals st' < num_goals st then
        let val timeout_opt1 = (Option.map (fn timeout => timeout - elapsed) timeout_opt)
        in apply_recursive recurse (elapsed0 + elapsed) timeout_opt1 apply st' end
      else (elapsed0 + elapsed, st')
   |_ => (elapsed0, st))

in

fun apply_raw_named_method (name : string) all_goals attrs timeout_opt
  (tagged : Try0.tagged_xref list) (st : Proof.state) : Try0.result option =
  let
    val st = Proof.map_contexts (silence_methods false) st
    val unused =
      tagged
      |> filter
        (fn (_, tags) => not (null tags) andalso null (inter (op =) tags (attrs |> map fst)))
      |> map fst

    val attrs = attrs_text attrs tagged

    val ctxt = Proof.context_of st

    val text =
      name ^ attrs
      |> parse_method ctxt
      |> Method.method_cmd ctxt
      |> Method.Basic
      |> (fn m => Method.Combinator (Method.no_combinator_info, Method.Select_Goals 1, [m]))

    val apply =
      Proof.using [Attrib.eval_thms ctxt unused |> map (rpair [] o single)]
      #> Proof.refine text #> Seq.filter_results
    val num_before = num_goals st
    val multiple_goals = all_goals andalso num_before > 1
    val (time, st') = apply_recursive multiple_goals Time.zeroTime timeout_opt apply st
    val num_after = num_goals st'
    val select = "[" ^ string_of_int (num_before - num_after)  ^ "]"
    val unused = implode_space (unused |> map string_of_xref)
    val command =
      (if unused <> "" then "using " ^ unused ^ " " else "") ^
      (if num_after = 0 then "by " else "apply ") ^
      (name ^ attrs |> attrs <> "" ? enclose "(" ")") ^
      (if multiple_goals andalso num_after > 0 then select else "")
  in
    if num_before > num_after then
      SOME {name = name, command = command, time = time, state = st'}
    else NONE
  end

end

end