(* Title:      HOL/Tools/try0_hol.ML
   Author:     Jasmin Blanchette, LMU Muenchen
   Author:     Martin Desharnais, LMU Muenchen
   Author:     Fabian Huch, TU Muenchen

General-purpose functions used by Try0.
*)

signature TRY0_UTIL =
sig
  val string_of_xref : Try0.xref -> string

  type facts_prefixes =
    {usings: string,
     simps : string,
     intros : string,
     elims : string,
     dests : string}
  val full_attrs : facts_prefixes
  val clas_attrs : facts_prefixes
  val simp_attrs : facts_prefixes
  val metis_attrs : facts_prefixes
  val no_attrs : facts_prefixes
  val apply_raw_named_method : string -> bool -> facts_prefixes ->
    (Proof.context -> Proof.context) -> Time.time option -> Try0.facts -> Proof.state ->
    Try0.result option
end

structure Try0_Util : TRY0_UTIL = struct

fun string_of_xref ((xref, args) : Try0.xref) =
  (case xref of
    Facts.Fact literal => literal |> Symbol_Pos.explode0 |> Symbol_Pos.implode |> cartouche
  | _ =>
      Facts.string_of_ref xref) ^ implode
        (map (enclose "[" "]" o Pretty.unformatted_string_of o Token.pretty_src \<^context>) args)


type facts_prefixes =
  {usings: string,
   simps : string,
   intros : string,
   elims : string,
   dests : string}

val no_attrs : facts_prefixes =
  {usings = "", simps = "", intros = "", elims = "", dests = ""}
val full_attrs : facts_prefixes =
  {usings = "", simps = "simp", intros = "intro", elims = "elim", dests = "dest"}
val clas_attrs : facts_prefixes =
  {usings = "", simps = "", intros = "intro", elims = "elim", dests = "dest"}
val simp_attrs : facts_prefixes =
  {usings = "", simps = "add", intros = "", elims = "", dests = ""}
val metis_attrs : facts_prefixes = no_attrs

local

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

fun apply_raw_named_method (name : string) all_goals (prefixes: facts_prefixes)
  (silence_methods : Proof.context -> Proof.context) timeout_opt (facts : Try0.facts)
  (st : Proof.state) : Try0.result option =
  let
    val st = Proof.map_contexts silence_methods st
    val ctxt = Proof.context_of st

    val (unused_simps, simps_attrs) =
      if #simps prefixes = "" then
        (#simps facts, "")
      else
        ([], " " ^ #simps prefixes ^ ": " ^ space_implode "" (map string_of_xref (#simps facts)))

    val (unused_intros, intros_attrs) =
      if #intros prefixes = "" then
        (#intros facts, "")
      else
        ([], " " ^ #intros prefixes ^ ": " ^ space_implode "" (map string_of_xref (#intros facts)))

    val (unused_elims, elims_attrs) =
      if #elims prefixes = "" then
        (#elims facts, "")
      else
        ([], " " ^ #elims prefixes ^ ": " ^ space_implode "" (map string_of_xref (#elims facts)))

    val (unused_dests, dests_attrs) =
      if #dests prefixes = "" then
        (#dests facts, "")
      else
        ([], " " ^ #dests prefixes ^ ": " ^ space_implode "" (map string_of_xref (#dests facts)))

    val unused = #usings facts @ unused_simps @ unused_intros @ unused_elims @ unused_dests

    val attrs = simps_attrs ^ intros_attrs ^ elims_attrs ^ dests_attrs
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