(* Title:      HOL/Try0.thy
   Author:     Jasmin Blanchette, LMU Muenchen
   Author:     Martin Desharnais, LMU Muenchen
   Author:     Fabian Huch, TU Muenchen
*)

theory Try0
  imports Presburger
  keywords "try0" :: diag
begin

ML_file \<open>Tools/try0.ML\<close>

ML \<open>
local

fun string_of_xref ((xref, args) : Try0.xref) =
  (case xref of
    Facts.Fact literal => literal |> Symbol_Pos.explode0 |> Symbol_Pos.implode |> cartouche
  | _ =>
      Facts.string_of_ref xref) ^ implode
        (map (enclose "[" "]" o Pretty.unformatted_string_of o Token.pretty_src \<^context>) args)

fun add_attr_text (tagged : Try0.tagged_xref list) (tag, src) s =
  let
    val fs = tagged |> filter (fn (_, tags) => member (op =) tags tag) |> map (string_of_xref o fst)
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

val full_attrs = [(Try0.Simp, "simp"), (Try0.Intro, "intro"), (Try0.Elim, "elim"), (Try0.Dest, "dest")]
val clas_attrs = [(Try0.Intro, "intro"), (Try0.Elim, "elim"), (Try0.Dest, "dest")]
val simp_attrs = [(Try0.Simp, "add")]
val metis_attrs = [(Try0.Simp, ""), (Try0.Intro, ""), (Try0.Elim, ""), (Try0.Dest, "")]
val no_attrs = []

(* name * (run_if_auto_try * (all_goals * tags)) *)
val raw_named_methods =
  [("simp", (true, (false, simp_attrs))),
   ("auto", (true, (true, full_attrs))),
   ("blast", (true, (false, clas_attrs))),
   ("metis", (true, (false, metis_attrs))),
   ("argo", (true, (false, no_attrs))),
   ("linarith", (true, (false, no_attrs))),
   ("presburger", (true, (false, no_attrs))),
   ("algebra", (true, (false, no_attrs))),
   ("fast", (false, (false, clas_attrs))),
   ("fastforce", (false, (false, full_attrs))),
   ("force", (false, (false, full_attrs))),
   ("meson", (false, (false, metis_attrs))),
   ("satx", (false, (false, no_attrs))),
   ("order", (true, (false, no_attrs)))]

fun apply_raw_named_method name (all_goals, attrs) timeout_opt tagged st :
    Try0.result option =
  let
    val st = Proof.map_contexts (Try0.silence_methods false) st
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

in

val () = raw_named_methods
  |> List.app (fn (name, (run_if_auto_try, raw_method)) =>
    let val meth : Try0.proof_method = apply_raw_named_method name raw_method in
      Try0.register_proof_method name {run_if_auto_try = run_if_auto_try} meth
      handle Symtab.DUP _ => ()
    end)

end
\<close>

end