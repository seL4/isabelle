(* Title:      HOL/Tools/try0_util.ML
   Author:     Jasmin Blanchette, LMU Muenchen
   Author:     Martin Desharnais, LMU Muenchen
   Author:     Fabian Huch, TU Muenchen

General-purpose functions used by Try0.
*)

signature TRY0_UTIL =
sig
  val string_of_xref : Try0.xref -> string

  datatype facts_config =
    No_Args
  | Direct_Args
  | Prefixed_Args of {class : string, prefix : string} list
  val full_attrs : facts_config
  val clas_attrs : facts_config
  val simp_attrs : facts_config
  val apply_raw_named_method : string -> bool -> facts_config ->
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

datatype facts_config =
  No_Args
| Direct_Args
| Prefixed_Args of {class : string, prefix : string} list

val full_attrs : facts_config =
  Prefixed_Args
    [{class = Try0.simpN, prefix = "simp: "},
     {class = Try0.introN, prefix = "intro: "},
     {class = Try0.elimN, prefix = "elim: "},
     {class = Try0.destN, prefix = "dest: "},
     {class = Try0.splitN, prefix = "split: "},
     {class = Try0.iffN, prefix = "iff: "},
     {class = Try0.congN, prefix = "cong: "}]
val clas_attrs : facts_config =
  Prefixed_Args
    [{class = Try0.introN, prefix = "intro: "},
     {class = Try0.elimN, prefix = "elim: "},
     {class = Try0.destN, prefix = "dest: "}]
val simp_attrs : facts_config =
  Prefixed_Args
    [{class = Try0.simpN, prefix = "add: "},
     {class = Try0.splitN, prefix = "split: "},
     {class = Try0.congN, prefix = "cong: "}]

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
  in
    (case Exn.capture (with_timeout (Seq.pull o tac)) st of
      Exn.Res res => Option.map fst res
    | Exn.Exn exn =>
        (* the thread ran out of stack, e.g. because of a looping simp rule *)
        if Exn.is_interrupt_breakdown exn then NONE else Exn.reraise exn)
  end

val num_goals = Thm.nprems_of o #goal o Proof.goal

fun apply_recursive recurse elapsed0 timeout_opt apply st =
  (case Timing.timing (Option.join o try (run_tac timeout_opt apply)) st of
    ({elapsed, ...}, SOME st') =>
      if recurse andalso num_goals st' > 0 andalso num_goals st' < num_goals st then
        let val timeout_opt1 = (Option.map (fn timeout => timeout - elapsed) timeout_opt)
        in apply_recursive recurse (elapsed0 + elapsed) timeout_opt1 apply st' end
      else (elapsed0 + elapsed, st')
   |_ => (elapsed0, st))

fun classes_in_canonical_order (facts : Try0.facts) : string list =
  Try0.native_classes @ subtract (op =) Try0.native_classes (Symtab.keys (#classified facts))

fun all_classified_xxrefs (facts : Try0.facts) : Try0.xxrefs =
  fold (fn class => fn acc => Try0.union_xxrefs acc (Try0.get_class_xxrefs class facts))
    (classes_in_canonical_order facts) {usings = [], directs = []}

fun all_class_xxrefs (facts : Try0.facts) : Try0.xxrefs =
  Try0.union_xxrefs (#unclassified facts) (all_classified_xxrefs facts)

fun accumulate_listed_class (facts : Try0.facts) {class : string, prefix : string}
    (class_attrs : string, unsupported : Try0.xxrefs) : string * Try0.xxrefs =
  (case Try0.get_class_xxrefs class facts of
    {usings = [], directs = []} => (class_attrs, unsupported)
  | xxrefs =>
      (class_attrs ^ " " ^ prefix ^
        implode_space (map string_of_xref (#usings xxrefs @ #directs xxrefs)),
       unsupported))

fun accumulate_unlisted_class (facts : Try0.facts) (class : string)
    (class_attrs : string, unsupported : Try0.xxrefs) : string * Try0.xxrefs =
  (class_attrs, Try0.union_xxrefs unsupported (Try0.get_class_xxrefs class facts))

fun mk_attrs_and_usings No_Args (facts : Try0.facts) : string * Try0.xref list =
      let val {usings, directs} = all_class_xxrefs facts in ("", directs @ usings) end
  | mk_attrs_and_usings Direct_Args facts =
      let val {usings, directs} = all_class_xxrefs facts in
        ((if null directs then "" else " " ^ implode_space (map string_of_xref directs)), usings)
      end
  | mk_attrs_and_usings (Prefixed_Args class_prefixes) facts =
      let
        val listed_classes = map #class class_prefixes
        val unlisted_classes_in_canonical_order =
          subtract (op =) listed_classes (classes_in_canonical_order facts)

        val (class_attrs, unsupported) =
          ("", {usings = [], directs = []})
          |> fold (accumulate_listed_class facts) class_prefixes
          |> fold (accumulate_unlisted_class facts) unlisted_classes_in_canonical_order

        val {usings, directs} = Try0.union_xxrefs (#unclassified facts) unsupported
      in (class_attrs, directs @ usings) end

in

fun apply_raw_named_method (name : string) all_goals (facts_config: facts_config)
  (silence_methods : Proof.context -> Proof.context) timeout_opt (facts : Try0.facts)
  (st : Proof.state) : Try0.result option =
  let
    val st = Proof.map_contexts silence_methods st
    val ctxt = Proof.context_of st

    val (attrs, usings) = mk_attrs_and_usings facts_config facts

    val text =
      name ^ attrs
      |> parse_method ctxt
      |> Method.method_cmd ctxt
      |> Method.Basic
      |> (fn m => Method.Combinator (Method.no_combinator_info, Method.Select_Goals 1, [m]))

    val apply =
      Proof.using [Attrib.eval_thms ctxt usings |> map (rpair [] o single)]
      #> Proof.refine text #> Seq.filter_results
    val num_before = num_goals st
    val multiple_goals = all_goals andalso num_before > 1
    val (time, st') = apply_recursive multiple_goals Time.zeroTime timeout_opt apply st
    val num_after = num_goals st'
    val command =
      let
        val usings = map (Pretty.str o string_of_xref) usings
        val using_clause = if null usings then [] else Pretty.str "using" :: usings
        val select = "[" ^ string_of_int (num_before - num_after)  ^ "]"
        val command_clause =
          [Pretty.str ((if num_after = 0 then "by " else "apply ") ^
              (name ^ attrs |> attrs <> "" ? enclose "(" ")"))] @
          (if multiple_goals andalso num_after > 0 then [Pretty.str select] else [])
      in
        using_clause @ command_clause
        |> Pretty.block o Pretty.breaks
        |> Pretty.symbolic_string_of (* markup string *)
      end
  in
    if num_before > num_after then
      SOME {name = name, command = command, time = time, state = st'}
    else
      NONE
  end

end

end
