(*  Title:      HOL/Boogie/Tools/boogie_commands.ML
    Author:     Sascha Boehme, TU Muenchen

Isar commands to create a Boogie environment simulation.
*)

signature BOOGIE_COMMANDS =
sig
  val setup: theory -> theory
end

structure Boogie_Commands: BOOGIE_COMMANDS =
struct

(* commands *)

fun boogie_open ((quiet, files), offsets) thy =
  let
    val ([{src_path = path, text, ...}: Token.file], thy') = files thy

    val ext = "b2i"
    val _ = snd (Path.split_ext path) = ext orelse
      error ("Bad file ending of file " ^ Path.print path ^ ", " ^
        "expected file ending " ^ quote ext)

    val _ = Boogie_VCs.is_closed thy orelse
      error ("Found the beginning of a new Boogie environment, " ^
        "but another Boogie environment is still open.")
  in
    thy'
    |> Boogie_Loader.parse_b2i (not quiet) offsets text
  end


datatype vc_opts =
  VC_Complete |
  VC_Take of int list * (bool * string list) option |
  VC_Only of string list |
  VC_Without of string list |
  VC_Examine of string list |
  VC_Single of string

fun get_vc thy vc_name =
  (case Boogie_VCs.lookup thy vc_name of
    SOME vc => vc
  | NONE =>
      (case AList.lookup (op =) (Boogie_VCs.state_of thy) vc_name of
        SOME Boogie_VCs.Proved => error ("The verification condition " ^
          quote vc_name ^ " has already been proved.")
      | _ => error ("There is no verification condition " ^
          quote vc_name ^ ".")))

local
  fun split_goal t =
    (case Boogie_Tactics.split t of
      [tp] => tp
    | _ => error "Multiple goals.")

  fun single_prep t =
    let
      val (us, u) = split_goal t
      val assms = [((@{binding vc_trace}, []), map (rpair []) us)]
    in
      pair [u] o snd o Proof_Context.add_assms_i Assumption.assume_export assms
    end

  fun single_prove goal ctxt thm =
    Goal.prove ctxt [] [] goal (fn {context, ...} => HEADGOAL (
      Boogie_Tactics.split_tac
      THEN' Boogie_Tactics.drop_assert_at_tac
      THEN' SUBPROOF (fn _ => Tactic.rtac thm 1) context))
in
fun boogie_vc (vc_name, vc_opts) thy =
  let
    val vc = get_vc thy vc_name

    fun extract vc l =
      (case Boogie_VCs.extract vc l of
        SOME vc' => vc'
      | NONE => error ("There is no assertion to be proved with label " ^
          quote l ^ "."))

    val vcs =
      (case vc_opts of
        VC_Complete => [vc]
      | VC_Take (ps, NONE) => [Boogie_VCs.paths_and ps [] vc]
      | VC_Take (ps, SOME (true, ls)) => [Boogie_VCs.paths_and ps ls vc]
      | VC_Take (ps, SOME (false, ls)) => [Boogie_VCs.paths_without ps ls vc]
      | VC_Only ls => [Boogie_VCs.only ls vc]
      | VC_Without ls => [Boogie_VCs.without ls vc]
      | VC_Examine ls => map (extract vc) ls
      | VC_Single l => [extract vc l])
    val ts = map Boogie_VCs.prop_of_vc vcs

    val (prepare, finish) =
      (case vc_opts of
         VC_Single _ => (single_prep (hd ts), single_prove (hd ts))
      | _ => (pair ts, K I))

    val discharge = fold (Boogie_VCs.discharge o pair vc_name)
    fun after_qed [thms] = Proof_Context.background_theory (discharge (vcs ~~ thms))
      | after_qed _ = I
  in
    Proof_Context.init_global thy
    |> fold Variable.auto_fixes ts
    |> (fn ctxt1 => ctxt1
    |> prepare
    |-> (fn us => fn ctxt2 => ctxt2
    |> Proof.theorem NONE (fn thmss => fn ctxt =>
         let val export = map (finish ctxt1) o Proof_Context.export ctxt ctxt2
         in after_qed (map export thmss) ctxt end) [map (rpair []) us]))
  end
end

fun write_list head =
  map Pretty.str o sort (dict_ord string_ord o pairself raw_explode) #>
  Pretty.writeln o Pretty.big_list head

fun parens s = "(" ^ s ^ ")"

fun boogie_status thy =
  let
    fun string_of_state Boogie_VCs.Proved = "proved"
      | string_of_state Boogie_VCs.NotProved = "not proved"
      | string_of_state Boogie_VCs.PartiallyProved = "partially proved"
  in
    Boogie_VCs.state_of thy
    |> map (fn (name, proved) => name ^ " " ^ parens (string_of_state proved))
    |> write_list "Boogie verification conditions:"
  end

fun boogie_status_vc full vc_name thy =
  let
    fun pretty tag s = s ^ " " ^ parens tag

    val (not_proved, proved) = Boogie_VCs.state_of_vc thy vc_name
  in
    if full
    then write_list ("Assertions of Boogie verification condition " ^
      quote vc_name ^ ":")
      (map (pretty "proved") proved @ map (pretty "not proved") not_proved)
    else write_list ("Unproved assertions of Boogie verification condition " ^
      quote vc_name ^ ":") not_proved
  end

fun boogie_status_vc_paths full vc_name thy =
  let
    fun labels ls = Pretty.blk (0, Pretty.breaks (map Pretty.str ls))

    fun pp (i, ns) =
      if full
      then
        [Pretty.big_list ("Path " ^ string_of_int (i+1) ^ ":")
          [labels (map (fn (n, true) => n | (n, _) => parens n) ns)]]
      else
        let val ns' = map_filter (fn (n, true) => SOME n | _ => NONE) ns
        in
          if null ns' then []
          else
            [Pretty.big_list ("Unproved assertions of path " ^
              string_of_int (i+1) ^ ":") [labels ns']]
        end
  in
    Pretty.writeln
      (Pretty.big_list
        ("Paths of Boogie verification condition " ^ quote vc_name ^ ":")
        (flat (map_index pp (Boogie_VCs.path_names_of (get_vc thy vc_name)))))
  end


local
  fun trying s = tracing ("Trying " ^ s ^ " ...")
  fun success_on s = tracing ("Succeeded on " ^ s ^ ".")
  fun failure_on s c = tracing ("Failed on " ^ s ^ c)

  fun string_of_asserts vc = space_implode ", " (fst (Boogie_VCs.names_of vc))

  fun string_of_path (i, n) =
    "path " ^ string_of_int i ^ " of " ^ string_of_int n

  fun itemize_paths ps =
    let val n = length ps
    in fst (fold_map (fn p => fn i => (((i, n), p), i+1)) ps 1) end

  fun par_map f = flat o Par_List.map f

  fun divide f vc =
    let val n = Boogie_VCs.size_of vc
    in
      if n <= 1 then fst (Boogie_VCs.names_of vc)
      else
        let val (vc1, vc2) = the (Boogie_VCs.split_path (n div 2) vc)
        in par_map f [vc1, vc2] end
    end

  fun prove thy meth vc =
    Proof_Context.init_global thy
    |> Proof.theorem NONE (K I) [[(Boogie_VCs.prop_of_vc vc, [])]]
    |> Proof.apply meth
    |> Seq.hd
    |> Proof.global_done_proof
in
fun boogie_narrow_vc (quick, timeout) vc_name meth thy =
  let
    fun tp t = TimeLimit.timeLimit (Time.fromSeconds t) (prove thy meth)

    fun try_vc t (tag, split_tag) split vc = (trying tag;
      (case try (tp t) vc of
        SOME _ => (success_on tag; [])
      | NONE => (failure_on tag split_tag; split vc)))

    fun some_asserts vc =
      let
        val (t, sep) = if Boogie_VCs.size_of vc = 1 then (timeout, ".")
          else (quick, ", further splitting ...")
      in try_vc t (string_of_asserts vc, sep) (divide some_asserts) vc end

    fun single_path p =
      try_vc quick (string_of_path p, ", splitting into assertions ...")
        (divide some_asserts)

    val complete_vc =
      try_vc quick ("full goal", ", splitting into paths ...")
        (par_map (uncurry single_path) o itemize_paths o Boogie_VCs.paths_of)

    val unsolved = complete_vc (get_vc thy vc_name)
  in
    if null unsolved
    then writeln ("Completely solved Boogie verification condition " ^
      quote vc_name ^ ".")
    else write_list ("Unsolved assertions of Boogie verification condition " ^
      quote vc_name ^ ":") unsolved
  end

fun boogie_scan_vc timeout vc_name meth thy =
  let
    val tp = TimeLimit.timeLimit (Time.fromSeconds timeout) (prove thy meth)

    val vc = get_vc thy vc_name
    fun prove_assert name =
      (trying name; tp (the (Boogie_VCs.extract vc name)))
    val find_first_failure = find_first (is_none o try prove_assert)
  in
    (case find_first_failure (fst (Boogie_VCs.names_of vc)) of
      SOME name => writeln ("failed on " ^ quote name)
    | NONE => writeln "succeeded")
  end
end



fun boogie_end thy =
  let
    fun not_proved (_, Boogie_VCs.Proved) = NONE
      | not_proved (name, _) = SOME name

    val unproved = map_filter not_proved (Boogie_VCs.state_of thy)
  in
    if null unproved then Boogie_VCs.close thy
    else error (Pretty.string_of (Pretty.big_list
      "The following verification conditions have not been proved:"
      (map Pretty.str unproved)))
  end



(* syntax and setup *)

fun scan_val n f = Args.$$$ n -- Args.colon |-- f
fun scan_arg f = Args.parens f
fun scan_opt n = Scan.optional (scan_arg (Args.$$$ n >> K true)) false

val vc_offsets = Scan.optional (Args.bracks (Parse.list1
  (Parse.string --| Args.colon -- Parse.nat))) []

val _ =
  Outer_Syntax.command @{command_spec "boogie_open"}
    "open a new Boogie environment and load a Boogie-generated .b2i file"
    (scan_opt "quiet" -- Thy_Load.provide_parse_files "boogie_open" -- vc_offsets >>
      (Toplevel.theory o boogie_open))


val vc_name = Parse.name

val vc_label = Parse.name
val vc_labels = Scan.repeat1 vc_label

val vc_paths =
  Parse.nat -- (Args.$$$ "-" |-- Parse.nat) >> (op upto) ||
  Parse.nat >> single

val vc_opts =
  scan_arg
   (scan_val "assertion" vc_label >> VC_Single ||
    scan_val "examine" vc_labels >> VC_Examine ||
    scan_val "take" ((Parse.list vc_paths >> flat) -- Scan.option (
      scan_val "without" vc_labels >> pair false ||
      scan_val "and_also" vc_labels >> pair true) >> VC_Take) ||
    scan_val "only" vc_labels >> VC_Only ||
    scan_val "without" vc_labels >> VC_Without) ||
  Scan.succeed VC_Complete

val _ =
  Outer_Syntax.command @{command_spec "boogie_vc"}
    "enter into proof mode for a specific verification condition"
    (vc_name -- vc_opts >> (fn args =>
      (Toplevel.print o Toplevel.theory_to_proof (boogie_vc args))))


val quick_timeout = 5
val default_timeout = 20

fun timeout name = Scan.optional (scan_val name Parse.nat)

val status_test =
  scan_arg (
    Args.$$$ "scan" |-- timeout "timeout" quick_timeout >> boogie_scan_vc ||
    Args.$$$ "narrow" |-- timeout "step_timeout" quick_timeout --
      timeout "final_timeout" default_timeout >> boogie_narrow_vc) --
  vc_name -- Method.parse >>
  (fn ((f, vc_name), (meth, _)) => f vc_name meth)

val status_vc =
  (scan_arg
    (Args.$$$ "full" |--
      (Args.$$$ "paths" >> K (boogie_status_vc_paths true) ||
       Scan.succeed (boogie_status_vc true)) ||
     Args.$$$ "paths" >> K (boogie_status_vc_paths false)) ||
   Scan.succeed (boogie_status_vc false)) --
  vc_name >> (fn (f, vc_name) => f vc_name)

fun status_cmd f = Toplevel.no_timing o Toplevel.keep (fn state =>
  f (Toplevel.theory_of state))

val _ =
  Outer_Syntax.improper_command @{command_spec "boogie_status"}
    "show the name and state of all loaded verification conditions"
    (status_test >> status_cmd ||
     status_vc >> status_cmd ||
     Scan.succeed (status_cmd boogie_status))


val _ =
  Outer_Syntax.command @{command_spec "boogie_end"}
    "close the current Boogie environment"
    (Scan.succeed (Toplevel.theory boogie_end))


val setup = Theory.at_end (fn thy =>
  let
    val _ = Boogie_VCs.is_closed thy
      orelse error ("Found the end of the theory, " ^
        "but the last Boogie environment is still open.")
  in NONE end)

end
