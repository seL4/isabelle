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

fun boogie_load (quiet, base_name) thy =
  let
    val path = Path.explode (base_name ^ ".b2i")
    val _ = File.exists path orelse
      error ("Unable to find file " ^ quote (Path.implode path))
    val _ = Boogie_VCs.is_closed thy orelse
      error ("Found the beginning of a new Boogie environment, " ^
        "but another Boogie environment is still open.")
  in Boogie_Loader.load_b2i (not quiet) path thy end


datatype vc_opts = VC_full of bool | VC_only of string list

fun get_vc thy vc_name =
  (case Boogie_VCs.lookup thy vc_name of
    SOME vc => vc
  | NONE => 
      (case AList.lookup (op =) (Boogie_VCs.state_of thy) vc_name of
        SOME Boogie_VCs.Proved => error ("The verification condition " ^
          quote vc_name ^ " has already been proved.")
      | _ => error ("There is no verification condition " ^
          quote vc_name ^ ".")))

fun boogie_vc (vc_opts, vc_name) lthy =
  let
    val thy = ProofContext.theory_of lthy
    val vc = get_vc thy vc_name

    val (sks, ts) = split_list
      (case vc_opts of
        VC_full paths => [vc] |> paths ? maps Boogie_VCs.paths_of
      | VC_only assertions => map_filter (Boogie_VCs.extract vc) assertions)

    val discharge = fold (Boogie_VCs.discharge o pair vc_name)
    fun after_qed [thms] = Local_Theory.theory (discharge (sks ~~ thms))
      | after_qed _ = I
  in
    lthy
    |> fold Variable.auto_fixes ts
    |> Proof.theorem_i NONE after_qed [map (rpair []) ts]
  end


fun write_list head pp xs = Pretty.writeln (Pretty.big_list head (map pp xs))

fun boogie_status thy =
  let
    fun string_of_state Boogie_VCs.Proved = "proved"
      | string_of_state Boogie_VCs.NotProved = "not proved"
      | string_of_state Boogie_VCs.PartiallyProved = "partially proved"

    fun pretty_vc_name (name, proved) =
      Pretty.str (name ^ " (" ^ string_of_state proved ^ ")")
  in
    Boogie_VCs.state_of thy
    |> write_list "Boogie verification conditions:" pretty_vc_name
  end

fun boogie_status_vc (full, vc_name) thy =
  let
    fun pretty tag s = s ^ " (" ^ tag ^ ")"

    val (ps, us) = Boogie_VCs.state_of_vc thy vc_name
  in
    if full
    then write_list ("Assertions of Boogie verification condition " ^
      quote vc_name ^ ":") Pretty.str (sort fast_string_ord
        (map (pretty "proved") ps @ map (pretty "not proved") us))
    else write_list ("Unproved assertions of Boogie verification condition " ^
      quote vc_name ^ ":") Pretty.str (sort fast_string_ord us)
  end


local
  fun trying s = tracing ("Trying " ^ s ^ " ...")
  fun success_on s = tracing ("Succeeded on " ^ s ^ ".")
  fun failure_on s c = tracing ("Failed on " ^ s ^ c)

  fun string_of_asserts goal = space_implode ", " (Boogie_VCs.names_of goal)

  fun string_of_path (i, n) =
    "path " ^ string_of_int i ^ " of " ^ string_of_int n

  fun itemize_paths ps =
    let val n = length ps
    in fst (fold_map (fn p => fn i => (((i, n), p), i+1)) ps 1) end

  fun par_map f = flat o Par_List.map f

  fun divide f goal =
    let val n = Boogie_VCs.size_of goal
    in
      if n = 1 then Boogie_VCs.names_of goal
      else
        let val (goal1, goal2) = Boogie_VCs.split_path (n div 2) goal
        in par_map f [goal1, goal2] end
    end

  fun prove thy meth (_, goal) =
    ProofContext.init thy
    |> Proof.theorem_i NONE (K I) [[(goal, [])]]
    |> Proof.apply meth
    |> Seq.hd
    |> Proof.global_done_proof
in
fun boogie_narrow_vc ((timeout, vc_name), meth) thy =
  let
    val tp = TimeLimit.timeLimit (Time.fromSeconds timeout) (prove thy meth)

    fun try_goal (tag, split_tag) split goal = (trying tag;
      (case try tp goal of
        SOME _ => (success_on tag; [])
      | NONE => (failure_on tag split_tag; split goal)))

    fun group_goal goal =
      try_goal (string_of_asserts goal,
        if Boogie_VCs.size_of goal = 1 then "." else ", further splitting ...")
        (divide group_goal) goal

    fun path_goal p =
      try_goal (string_of_path p, ", splitting into assertions ...")
        (divide group_goal)

    val full_goal =
      try_goal ("full goal", ", splitting into paths ...")
        (par_map (uncurry path_goal) o itemize_paths o Boogie_VCs.paths_of)

    val unsolved = full_goal (get_vc thy vc_name)
  in
    if null unsolved
    then writeln ("Completely solved Boogie verification condition " ^
      quote vc_name ^ ".")
    else write_list ("Unsolved assertions of Boogie verification condition " ^
      quote vc_name ^ ":") Pretty.str (sort fast_string_ord unsolved)
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
fun scan_opt n = Scan.optional (scan_arg (Args.$$$ n) >> K true) false


val _ =
  OuterSyntax.command "boogie_open"
    "Open a new Boogie environment and load a Boogie-generated .b2i file."
    OuterKeyword.thy_decl
    (scan_opt "quiet" -- OuterParse.name >> (Toplevel.theory o boogie_load))


val vc_name = OuterParse.name
val vc_opts =
  scan_arg (scan_val "only" (Scan.repeat1 OuterParse.name)) >> VC_only ||
  scan_opt "paths" >> VC_full

fun vc_cmd f = Toplevel.print o Toplevel.local_theory_to_proof NONE f

val _ =
  OuterSyntax.command "boogie_vc"
    "Enter into proof mode for a specific verification condition."
    OuterKeyword.thy_goal
    (vc_opts -- vc_name >> (vc_cmd o boogie_vc))


val default_timeout = 5

val status_narrow_vc =
  scan_arg (Args.$$$ "narrow" |--
    Scan.optional (scan_val "timeout" OuterParse.nat) default_timeout) --
  vc_name --
  scan_arg (scan_val "try" Method.parse)

val status_vc_opts = scan_opt "full"

fun status_cmd f = Toplevel.no_timing o Toplevel.keep (fn state =>
  f (Toplevel.theory_of state))

val _ =
  OuterSyntax.improper_command "boogie_status"
    "Show the name and state of all loaded verification conditions."
    OuterKeyword.diag
    (status_narrow_vc >> (status_cmd o boogie_narrow_vc) ||
     status_vc_opts -- vc_name >> (status_cmd o boogie_status_vc) ||
     Scan.succeed (status_cmd boogie_status))


val _ =
  OuterSyntax.command "boogie_end"
    "Close the current Boogie environment."
    OuterKeyword.thy_decl
    (Scan.succeed (Toplevel.theory boogie_end))


val setup = Theory.at_end (fn thy =>
  let
    val _ = Boogie_VCs.is_closed thy
      orelse error ("Found the end of the theory, " ^ 
        "but the last Boogie environment is still open.")
  in NONE end)

end
