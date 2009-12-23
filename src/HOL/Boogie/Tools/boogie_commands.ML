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

fun boogie_open (quiet, base_name) thy =
  let
    val path = Path.explode (base_name ^ ".b2i")
    val _ = File.exists path orelse
      error ("Unable to find file " ^ quote (Path.implode path))
    val _ = Boogie_VCs.is_closed thy orelse
      error ("Found the beginning of a new Boogie environment, " ^
        "but another Boogie environment is still open.")
  in Boogie_Loader.load_b2i (not quiet) path thy end


datatype vc_opts =
  VC_Complete |
  VC_Take of int list * (bool * string list) option |
  VC_Only of string list |
  VC_Without of string list |
  VC_Examine of string list 

fun get_vc thy vc_name =
  (case Boogie_VCs.lookup thy vc_name of
    SOME vc => vc
  | NONE => 
      (case AList.lookup (op =) (Boogie_VCs.state_of thy) vc_name of
        SOME Boogie_VCs.Proved => error ("The verification condition " ^
          quote vc_name ^ " has already been proved.")
      | _ => error ("There is no verification condition " ^
          quote vc_name ^ ".")))

fun boogie_vc (vc_name, vc_opts) lthy =
  let
    val thy = ProofContext.theory_of lthy
    val vc = get_vc thy vc_name

    val vcs =
      (case vc_opts of
        VC_Complete => [vc]
      | VC_Take (ps, NONE) => [Boogie_VCs.paths_and ps [] vc]
      | VC_Take (ps, SOME (true, ls)) => [Boogie_VCs.paths_and ps ls vc]
      | VC_Take (ps, SOME (false, ls)) => [Boogie_VCs.paths_without ps ls vc]
      | VC_Only ls => [Boogie_VCs.only ls vc]
      | VC_Without ls => [Boogie_VCs.without ls vc]
      | VC_Examine ls => map_filter (Boogie_VCs.extract vc) ls)
    val ts = map Boogie_VCs.prop_of_vc vcs

    val discharge = fold (Boogie_VCs.discharge o pair vc_name)
    fun after_qed [thms] = Local_Theory.theory (discharge (vcs ~~ thms))
      | after_qed _ = I
  in
    lthy
    |> fold Variable.auto_fixes ts
    |> Proof.theorem_i NONE after_qed [map (rpair []) ts]
  end


fun write_list head =
  map Pretty.str o sort (dict_ord string_ord o pairself explode) #>
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
    ProofContext.init thy
    |> Proof.theorem_i NONE (K I) [[(Boogie_VCs.prop_of_vc vc, [])]]
    |> Proof.apply meth
    |> Seq.hd
    |> Proof.global_done_proof
in
fun boogie_narrow_vc timeout vc_name meth thy =
  let
    val tp = TimeLimit.timeLimit (Time.fromSeconds timeout) (prove thy meth)

    fun try_vc (tag, split_tag) split vc = (trying tag;
      (case try tp vc of
        SOME _ => (success_on tag; [])
      | NONE => (failure_on tag split_tag; split vc)))

    fun some_asserts vc =
      try_vc (string_of_asserts vc,
        if Boogie_VCs.size_of vc = 1 then "." else ", further splitting ...")
        (divide some_asserts) vc

    fun single_path p =
      try_vc (string_of_path p, ", splitting into assertions ...")
        (divide some_asserts)

    val complete_vc =
      try_vc ("full goal", ", splitting into paths ...")
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

val _ =
  OuterSyntax.command "boogie_open"
    "Open a new Boogie environment and load a Boogie-generated .b2i file."
    OuterKeyword.thy_decl
    (scan_opt "quiet" -- OuterParse.name >> (Toplevel.theory o boogie_open))


val vc_name = OuterParse.name

val vc_labels = Scan.repeat1 OuterParse.name

val vc_paths =
  OuterParse.nat -- (Args.$$$ "-" |-- OuterParse.nat) >> (op upto) ||
  OuterParse.nat >> single

val vc_opts =
  scan_arg
   (scan_val "examine" vc_labels >> VC_Examine ||
    scan_val "take" ((OuterParse.list vc_paths >> flat) -- Scan.option (
      scan_val "without" vc_labels >> pair false ||
      scan_val "and_also" vc_labels >> pair true) >> VC_Take) ||
    scan_val "only" vc_labels >> VC_Only ||
    scan_val "without" vc_labels >> VC_Without) ||
  Scan.succeed VC_Complete  

val _ =
  OuterSyntax.command "boogie_vc"
    "Enter into proof mode for a specific verification condition."
    OuterKeyword.thy_goal
    (vc_name -- vc_opts >> (fn args =>
      (Toplevel.print o Toplevel.local_theory_to_proof NONE (boogie_vc args))))


val default_timeout = 5

val status_test =
  scan_arg (
    (Args.$$$ "scan" >> K boogie_scan_vc ||
     Args.$$$ "narrow" >> K boogie_narrow_vc) --
    Scan.optional (scan_val "timeout" OuterParse.nat) default_timeout) --
  vc_name -- Method.parse >>
  (fn (((f, timeout), vc_name), meth) => f timeout vc_name meth)

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
  OuterSyntax.improper_command "boogie_status"
    "Show the name and state of all loaded verification conditions."
    OuterKeyword.diag
    (status_test >> status_cmd ||
     status_vc >> status_cmd ||
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
