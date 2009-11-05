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

fun boogie_load (verbose, base_name) thy =
  let
    val path = Path.explode (base_name ^ ".b2i")
    val _ = File.exists path orelse
      error ("Unable to find file " ^ quote (Path.implode path))
    val _ = Boogie_VCs.is_closed thy orelse
      error ("Found the beginning of a new Boogie environment, " ^
        "but another Boogie environment is still open.")
  in Boogie_Loader.load_b2i verbose path thy end

fun boogie_status thy =
  let 
    fun pretty_vc_name (name, _, proved) = 
      let val s = if proved then "proved" else "not proved"
      in Pretty.str (name ^ " (" ^ s ^ ")") end
  in
    Pretty.writeln (Pretty.big_list "Boogie verification conditions:"
      (map pretty_vc_name (Boogie_VCs.as_list thy)))
  end

fun boogie_vc name lthy =
  (case Boogie_VCs.lookup (ProofContext.theory_of lthy) name of
    NONE => error ("There is no verification condition " ^ quote name ^ ".")
  | SOME vc =>
      let
        fun store thm = Boogie_VCs.discharge (name, thm)
        fun after_qed [[thm]] = LocalTheory.theory (store thm)
          | after_qed _ = I
      in
        lthy
        |> Variable.auto_fixes vc
        |> Proof.theorem_i NONE after_qed [[(vc, [])]]
      end)

fun boogie_end thy =
  let
    fun not_proved (name, _, proved) = if not proved then SOME name else NONE
    val unproved = map_filter not_proved (Boogie_VCs.as_list thy)
  in
    if null unproved then Boogie_VCs.close thy
    else error (Pretty.string_of (Pretty.big_list 
      "The following verification conditions have not been proved:"
      (map Pretty.str unproved)))
  end

val _ =
  OuterSyntax.command "boogie_open"
    "Open a new Boogie environment and load a Boogie-generated .b2i file."
    OuterKeyword.thy_decl
    (Scan.optional (Args.parens (Args.$$$ "quiet") >> K false) true --
     OuterParse.name >> (Toplevel.theory o boogie_load))

val _ =
  OuterSyntax.improper_command "boogie_status"
    "Show the name and state of all loaded verification conditions."
    OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.keep (fn state =>
      boogie_status (Toplevel.theory_of state))))

val _ =
  OuterSyntax.command "boogie_vc"
    "Enter the proof mode for a specific verification condition."
    OuterKeyword.thy_goal
    (OuterParse.name >> (fn name => Toplevel.print o
      Toplevel.local_theory_to_proof NONE (boogie_vc name)))

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
