(*  Title:      Tools/solve_direct.ML
    Author:     Timothy Bourke and Gerwin Klein, NICTA

Check whether a newly stated theorem can be solved directly by an
existing theorem.  Duplicate lemmas can be detected in this way.

The implementation relies critically on the Find_Theorems solves
feature.
*)

signature SOLVE_DIRECT =
sig
  val solve_directN: string
  val someN: string
  val noneN: string
  val unknownN: string
  val max_solutions: int Config.T
  val strict_warnings: bool Config.T
  val solve_direct: Proof.state -> bool * (string * string list)
end;

structure Solve_Direct: SOLVE_DIRECT =
struct

datatype mode = Auto_Try | Try | Normal

val solve_directN = "solve_direct";

val someN = "some";
val noneN = "none";
val unknownN = "none";


(* preferences *)

val max_solutions = Attrib.setup_config_int \<^binding>\<open>solve_direct_max_solutions\<close> (K 5);
val strict_warnings = Attrib.setup_config_bool \<^binding>\<open>solve_direct_strict_warnings\<close> (K false);


(* solve_direct command *)

fun do_solve_direct mode state =
  let
    val ctxt = Proof.context_of state;

    fun find goal =
      #2 (Find_Theorems.find_theorems ctxt (SOME goal)
        (SOME (Config.get ctxt max_solutions)) false [(true, Find_Theorems.Solves)]);

    fun prt_result (subgoal, results) =
      Pretty.big_list
        ((if mode = Auto_Try then "Auto " else "") ^ solve_directN ^ ": " ^
          (case subgoal of NONE => "the current goal" | SOME i => "subgoal #" ^ string_of_int i) ^
          " can be solved directly with")
        (map (Find_Theorems.pretty_thm ctxt) results);

    fun seek_against_goal () =
      (case try (#goal o Proof.simple_goal) state of
        NONE => NONE
      | SOME goal =>
          let
            val subgoals = Drule.strip_imp_prems (Thm.cprop_of goal);
            val rs =
              if length subgoals = 1
              then [(NONE, find goal)]
              else map_index (fn (i, sg) => (SOME (i + 1), find (Goal.init sg))) subgoals;
            val results = filter_out (null o #2) rs;
          in if null results then NONE else SOME results end);
  in
    (case try seek_against_goal () of
      SOME (SOME results) =>
        (someN,
          let
            val chunks = separate (Pretty.str "") (map prt_result results);
            val msg = Pretty.string_of (Pretty.chunks chunks);
          in
            if Config.get ctxt strict_warnings then (warning msg; [])
            else if mode = Auto_Try then [msg]
            else (writeln msg; [])
          end)
    | SOME NONE =>
        (if mode = Normal then writeln "No proof found" else ();
         (noneN, []))
    | NONE =>
        (if mode = Normal then writeln "An error occurred" else ();
         (unknownN, [])))
  end
  |> `(fn (outcome_code, _) => outcome_code = someN);

val solve_direct = do_solve_direct Normal

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>solve_direct\<close>
    "try to solve conjectures directly with existing theorems"
    (Scan.succeed (Toplevel.keep_proof (ignore o solve_direct o Toplevel.proof_of)));


(* 'try' setup *)

val _ =
  Try.tool_setup
   {name = solve_directN, weight = 10, auto_option = \<^system_option>\<open>auto_solve_direct\<close>,
    body = fn auto => do_solve_direct (if auto then Auto_Try else Try)};

end;
