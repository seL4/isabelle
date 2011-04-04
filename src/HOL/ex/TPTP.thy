(*  Title:      HOL/ex/TPTP.thy
    Author:     Jasmin Blanchette
    Copyright   2011

TPTP "IsabelleP" tactic.
*)

theory TPTP
imports Main
uses "sledgehammer_tactics.ML"
begin

declare mem_def [simp add]

declare [[smt_oracle]]

refute_params [maxtime = 10000, no_assms, expect = genuine]
nitpick_params [timeout = none, card = 1-50, verbose, dont_box, no_assms,
                batch_size = 1, expect = genuine]

ML {* Proofterm.proofs := 0 *}

ML {*
fun SOLVE_TIMEOUT seconds name tac st =
  let
    val result =
      TimeLimit.timeLimit (Time.fromSeconds seconds)
        (fn () => SINGLE (SOLVE tac) st) ()
      handle TimeLimit.TimeOut => NONE
        | ERROR _ => NONE
  in
    (case result of
      NONE => (warning ("FAILURE: " ^ name); Seq.empty)
    | SOME st' => (warning ("SUCCESS: " ^ name); Seq.single st'))
  end
*}

ML {*
fun isabellep_tac ctxt cs ss css max_secs =
   SOLVE_TIMEOUT (max_secs div 10) "smt" (ALLGOALS (SMT_Solver.smt_tac ctxt []))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 5) "sledgehammer"
       (ALLGOALS (Sledgehammer_Tactics.sledgehammer_as_oracle_tac ctxt))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 10) "simp" (ALLGOALS (asm_full_simp_tac ss))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 20) "blast" (ALLGOALS (blast_tac cs))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 10) "auto" (auto_tac css
       THEN ALLGOALS (Sledgehammer_Tactics.sledgehammer_as_oracle_tac ctxt))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 10) "metis" (ALLGOALS (Metis_Tactics.metis_tac ctxt []))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 10) "fast" (ALLGOALS (fast_tac cs))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 10) "best" (ALLGOALS (best_tac cs))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 10) "force" (ALLGOALS (force_tac css))
   ORELSE
   SOLVE_TIMEOUT max_secs "fastsimp" (ALLGOALS (fast_simp_tac css))
*}

end
