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
      NONE => (writeln ("FAILURE: " ^ name); Seq.empty)
    | SOME st' => (writeln ("SUCCESS: " ^ name); Seq.single st'))
  end
*}

ML {*
fun isabellep_tac max_secs =
   SOLVE_TIMEOUT (max_secs div 5) "sledgehammer"
       (ALLGOALS (Sledgehammer_Tactics.sledgehammer_as_oracle_tac @{context}))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 10) "simp" (ALLGOALS (asm_full_simp_tac @{simpset}))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 20) "blast" (ALLGOALS (blast_tac @{claset}))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 10) "auto" (auto_tac @{clasimpset}
       THEN ALLGOALS (Sledgehammer_Tactics.sledgehammer_as_oracle_tac @{context}))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 10) "metis" (ALLGOALS (Metis_Tactics.metis_tac @{context} []))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 5) "fast" (ALLGOALS (fast_tac @{claset}))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 10) "best" (ALLGOALS (best_tac @{claset}))
   ORELSE
   SOLVE_TIMEOUT (max_secs div 10) "force" (ALLGOALS (force_tac @{clasimpset}))
   ORELSE
   SOLVE_TIMEOUT max_secs "fastsimp" (ALLGOALS (fast_simp_tac @{clasimpset}))
*}

end
