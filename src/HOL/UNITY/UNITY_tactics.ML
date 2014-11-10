(*  Title:      HOL/UNITY/UNITY_tactics.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2003  University of Cambridge

Specialized UNITY tactics.
*)

(*Combines two invariance ASSUMPTIONS into one.  USEFUL??*)
fun Always_Int_tac ctxt =
  dtac @{thm Always_Int_I} THEN' assume_tac ctxt THEN' etac @{thm Always_thin}

(*Combines a list of invariance THEOREMS into one.*)
val Always_Int_rule = foldr1 (fn (th1,th2) => [th1,th2] MRS @{thm Always_Int_I})

(*Proves "co" properties when the program is specified.  Any use of invariants
  (from weak constrains) must have been done already.*)
fun constrains_tac ctxt i =
  SELECT_GOAL
    (EVERY
     [REPEAT (Always_Int_tac ctxt 1),
      (*reduce the fancy safety properties to "constrains"*)
      REPEAT (etac @{thm Always_ConstrainsI} 1
              ORELSE
              resolve_tac [@{thm StableI}, @{thm stableI},
                           @{thm constrains_imp_Constrains}] 1),
      (*for safety, the totalize operator can be ignored*)
      simp_tac (put_simpset HOL_ss ctxt
        addsimps [@{thm mk_total_program_def}, @{thm totalize_constrains_iff}]) 1,
      rtac @{thm constrainsI} 1,
      full_simp_tac ctxt 1,
      REPEAT (FIRSTGOAL (etac disjE)),
      ALLGOALS (clarify_tac ctxt),
      ALLGOALS (asm_full_simp_tac ctxt)]) i;

(*proves "ensures/leadsTo" properties when the program is specified*)
fun ensures_tac ctxt sact =
  SELECT_GOAL
    (EVERY
     [REPEAT (Always_Int_tac ctxt 1),
      etac @{thm Always_LeadsTo_Basis} 1
          ORELSE   (*subgoal may involve LeadsTo, leadsTo or ensures*)
          REPEAT (ares_tac [@{thm LeadsTo_Basis}, @{thm leadsTo_Basis},
                            @{thm EnsuresI}, @{thm ensuresI}] 1),
      (*now there are two subgoals: co & transient*)
      simp_tac (ctxt addsimps [@{thm mk_total_program_def}]) 2,
      res_inst_tac ctxt
        [(("act", 0), sact)] @{thm totalize_transientI} 2
      ORELSE res_inst_tac ctxt
        [(("act", 0), sact)] @{thm transientI} 2,
         (*simplify the command's domain*)
      simp_tac (ctxt addsimps @{thms Domain_unfold}) 3,
      constrains_tac ctxt 1,
      ALLGOALS (clarify_tac ctxt),
      ALLGOALS (asm_lr_simp_tac ctxt)]);


(*Composition equivalences, from Lift_prog*)

fun make_o_equivs ctxt th =
  [th,
   th RS @{thm o_equiv_assoc} |> simplify (put_simpset HOL_ss ctxt addsimps [@{thm o_assoc}]),
   th RS @{thm o_equiv_apply} |> simplify (put_simpset HOL_ss ctxt addsimps [@{thm o_def}, @{thm sub_def}])];

