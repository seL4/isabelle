(*  Title:      HOLCF/IOA/TrivEx.thy
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1995  TU Muenchen

Trivial Abstraction Example
*)

val prems = goal HOL.thy "(P ==> Q-->R) ==> P&Q --> R";
  by(fast_tac (claset() addDs prems) 1);
qed "imp_conj_lemma";


goalw  thy [is_abstraction_def] 
"is_abstraction h_abs C_ioa A_ioa";
by (rtac conjI 1);
(* ------------- start states ------------ *)
by (simp_tac (simpset() addsimps 
    [h_abs_def,starts_of_def,C_ioa_def,A_ioa_def]) 1);
(* -------------- step case ---------------- *)
by (REPEAT (rtac allI 1));
by (rtac imp_conj_lemma 1);
by (simp_tac (simpset() addsimps [trans_of_def,
        C_ioa_def,A_ioa_def,C_trans_def,A_trans_def])1);
by (simp_tac (simpset() addsimps [h_abs_def]) 1);
by (action.induct_tac "a" 1);
auto();
qed"h_abs_is_abstraction";


goal thy "validIOA C_ioa (<>[] <%(n,a,m). n~=0>)";
br AbsRuleT1 1;
br h_abs_is_abstraction 1;
br MC_result 1;
by (abstraction_tac 1);
by (asm_full_simp_tac (simpset() addsimps [h_abs_def]) 1);
qed"TrivEx_abstraction";


