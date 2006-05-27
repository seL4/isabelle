(*  Title:      HOLCF/IOA/TrivEx.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* Trivial Abstraction Example with fairness *}

theory TrivEx2
imports IOA Abstraction
begin

datatype action = INC

consts

C_asig   ::  "action signature"
C_trans  :: "(action, nat)transition set"
C_ioa    :: "(action, nat)ioa"
C_live_ioa :: "(action, nat)live_ioa"

A_asig   :: "action signature"
A_trans  :: "(action, bool)transition set"
A_ioa    :: "(action, bool)ioa"
A_live_ioa :: "(action, bool)live_ioa"

h_abs    :: "nat => bool"

defs

C_asig_def:
  "C_asig == ({},{INC},{})"

C_trans_def: "C_trans ==
 {tr. let s = fst(tr);
          t = snd(snd(tr))
      in case fst(snd(tr))
      of
      INC       => t = Suc(s)}"

C_ioa_def: "C_ioa ==
 (C_asig, {0}, C_trans,{},{})"

C_live_ioa_def:
  "C_live_ioa == (C_ioa, WF C_ioa {INC})"

A_asig_def:
  "A_asig == ({},{INC},{})"

A_trans_def: "A_trans ==
 {tr. let s = fst(tr);
          t = snd(snd(tr))
      in case fst(snd(tr))
      of
      INC       => t = True}"

A_ioa_def: "A_ioa ==
 (A_asig, {False}, A_trans,{},{})"

A_live_ioa_def:
  "A_live_ioa == (A_ioa, WF A_ioa {INC})"


h_abs_def:
  "h_abs n == n~=0"

axioms

MC_result:
  "validLIOA (A_ioa,WF A_ioa {INC}) (<>[] <%(b,a,c). b>)"


lemma h_abs_is_abstraction:
"is_abstraction h_abs C_ioa A_ioa"
apply (unfold is_abstraction_def)
apply (rule conjI)
txt {* start states *}
apply (simp (no_asm) add: h_abs_def starts_of_def C_ioa_def A_ioa_def)
txt {* step case *}
apply (rule allI)+
apply (rule imp_conj_lemma)
apply (simp (no_asm) add: trans_of_def C_ioa_def A_ioa_def C_trans_def A_trans_def)
apply (induct_tac "a")
apply (simp (no_asm) add: h_abs_def)
done


lemma Enabled_implication:
    "!!s. Enabled A_ioa {INC} (h_abs s) ==> Enabled C_ioa {INC} s"
  apply (unfold Enabled_def enabled_def h_abs_def A_ioa_def C_ioa_def A_trans_def
    C_trans_def trans_of_def)
  apply auto
  done


lemma h_abs_is_liveabstraction:
"is_live_abstraction h_abs (C_ioa, WF C_ioa {INC}) (A_ioa, WF A_ioa {INC})"
apply (unfold is_live_abstraction_def)
apply auto
txt {* is_abstraction *}
apply (rule h_abs_is_abstraction)
txt {* temp_weakening *}
apply (tactic "abstraction_tac 1")
apply (erule Enabled_implication)
done


lemma TrivEx2_abstraction:
  "validLIOA C_live_ioa (<>[] <%(n,a,m). n~=0>)"
apply (unfold C_live_ioa_def)
apply (rule AbsRuleT2)
apply (rule h_abs_is_liveabstraction)
apply (rule MC_result)
apply (tactic "abstraction_tac 1")
apply (simp add: h_abs_def)
done

end
