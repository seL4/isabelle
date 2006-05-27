(*  Title:      HOLCF/IOA/TrivEx.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* Trivial Abstraction Example *}

theory TrivEx
imports Abstraction
begin

datatype action = INC

consts

C_asig   ::  "action signature"
C_trans  :: "(action, nat)transition set"
C_ioa    :: "(action, nat)ioa"

A_asig   :: "action signature"
A_trans  :: "(action, bool)transition set"
A_ioa    :: "(action, bool)ioa"

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

h_abs_def:
  "h_abs n == n~=0"

axioms

MC_result:
  "validIOA A_ioa (<>[] <%(b,a,c). b>)"

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
apply (simp add: h_abs_def)
done

lemma TrivEx_abstraction: "validIOA C_ioa (<>[] <%(n,a,m). n~=0>)"
apply (rule AbsRuleT1)
apply (rule h_abs_is_abstraction)
apply (rule MC_result)
apply (tactic "abstraction_tac 1")
apply (simp add: h_abs_def)
done

end
