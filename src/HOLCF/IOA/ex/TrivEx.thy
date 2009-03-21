(*  Title:      HOLCF/IOA/TrivEx.thy
    Author:     Olaf Müller
*)

header {* Trivial Abstraction Example *}

theory TrivEx
imports Abstraction
begin

datatype action = INC

definition
  C_asig :: "action signature" where
  "C_asig = ({},{INC},{})"
definition
  C_trans :: "(action, nat)transition set" where
  "C_trans =
   {tr. let s = fst(tr);
            t = snd(snd(tr))
        in case fst(snd(tr))
        of
        INC       => t = Suc(s)}"
definition
  C_ioa :: "(action, nat)ioa" where
  "C_ioa = (C_asig, {0}, C_trans,{},{})"

definition
  A_asig :: "action signature" where
  "A_asig = ({},{INC},{})"
definition
  A_trans :: "(action, bool)transition set" where
  "A_trans =
   {tr. let s = fst(tr);
            t = snd(snd(tr))
        in case fst(snd(tr))
        of
        INC       => t = True}"
definition
  A_ioa :: "(action, bool)ioa" where
  "A_ioa = (A_asig, {False}, A_trans,{},{})"

definition
  h_abs :: "nat => bool" where
  "h_abs n = (n~=0)"

axiomatization where
  MC_result: "validIOA A_ioa (<>[] <%(b,a,c). b>)"

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
apply abstraction
apply (simp add: h_abs_def)
done

end
