(*  Title:      CTT/Bool.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section \<open>The two-element type (booleans and conditionals)\<close>

theory Bool
  imports CTT
begin

definition Bool :: "t"
  where "Bool \<equiv> T+T"

definition true :: "i"
  where "true \<equiv> inl(tt)"

definition false :: "i"
  where "false \<equiv> inr(tt)"

definition cond :: "[i,i,i]\<Rightarrow>i"
  where "cond(a,b,c) \<equiv> when(a, \<lambda>u. b, \<lambda>u. c)"

lemmas bool_defs = Bool_def true_def false_def cond_def


subsection \<open>Derivation of rules for the type \<open>Bool\<close>\<close>

text \<open>Formation rule.\<close>
lemma boolF: "Bool type"
  unfolding bool_defs by typechk

text \<open>Introduction rules for \<open>true\<close>, \<open>false\<close>.\<close>

lemma boolI_true: "true : Bool"
  unfolding bool_defs by typechk

lemma boolI_false: "false : Bool"
  unfolding bool_defs by typechk

text \<open>Elimination rule: typing of \<open>cond\<close>.\<close>
lemma boolE: "\<lbrakk>p:Bool; a : C(true); b : C(false)\<rbrakk> \<Longrightarrow> cond(p,a,b) : C(p)"
  unfolding bool_defs
  apply (typechk; erule TE)
   apply typechk
  done

lemma boolEL: "\<lbrakk>p = q : Bool; a = c : C(true); b = d : C(false)\<rbrakk>
  \<Longrightarrow> cond(p,a,b) = cond(q,c,d) : C(p)"
  unfolding bool_defs
  apply (rule PlusEL)
    apply (erule asm_rl refl_elem [THEN TEL])+
  done

text \<open>Computation rules for \<open>true\<close>, \<open>false\<close>.\<close>

lemma boolC_true: "\<lbrakk>a : C(true); b : C(false)\<rbrakk> \<Longrightarrow> cond(true,a,b) = a : C(true)"
  unfolding bool_defs
  apply (rule comp_rls)
    apply typechk
   apply (erule_tac [!] TE)
   apply typechk
  done

lemma boolC_false: "\<lbrakk>a : C(true); b : C(false)\<rbrakk> \<Longrightarrow> cond(false,a,b) = b : C(false)"
  unfolding bool_defs
  apply (rule comp_rls)
    apply typechk
   apply (erule_tac [!] TE)
   apply typechk
  done

end
