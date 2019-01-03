(*  Title:      FOL/ex/If.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section \<open>First-Order Logic: the 'if' example\<close>

theory If
imports FOL
begin

definition "if" :: \<open>[o,o,o]=>o\<close>
  where \<open>if(P,Q,R) \<equiv> P \<and> Q \<or> \<not> P \<and> R\<close>

lemma ifI: \<open>\<lbrakk>P \<Longrightarrow> Q; \<not> P \<Longrightarrow> R\<rbrakk> \<Longrightarrow> if(P,Q,R)\<close>
  unfolding if_def by blast

lemma ifE: \<open>\<lbrakk>if(P,Q,R); \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> S; \<lbrakk>\<not> P; R\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S\<close>
  unfolding if_def by blast

lemma if_commute: \<open>if(P, if(Q,A,B), if(Q,C,D)) \<longleftrightarrow> if(Q, if(P,A,C), if(P,B,D))\<close>
  apply (rule iffI)
  apply (erule ifE)
  apply (erule ifE)
  apply (rule ifI)
  apply (rule ifI)
  oops

text\<open>Trying again from the beginning in order to use \<open>blast\<close>\<close>
declare ifI [intro!]
declare ifE [elim!]

lemma if_commute: \<open>if(P, if(Q,A,B), if(Q,C,D)) \<longleftrightarrow> if(Q, if(P,A,C), if(P,B,D))\<close>
  by blast


lemma \<open>if(if(P,Q,R), A, B) \<longleftrightarrow> if(P, if(Q,A,B), if(R,A,B))\<close>
  by blast

text\<open>Trying again from the beginning in order to prove from the definitions\<close>
lemma \<open>if(if(P,Q,R), A, B) \<longleftrightarrow> if(P, if(Q,A,B), if(R,A,B))\<close>
  unfolding if_def by blast


text \<open>An invalid formula. High-level rules permit a simpler diagnosis.\<close>
lemma \<open>if(if(P,Q,R), A, B) \<longleftrightarrow> if(P, if(Q,A,B), if(R,B,A))\<close>
  apply auto
    \<comment> \<open>The next step will fail unless subgoals remain\<close>
  apply (tactic all_tac)
  oops

text \<open>Trying again from the beginning in order to prove from the definitions.\<close>
lemma \<open>if(if(P,Q,R), A, B) \<longleftrightarrow> if(P, if(Q,A,B), if(R,B,A))\<close>
  unfolding if_def
  apply auto
    \<comment> \<open>The next step will fail unless subgoals remain\<close>
  apply (tactic all_tac)
  oops

end
