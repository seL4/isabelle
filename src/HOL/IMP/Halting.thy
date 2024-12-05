(*
Undecidability of the special Halting problem:
  Does a program applied to an encoding of itself terminate?
Author: Fabian Huch
*)

theory Halting
  imports "HOL-IMP.Big_Step"
begin

definition "halts c s \<equiv> (\<exists>s'. (c, s) \<Rightarrow> s')"

text \<open>A simple program that does not halt:\<close>
definition "loop \<equiv> WHILE Bc True DO SKIP"

lemma loop_never_halts[simp]: "\<not> halts loop s"
  unfolding halts_def
proof clarify
  fix s' assume "(loop, s) \<Rightarrow> s'"
  then show False
    by (induction loop s s' rule: big_step_induct) (simp_all add: loop_def)
qed

section \<open>Halting Problem\<close>

text \<open>
Given any encoding \<open>f\<close> (of programs to states), there is no Program \<open>H\<close> such that 
for all programs \<open>c\<close>, \<open>H\<close> terminates in a state \<open>s'\<close> which has at variable \<open>x\<close> the
answer whether \<open>c\<close> halts.\<close>

theorem halting: 
  "\<nexists>H. \<forall>c. \<exists>s'. (H, f c) \<Rightarrow> s' \<and> (halts c (f c) \<longleftrightarrow> s' x > 0)"
  (is "\<nexists>H. ?P H")
proof clarify
  fix H assume assm: "?P H"

  \<comment> \<open>inverted H: loops if input halts\<close>
  let ?inv_H = "H ;; IF Less (V x) (N 1) THEN SKIP ELSE loop" 

  \<comment> \<open>compute in \<open>s'\<close> whether inverted \<open>H\<close> halts when applied to itself\<close>
  obtain s' where 
    s'_def: "(H, f ?inv_H) \<Rightarrow> s'" and 
    s'_halts: "halts ?inv_H (f ?inv_H) \<longleftrightarrow> (s' x > 0)" 
    using assm by blast

  \<comment> \<open>contradiction: if it terminates, loop must have terminated; if not, SKIP must have looped!\<close>
  show False
  proof(cases "halts ?inv_H (f ?inv_H)")
    case True

    then have "halts (IF Less (V x) (N 1) THEN SKIP ELSE loop) s'"
      unfolding halts_def using big_step_determ s'_def by fast

    then have "halts loop s'"
      using s'_halts True halts_def by auto

    then show False by auto
  next
    case False

    then have "\<not> halts SKIP s'"
      using s'_def s'_halts halts_def by force

    then show False using halts_def by auto
  qed
qed

end
