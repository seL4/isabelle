theory Collecting1
imports Collecting
begin

subsection "A small step semantics on annotated commands"

text{* The idea: the state is propagated through the annotated command as an
annotation @{term "{s}"}, all other annotations are @{term "{}"}. It is easy
to show that this semantics approximates the collecting semantics. *}

lemma step_preserves_le:
  "\<lbrakk> step S cs = cs; S' \<subseteq> S; cs' \<le> cs \<rbrakk> \<Longrightarrow>
   step S' cs' \<le> cs"
by (metis mono2_step)

lemma steps_empty_preserves_le: assumes "step S cs = cs"
shows "cs' \<le> cs \<Longrightarrow> (step {} ^^ n) cs' \<le> cs"
proof(induction n arbitrary: cs')
  case 0 thus ?case by simp
next
  case (Suc n) thus ?case
    using Suc.IH[OF step_preserves_le[OF assms empty_subsetI Suc.prems]]
    by(simp add:funpow_swap1)
qed


definition steps :: "state \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> state set acom" where
"steps s c n = ((step {})^^n) (step {s} (anno {} c))"

lemma steps_approx_fix_step: assumes "step S cs = cs" and "s:S"
shows "steps s (strip cs) n \<le> cs"
proof-
  let ?bot = "anno {} (strip cs)"
  have "?bot \<le> cs" by(induction cs) auto
  from step_preserves_le[OF assms(1)_ this, of "{s}"] `s:S`
  have 1: "step {s} ?bot \<le> cs" by simp
  from steps_empty_preserves_le[OF assms(1) 1]
  show ?thesis by(simp add: steps_def)
qed

theorem steps_approx_CS: "steps s c n \<le> CS c"
by (metis CS_unfold UNIV_I steps_approx_fix_step strip_CS)

end
