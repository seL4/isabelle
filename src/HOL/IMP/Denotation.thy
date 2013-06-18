(* Authors: Heiko Loetzbeyer, Robert Sandner, Tobias Nipkow *)

header "Denotational Semantics of Commands"

theory Denotation imports Big_Step begin

type_synonym com_den = "(state \<times> state) set"

definition W :: "bexp \<Rightarrow> com_den \<Rightarrow> (com_den \<Rightarrow> com_den)" where
"W b rc = (\<lambda>rw. {(s,t). if bval b s then (s,t) \<in> rc O rw else s=t})"

fun C :: "com \<Rightarrow> com_den" where
"C SKIP   = {(s,t). s=t}" |
"C (x ::= a) = {(s,t). t = s(x := aval a s)}" |
"C (c0;;c1)  = C(c0) O C(c1)" |
"C (IF b THEN c1 ELSE c2)
 = {(s,t). if bval b s then (s,t) \<in> C c1 else (s,t) \<in> C c2}" |
"C(WHILE b DO c) = lfp (W b (C c))"

lemma W_mono: "mono (W b r)"
by (unfold W_def mono_def) auto

lemma C_While_If:
  "C(WHILE b DO c) = C(IF b THEN c;;WHILE b DO c ELSE SKIP)"
apply simp
apply (subst lfp_unfold [OF W_mono])  --{*lhs only*}
apply (simp add: W_def)
done

text{* Equivalence of denotational and big-step semantics: *}

lemma C_if_big_step:  "(c,s) \<Rightarrow> t \<Longrightarrow> (s,t) \<in> C(c)"
proof (induction rule: big_step_induct)
  case WhileFalse
  with C_While_If show ?case by auto
next
  case WhileTrue
  show ?case unfolding C_While_If using WhileTrue by auto
qed auto

abbreviation Big_step :: "com \<Rightarrow> com_den" where
"Big_step c \<equiv> {(s,t). (c,s) \<Rightarrow> t}"

lemma Big_step_if_C:  "(s,t) \<in> C(c) \<Longrightarrow> (s,t) : Big_step c"
proof (induction c arbitrary: s t)
  case Seq thus ?case by fastforce
next
  case (While b c)
  let ?B = "Big_step (WHILE b DO c)"
  have "W b (C c) ?B <= ?B" using While.IH by (auto simp: W_def)
  from lfp_lowerbound[where ?f = "W b (C c)", OF this] While.prems
  show ?case by auto
qed (auto split: if_splits)

theorem denotational_is_big_step:
  "(s,t) \<in> C(c)  =  ((c,s) \<Rightarrow> t)"
by (metis C_if_big_step Big_step_if_C[simplified])

end
