(* Author: Tobias Nipkow *)

subsection "Backward Analysis of Expressions"

theory Abs_Int2
imports Abs_Int1
begin

instantiation prod :: (order,order) order
begin

definition "less_eq_prod p1 p2 = (fst p1 \<le> fst p2 \<and> snd p1 \<le> snd p2)"
definition "less_prod p1 p2 = (p1 \<le> p2 \<and> \<not> p2 \<le> (p1::'a*'b))"

instance
proof (standard, goal_cases)
  case 1 show ?case by(rule less_prod_def)
next
  case 2 show ?case by(simp add: less_eq_prod_def)
next
  case 3 thus ?case unfolding less_eq_prod_def by(metis order_trans)
next
  case 4 thus ?case by(simp add: less_eq_prod_def)(metis eq_iff surjective_pairing)
qed

end


subsubsection "Extended Framework"

subclass (in bounded_lattice) semilattice_sup_top ..

locale Val_lattice_gamma = Gamma_semilattice where \<gamma> = \<gamma>
  for \<gamma> :: "'av::bounded_lattice \<Rightarrow> val set" +
assumes inter_gamma_subset_gamma_inf:
  "\<gamma> a1 \<inter> \<gamma> a2 \<subseteq> \<gamma>(a1 \<sqinter> a2)"
and gamma_bot[simp]: "\<gamma> \<bottom> = {}"
begin

lemma in_gamma_inf: "x \<in> \<gamma> a1 \<Longrightarrow> x \<in> \<gamma> a2 \<Longrightarrow> x \<in> \<gamma>(a1 \<sqinter> a2)"
by (metis IntI inter_gamma_subset_gamma_inf subsetD)

lemma gamma_inf: "\<gamma>(a1 \<sqinter> a2) = \<gamma> a1 \<inter> \<gamma> a2"
by(rule equalityI[OF _ inter_gamma_subset_gamma_inf])
  (metis inf_le1 inf_le2 le_inf_iff mono_gamma)

end


locale Val_inv = Val_lattice_gamma where \<gamma> = \<gamma>
   for \<gamma> :: "'av::bounded_lattice \<Rightarrow> val set" +
fixes test_num' :: "val \<Rightarrow> 'av \<Rightarrow> bool"
and inv_plus' :: "'av \<Rightarrow> 'av \<Rightarrow> 'av \<Rightarrow> 'av * 'av"
and inv_less' :: "bool \<Rightarrow> 'av \<Rightarrow> 'av \<Rightarrow> 'av * 'av"
assumes test_num': "test_num' i a = (i \<in> \<gamma> a)"
and inv_plus': "inv_plus' a a1 a2 = (a\<^sub>1',a\<^sub>2') \<Longrightarrow>
  i1 \<in> \<gamma> a1 \<Longrightarrow> i2 \<in> \<gamma> a2 \<Longrightarrow> i1+i2 \<in> \<gamma> a \<Longrightarrow> i1 \<in> \<gamma> a\<^sub>1' \<and> i2 \<in> \<gamma> a\<^sub>2'"
and inv_less': "inv_less' (i1<i2) a1 a2 = (a\<^sub>1',a\<^sub>2') \<Longrightarrow>
  i1 \<in> \<gamma> a1 \<Longrightarrow> i2 \<in> \<gamma> a2 \<Longrightarrow> i1 \<in> \<gamma> a\<^sub>1' \<and> i2 \<in> \<gamma> a\<^sub>2'"


locale Abs_Int_inv = Val_inv where \<gamma> = \<gamma>
  for \<gamma> :: "'av::bounded_lattice \<Rightarrow> val set"
begin

lemma in_gamma_sup_UpI:
  "s \<in> \<gamma>\<^sub>o S1 \<or> s \<in> \<gamma>\<^sub>o S2 \<Longrightarrow> s \<in> \<gamma>\<^sub>o(S1 \<squnion> S2)"
by (metis (opaque_lifting, no_types) sup_ge1 sup_ge2 mono_gamma_o subsetD)

fun aval'' :: "aexp \<Rightarrow> 'av st option \<Rightarrow> 'av" where
"aval'' e None = \<bottom>" |
"aval'' e (Some S) = aval' e S"

lemma aval''_correct: "s \<in> \<gamma>\<^sub>o S \<Longrightarrow> aval a s \<in> \<gamma>(aval'' a S)"
by(cases S)(auto simp add: aval'_correct split: option.splits)

subsubsection "Backward analysis"

fun inv_aval' :: "aexp \<Rightarrow> 'av \<Rightarrow> 'av st option \<Rightarrow> 'av st option" where
"inv_aval' (N n) a S = (if test_num' n a then S else None)" |
"inv_aval' (V x) a S = (case S of None \<Rightarrow> None | Some S \<Rightarrow>
  let a' = fun S x \<sqinter> a in
  if a' = \<bottom> then None else Some(update S x a'))" |
"inv_aval' (Plus e1 e2) a S =
 (let (a1,a2) = inv_plus' a (aval'' e1 S) (aval'' e2 S)
  in inv_aval' e1 a1 (inv_aval' e2 a2 S))"

text\<open>The test for \<^const>\<open>bot\<close> in the \<^const>\<open>V\<close>-case is important: \<^const>\<open>bot\<close> indicates that a variable has no possible values, i.e.\ that the current
program point is unreachable. But then the abstract state should collapse to
\<^const>\<open>None\<close>. Put differently, we maintain the invariant that in an abstract
state of the form \<^term>\<open>Some s\<close>, all variables are mapped to non-\<^const>\<open>bot\<close> values. Otherwise the (pointwise) sup of two abstract states, one of
which contains \<^const>\<open>bot\<close> values, may produce too large a result, thus
making the analysis less precise.\<close>


fun inv_bval' :: "bexp \<Rightarrow> bool \<Rightarrow> 'av st option \<Rightarrow> 'av st option" where
"inv_bval' (Bc v) res S = (if v=res then S else None)" |
"inv_bval' (Not b) res S = inv_bval' b (\<not> res) S" |
"inv_bval' (And b1 b2) res S =
  (if res then inv_bval' b1 True (inv_bval' b2 True S)
   else inv_bval' b1 False S \<squnion> inv_bval' b2 False S)" |
"inv_bval' (Less e1 e2) res S =
  (let (a1,a2) = inv_less' res (aval'' e1 S) (aval'' e2 S)
   in inv_aval' e1 a1 (inv_aval' e2 a2 S))"

lemma inv_aval'_correct: "s \<in> \<gamma>\<^sub>o S \<Longrightarrow> aval e s \<in> \<gamma> a \<Longrightarrow> s \<in> \<gamma>\<^sub>o (inv_aval' e a S)"
proof(induction e arbitrary: a S)
  case N thus ?case by simp (metis test_num')
next
  case (V x)
  obtain S' where "S = Some S'" and "s \<in> \<gamma>\<^sub>s S'" using \<open>s \<in> \<gamma>\<^sub>o S\<close>
    by(auto simp: in_gamma_option_iff)
  moreover hence "s x \<in> \<gamma> (fun S' x)"
    by(simp add: \<gamma>_st_def)
  moreover have "s x \<in> \<gamma> a" using V(2) by simp
  ultimately show ?case
    by(simp add: Let_def \<gamma>_st_def)
      (metis mono_gamma emptyE in_gamma_inf gamma_bot subset_empty)
next
  case (Plus e1 e2) thus ?case
    using inv_plus'[OF _ aval''_correct aval''_correct]
    by (auto split: prod.split)
qed

lemma inv_bval'_correct: "s \<in> \<gamma>\<^sub>o S \<Longrightarrow> bv = bval b s \<Longrightarrow> s \<in> \<gamma>\<^sub>o(inv_bval' b bv S)"
proof(induction b arbitrary: S bv)
  case Bc thus ?case by simp
next
  case (Not b) thus ?case by simp
next
  case (And b1 b2) thus ?case
    by simp (metis And(1) And(2) in_gamma_sup_UpI)
next
  case (Less e1 e2) thus ?case
    apply hypsubst_thin
    apply (auto split: prod.split)
    apply (metis (lifting) inv_aval'_correct aval''_correct inv_less')
    done
qed

definition "step' = Step
  (\<lambda>x e S. case S of None \<Rightarrow> None | Some S \<Rightarrow> Some(update S x (aval' e S)))
  (\<lambda>b S. inv_bval' b True S)"

definition AI :: "com \<Rightarrow> 'av st option acom option" where
"AI c = pfp (step' \<top>) (bot c)"

lemma strip_step'[simp]: "strip(step' S c) = strip c"
by(simp add: step'_def)

lemma top_on_inv_aval': "\<lbrakk> top_on_opt S X;  vars e \<subseteq> -X \<rbrakk> \<Longrightarrow> top_on_opt (inv_aval' e a S) X"
by(induction e arbitrary: a S) (auto simp: Let_def split: option.splits prod.split)

lemma top_on_inv_bval': "\<lbrakk>top_on_opt S X; vars b \<subseteq> -X\<rbrakk> \<Longrightarrow> top_on_opt (inv_bval' b r S) X"
by(induction b arbitrary: r S) (auto simp: top_on_inv_aval' top_on_sup split: prod.split)

lemma top_on_step': "top_on_acom C (- vars C) \<Longrightarrow> top_on_acom (step' \<top> C) (- vars C)"
unfolding step'_def
by(rule top_on_Step)
  (auto simp add: top_on_top top_on_inv_bval' split: option.split)

subsubsection "Correctness"

lemma step_step': "step (\<gamma>\<^sub>o S) (\<gamma>\<^sub>c C) \<le> \<gamma>\<^sub>c (step' S C)"
unfolding step_def step'_def
by(rule gamma_Step_subcomm)
  (auto simp: intro!: aval'_correct inv_bval'_correct in_gamma_update split: option.splits)

lemma AI_correct: "AI c = Some C \<Longrightarrow> CS c \<le> \<gamma>\<^sub>c C"
proof(simp add: CS_def AI_def)
  assume 1: "pfp (step' \<top>) (bot c) = Some C"
  have pfp': "step' \<top> C \<le> C" by(rule pfp_pfp[OF 1])
  have 2: "step (\<gamma>\<^sub>o \<top>) (\<gamma>\<^sub>c C) \<le> \<gamma>\<^sub>c C"  \<comment> \<open>transfer the pfp'\<close>
  proof(rule order_trans)
    show "step (\<gamma>\<^sub>o \<top>) (\<gamma>\<^sub>c C) \<le> \<gamma>\<^sub>c (step' \<top> C)" by(rule step_step')
    show "... \<le> \<gamma>\<^sub>c C" by (metis mono_gamma_c[OF pfp'])
  qed
  have 3: "strip (\<gamma>\<^sub>c C) = c" by(simp add: strip_pfp[OF _ 1] step'_def)
  have "lfp c (step (\<gamma>\<^sub>o \<top>)) \<le> \<gamma>\<^sub>c C"
    by(rule lfp_lowerbound[simplified,where f="step (\<gamma>\<^sub>o \<top>)", OF 3 2])
  thus "lfp c (step UNIV) \<le> \<gamma>\<^sub>c C" by simp
qed

end


subsubsection "Monotonicity"

locale Abs_Int_inv_mono = Abs_Int_inv +
assumes mono_plus': "a1 \<le> b1 \<Longrightarrow> a2 \<le> b2 \<Longrightarrow> plus' a1 a2 \<le> plus' b1 b2"
and mono_inv_plus': "a1 \<le> b1 \<Longrightarrow> a2 \<le> b2 \<Longrightarrow> r \<le> r' \<Longrightarrow>
  inv_plus' r a1 a2 \<le> inv_plus' r' b1 b2"
and mono_inv_less': "a1 \<le> b1 \<Longrightarrow> a2 \<le> b2 \<Longrightarrow>
  inv_less' bv a1 a2 \<le> inv_less' bv b1 b2"
begin

lemma mono_aval':
  "S1 \<le> S2 \<Longrightarrow> aval' e S1 \<le> aval' e S2"
by(induction e) (auto simp: mono_plus' mono_fun)

lemma mono_aval'':
  "S1 \<le> S2 \<Longrightarrow> aval'' e S1 \<le> aval'' e S2"
apply(cases S1)
 apply simp
apply(cases S2)
 apply simp
by (simp add: mono_aval')

lemma mono_inv_aval': "r1 \<le> r2 \<Longrightarrow> S1 \<le> S2 \<Longrightarrow> inv_aval' e r1 S1 \<le> inv_aval' e r2 S2"
apply(induction e arbitrary: r1 r2 S1 S2)
   apply(auto simp: test_num' Let_def inf_mono split: option.splits prod.splits)
   apply (metis mono_gamma subsetD)
  apply (metis le_bot inf_mono le_st_iff)
 apply (metis inf_mono mono_update le_st_iff)
apply(metis mono_aval'' mono_inv_plus'[simplified less_eq_prod_def] fst_conv snd_conv)
done

lemma mono_inv_bval': "S1 \<le> S2 \<Longrightarrow> inv_bval' b bv S1 \<le> inv_bval' b bv S2"
apply(induction b arbitrary: bv S1 S2)
   apply(simp)
  apply(simp)
 apply simp
 apply(metis order_trans[OF _ sup_ge1] order_trans[OF _ sup_ge2])
apply (simp split: prod.splits)
apply(metis mono_aval'' mono_inv_aval' mono_inv_less'[simplified less_eq_prod_def] fst_conv snd_conv)
done

theorem mono_step': "S1 \<le> S2 \<Longrightarrow> C1 \<le> C2 \<Longrightarrow> step' S1 C1 \<le> step' S2 C2"
unfolding step'_def
by(rule mono2_Step) (auto simp: mono_aval' mono_inv_bval' split: option.split)

lemma mono_step'_top: "C1 \<le> C2 \<Longrightarrow> step' \<top> C1 \<le> step' \<top> C2"
by (metis mono_step' order_refl)

end

end
