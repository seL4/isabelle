(* Author: Tobias Nipkow *)

theory Abs_Int2
imports Abs_Int1
begin

instantiation prod :: (order,order) order
begin

definition "less_eq_prod p1 p2 = (fst p1 \<le> fst p2 \<and> snd p1 \<le> snd p2)"
definition "less_prod p1 p2 = (p1 \<le> p2 \<and> \<not> p2 \<le> (p1::'a*'b))"

instance
proof
  case goal1 show ?case by(rule less_prod_def)
next
  case goal2 show ?case by(simp add: less_eq_prod_def)
next
  case goal3 thus ?case unfolding less_eq_prod_def by(metis order_trans)
next
  case goal4 thus ?case by(simp add: less_eq_prod_def)(metis eq_iff surjective_pairing)
qed

end


subsection "Backward Analysis of Expressions"

subclass (in bounded_lattice) semilattice_sup_top ..

locale Val_abs1_gamma = Gamma where \<gamma> = \<gamma>
  for \<gamma> :: "'av::bounded_lattice \<Rightarrow> val set" +
assumes inter_gamma_subset_gamma_inf:
  "\<gamma> a1 \<inter> \<gamma> a2 \<subseteq> \<gamma>(a1 \<sqinter> a2)"
and gamma_bot[simp]: "\<gamma> \<bottom> = {}"
begin

lemma in_gamma_inf: "x : \<gamma> a1 \<Longrightarrow> x : \<gamma> a2 \<Longrightarrow> x : \<gamma>(a1 \<sqinter> a2)"
by (metis IntI inter_gamma_subset_gamma_inf set_mp)

lemma gamma_inf: "\<gamma>(a1 \<sqinter> a2) = \<gamma> a1 \<inter> \<gamma> a2"
by(rule equalityI[OF _ inter_gamma_subset_gamma_inf])
  (metis inf_le1 inf_le2 le_inf_iff mono_gamma)

end


locale Val_abs1 = Val_abs1_gamma where \<gamma> = \<gamma>
   for \<gamma> :: "'av::bounded_lattice \<Rightarrow> val set" +
fixes test_num' :: "val \<Rightarrow> 'av \<Rightarrow> bool"
and filter_plus' :: "'av \<Rightarrow> 'av \<Rightarrow> 'av \<Rightarrow> 'av * 'av"
and filter_less' :: "bool \<Rightarrow> 'av \<Rightarrow> 'av \<Rightarrow> 'av * 'av"
assumes test_num': "test_num' n a = (n : \<gamma> a)"
and filter_plus': "filter_plus' a a1 a2 = (b1,b2) \<Longrightarrow>
  n1 : \<gamma> a1 \<Longrightarrow> n2 : \<gamma> a2 \<Longrightarrow> n1+n2 : \<gamma> a \<Longrightarrow> n1 : \<gamma> b1 \<and> n2 : \<gamma> b2"
and filter_less': "filter_less' (n1<n2) a1 a2 = (b1,b2) \<Longrightarrow>
  n1 : \<gamma> a1 \<Longrightarrow> n2 : \<gamma> a2 \<Longrightarrow> n1 : \<gamma> b1 \<and> n2 : \<gamma> b2"


locale Abs_Int1 = Val_abs1 where \<gamma> = \<gamma>
  for \<gamma> :: "'av::bounded_lattice \<Rightarrow> val set"
begin

lemma in_gamma_sup_UpI:
  "s : \<gamma>\<^isub>o S1 \<or> s : \<gamma>\<^isub>o S2 \<Longrightarrow> s : \<gamma>\<^isub>o(S1 \<squnion> S2)"
by (metis (hide_lams, no_types) sup_ge1 sup_ge2 mono_gamma_o subsetD)

fun aval'' :: "aexp \<Rightarrow> 'av st option \<Rightarrow> 'av" where
"aval'' e None = \<bottom>" |
"aval'' e (Some S) = aval' e S"

lemma aval''_sound: "s : \<gamma>\<^isub>o S \<Longrightarrow> aval a s : \<gamma>(aval'' a S)"
by(cases S)(auto simp add: aval'_sound split: option.splits)

subsubsection "Backward analysis"

fun afilter :: "aexp \<Rightarrow> 'av \<Rightarrow> 'av st option \<Rightarrow> 'av st option" where
"afilter (N n) a S = (if test_num' n a then S else None)" |
"afilter (V x) a S = (case S of None \<Rightarrow> None | Some S \<Rightarrow>
  let a' = fun S x \<sqinter> a in
  if a' = \<bottom> then None else Some(update S x a'))" |
"afilter (Plus e1 e2) a S =
 (let (a1,a2) = filter_plus' a (aval'' e1 S) (aval'' e2 S)
  in afilter e1 a1 (afilter e2 a2 S))"

text{* The test for @{const bot} in the @{const V}-case is important: @{const
bot} indicates that a variable has no possible values, i.e.\ that the current
program point is unreachable. But then the abstract state should collapse to
@{const None}. Put differently, we maintain the invariant that in an abstract
state of the form @{term"Some s"}, all variables are mapped to non-@{const
bot} values. Otherwise the (pointwise) sup of two abstract states, one of
which contains @{const bot} values, may produce too large a result, thus
making the analysis less precise. *}


fun bfilter :: "bexp \<Rightarrow> bool \<Rightarrow> 'av st option \<Rightarrow> 'av st option" where
"bfilter (Bc v) res S = (if v=res then S else None)" |
"bfilter (Not b) res S = bfilter b (\<not> res) S" |
"bfilter (And b1 b2) res S =
  (if res then bfilter b1 True (bfilter b2 True S)
   else bfilter b1 False S \<squnion> bfilter b2 False S)" |
"bfilter (Less e1 e2) res S =
  (let (a1,a2) = filter_less' res (aval'' e1 S) (aval'' e2 S)
   in afilter e1 a1 (afilter e2 a2 S))"

lemma afilter_sound: "s : \<gamma>\<^isub>o S \<Longrightarrow> aval e s : \<gamma> a \<Longrightarrow> s : \<gamma>\<^isub>o (afilter e a S)"
proof(induction e arbitrary: a S)
  case N thus ?case by simp (metis test_num')
next
  case (V x)
  obtain S' where "S = Some S'" and "s : \<gamma>\<^isub>s S'" using `s : \<gamma>\<^isub>o S`
    by(auto simp: in_gamma_option_iff)
  moreover hence "s x : \<gamma> (fun S' x)"
    by(simp add: \<gamma>_st_def)
  moreover have "s x : \<gamma> a" using V(2) by simp
  ultimately show ?case
    by(simp add: Let_def \<gamma>_st_def)
      (metis mono_gamma emptyE in_gamma_inf gamma_bot subset_empty)
next
  case (Plus e1 e2) thus ?case
    using filter_plus'[OF _ aval''_sound aval''_sound]
    by (auto split: prod.split)
qed

lemma bfilter_sound: "s : \<gamma>\<^isub>o S \<Longrightarrow> bv = bval b s \<Longrightarrow> s : \<gamma>\<^isub>o(bfilter b bv S)"
proof(induction b arbitrary: S bv)
  case Bc thus ?case by simp
next
  case (Not b) thus ?case by simp
next
  case (And b1 b2) thus ?case
    by simp (metis And(1) And(2) in_gamma_sup_UpI)
next
  case (Less e1 e2) thus ?case
    by(auto split: prod.split)
      (metis (lifting) afilter_sound aval''_sound filter_less')
qed

definition "step' = Step
  (\<lambda>x e S. case S of None \<Rightarrow> None | Some S \<Rightarrow> Some(update S x (aval' e S)))
  (\<lambda>b S. bfilter b True S)"

definition AI :: "com \<Rightarrow> 'av st option acom option" where
"AI c = pfp (step' \<top>) (bot c)"

lemma strip_step'[simp]: "strip(step' S c) = strip c"
by(simp add: step'_def)

lemma top_on_afilter: "\<lbrakk> top_on_opt S X;  vars e \<subseteq> -X \<rbrakk> \<Longrightarrow> top_on_opt (afilter e a S) X"
by(induction e arbitrary: a S) (auto simp: Let_def split: option.splits prod.split)

lemma top_on_bfilter: "\<lbrakk>top_on_opt S X; vars b \<subseteq> -X\<rbrakk> \<Longrightarrow> top_on_opt (bfilter b r S) X"
by(induction b arbitrary: r S) (auto simp: top_on_afilter top_on_sup split: prod.split)

lemma top_on_step': "top_on_acom C (- vars C) \<Longrightarrow> top_on_acom (step' \<top> C) (- vars C)"
unfolding step'_def
by(rule top_on_Step)
  (auto simp add: top_on_top top_on_bfilter split: option.split)

subsubsection "Soundness"

lemma step_step': "step (\<gamma>\<^isub>o S) (\<gamma>\<^isub>c C) \<le> \<gamma>\<^isub>c (step' S C)"
unfolding step_def step'_def
by(rule gamma_Step_subcomm)
  (auto simp: intro!: aval'_sound bfilter_sound in_gamma_update split: option.splits)

lemma AI_sound: "AI c = Some C \<Longrightarrow> CS c \<le> \<gamma>\<^isub>c C"
proof(simp add: CS_def AI_def)
  assume 1: "pfp (step' \<top>) (bot c) = Some C"
  have pfp': "step' \<top> C \<le> C" by(rule pfp_pfp[OF 1])
  have 2: "step (\<gamma>\<^isub>o \<top>) (\<gamma>\<^isub>c C) \<le> \<gamma>\<^isub>c C"  --"transfer the pfp'"
  proof(rule order_trans)
    show "step (\<gamma>\<^isub>o \<top>) (\<gamma>\<^isub>c C) \<le> \<gamma>\<^isub>c (step' \<top> C)" by(rule step_step')
    show "... \<le> \<gamma>\<^isub>c C" by (metis mono_gamma_c[OF pfp'])
  qed
  have 3: "strip (\<gamma>\<^isub>c C) = c" by(simp add: strip_pfp[OF _ 1] step'_def)
  have "lfp c (step (\<gamma>\<^isub>o \<top>)) \<le> \<gamma>\<^isub>c C"
    by(rule lfp_lowerbound[simplified,where f="step (\<gamma>\<^isub>o \<top>)", OF 3 2])
  thus "lfp c (step UNIV) \<le> \<gamma>\<^isub>c C" by simp
qed

end


subsubsection "Monotonicity"

locale Abs_Int1_mono = Abs_Int1 +
assumes mono_plus': "a1 \<le> b1 \<Longrightarrow> a2 \<le> b2 \<Longrightarrow> plus' a1 a2 \<le> plus' b1 b2"
and mono_filter_plus': "a1 \<le> b1 \<Longrightarrow> a2 \<le> b2 \<Longrightarrow> r \<le> r' \<Longrightarrow>
  filter_plus' r a1 a2 \<le> filter_plus' r' b1 b2"
and mono_filter_less': "a1 \<le> b1 \<Longrightarrow> a2 \<le> b2 \<Longrightarrow>
  filter_less' bv a1 a2 \<le> filter_less' bv b1 b2"
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

lemma mono_afilter: "r1 \<le> r2 \<Longrightarrow> S1 \<le> S2 \<Longrightarrow> afilter e r1 S1 \<le> afilter e r2 S2"
apply(induction e arbitrary: r1 r2 S1 S2)
   apply(auto simp: test_num' Let_def inf_mono split: option.splits prod.splits)
   apply (metis mono_gamma subsetD)
  apply (metis le_bot inf_mono le_st_iff)
 apply (metis inf_mono mono_update le_st_iff)
apply(metis mono_aval'' mono_filter_plus'[simplified less_eq_prod_def] fst_conv snd_conv)
done

lemma mono_bfilter: "S1 \<le> S2 \<Longrightarrow> bfilter b bv S1 \<le> bfilter b bv S2"
apply(induction b arbitrary: bv S1 S2)
   apply(simp)
  apply(simp)
 apply simp
 apply(metis order_trans[OF _ sup_ge1] order_trans[OF _ sup_ge2])
apply (simp split: prod.splits)
apply(metis mono_aval'' mono_afilter mono_filter_less'[simplified less_eq_prod_def] fst_conv snd_conv)
done

theorem mono_step': "S1 \<le> S2 \<Longrightarrow> C1 \<le> C2 \<Longrightarrow> step' S1 C1 \<le> step' S2 C2"
unfolding step'_def
by(rule mono2_Step) (auto simp: mono_aval' mono_bfilter split: option.split)

lemma mono_step'_top: "C1 \<le> C2 \<Longrightarrow> step' \<top> C1 \<le> step' \<top> C2"
by (metis mono_step' order_refl)

end

end
