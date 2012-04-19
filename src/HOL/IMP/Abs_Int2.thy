(* Author: Tobias Nipkow *)

theory Abs_Int2
imports Abs_Int1
begin

instantiation prod :: (preord,preord) preord
begin

definition "le_prod p1 p2 = (fst p1 \<sqsubseteq> fst p2 \<and> snd p1 \<sqsubseteq> snd p2)"

instance
proof
  case goal1 show ?case by(simp add: le_prod_def)
next
  case goal2 thus ?case unfolding le_prod_def by(metis le_trans)
qed

end


subsection "Backward Analysis of Expressions"

class L_top_bot = SL_top + Bot +
fixes meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 65)
assumes meet_le1 [simp]: "x \<sqinter> y \<sqsubseteq> x"
and meet_le2 [simp]: "x \<sqinter> y \<sqsubseteq> y"
and meet_greatest: "x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<sqinter> z"
begin

lemma mono_meet: "x \<sqsubseteq> x' \<Longrightarrow> y \<sqsubseteq> y' \<Longrightarrow> x \<sqinter> y \<sqsubseteq> x' \<sqinter> y'"
by (metis meet_greatest meet_le1 meet_le2 le_trans)

end

locale Val_abs1_gamma =
  Gamma where \<gamma> = \<gamma> for \<gamma> :: "'av::L_top_bot \<Rightarrow> val set" +
assumes inter_gamma_subset_gamma_meet:
  "\<gamma> a1 \<inter> \<gamma> a2 \<subseteq> \<gamma>(a1 \<sqinter> a2)"
and gamma_Bot[simp]: "\<gamma> \<bottom> = {}"
begin

lemma in_gamma_meet: "x : \<gamma> a1 \<Longrightarrow> x : \<gamma> a2 \<Longrightarrow> x : \<gamma>(a1 \<sqinter> a2)"
by (metis IntI inter_gamma_subset_gamma_meet set_mp)

lemma gamma_meet[simp]: "\<gamma>(a1 \<sqinter> a2) = \<gamma> a1 \<inter> \<gamma> a2"
by (metis equalityI inter_gamma_subset_gamma_meet le_inf_iff mono_gamma meet_le1 meet_le2)

end


locale Val_abs1 =
  Val_abs1_gamma where \<gamma> = \<gamma>
   for \<gamma> :: "'av::L_top_bot \<Rightarrow> val set" +
fixes test_num' :: "val \<Rightarrow> 'av \<Rightarrow> bool"
and filter_plus' :: "'av \<Rightarrow> 'av \<Rightarrow> 'av \<Rightarrow> 'av * 'av"
and filter_less' :: "bool \<Rightarrow> 'av \<Rightarrow> 'av \<Rightarrow> 'av * 'av"
assumes test_num': "test_num' n a = (n : \<gamma> a)"
and filter_plus': "filter_plus' a a1 a2 = (b1,b2) \<Longrightarrow>
  n1 : \<gamma> a1 \<Longrightarrow> n2 : \<gamma> a2 \<Longrightarrow> n1+n2 : \<gamma> a \<Longrightarrow> n1 : \<gamma> b1 \<and> n2 : \<gamma> b2"
and filter_less': "filter_less' (n1<n2) a1 a2 = (b1,b2) \<Longrightarrow>
  n1 : \<gamma> a1 \<Longrightarrow> n2 : \<gamma> a2 \<Longrightarrow> n1 : \<gamma> b1 \<and> n2 : \<gamma> b2"


locale Abs_Int1 =
  Val_abs1 where \<gamma> = \<gamma> for \<gamma> :: "'av::L_top_bot \<Rightarrow> val set"
begin

lemma in_gamma_join_UpI:
  "wt S1 X \<Longrightarrow> wt S2 X \<Longrightarrow> s : \<gamma>\<^isub>o S1 \<or> s : \<gamma>\<^isub>o S2 \<Longrightarrow> s : \<gamma>\<^isub>o(S1 \<squnion> S2)"
by (metis (hide_lams, no_types) SL_top_wt_class.join_ge1 SL_top_wt_class.join_ge2 mono_gamma_o subsetD)

fun aval'' :: "aexp \<Rightarrow> 'av st option \<Rightarrow> 'av" where
"aval'' e None = \<bottom>" |
"aval'' e (Some sa) = aval' e sa"

lemma aval''_sound: "s : \<gamma>\<^isub>o S \<Longrightarrow> wt S X \<Longrightarrow> vars a \<subseteq> X \<Longrightarrow> aval a s : \<gamma>(aval'' a S)"
by(simp add: wt_option_def wt_st_def aval'_sound split: option.splits)

subsubsection "Backward analysis"

fun afilter :: "aexp \<Rightarrow> 'av \<Rightarrow> 'av st option \<Rightarrow> 'av st option" where
"afilter (N n) a S = (if test_num' n a then S else None)" |
"afilter (V x) a S = (case S of None \<Rightarrow> None | Some S \<Rightarrow>
  let a' = fun S x \<sqinter> a in
  if a' \<sqsubseteq> \<bottom> then None else Some(update S x a'))" |
"afilter (Plus e1 e2) a S =
 (let (a1,a2) = filter_plus' a (aval'' e1 S) (aval'' e2 S)
  in afilter e1 a1 (afilter e2 a2 S))"

text{* The test for @{const bot} in the @{const V}-case is important: @{const
bot} indicates that a variable has no possible values, i.e.\ that the current
program point is unreachable. But then the abstract state should collapse to
@{const None}. Put differently, we maintain the invariant that in an abstract
state of the form @{term"Some s"}, all variables are mapped to non-@{const
bot} values. Otherwise the (pointwise) join of two abstract states, one of
which contains @{const bot} values, may produce too large a result, thus
making the analysis less precise. *}


fun bfilter :: "bexp \<Rightarrow> bool \<Rightarrow> 'av st option \<Rightarrow> 'av st option" where
"bfilter (Bc v) res S = (if v=res then S else None)" |
"bfilter (Not b) res S = bfilter b (\<not> res) S" |
"bfilter (And b1 b2) res S =
  (if res then bfilter b1 True (bfilter b2 True S)
   else bfilter b1 False S \<squnion> bfilter b2 False S)" |
"bfilter (Less e1 e2) res S =
  (let (res1,res2) = filter_less' res (aval'' e1 S) (aval'' e2 S)
   in afilter e1 res1 (afilter e2 res2 S))"

lemma wt_afilter: "wt S X \<Longrightarrow> vars e \<subseteq> X ==> wt (afilter e a S) X"
by(induction e arbitrary: a S)
  (auto simp: Let_def update_def wt_st_def
           split: option.splits prod.split)

lemma afilter_sound: "wt S X \<Longrightarrow> vars e \<subseteq> X \<Longrightarrow>
  s : \<gamma>\<^isub>o S \<Longrightarrow> aval e s : \<gamma> a \<Longrightarrow> s : \<gamma>\<^isub>o (afilter e a S)"
proof(induction e arbitrary: a S)
  case N thus ?case by simp (metis test_num')
next
  case (V x)
  obtain S' where "S = Some S'" and "s : \<gamma>\<^isub>f S'" using `s : \<gamma>\<^isub>o S`
    by(auto simp: in_gamma_option_iff)
  moreover hence "s x : \<gamma> (fun S' x)"
    using V(1,2) by(simp add: \<gamma>_st_def wt_st_def)
  moreover have "s x : \<gamma> a" using V by simp
  ultimately show ?case using V(3)
    by(simp add: Let_def \<gamma>_st_def)
      (metis mono_gamma emptyE in_gamma_meet gamma_Bot subset_empty)
next
  case (Plus e1 e2) thus ?case
    using filter_plus'[OF _ aval''_sound[OF Plus.prems(3)] aval''_sound[OF Plus.prems(3)]]
    by (auto simp: wt_afilter split: prod.split)
qed

lemma wt_bfilter: "wt S X \<Longrightarrow> vars b \<subseteq> X \<Longrightarrow> wt (bfilter b bv S) X"
by(induction b arbitrary: bv S)
  (auto simp: wt_afilter split: prod.split)

lemma bfilter_sound: "wt S X \<Longrightarrow> vars b \<subseteq> X \<Longrightarrow>
  s : \<gamma>\<^isub>o S \<Longrightarrow> bv = bval b s \<Longrightarrow> s : \<gamma>\<^isub>o(bfilter b bv S)"
proof(induction b arbitrary: S bv)
  case Bc thus ?case by simp
next
  case (Not b) thus ?case by simp
next
  case (And b1 b2) thus ?case
    by simp (metis And(1) And(2) wt_bfilter in_gamma_join_UpI)
next
  case (Less e1 e2) thus ?case
    by(auto split: prod.split)
      (metis (lifting) wt_afilter afilter_sound aval''_sound filter_less')
qed


fun step' :: "'av st option \<Rightarrow> 'av st option acom \<Rightarrow> 'av st option acom"
 where
"step' S (SKIP {P}) = (SKIP {S})" |
"step' S (x ::= e {P}) =
  x ::= e {case S of None \<Rightarrow> None | Some S \<Rightarrow> Some(update S x (aval' e S))}" |
"step' S (C1; C2) = step' S C1; step' (post C1) C2" |
"step' S (IF b THEN C1 ELSE C2 {P}) =
  (let D1 = step' (bfilter b True S) C1; D2 = step' (bfilter b False S) C2
   in IF b THEN D1 ELSE D2 {post C1 \<squnion> post C2})" |
"step' S ({Inv} WHILE b DO C {P}) =
   {S \<squnion> post C}
   WHILE b DO step' (bfilter b True Inv) C
   {bfilter b False Inv}"

definition AI :: "com \<Rightarrow> 'av st option acom option" where
"AI c = lpfp (step' \<top>\<^bsub>c\<^esub>) c"

lemma strip_step'[simp]: "strip(step' S c) = strip c"
by(induct c arbitrary: S) (simp_all add: Let_def)


subsubsection "Soundness"

lemma in_gamma_update:
  "\<lbrakk> s : \<gamma>\<^isub>f S; i : \<gamma> a \<rbrakk> \<Longrightarrow> s(x := i) : \<gamma>\<^isub>f(update S x a)"
by(simp add: \<gamma>_st_def)

theorem step_preserves_le:
  "\<lbrakk> S \<subseteq> \<gamma>\<^isub>o S'; C \<le> \<gamma>\<^isub>c C'; wt C' X; wt S' X \<rbrakk> \<Longrightarrow> step S C \<le> \<gamma>\<^isub>c (step' S' C')"
proof(induction C arbitrary: C' S S')
  case SKIP thus ?case by(auto simp:SKIP_le map_acom_SKIP)
next
  case Assign thus ?case
    by (fastforce simp: Assign_le map_acom_Assign wt_option_def wt_st_def
        intro: aval'_sound in_gamma_update  split: option.splits del:subsetD)
next
  case Semi thus ?case apply (auto simp: Semi_le map_acom_Semi)
    by (metis le_post post_map_acom wt_post)
next
  case (If b C1 C2 P)
  then obtain C1' C2' P' where
      "C' = IF b THEN C1' ELSE C2' {P'}"
      "P \<subseteq> \<gamma>\<^isub>o P'" "C1 \<le> \<gamma>\<^isub>c C1'" "C2 \<le> \<gamma>\<^isub>c C2'"
    by (fastforce simp: If_le map_acom_If)
  moreover from this(1) `wt C' X` have wt: "wt C1' X" "wt C2' X"
    and "vars b \<subseteq> X" by simp_all
  moreover have "post C1 \<subseteq> \<gamma>\<^isub>o(post C1' \<squnion> post C2')"
    by (metis (no_types) `C1 \<le> \<gamma>\<^isub>c C1'` join_ge1 le_post mono_gamma_o order_trans post_map_acom wt_post wt)
  moreover have "post C2 \<subseteq> \<gamma>\<^isub>o(post C1' \<squnion> post C2')"
    by (metis (no_types) `C2 \<le> \<gamma>\<^isub>c C2'` join_ge2 le_post mono_gamma_o order_trans post_map_acom wt_post wt)
  moreover note vars = `wt S' X` `vars b \<subseteq> X`
  ultimately show ?case using `S \<subseteq> \<gamma>\<^isub>o S'`
    by (simp add: If.IH subset_iff bfilter_sound[OF vars] wt_bfilter[OF vars])
next
  case (While I b C1 P)
  then obtain C1' I' P' where
    "C' = {I'} WHILE b DO C1' {P'}"
    "I \<subseteq> \<gamma>\<^isub>o I'" "P \<subseteq> \<gamma>\<^isub>o P'" "C1 \<le> \<gamma>\<^isub>c C1'"
    by (fastforce simp: map_acom_While While_le)
  moreover from this(1) `wt C' X`
  have wt: "wt C1' X" "wt I' X" and "vars b \<subseteq> X" by simp_all
  moreover note compat = `wt S' X` wt_post[OF wt(1)]
  moreover note vars = `wt I' X` `vars b \<subseteq> X`
  moreover have "S \<union> post C1 \<subseteq> \<gamma>\<^isub>o (S' \<squnion> post C1')"
    using `S \<subseteq> \<gamma>\<^isub>o S'` le_post[OF `C1 \<le> \<gamma>\<^isub>c C1'`, simplified]
    by (metis (no_types) join_ge1[OF compat] join_ge2[OF compat] le_sup_iff mono_gamma_o order_trans)
  ultimately show ?case
    by (simp add: While.IH subset_iff bfilter_sound[OF vars] wt_bfilter[OF vars])
qed

lemma wt_step'[simp]:
  "\<lbrakk> wt C X; wt S X \<rbrakk> \<Longrightarrow> wt (step' S C) X"
proof(induction C arbitrary: S)
  case Assign thus ?case by(simp add: wt_option_def wt_st_def update_def split: option.splits)
qed (auto simp add: wt_bfilter)

theorem AI_sound: "AI c = Some C \<Longrightarrow> CS c \<le> \<gamma>\<^isub>c C"
proof(simp add: CS_def AI_def)
  assume 1: "lpfp (step' (top c)) c = Some C"
  have "wt C (vars c)"
    by(rule lpfp_inv[where P = "%C. wt C (vars c)", OF 1 _ wt_bot])
      (erule wt_step'[OF _ wt_top])
  have 2: "step' (top c) C \<sqsubseteq> C" by(rule lpfpc_pfp[OF 1])
  have 3: "strip (\<gamma>\<^isub>c (step' (top c) C)) = c"
    by(simp add: strip_lpfp[OF _ 1])
  have "lfp (step UNIV) c \<le> \<gamma>\<^isub>c (step' (top c) C)"
  proof(rule lfp_lowerbound[simplified,OF 3])
    show "step UNIV (\<gamma>\<^isub>c (step' (top c) C)) \<le> \<gamma>\<^isub>c (step' (top c) C)"
    proof(rule step_preserves_le[OF _ _ `wt C (vars c)` wt_top])
      show "UNIV \<subseteq> \<gamma>\<^isub>o (top c)" by simp
      show "\<gamma>\<^isub>c (step' (top c) C) \<le> \<gamma>\<^isub>c C" by(rule mono_gamma_c[OF 2])
    qed
  qed
  from this 2 show "lfp (step UNIV) c \<le> \<gamma>\<^isub>c C"
    by (blast intro: mono_gamma_c order_trans)
qed

end


subsubsection "Monotonicity"

locale Abs_Int1_mono = Abs_Int1 +
assumes mono_plus': "a1 \<sqsubseteq> b1 \<Longrightarrow> a2 \<sqsubseteq> b2 \<Longrightarrow> plus' a1 a2 \<sqsubseteq> plus' b1 b2"
and mono_filter_plus': "a1 \<sqsubseteq> b1 \<Longrightarrow> a2 \<sqsubseteq> b2 \<Longrightarrow> r \<sqsubseteq> r' \<Longrightarrow>
  filter_plus' r a1 a2 \<sqsubseteq> filter_plus' r' b1 b2"
and mono_filter_less': "a1 \<sqsubseteq> b1 \<Longrightarrow> a2 \<sqsubseteq> b2 \<Longrightarrow>
  filter_less' bv a1 a2 \<sqsubseteq> filter_less' bv b1 b2"
begin

lemma mono_aval':
  "S1 \<sqsubseteq> S2 \<Longrightarrow> wt S1 X \<Longrightarrow> vars e \<subseteq> X \<Longrightarrow> aval' e S1 \<sqsubseteq> aval' e S2"
by(induction e) (auto simp: le_st_def mono_plus' wt_st_def)

lemma mono_aval'':
  "S1 \<sqsubseteq> S2 \<Longrightarrow> wt S1 X \<Longrightarrow> vars e \<subseteq> X \<Longrightarrow> aval'' e S1 \<sqsubseteq> aval'' e S2"
apply(cases S1)
 apply simp
apply(cases S2)
 apply simp
by (simp add: mono_aval')

lemma mono_afilter: "wt S1 X \<Longrightarrow> wt S2 X \<Longrightarrow> vars e \<subseteq> X \<Longrightarrow>
  r1 \<sqsubseteq> r2 \<Longrightarrow> S1 \<sqsubseteq> S2 \<Longrightarrow> afilter e r1 S1 \<sqsubseteq> afilter e r2 S2"
apply(induction e arbitrary: r1 r2 S1 S2)
apply(auto simp: test_num' Let_def mono_meet split: option.splits prod.splits)
apply (metis mono_gamma subsetD)
apply(drule (2) mono_fun_wt)
apply (metis mono_meet le_trans)
apply(metis mono_aval'' mono_filter_plus'[simplified le_prod_def] fst_conv snd_conv wt_afilter)
done

lemma mono_bfilter: "wt S1 X \<Longrightarrow> wt S2 X \<Longrightarrow> vars b \<subseteq> X \<Longrightarrow>
  S1 \<sqsubseteq> S2 \<Longrightarrow> bfilter b bv S1 \<sqsubseteq> bfilter b bv S2"
apply(induction b arbitrary: bv S1 S2)
apply(simp)
apply(simp)
apply simp
apply(metis join_least le_trans[OF _ join_ge1] le_trans[OF _ join_ge2] wt_bfilter)
apply (simp split: prod.splits)
apply(metis mono_aval'' mono_afilter mono_filter_less'[simplified le_prod_def] fst_conv snd_conv wt_afilter)
done

theorem mono_step': "wt S1 X \<Longrightarrow> wt S2 X \<Longrightarrow> wt C1 X \<Longrightarrow> wt C2 X \<Longrightarrow>
  S1 \<sqsubseteq> S2 \<Longrightarrow> C1 \<sqsubseteq> C2 \<Longrightarrow> step' S1 C1 \<sqsubseteq> step' S2 C2"
apply(induction C1 C2 arbitrary: S1 S2 rule: le_acom.induct)
apply (auto simp: Let_def mono_bfilter mono_aval' mono_post
  le_join_disj le_join_disj[OF  wt_post wt_post] wt_bfilter
            split: option.split)
done

lemma mono_step'_top: "wt C1 (vars c) \<Longrightarrow> wt C2 (vars c) \<Longrightarrow> C1 \<sqsubseteq> C2 \<Longrightarrow> step' (top c) C1 \<sqsubseteq> step' (top c) C2"
by (metis wt_top mono_step' preord_class.le_refl)

end

end
