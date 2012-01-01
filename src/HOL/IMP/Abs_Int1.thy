(* Author: Tobias Nipkow *)

theory Abs_Int1
imports Abs_Int0
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

hide_const bot

class L_top_bot = SL_top +
fixes meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 65)
and bot :: "'a" ("\<bottom>")
assumes meet_le1 [simp]: "x \<sqinter> y \<sqsubseteq> x"
and meet_le2 [simp]: "x \<sqinter> y \<sqsubseteq> y"
and meet_greatest: "x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<sqinter> z"
assumes bot[simp]: "\<bottom> \<sqsubseteq> x"
begin

lemma mono_meet: "x \<sqsubseteq> x' \<Longrightarrow> y \<sqsubseteq> y' \<Longrightarrow> x \<sqinter> y \<sqsubseteq> x' \<sqinter> y'"
by (metis meet_greatest meet_le1 meet_le2 le_trans)

end

locale Val_abs1_gamma =
  Val_abs where \<gamma> = \<gamma> for \<gamma> :: "'av::L_top_bot \<Rightarrow> val set" +
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
fixes filter_plus' :: "'av \<Rightarrow> 'av \<Rightarrow> 'av \<Rightarrow> 'av * 'av"
and filter_less' :: "bool \<Rightarrow> 'av \<Rightarrow> 'av \<Rightarrow> 'av * 'av"
assumes filter_plus': "filter_plus' a a1 a2 = (a1',a2') \<Longrightarrow>
  n1 : \<gamma> a1 \<Longrightarrow> n2 : \<gamma> a2 \<Longrightarrow> n1+n2 : \<gamma> a \<Longrightarrow> n1 : \<gamma> a1' \<and> n2 : \<gamma> a2'"
and filter_less': "filter_less' (n1<n2) a1 a2 = (a1',a2') \<Longrightarrow>
  n1 : \<gamma> a1 \<Longrightarrow> n2 : \<gamma> a2 \<Longrightarrow> n1 : \<gamma> a1' \<and> n2 : \<gamma> a2'"


locale Abs_Int1 =
  Val_abs1 where \<gamma> = \<gamma> for \<gamma> :: "'av::L_top_bot \<Rightarrow> val set"
begin

lemma in_gamma_join_UpI: "s : \<gamma>\<^isub>o S1 \<or> s : \<gamma>\<^isub>o S2 \<Longrightarrow> s : \<gamma>\<^isub>o(S1 \<squnion> S2)"
by (metis (no_types) join_ge1 join_ge2 mono_gamma_o set_rev_mp)

fun aval'' :: "aexp \<Rightarrow> 'av st option \<Rightarrow> 'av" where
"aval'' e None = \<bottom>" |
"aval'' e (Some sa) = aval' e sa"

lemma aval''_sound: "s : \<gamma>\<^isub>o S \<Longrightarrow> aval a s : \<gamma>(aval'' a S)"
by(cases S)(simp add: aval'_sound)+

subsubsection "Backward analysis"

fun afilter :: "aexp \<Rightarrow> 'av \<Rightarrow> 'av st option \<Rightarrow> 'av st option" where
"afilter (N n) a S = (if n : \<gamma> a then S else None)" |
"afilter (V x) a S = (case S of None \<Rightarrow> None | Some S \<Rightarrow>
  let a' = lookup S x \<sqinter> a in
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

lemma afilter_sound: "s : \<gamma>\<^isub>o S \<Longrightarrow> aval e s : \<gamma> a \<Longrightarrow> s : \<gamma>\<^isub>o (afilter e a S)"
proof(induction e arbitrary: a S)
  case N thus ?case by simp
next
  case (V x)
  obtain S' where "S = Some S'" and "s : \<gamma>\<^isub>f S'" using `s : \<gamma>\<^isub>o S`
    by(auto simp: in_gamma_option_iff)
  moreover hence "s x : \<gamma> (lookup S' x)" by(simp add: \<gamma>_st_def)
  moreover have "s x : \<gamma> a" using V by simp
  ultimately show ?case using V(1)
    by(simp add: lookup_update Let_def \<gamma>_st_def)
      (metis mono_gamma emptyE in_gamma_meet gamma_Bot subset_empty)
next
  case (Plus e1 e2) thus ?case
    using filter_plus'[OF _ aval''_sound[OF Plus(3)] aval''_sound[OF Plus(3)]]
    by (auto split: prod.split)
qed

lemma bfilter_sound: "s : \<gamma>\<^isub>o S \<Longrightarrow> bv = bval b s \<Longrightarrow> s : \<gamma>\<^isub>o(bfilter b bv S)"
proof(induction b arbitrary: S bv)
  case Bc thus ?case by simp
next
  case (Not b) thus ?case by simp
next
  case (And b1 b2) thus ?case by(fastforce simp: in_gamma_join_UpI)
next
  case (Less e1 e2) thus ?case
    by (auto split: prod.split)
       (metis afilter_sound filter_less' aval''_sound Less)
qed


fun step' :: "'av st option \<Rightarrow> 'av st option acom \<Rightarrow> 'av st option acom"
 where
"step' S (SKIP {P}) = (SKIP {S})" |
"step' S (x ::= e {P}) =
  x ::= e {case S of None \<Rightarrow> None | Some S \<Rightarrow> Some(update S x (aval' e S))}" |
"step' S (c1; c2) = step' S c1; step' (post c1) c2" |
"step' S (IF b THEN c1 ELSE c2 {P}) =
  (let c1' = step' (bfilter b True S) c1; c2' = step' (bfilter b False S) c2
   in IF b THEN c1' ELSE c2' {post c1 \<squnion> post c2})" |
"step' S ({Inv} WHILE b DO c {P}) =
   {S \<squnion> post c}
   WHILE b DO step' (bfilter b True Inv) c
   {bfilter b False Inv}"

definition AI :: "com \<Rightarrow> 'av st option acom option" where
"AI = lpfp\<^isub>c (step' \<top>)"

lemma strip_step'[simp]: "strip(step' S c) = strip c"
by(induct c arbitrary: S) (simp_all add: Let_def)


subsubsection "Soundness"

lemma in_gamma_update:
  "\<lbrakk> s : \<gamma>\<^isub>f S; i : \<gamma> a \<rbrakk> \<Longrightarrow> s(x := i) : \<gamma>\<^isub>f(update S x a)"
by(simp add: \<gamma>_st_def lookup_update)


lemma step_preserves_le2:
  "\<lbrakk> S \<subseteq> \<gamma>\<^isub>o sa; cs \<le> \<gamma>\<^isub>c ca; strip cs = c; strip ca = c \<rbrakk>
   \<Longrightarrow> step S cs \<le> \<gamma>\<^isub>c (step' sa ca)"
proof(induction c arbitrary: cs ca S sa)
  case SKIP thus ?case
    by(auto simp:strip_eq_SKIP)
next
  case Assign thus ?case
    by (fastforce simp: strip_eq_Assign intro: aval'_sound in_gamma_update
      split: option.splits del:subsetD)
next
  case Semi thus ?case apply (auto simp: strip_eq_Semi)
    by (metis le_post post_map_acom)
next
  case (If b c1 c2)
  then obtain cs1 cs2 ca1 ca2 P Pa where
      "cs= IF b THEN cs1 ELSE cs2 {P}" "ca= IF b THEN ca1 ELSE ca2 {Pa}"
      "P \<subseteq> \<gamma>\<^isub>o Pa" "cs1 \<le> \<gamma>\<^isub>c ca1" "cs2 \<le> \<gamma>\<^isub>c ca2"
      "strip cs1 = c1" "strip ca1 = c1" "strip cs2 = c2" "strip ca2 = c2"
    by (fastforce simp: strip_eq_If)
  moreover have "post cs1 \<subseteq> \<gamma>\<^isub>o(post ca1 \<squnion> post ca2)"
    by (metis (no_types) `cs1 \<le> \<gamma>\<^isub>c ca1` join_ge1 le_post mono_gamma_o order_trans post_map_acom)
  moreover have "post cs2 \<subseteq> \<gamma>\<^isub>o(post ca1 \<squnion> post ca2)"
    by (metis (no_types) `cs2 \<le> \<gamma>\<^isub>c ca2` join_ge2 le_post mono_gamma_o order_trans post_map_acom)
  ultimately show ?case using `S \<subseteq> \<gamma>\<^isub>o sa`
    by (simp add: If.IH subset_iff bfilter_sound)
next
  case (While b c1)
  then obtain cs1 ca1 I P Ia Pa where
    "cs = {I} WHILE b DO cs1 {P}" "ca = {Ia} WHILE b DO ca1 {Pa}"
    "I \<subseteq> \<gamma>\<^isub>o Ia" "P \<subseteq> \<gamma>\<^isub>o Pa" "cs1 \<le> \<gamma>\<^isub>c ca1"
    "strip cs1 = c1" "strip ca1 = c1"
    by (fastforce simp: strip_eq_While)
  moreover have "S \<union> post cs1 \<subseteq> \<gamma>\<^isub>o (sa \<squnion> post ca1)"
    using `S \<subseteq> \<gamma>\<^isub>o sa` le_post[OF `cs1 \<le> \<gamma>\<^isub>c ca1`, simplified]
    by (metis (no_types) join_ge1 join_ge2 le_sup_iff mono_gamma_o order_trans)
  ultimately show ?case by (simp add: While.IH subset_iff bfilter_sound)
qed

lemma step_preserves_le:
  "\<lbrakk> S \<subseteq> \<gamma>\<^isub>o sa; cs \<le> \<gamma>\<^isub>c ca; strip cs = c \<rbrakk>
   \<Longrightarrow> step S cs \<le> \<gamma>\<^isub>c(step' sa ca)"
by (metis le_strip step_preserves_le2 strip_acom)

lemma AI_sound: "AI c = Some c' \<Longrightarrow> CS UNIV c \<le> \<gamma>\<^isub>c c'"
proof(simp add: CS_def AI_def)
  assume 1: "lpfp\<^isub>c (step' \<top>) c = Some c'"
  have 2: "step' \<top> c' \<sqsubseteq> c'" by(rule lpfpc_pfp[OF 1])
  have 3: "strip (\<gamma>\<^isub>c (step' \<top> c')) = c"
    by(simp add: strip_lpfpc[OF _ 1])
  have "lfp c (step UNIV) \<le> \<gamma>\<^isub>c (step' \<top> c')"
  proof(rule lfp_lowerbound[simplified,OF 3])
    show "step UNIV (\<gamma>\<^isub>c (step' \<top> c')) \<le> \<gamma>\<^isub>c (step' \<top> c')"
    proof(rule step_preserves_le[OF _ _ 3])
      show "UNIV \<subseteq> \<gamma>\<^isub>o \<top>" by simp
      show "\<gamma>\<^isub>c (step' \<top> c') \<le> \<gamma>\<^isub>c c'" by(rule mono_gamma_c[OF 2])
    qed
  qed
  from this 2 show "lfp c (step UNIV) \<le> \<gamma>\<^isub>c c'"
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

lemma mono_aval': "S \<sqsubseteq> S' \<Longrightarrow> aval' e S \<sqsubseteq> aval' e S'"
by(induction e) (auto simp: le_st_def lookup_def mono_plus')

lemma mono_aval'': "S \<sqsubseteq> S' \<Longrightarrow> aval'' e S \<sqsubseteq> aval'' e S'"
apply(cases S)
 apply simp
apply(cases S')
 apply simp
by (simp add: mono_aval')

lemma mono_afilter: "r \<sqsubseteq> r' \<Longrightarrow> S \<sqsubseteq> S' \<Longrightarrow> afilter e r S \<sqsubseteq> afilter e r' S'"
apply(induction e arbitrary: r r' S S')
apply(auto simp: Let_def split: option.splits prod.splits)
apply (metis mono_gamma subsetD)
apply(drule_tac x = "list" in mono_lookup)
apply (metis mono_meet le_trans)
apply (metis mono_meet mono_lookup mono_update)
apply(metis mono_aval'' mono_filter_plus'[simplified le_prod_def] fst_conv snd_conv)
done

lemma mono_bfilter: "S \<sqsubseteq> S' \<Longrightarrow> bfilter b r S \<sqsubseteq> bfilter b r S'"
apply(induction b arbitrary: r S S')
apply(auto simp: le_trans[OF _ join_ge1] le_trans[OF _ join_ge2] split: prod.splits)
apply(metis mono_aval'' mono_afilter mono_filter_less'[simplified le_prod_def] fst_conv snd_conv)
done


lemma post_le_post: "c \<sqsubseteq> c' \<Longrightarrow> post c \<sqsubseteq> post c'"
by (induction c c' rule: le_acom.induct) simp_all

lemma mono_step'_aux: "S \<sqsubseteq> S' \<Longrightarrow> c \<sqsubseteq> c' \<Longrightarrow> step' S c \<sqsubseteq> step' S' c'"
apply(induction c c' arbitrary: S S' rule: le_acom.induct)
apply (auto simp: post_le_post Let_def mono_bfilter mono_update mono_aval' le_join_disj
  split: option.split)
done

lemma mono_step': "mono (step' S)"
by(simp add: mono_def mono_step'_aux[OF le_refl])

end

end
