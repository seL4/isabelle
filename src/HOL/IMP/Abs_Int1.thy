(* Author: Tobias Nipkow *)

theory Abs_Int1
imports Abs_State
begin

lemma le_iff_le_annos_zip: "C1 \<sqsubseteq> C2 \<longleftrightarrow>
 (\<forall> (a1,a2) \<in> set(zip (annos C1) (annos C2)). a1 \<sqsubseteq> a2) \<and> strip C1 = strip C2"
by(induct C1 C2 rule: le_acom.induct) (auto simp: size_annos_same2)

lemma le_iff_le_annos: "C1 \<sqsubseteq> C2 \<longleftrightarrow>
  strip C1 = strip C2 \<and> (\<forall> i<size(annos C1). annos C1 ! i \<sqsubseteq> annos C2 ! i)"
by(auto simp add: le_iff_le_annos_zip set_zip) (metis size_annos_same2)


lemma mono_fun_wt[simp]: "wt F X \<Longrightarrow> F \<sqsubseteq> G \<Longrightarrow> x : X \<Longrightarrow> fun F x \<sqsubseteq> fun G x"
by(simp add: mono_fun wt_st_def)

lemma wt_bot[simp]: "wt (bot c) (vars c)"
by(simp add: wt_acom_def bot_def)

lemma wt_acom_simps[simp]: "wt (SKIP {P}) X \<longleftrightarrow> wt P X"
  "wt (x ::= e {P}) X \<longleftrightarrow> x : X \<and> vars e \<subseteq> X \<and> wt P X"
  "wt (C1;C2) X \<longleftrightarrow> wt C1 X \<and> wt C2 X"
  "wt (IF b THEN C1 ELSE C2 {P}) X \<longleftrightarrow>
   vars b \<subseteq> X \<and> wt C1 X \<and> wt C2 X \<and> wt P X"
  "wt ({I} WHILE b DO C {P}) X \<longleftrightarrow>
   wt I X \<and> vars b \<subseteq> X \<and> wt C X \<and> wt P X"
by(auto simp add: wt_acom_def)

lemma wt_post[simp]: "wt c  X \<Longrightarrow> wt (post c) X"
by(induction c)(auto simp: wt_acom_def)

lemma lpfp_inv:
assumes "lpfp f x0 = Some x" and "\<And>x. P x \<Longrightarrow> P(f x)" and "P(bot x0)"
shows "P x"
using assms unfolding lpfp_def pfp_def
by (metis (lifting) while_option_rule)


subsection "Computable Abstract Interpretation"

text{* Abstract interpretation over type @{text st} instead of
functions. *}

context Gamma
begin

fun aval' :: "aexp \<Rightarrow> 'av st \<Rightarrow> 'av" where
"aval' (N n) S = num' n" |
"aval' (V x) S = fun S x" |
"aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

lemma aval'_sound: "s : \<gamma>\<^isub>f S \<Longrightarrow> vars a \<subseteq> dom S \<Longrightarrow> aval a s : \<gamma>(aval' a S)"
by (induction a) (auto simp: gamma_num' gamma_plus' \<gamma>_st_def)

end

text{* The for-clause (here and elsewhere) only serves the purpose of fixing
the name of the type parameter @{typ 'av} which would otherwise be renamed to
@{typ 'a}. *}

locale Abs_Int = Gamma where \<gamma>=\<gamma> for \<gamma> :: "'av::SL_top \<Rightarrow> val set"
begin

fun step' :: "'av st option \<Rightarrow> 'av st option acom \<Rightarrow> 'av st option acom" where
"step' S (SKIP {P}) = (SKIP {S})" |
"step' S (x ::= e {P}) =
  x ::= e {case S of None \<Rightarrow> None | Some S \<Rightarrow> Some(update S x (aval' e S))}" |
"step' S (C1; C2) = step' S C1; step' (post C1) C2" |
"step' S (IF b THEN C1 ELSE C2 {P}) =
  (IF b THEN step' S C1 ELSE step' S C2 {post C1 \<squnion> post C2})" |
"step' S ({Inv} WHILE b DO C {P}) =
   {S \<squnion> post C} WHILE b DO step' Inv C {Inv}"

definition AI :: "com \<Rightarrow> 'av st option acom option" where
"AI c = lpfp (step' (top c)) c"


lemma strip_step'[simp]: "strip(step' S C) = strip C"
by(induct C arbitrary: S) (simp_all add: Let_def)


text{* Soundness: *}

lemma in_gamma_update:
  "\<lbrakk> s : \<gamma>\<^isub>f S; i : \<gamma> a \<rbrakk> \<Longrightarrow> s(x := i) : \<gamma>\<^isub>f(update S x a)"
by(simp add: \<gamma>_st_def)

theorem step_preserves_le:
  "\<lbrakk> S \<subseteq> \<gamma>\<^isub>o S'; C \<le> \<gamma>\<^isub>c C';  wt C' X; wt S' X \<rbrakk> \<Longrightarrow> step S C \<le> \<gamma>\<^isub>c (step' S' C')"
proof(induction C arbitrary: C' S S')
  case SKIP thus ?case by(auto simp:SKIP_le map_acom_SKIP)
next
  case Assign thus ?case
    by(fastforce simp: Assign_le map_acom_Assign wt_st_def
        intro: aval'_sound in_gamma_update split: option.splits)
next
  case Seq thus ?case apply (auto simp: Seq_le map_acom_Seq)
    by (metis le_post post_map_acom wt_post)
next
  case (If b C1 C2 P)
  then obtain C1' C2' P' where
      "C' = IF b THEN C1' ELSE C2' {P'}"
      "P \<subseteq> \<gamma>\<^isub>o P'" "C1 \<le> \<gamma>\<^isub>c C1'" "C2 \<le> \<gamma>\<^isub>c C2'"
    by (fastforce simp: If_le map_acom_If)
  moreover from this(1) `wt C' X` have wt: "wt C1' X" "wt C2' X"
    by simp_all
  moreover have "post C1 \<subseteq> \<gamma>\<^isub>o(post C1' \<squnion> post C2')"
    by (metis (no_types) `C1 \<le> \<gamma>\<^isub>c C1'` join_ge1 le_post mono_gamma_o order_trans post_map_acom wt wt_post)
  moreover have "post C2 \<subseteq> \<gamma>\<^isub>o(post C1' \<squnion> post C2')"
    by (metis (no_types) `C2 \<le> \<gamma>\<^isub>c C2'` join_ge2 le_post mono_gamma_o order_trans post_map_acom wt wt_post)
  ultimately show ?case using `S \<subseteq> \<gamma>\<^isub>o S'` `wt S' X`
    by (simp add: If.IH subset_iff)
next
  case (While I b C1 P)
  then obtain C1' I' P' where
    "C' = {I'} WHILE b DO C1' {P'}"
    "I \<subseteq> \<gamma>\<^isub>o I'" "P \<subseteq> \<gamma>\<^isub>o P'" "C1 \<le> \<gamma>\<^isub>c C1'"
    by (fastforce simp: map_acom_While While_le)
  moreover from this(1) `wt C' X`
  have wt: "wt C1' X" "wt I' X" by simp_all
  moreover note compat = `wt S' X` wt_post[OF wt(1)]
  moreover have "S \<union> post C1 \<subseteq> \<gamma>\<^isub>o (S' \<squnion> post C1')"
    using `S \<subseteq> \<gamma>\<^isub>o S'` le_post[OF `C1 \<le> \<gamma>\<^isub>c C1'`, simplified]
    by (metis (no_types) join_ge1[OF compat] join_ge2[OF compat] le_sup_iff mono_gamma_o order_trans)
  ultimately show ?case by (simp add: While.IH subset_iff)
qed

lemma wt_step'[simp]:
  "\<lbrakk> wt C X; wt S X \<rbrakk> \<Longrightarrow> wt (step' S C) X"
proof(induction C arbitrary: S)
  case Assign thus ?case
    by(auto simp: wt_st_def update_def split: option.splits)
qed auto

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

lemma le_join_disj: "wt y X \<Longrightarrow> wt (z::_::SL_top_wt) X \<Longrightarrow> x \<sqsubseteq> y \<or> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<squnion> z"
by (metis join_ge1 join_ge2 preord_class.le_trans)

locale Abs_Int_mono = Abs_Int +
assumes mono_plus': "a1 \<sqsubseteq> b1 \<Longrightarrow> a2 \<sqsubseteq> b2 \<Longrightarrow> plus' a1 a2 \<sqsubseteq> plus' b1 b2"
begin

lemma mono_aval': "S1 \<sqsubseteq> S2 \<Longrightarrow> wt S1 X \<Longrightarrow> vars e \<subseteq> X \<Longrightarrow> aval' e S1 \<sqsubseteq> aval' e S2"
by(induction e) (auto simp: le_st_def mono_plus' wt_st_def)

theorem mono_step': "wt S1 X \<Longrightarrow> wt S2 X \<Longrightarrow> wt C1 X \<Longrightarrow> wt C2 X \<Longrightarrow>
  S1 \<sqsubseteq> S2 \<Longrightarrow> C1 \<sqsubseteq> C2 \<Longrightarrow> step' S1 C1 \<sqsubseteq> step' S2 C2"
apply(induction C1 C2 arbitrary: S1 S2 rule: le_acom.induct)
apply (auto simp: Let_def mono_aval' mono_post
  le_join_disj le_join_disj[OF  wt_post wt_post]
            split: option.split)
done

lemma mono_step'_top: "wt c (vars c0) \<Longrightarrow> wt c' (vars c0) \<Longrightarrow> c \<sqsubseteq> c' \<Longrightarrow> step' (top c0) c \<sqsubseteq> step' (top c0) c'"
by (metis wt_top mono_step' preord_class.le_refl)

end


subsubsection "Termination"

abbreviation sqless (infix "\<sqsubset>" 50) where
"x \<sqsubset> y == x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x"

lemma pfp_termination:
fixes x0 :: "'a::preord" and m :: "'a \<Rightarrow> nat"
assumes mono: "\<And>x y. I x \<Longrightarrow> I y \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
and m: "\<And>x y. I x \<Longrightarrow> I y \<Longrightarrow> x \<sqsubset> y \<Longrightarrow> m x > m y"
and I: "\<And>x y. I x \<Longrightarrow> I(f x)" and "I x0" and "x0 \<sqsubseteq> f x0"
shows "EX x. pfp f x0 = Some x"
proof(simp add: pfp_def, rule wf_while_option_Some[where P = "%x. I x & x \<sqsubseteq> f x"])
  show "wf {(y,x). ((I x \<and> x \<sqsubseteq> f x) \<and> \<not> f x \<sqsubseteq> x) \<and> y = f x}"
    by(rule wf_subset[OF wf_measure[of m]]) (auto simp: m I)
next
  show "I x0 \<and> x0 \<sqsubseteq> f x0" using `I x0` `x0 \<sqsubseteq> f x0` by blast
next
  fix x assume "I x \<and> x \<sqsubseteq> f x" thus "I(f x) \<and> f x \<sqsubseteq> f(f x)"
    by (blast intro: I mono)
qed

lemma lpfp_termination:
fixes f :: "'a::preord option acom \<Rightarrow> 'a option acom"
and m :: "'a option acom \<Rightarrow> nat" and I :: "'a option acom \<Rightarrow> bool"
assumes "\<And>x y. I x \<Longrightarrow> I y \<Longrightarrow> x \<sqsubset> y \<Longrightarrow> m x > m y"
and "\<And>x y. I x \<Longrightarrow> I y \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
and "\<And>x y. I x \<Longrightarrow> I(f x)" and "I(bot c)"
and "\<And>C. strip (f C) = strip C"
shows "\<exists>c'. lpfp f c = Some c'"
unfolding lpfp_def
by(fastforce intro: pfp_termination[where I=I and m=m] assms bot_least
   simp: assms(5))


locale Abs_Int_measure =
  Abs_Int_mono where \<gamma>=\<gamma> for \<gamma> :: "'av::SL_top \<Rightarrow> val set" +
fixes m :: "'av \<Rightarrow> nat"
fixes h :: "nat"
assumes m1: "x \<sqsubseteq> y \<Longrightarrow> m x \<ge> m y"
assumes m2: "x \<sqsubset> y \<Longrightarrow> m x > m y"
assumes h: "m x \<le> h"
begin

definition "m_st S = (\<Sum> x \<in> dom S. m(fun S x))"

lemma m_st1: "S1 \<sqsubseteq> S2 \<Longrightarrow> m_st S1 \<ge> m_st S2"
proof(auto simp add: le_st_def m_st_def)
  assume "\<forall>x\<in>dom S2. fun S1 x \<sqsubseteq> fun S2 x"
  hence "\<forall>x\<in>dom S2. m(fun S1 x) \<ge> m(fun S2 x)" by (metis m1)
  thus "(\<Sum>x\<in>dom S2. m (fun S2 x)) \<le> (\<Sum>x\<in>dom S2. m (fun S1 x))"
    by (metis setsum_mono)
qed

lemma m_st2: "finite(dom S1) \<Longrightarrow> S1 \<sqsubset> S2 \<Longrightarrow> m_st S1 > m_st S2"
proof(auto simp add: le_st_def m_st_def)
  assume "finite(dom S2)" and 0: "\<forall>x\<in>dom S2. fun S1 x \<sqsubseteq> fun S2 x"
  hence 1: "\<forall>x\<in>dom S2. m(fun S1 x) \<ge> m(fun S2 x)" by (metis m1)
  fix x assume "x \<in> dom S2" "\<not> fun S2 x \<sqsubseteq> fun S1 x"
  hence 2: "\<exists>x\<in>dom S2. m(fun S1 x) > m(fun S2 x)" using 0 m2 by blast
  from setsum_strict_mono_ex1[OF `finite(dom S2)` 1 2]
  show "(\<Sum>x\<in>dom S2. m (fun S2 x)) < (\<Sum>x\<in>dom S2. m (fun S1 x))" .
qed


definition m_o :: "nat \<Rightarrow> 'av st option \<Rightarrow> nat" where
"m_o d opt = (case opt of None \<Rightarrow> h*d+1 | Some S \<Rightarrow> m_st S)"

definition m_c :: "'av st option acom \<Rightarrow> nat" where
"m_c c = (\<Sum>i<size(annos c). m_o (card(vars(strip c))) (annos c ! i))"

lemma m_st_h: "wt x X \<Longrightarrow> finite X \<Longrightarrow> m_st x \<le> h * card X"
by(simp add: wt_st_def m_st_def)
  (metis nat_mult_commute of_nat_id setsum_bounded[OF h])

lemma m_o1: "finite X \<Longrightarrow> wt o1 X \<Longrightarrow> wt o2 X \<Longrightarrow>
  o1 \<sqsubseteq> o2 \<Longrightarrow> m_o (card X) o1 \<ge> m_o (card X) o2"
proof(induction o1 o2 rule: le_option.induct)
  case 1 thus ?case by (simp add: m_o_def)(metis m_st1)
next
  case 2 thus ?case
    by(simp add: wt_option_def m_o_def le_SucI m_st_h split: option.splits)
next
  case 3 thus ?case by simp
qed

lemma m_o2: "finite X \<Longrightarrow> wt o1 X \<Longrightarrow> wt o2 X \<Longrightarrow>
  o1 \<sqsubset> o2 \<Longrightarrow> m_o (card X) o1 > m_o (card X) o2"
proof(induction o1 o2 rule: le_option.induct)
  case 1 thus ?case by (simp add: m_o_def wt_st_def m_st2)
next
  case 2 thus ?case
    by(auto simp add: m_o_def le_imp_less_Suc m_st_h)
next
  case 3 thus ?case by simp
qed

lemma m_c2: "wt c1 (vars(strip c1)) \<Longrightarrow> wt c2 (vars(strip c2)) \<Longrightarrow>
  c1 \<sqsubset> c2 \<Longrightarrow> m_c c1 > m_c c2"
proof(auto simp add: le_iff_le_annos m_c_def size_annos_same[of c1 c2] wt_acom_def)
  let ?X = "vars(strip c2)"
  let ?n = "card ?X"
  assume V1: "\<forall>a\<in>set(annos c1). wt a ?X"
    and V2: "\<forall>a\<in>set(annos c2). wt a ?X"
    and strip_eq: "strip c1 = strip c2"
    and 0: "\<forall>i<size(annos c2). annos c1 ! i \<sqsubseteq> annos c2 ! i"
  hence 1: "\<forall>i<size(annos c2). m_o ?n (annos c1 ! i) \<ge> m_o ?n (annos c2 ! i)"
    by (auto simp: all_set_conv_all_nth)
       (metis finite_cvars m_o1 size_annos_same2)
  fix i assume "i < size(annos c2)" "\<not> annos c2 ! i \<sqsubseteq> annos c1 ! i"
  hence "m_o ?n (annos c1 ! i) > m_o ?n (annos c2 ! i)" (is "?P i")
    by(metis m_o2[OF finite_cvars] V1 V2 strip_eq nth_mem size_annos_same 0)
  hence 2: "\<exists>i < size(annos c2). ?P i" using `i < size(annos c2)` by blast
  show "(\<Sum>i<size(annos c2). m_o ?n (annos c2 ! i))
         < (\<Sum>i<size(annos c2). m_o ?n (annos c1 ! i))"
    apply(rule setsum_strict_mono_ex1) using 1 2 by (auto)
qed

lemma AI_Some_measure: "\<exists>C. AI c = Some C"
unfolding AI_def
apply(rule lpfp_termination[where I = "%C. strip C = c \<and> wt C (vars c)"
  and m="m_c"])
apply(simp_all add: m_c2 mono_step'_top)
done

end

end
