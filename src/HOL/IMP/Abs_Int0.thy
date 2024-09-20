(* Author: Tobias Nipkow *)

subsection "Abstract Interpretation"

theory Abs_Int0
imports Abs_Int_init
begin

subsubsection "Orderings"

text\<open>The basic type classes \<^class>\<open>order\<close>, \<^class>\<open>semilattice_sup\<close> and \<^class>\<open>order_top\<close> are
defined in \<^theory>\<open>Main\<close>, more precisely in theories \<^theory>\<open>HOL.Orderings\<close> and \<^theory>\<open>HOL.Lattices\<close>.
If you view this theory with jedit, just click on the names to get there.\<close>

class semilattice_sup_top = semilattice_sup + order_top


instance "fun" :: (type, semilattice_sup_top) semilattice_sup_top ..

instantiation option :: (order)order
begin

fun less_eq_option where
"Some x \<le> Some y = (x \<le> y)" |
"None \<le> y = True" |
"Some _ \<le> None = False"

definition less_option where "x < (y::'a option) = (x \<le> y \<and> \<not> y \<le> x)"

lemma le_None[simp]: "(x \<le> None) = (x = None)"
by (cases x) simp_all

lemma Some_le[simp]: "(Some x \<le> u) = (\<exists>y. u = Some y \<and> x \<le> y)"
by (cases u) auto

instance
proof (standard, goal_cases)
  case 1 show ?case by(rule less_option_def)
next
  case (2 x) show ?case by(cases x, simp_all)
next
  case (3 x y z) thus ?case by(cases z, simp, cases y, simp, cases x, auto)
next
  case (4 x y) thus ?case by(cases y, simp, cases x, auto)
qed

end

instantiation option :: (sup)sup
begin

fun sup_option where
"Some x \<squnion> Some y = Some(x \<squnion> y)" |
"None \<squnion> y = y" |
"x \<squnion> None = x"

lemma sup_None2[simp]: "x \<squnion> None = x"
by (cases x) simp_all

instance ..

end

instantiation option :: (semilattice_sup_top)semilattice_sup_top
begin

definition top_option where "\<top> = Some \<top>"

instance
proof (standard, goal_cases)
  case (4 a) show ?case by(cases a, simp_all add: top_option_def)
next
  case (1 x y) thus ?case by(cases x, simp, cases y, simp_all)
next
  case (2 x y) thus ?case by(cases y, simp, cases x, simp_all)
next
  case (3 x y z) thus ?case by(cases z, simp, cases y, simp, cases x, simp_all)
qed

end

lemma [simp]: "(Some x < Some y) = (x < y)"
by(auto simp: less_le)

instantiation option :: (order)order_bot
begin

definition bot_option :: "'a option" where
"\<bottom> = None"

instance
proof (standard, goal_cases)
  case 1 thus ?case by(auto simp: bot_option_def)
qed

end


definition bot :: "com \<Rightarrow> 'a option acom" where
"bot c = annotate (\<lambda>p. None) c"

lemma bot_least: "strip C = c \<Longrightarrow> bot c \<le> C"
by(auto simp: bot_def less_eq_acom_def)

lemma strip_bot[simp]: "strip(bot c) = c"
by(simp add: bot_def)


subsubsection "Pre-fixpoint iteration"

definition pfp :: "(('a::order) \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option" where
"pfp f = while_option (\<lambda>x. \<not> f x \<le> x) f"

lemma pfp_pfp: assumes "pfp f x0 = Some x" shows "f x \<le> x"
using while_option_stop[OF assms[simplified pfp_def]] by simp

lemma while_least:
fixes q :: "'a::order"
assumes "\<forall>x\<in>L.\<forall>y\<in>L. x \<le> y \<longrightarrow> f x \<le> f y" and "\<forall>x. x \<in> L \<longrightarrow> f x \<in> L"
and "\<forall>x \<in> L. b \<le> x" and "b \<in> L" and "f q \<le> q" and "q \<in> L"
and "while_option P f b = Some p"
shows "p \<le> q"
using while_option_rule[OF _  assms(7)[unfolded pfp_def],
                        where P = "%x. x \<in> L \<and> x \<le> q"]
by (metis assms(1-6) order_trans)

lemma pfp_bot_least:
assumes "\<forall>x\<in>{C. strip C = c}.\<forall>y\<in>{C. strip C = c}. x \<le> y \<longrightarrow> f x \<le> f y"
and "\<forall>C. C \<in> {C. strip C = c} \<longrightarrow> f C \<in> {C. strip C = c}"
and "f C' \<le> C'" "strip C' = c" "pfp f (bot c) = Some C"
shows "C \<le> C'"
by(rule while_least[OF assms(1,2) _ _ assms(3) _ assms(5)[unfolded pfp_def]])
  (simp_all add: assms(4) bot_least)

lemma pfp_inv:
  "pfp f x = Some y \<Longrightarrow> (\<And>x. P x \<Longrightarrow> P(f x)) \<Longrightarrow> P x \<Longrightarrow> P y"
unfolding pfp_def by (blast intro: while_option_rule)

lemma strip_pfp:
assumes "\<And>x. g(f x) = g x" and "pfp f x0 = Some x" shows "g x = g x0"
using pfp_inv[OF assms(2), where P = "%x. g x = g x0"] assms(1) by simp


subsubsection "Abstract Interpretation"

definition \<gamma>_fun :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b)set" where
"\<gamma>_fun \<gamma> F = {f. \<forall>x. f x \<in> \<gamma>(F x)}"

fun \<gamma>_option :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a option \<Rightarrow> 'b set" where
"\<gamma>_option \<gamma> None = {}" |
"\<gamma>_option \<gamma> (Some a) = \<gamma> a"

text\<open>The interface for abstract values:\<close>

locale Val_semilattice =
fixes \<gamma> :: "'av::semilattice_sup_top \<Rightarrow> val set"
  assumes mono_gamma: "a \<le> b \<Longrightarrow> \<gamma> a \<le> \<gamma> b"
  and gamma_Top[simp]: "\<gamma> \<top> = UNIV"
fixes num' :: "val \<Rightarrow> 'av"
and plus' :: "'av \<Rightarrow> 'av \<Rightarrow> 'av"
  assumes gamma_num': "i \<in> \<gamma>(num' i)"
  and gamma_plus': "i1 \<in> \<gamma> a1 \<Longrightarrow> i2 \<in> \<gamma> a2 \<Longrightarrow> i1+i2 \<in> \<gamma>(plus' a1 a2)"

type_synonym 'av st = "(vname \<Rightarrow> 'av)"

text\<open>The for-clause (here and elsewhere) only serves the purpose of fixing
the name of the type parameter \<^typ>\<open>'av\<close> which would otherwise be renamed to
\<^typ>\<open>'a\<close>.\<close>

locale Abs_Int_fun = Val_semilattice where \<gamma>=\<gamma>
  for \<gamma> :: "'av::semilattice_sup_top \<Rightarrow> val set"
begin

fun aval' :: "aexp \<Rightarrow> 'av st \<Rightarrow> 'av" where
"aval' (N i) S = num' i" |
"aval' (V x) S = S x" |
"aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

definition "asem x e S = (case S of None \<Rightarrow> None | Some S \<Rightarrow> Some(S(x := aval' e S)))"

definition "step' = Step asem (\<lambda>b S. S)"

lemma strip_step'[simp]: "strip(step' S C) = strip C"
by(simp add: step'_def)

definition AI :: "com \<Rightarrow> 'av st option acom option" where
"AI c = pfp (step' \<top>) (bot c)"


abbreviation \<gamma>\<^sub>s :: "'av st \<Rightarrow> state set"
where "\<gamma>\<^sub>s == \<gamma>_fun \<gamma>"

abbreviation \<gamma>\<^sub>o :: "'av st option \<Rightarrow> state set"
where "\<gamma>\<^sub>o == \<gamma>_option \<gamma>\<^sub>s"

abbreviation \<gamma>\<^sub>c :: "'av st option acom \<Rightarrow> state set acom"
where "\<gamma>\<^sub>c == map_acom \<gamma>\<^sub>o"

lemma gamma_s_Top[simp]: "\<gamma>\<^sub>s \<top> = UNIV"
by(simp add: top_fun_def \<gamma>_fun_def)

lemma gamma_o_Top[simp]: "\<gamma>\<^sub>o \<top> = UNIV"
by (simp add: top_option_def)

lemma mono_gamma_s: "f1 \<le> f2 \<Longrightarrow> \<gamma>\<^sub>s f1 \<subseteq> \<gamma>\<^sub>s f2"
by(auto simp: le_fun_def \<gamma>_fun_def dest: mono_gamma)

lemma mono_gamma_o:
  "S1 \<le> S2 \<Longrightarrow> \<gamma>\<^sub>o S1 \<subseteq> \<gamma>\<^sub>o S2"
by(induction S1 S2 rule: less_eq_option.induct)(simp_all add: mono_gamma_s)

lemma mono_gamma_c: "C1 \<le> C2 \<Longrightarrow> \<gamma>\<^sub>c C1 \<le> \<gamma>\<^sub>c C2"
by (simp add: less_eq_acom_def mono_gamma_o size_annos anno_map_acom size_annos_same[of C1 C2])

text\<open>Correctness:\<close>

lemma aval'_correct: "s \<in> \<gamma>\<^sub>s S \<Longrightarrow> aval a s \<in> \<gamma>(aval' a S)"
by (induct a) (auto simp: gamma_num' gamma_plus' \<gamma>_fun_def)

lemma in_gamma_update: "\<lbrakk> s \<in> \<gamma>\<^sub>s S; i \<in> \<gamma> a \<rbrakk> \<Longrightarrow> s(x := i) \<in> \<gamma>\<^sub>s(S(x := a))"
by(simp add: \<gamma>_fun_def)

lemma gamma_Step_subcomm:
  assumes "\<And>x e S. f1 x e (\<gamma>\<^sub>o S) \<subseteq> \<gamma>\<^sub>o (f2 x e S)"  "\<And>b S. g1 b (\<gamma>\<^sub>o S) \<subseteq> \<gamma>\<^sub>o (g2 b S)"
  shows "Step f1 g1 (\<gamma>\<^sub>o S) (\<gamma>\<^sub>c C) \<le> \<gamma>\<^sub>c (Step f2 g2 S C)"
by (induction C arbitrary: S) (auto simp: mono_gamma_o assms)

lemma step_step': "step (\<gamma>\<^sub>o S) (\<gamma>\<^sub>c C) \<le> \<gamma>\<^sub>c (step' S C)"
unfolding step_def step'_def
by(rule gamma_Step_subcomm)
  (auto simp: aval'_correct in_gamma_update asem_def split: option.splits)

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

locale Abs_Int_fun_mono = Abs_Int_fun +
assumes mono_plus': "a1 \<le> b1 \<Longrightarrow> a2 \<le> b2 \<Longrightarrow> plus' a1 a2 \<le> plus' b1 b2"
begin

lemma mono_aval': "S \<le> S' \<Longrightarrow> aval' e S \<le> aval' e S'"
by(induction e)(auto simp: le_fun_def mono_plus')

lemma mono_update: "a \<le> a' \<Longrightarrow> S \<le> S' \<Longrightarrow> S(x := a) \<le> S'(x := a')"
by(simp add: le_fun_def)

lemma mono_step': "S1 \<le> S2 \<Longrightarrow> C1 \<le> C2 \<Longrightarrow> step' S1 C1 \<le> step' S2 C2"
unfolding step'_def
by(rule mono2_Step)
  (auto simp: mono_update mono_aval' asem_def split: option.split)

lemma mono_step'_top: "C \<le> C' \<Longrightarrow> step' \<top> C \<le> step' \<top> C'"
by (metis mono_step' order_refl)

lemma AI_least_pfp: assumes "AI c = Some C" "step' \<top> C' \<le> C'" "strip C' = c"
shows "C \<le> C'"
by(rule pfp_bot_least[OF _ _ assms(2,3) assms(1)[unfolded AI_def]])
  (simp_all add: mono_step'_top)

end


instantiation acom :: (type) vars
begin

definition "vars_acom = vars o strip"

instance ..

end

lemma finite_Cvars: "finite(vars(C::'a acom))"
by(simp add: vars_acom_def)


subsubsection "Termination"

lemma pfp_termination:
fixes x0 :: "'a::order" and m :: "'a \<Rightarrow> nat"
assumes mono: "\<And>x y. I x \<Longrightarrow> I y \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
and m: "\<And>x y. I x \<Longrightarrow> I y \<Longrightarrow> x < y \<Longrightarrow> m x > m y"
and I: "\<And>x y. I x \<Longrightarrow> I(f x)" and "I x0" and "x0 \<le> f x0"
shows "\<exists>x. pfp f x0 = Some x"
proof(simp add: pfp_def, rule wf_while_option_Some[where P = "%x. I x & x \<le> f x"])
  show "wf {(y,x). ((I x \<and> x \<le> f x) \<and> \<not> f x \<le> x) \<and> y = f x}"
    by(rule wf_subset[OF wf_measure[of m]]) (auto simp: m I)
next
  show "I x0 \<and> x0 \<le> f x0" using \<open>I x0\<close> \<open>x0 \<le> f x0\<close> by blast
next
  fix x assume "I x \<and> x \<le> f x" thus "I(f x) \<and> f x \<le> f(f x)"
    by (blast intro: I mono)
qed

lemma le_iff_le_annos: "C1 \<le> C2 \<longleftrightarrow>
  strip C1 = strip C2 \<and> (\<forall> i<size(annos C1). annos C1 ! i \<le> annos C2 ! i)"
by(simp add: less_eq_acom_def anno_def)

locale Measure1_fun =
fixes m :: "'av::top \<Rightarrow> nat"
fixes h :: "nat"
assumes h: "m x \<le> h"
begin

definition m_s :: "'av st \<Rightarrow> vname set \<Rightarrow> nat" (\<open>m\<^sub>s\<close>) where
"m_s S X = (\<Sum> x \<in> X. m(S x))"

lemma m_s_h: "finite X \<Longrightarrow> m_s S X \<le> h * card X"
by(simp add: m_s_def) (metis mult.commute of_nat_id sum_bounded_above[OF h])

fun m_o :: "'av st option \<Rightarrow> vname set \<Rightarrow> nat" (\<open>m\<^sub>o\<close>) where
"m_o (Some S) X = m_s S X" |
"m_o None X = h * card X + 1"

lemma m_o_h: "finite X \<Longrightarrow> m_o opt X \<le> (h*card X + 1)"
by(cases opt)(auto simp add: m_s_h le_SucI dest: m_s_h)

definition m_c :: "'av st option acom \<Rightarrow> nat" (\<open>m\<^sub>c\<close>) where
"m_c C = sum_list (map (\<lambda>a. m_o a (vars C)) (annos C))"

text\<open>Upper complexity bound:\<close>
lemma m_c_h: "m_c C \<le> size(annos C) * (h * card(vars C) + 1)"
proof-
  let ?X = "vars C" let ?n = "card ?X" let ?a = "size(annos C)"
  have "m_c C = (\<Sum>i<?a. m_o (annos C ! i) ?X)"
    by(simp add: m_c_def sum_list_sum_nth atLeast0LessThan)
  also have "\<dots> \<le> (\<Sum>i<?a. h * ?n + 1)"
    apply(rule sum_mono) using m_o_h[OF finite_Cvars] by simp
  also have "\<dots> = ?a * (h * ?n + 1)" by simp
  finally show ?thesis .
qed

end


locale Measure_fun = Measure1_fun where m=m
  for m :: "'av::semilattice_sup_top \<Rightarrow> nat" +
assumes m2: "x < y \<Longrightarrow> m x > m y"
begin

text\<open>The predicates \<open>top_on_ty a X\<close> that follow describe that any abstract
state in \<open>a\<close> maps all variables in \<open>X\<close> to \<^term>\<open>\<top>\<close>.
This is an important invariant for the termination proof where we argue that only
the finitely many variables in the program change. That the others do not change
follows because they remain \<^term>\<open>\<top>\<close>.\<close>

fun top_on_st :: "'av st \<Rightarrow> vname set \<Rightarrow> bool" (\<open>top'_on\<^sub>s\<close>) where
"top_on_st S X = (\<forall>x\<in>X. S x = \<top>)"

fun top_on_opt :: "'av st option \<Rightarrow> vname set \<Rightarrow> bool" (\<open>top'_on\<^sub>o\<close>) where
"top_on_opt (Some S) X = top_on_st S X" |
"top_on_opt None X = True"

definition top_on_acom :: "'av st option acom \<Rightarrow> vname set \<Rightarrow> bool" (\<open>top'_on\<^sub>c\<close>) where
"top_on_acom C X = (\<forall>a \<in> set(annos C). top_on_opt a X)"

lemma top_on_top: "top_on_opt \<top> X"
by(auto simp: top_option_def)

lemma top_on_bot: "top_on_acom (bot c) X"
by(auto simp add: top_on_acom_def bot_def)

lemma top_on_post: "top_on_acom C X \<Longrightarrow> top_on_opt (post C) X"
by(simp add: top_on_acom_def post_in_annos)

lemma top_on_acom_simps:
  "top_on_acom (SKIP {Q}) X = top_on_opt Q X"
  "top_on_acom (x ::= e {Q}) X = top_on_opt Q X"
  "top_on_acom (C1;;C2) X = (top_on_acom C1 X \<and> top_on_acom C2 X)"
  "top_on_acom (IF b THEN {P1} C1 ELSE {P2} C2 {Q}) X =
   (top_on_opt P1 X \<and> top_on_acom C1 X \<and> top_on_opt P2 X \<and> top_on_acom C2 X \<and> top_on_opt Q X)"
  "top_on_acom ({I} WHILE b DO {P} C {Q}) X =
   (top_on_opt I X \<and> top_on_acom C X \<and> top_on_opt P X \<and> top_on_opt Q X)"
by(auto simp add: top_on_acom_def)

lemma top_on_sup:
  "top_on_opt o1 X \<Longrightarrow> top_on_opt o2 X \<Longrightarrow> top_on_opt (o1 \<squnion> o2) X"
apply(induction o1 o2 rule: sup_option.induct)
apply(auto)
done

lemma top_on_Step: fixes C :: "'av st option acom"
assumes "!!x e S. \<lbrakk>top_on_opt S X; x \<notin> X; vars e \<subseteq> -X\<rbrakk> \<Longrightarrow> top_on_opt (f x e S) X"
        "!!b S. top_on_opt S X \<Longrightarrow> vars b \<subseteq> -X \<Longrightarrow> top_on_opt (g b S) X"
shows "\<lbrakk> vars C \<subseteq> -X; top_on_opt S X; top_on_acom C X \<rbrakk> \<Longrightarrow> top_on_acom (Step f g S C) X"
proof(induction C arbitrary: S)
qed (auto simp: top_on_acom_simps vars_acom_def top_on_post top_on_sup assms)

lemma m1: "x \<le> y \<Longrightarrow> m x \<ge> m y"
by(auto simp: le_less m2)

lemma m_s2_rep: assumes "finite(X)" and "S1 = S2 on -X" and "\<forall>x. S1 x \<le> S2 x" and "S1 \<noteq> S2"
shows "(\<Sum>x\<in>X. m (S2 x)) < (\<Sum>x\<in>X. m (S1 x))"
proof-
  from assms(3) have 1: "\<forall>x\<in>X. m(S1 x) \<ge> m(S2 x)" by (simp add: m1)
  from assms(2,3,4) have "\<exists>x\<in>X. S1 x < S2 x"
    by(simp add: fun_eq_iff) (metis Compl_iff le_neq_trans)
  hence 2: "\<exists>x\<in>X. m(S1 x) > m(S2 x)" by (metis m2)
  from sum_strict_mono_ex1[OF \<open>finite X\<close> 1 2]
  show "(\<Sum>x\<in>X. m (S2 x)) < (\<Sum>x\<in>X. m (S1 x))" .
qed

lemma m_s2: "finite(X) \<Longrightarrow> S1 = S2 on -X \<Longrightarrow> S1 < S2 \<Longrightarrow> m_s S1 X > m_s S2 X"
apply(auto simp add: less_fun_def m_s_def)
apply(simp add: m_s2_rep le_fun_def)
done

lemma m_o2: "finite X \<Longrightarrow> top_on_opt o1 (-X) \<Longrightarrow> top_on_opt o2 (-X) \<Longrightarrow>
  o1 < o2 \<Longrightarrow> m_o o1 X > m_o o2 X"
proof(induction o1 o2 rule: less_eq_option.induct)
  case 1 thus ?case by (auto simp: m_s2 less_option_def)
next
  case 2 thus ?case by(auto simp: less_option_def le_imp_less_Suc m_s_h)
next
  case 3 thus ?case by (auto simp: less_option_def)
qed

lemma m_o1: "finite X \<Longrightarrow> top_on_opt o1 (-X) \<Longrightarrow> top_on_opt o2 (-X) \<Longrightarrow>
  o1 \<le> o2 \<Longrightarrow> m_o o1 X \<ge> m_o o2 X"
by(auto simp: le_less m_o2)


lemma m_c2: "top_on_acom C1 (-vars C1) \<Longrightarrow> top_on_acom C2 (-vars C2) \<Longrightarrow>
  C1 < C2 \<Longrightarrow> m_c C1 > m_c C2"
proof(auto simp add: le_iff_le_annos size_annos_same[of C1 C2] vars_acom_def less_acom_def)
  let ?X = "vars(strip C2)"
  assume top: "top_on_acom C1 (- vars(strip C2))"  "top_on_acom C2 (- vars(strip C2))"
  and strip_eq: "strip C1 = strip C2"
  and 0: "\<forall>i<size(annos C2). annos C1 ! i \<le> annos C2 ! i"
  hence 1: "\<forall>i<size(annos C2). m_o (annos C1 ! i) ?X \<ge> m_o (annos C2 ! i) ?X"
    apply (auto simp: all_set_conv_all_nth vars_acom_def top_on_acom_def)
    by (metis (lifting, no_types) finite_cvars m_o1 size_annos_same2)
  fix i assume i: "i < size(annos C2)" "\<not> annos C2 ! i \<le> annos C1 ! i"
  have topo1: "top_on_opt (annos C1 ! i) (- ?X)"
    using i(1) top(1) by(simp add: top_on_acom_def size_annos_same[OF strip_eq])
  have topo2: "top_on_opt (annos C2 ! i) (- ?X)"
    using i(1) top(2) by(simp add: top_on_acom_def size_annos_same[OF strip_eq])
  from i have "m_o (annos C1 ! i) ?X > m_o (annos C2 ! i) ?X" (is "?P i")
    by (metis 0 less_option_def m_o2[OF finite_cvars topo1] topo2)
  hence 2: "\<exists>i < size(annos C2). ?P i" using \<open>i < size(annos C2)\<close> by blast
  have "(\<Sum>i<size(annos C2). m_o (annos C2 ! i) ?X)
         < (\<Sum>i<size(annos C2). m_o (annos C1 ! i) ?X)"
    apply(rule sum_strict_mono_ex1) using 1 2 by (auto)
  thus ?thesis
    by(simp add: m_c_def vars_acom_def strip_eq sum_list_sum_nth atLeast0LessThan size_annos_same[OF strip_eq])
qed

end


locale Abs_Int_fun_measure =
  Abs_Int_fun_mono where \<gamma>=\<gamma> + Measure_fun where m=m
  for \<gamma> :: "'av::semilattice_sup_top \<Rightarrow> val set" and m :: "'av \<Rightarrow> nat"
begin

lemma top_on_step': "top_on_acom C (-vars C) \<Longrightarrow> top_on_acom (step' \<top> C) (-vars C)"
unfolding step'_def
by(rule top_on_Step)
  (auto simp add: top_option_def asem_def split: option.splits)

lemma AI_Some_measure: "\<exists>C. AI c = Some C"
unfolding AI_def
apply(rule pfp_termination[where I = "\<lambda>C. top_on_acom C (- vars C)" and m="m_c"])
apply(simp_all add: m_c2 mono_step'_top bot_least top_on_bot)
using top_on_step' apply(auto simp add: vars_acom_def)
done

end

text\<open>Problem: not executable because of the comparison of abstract states,
i.e. functions, in the pre-fixpoint computation.\<close>

end
