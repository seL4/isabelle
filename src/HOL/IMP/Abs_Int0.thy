(* Author: Tobias Nipkow *)

theory Abs_Int0
imports Abs_Int_init
begin

subsection "Orderings"

text{* The basic type classes @{class order}, @{class semilattice_sup} and @{class top} are
defined in @{theory Main}, more precisely in theories @{theory Orderings} and @{theory Lattices}.
If you view this theory with jedit, just click on the names to get there. *}

class semilattice = semilattice_sup + top


instance "fun" :: (type, semilattice) semilattice ..

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

instance proof
  case goal1 show ?case by(rule less_option_def)
next
  case goal2 show ?case by(cases x, simp_all)
next
  case goal3 thus ?case by(cases z, simp, cases y, simp, cases x, auto)
next
  case goal4 thus ?case by(cases y, simp, cases x, auto)
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

instantiation option :: (semilattice)semilattice
begin

definition top_option where "\<top> = Some \<top>"

instance proof
  case goal4 show ?case by(cases a, simp_all add: top_option_def)
next
  case goal1 thus ?case by(cases x, simp, cases y, simp_all)
next
  case goal2 thus ?case by(cases y, simp, cases x, simp_all)
next
  case goal3 thus ?case by(cases z, simp, cases y, simp, cases x, simp_all)
qed

end

lemma [simp]: "(Some x < Some y) = (x < y)"
by(auto simp: less_le)

instantiation option :: (order)bot
begin

definition bot_option :: "'a option" where
"\<bottom> = None"

instance
proof
  case goal1 thus ?case by(auto simp: bot_option_def)
qed

end


definition bot :: "com \<Rightarrow> 'a option acom" where
"bot c = anno None c"

lemma bot_least: "strip C = c \<Longrightarrow> bot c \<le> C"
by(induct C arbitrary: c)(auto simp: bot_def)

lemma strip_bot[simp]: "strip(bot c) = c"
by(simp add: bot_def)


subsubsection "Post-fixed point iteration"

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
unfolding pfp_def by (metis (lifting) while_option_rule)

lemma strip_pfp:
assumes "\<And>x. g(f x) = g x" and "pfp f x0 = Some x" shows "g x = g x0"
using pfp_inv[OF assms(2), where P = "%x. g x = g x0"] assms(1) by simp


subsection "Abstract Interpretation"

definition \<gamma>_fun :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b)set" where
"\<gamma>_fun \<gamma> F = {f. \<forall>x. f x \<in> \<gamma>(F x)}"

fun \<gamma>_option :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a option \<Rightarrow> 'b set" where
"\<gamma>_option \<gamma> None = {}" |
"\<gamma>_option \<gamma> (Some a) = \<gamma> a"

text{* The interface for abstract values: *}

locale Val_abs =
fixes \<gamma> :: "'av::semilattice \<Rightarrow> val set"
  assumes mono_gamma: "a \<le> b \<Longrightarrow> \<gamma> a \<le> \<gamma> b"
  and gamma_Top[simp]: "\<gamma> \<top> = UNIV"
fixes num' :: "val \<Rightarrow> 'av"
and plus' :: "'av \<Rightarrow> 'av \<Rightarrow> 'av"
  assumes gamma_num': "i \<in> \<gamma>(num' i)"
  and gamma_plus': "i1 \<in> \<gamma> a1 \<Longrightarrow> i2 \<in> \<gamma> a2 \<Longrightarrow> i1+i2 \<in> \<gamma>(plus' a1 a2)"

type_synonym 'av st = "(vname \<Rightarrow> 'av)"

locale Abs_Int_fun = Val_abs \<gamma> for \<gamma> :: "'av::semilattice \<Rightarrow> val set"
begin

fun aval' :: "aexp \<Rightarrow> 'av st \<Rightarrow> 'av" where
"aval' (N i) S = num' i" |
"aval' (V x) S = S x" |
"aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

definition "fa x e S = (case S of None \<Rightarrow> None | Some S \<Rightarrow> Some(S(x := aval' e S)))"

definition "step' = Step fa (\<lambda>b S. S)"

definition AI :: "com \<Rightarrow> 'av st option acom option" where
"AI c = pfp (step' \<top>) (bot c)"


abbreviation \<gamma>\<^isub>s :: "'av st \<Rightarrow> state set"
where "\<gamma>\<^isub>s == \<gamma>_fun \<gamma>"

abbreviation \<gamma>\<^isub>o :: "'av st option \<Rightarrow> state set"
where "\<gamma>\<^isub>o == \<gamma>_option \<gamma>\<^isub>s"

abbreviation \<gamma>\<^isub>c :: "'av st option acom \<Rightarrow> state set acom"
where "\<gamma>\<^isub>c == map_acom \<gamma>\<^isub>o"

lemma gamma_s_Top[simp]: "\<gamma>\<^isub>s \<top> = UNIV"
by(simp add: top_fun_def \<gamma>_fun_def)

lemma gamma_o_Top[simp]: "\<gamma>\<^isub>o \<top> = UNIV"
by (simp add: top_option_def)

lemma mono_gamma_s: "f1 \<le> f2 \<Longrightarrow> \<gamma>\<^isub>s f1 \<subseteq> \<gamma>\<^isub>s f2"
by(auto simp: le_fun_def \<gamma>_fun_def dest: mono_gamma)

lemma mono_gamma_o:
  "S1 \<le> S2 \<Longrightarrow> \<gamma>\<^isub>o S1 \<subseteq> \<gamma>\<^isub>o S2"
by(induction S1 S2 rule: less_eq_option.induct)(simp_all add: mono_gamma_s)

lemma mono_gamma_c: "C1 \<le> C2 \<Longrightarrow> \<gamma>\<^isub>c C1 \<le> \<gamma>\<^isub>c C2"
by (induction C1 C2 rule: less_eq_acom.induct) (simp_all add:mono_gamma_o)

text{* Soundness: *}

lemma aval'_sound: "s : \<gamma>\<^isub>s S \<Longrightarrow> aval a s : \<gamma>(aval' a S)"
by (induct a) (auto simp: gamma_num' gamma_plus' \<gamma>_fun_def)

lemma in_gamma_update: "\<lbrakk> s : \<gamma>\<^isub>s S; i : \<gamma> a \<rbrakk> \<Longrightarrow> s(x := i) : \<gamma>\<^isub>s(S(x := a))"
by(simp add: \<gamma>_fun_def)

lemma gamma_Step_subcomm:
  assumes "!!x e S. f1 x e (\<gamma>\<^isub>o S) \<subseteq> \<gamma>\<^isub>o (f2 x e S)"  "!!b S. g1 b (\<gamma>\<^isub>o S) \<subseteq> \<gamma>\<^isub>o (g2 b S)"
  shows "Step f1 g1 (\<gamma>\<^isub>o S) (\<gamma>\<^isub>c C) \<le> \<gamma>\<^isub>c (Step f2 g2 S C)"
proof(induction C arbitrary: S)
qed  (auto simp: mono_gamma_o assms)

lemma step_step': "step (\<gamma>\<^isub>o S) (\<gamma>\<^isub>c C) \<le> \<gamma>\<^isub>c (step' S C)"
unfolding step_def step'_def
by(rule gamma_Step_subcomm)
  (auto simp: aval'_sound in_gamma_update fa_def split: option.splits)

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

lemma mono_post: "C1 \<le> C2 \<Longrightarrow> post C1 \<le> post C2"
by(induction C1 C2 rule: less_eq_acom.induct) (auto)

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
  (auto simp: mono_update mono_aval' fa_def split: option.split)

end

text{* Problem: not executable because of the comparison of abstract states,
i.e. functions, in the post-fixedpoint computation. *}

end
