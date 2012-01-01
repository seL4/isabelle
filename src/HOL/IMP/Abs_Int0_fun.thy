(* Author: Tobias Nipkow *)

header "Abstract Interpretation"

theory Abs_Int0_fun
imports "~~/src/HOL/ex/Interpretation_with_Defs"
        "~~/src/HOL/Library/While_Combinator"
        Collecting
begin

subsection "Orderings"

class preord =
fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
assumes le_refl[simp]: "x \<sqsubseteq> x"
and le_trans: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
begin

definition mono where "mono f = (\<forall>x y. x \<sqsubseteq> y \<longrightarrow> f x \<sqsubseteq> f y)"

lemma monoD: "mono f \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y" by(simp add: mono_def)

lemma mono_comp: "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (g o f)"
by(simp add: mono_def)

declare le_trans[trans]

end

text{* Note: no antisymmetry. Allows implementations where some abstract
element is implemented by two different values @{prop "x \<noteq> y"}
such that @{prop"x \<sqsubseteq> y"} and @{prop"y \<sqsubseteq> x"}. Antisymmetry is not
needed because we never compare elements for equality but only for @{text"\<sqsubseteq>"}.
*}

class SL_top = preord +
fixes join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
fixes Top :: "'a" ("\<top>")
assumes join_ge1 [simp]: "x \<sqsubseteq> x \<squnion> y"
and join_ge2 [simp]: "y \<sqsubseteq> x \<squnion> y"
and join_least: "x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<squnion> y \<sqsubseteq> z"
and top[simp]: "x \<sqsubseteq> \<top>"
begin

lemma join_le_iff[simp]: "x \<squnion> y \<sqsubseteq> z \<longleftrightarrow> x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
by (metis join_ge1 join_ge2 join_least le_trans)

lemma le_join_disj: "x \<sqsubseteq> y \<or> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<squnion> z"
by (metis join_ge1 join_ge2 le_trans)

end

instantiation "fun" :: (type, SL_top) SL_top
begin

definition "f \<sqsubseteq> g = (ALL x. f x \<sqsubseteq> g x)"
definition "f \<squnion> g = (\<lambda>x. f x \<squnion> g x)"
definition "\<top> = (\<lambda>x. \<top>)"

lemma join_apply[simp]: "(f \<squnion> g) x = f x \<squnion> g x"
by (simp add: join_fun_def)

instance
proof
  case goal2 thus ?case by (metis le_fun_def preord_class.le_trans)
qed (simp_all add: le_fun_def Top_fun_def)

end


instantiation acom :: (preord) preord
begin

fun le_acom :: "('a::preord)acom \<Rightarrow> 'a acom \<Rightarrow> bool" where
"le_acom (SKIP {S}) (SKIP {S'}) = (S \<sqsubseteq> S')" |
"le_acom (x ::= e {S}) (x' ::= e' {S'}) = (x=x' \<and> e=e' \<and> S \<sqsubseteq> S')" |
"le_acom (c1;c2) (c1';c2') = (le_acom c1 c1' \<and> le_acom c2 c2')" |
"le_acom (IF b THEN c1 ELSE c2 {S}) (IF b' THEN c1' ELSE c2' {S'}) =
  (b=b' \<and> le_acom c1 c1' \<and> le_acom c2 c2' \<and> S \<sqsubseteq> S')" |
"le_acom ({Inv} WHILE b DO c {P}) ({Inv'} WHILE b' DO c' {P'}) =
  (b=b' \<and> le_acom c c' \<and> Inv \<sqsubseteq> Inv' \<and> P \<sqsubseteq> P')" |
"le_acom _ _ = False"

lemma [simp]: "SKIP {S} \<sqsubseteq> c \<longleftrightarrow> (\<exists>S'. c = SKIP {S'} \<and> S \<sqsubseteq> S')"
by (cases c) auto

lemma [simp]: "x ::= e {S} \<sqsubseteq> c \<longleftrightarrow> (\<exists>S'. c = x ::= e {S'} \<and> S \<sqsubseteq> S')"
by (cases c) auto

lemma [simp]: "c1;c2 \<sqsubseteq> c \<longleftrightarrow> (\<exists>c1' c2'. c = c1';c2' \<and> c1 \<sqsubseteq> c1' \<and> c2 \<sqsubseteq> c2')"
by (cases c) auto

lemma [simp]: "IF b THEN c1 ELSE c2 {S} \<sqsubseteq> c \<longleftrightarrow>
  (\<exists>c1' c2' S'. c = IF b THEN c1' ELSE c2' {S'} \<and> c1 \<sqsubseteq> c1' \<and> c2 \<sqsubseteq> c2' \<and> S \<sqsubseteq> S')"
by (cases c) auto

lemma [simp]: "{Inv} WHILE b DO c {P} \<sqsubseteq> w \<longleftrightarrow>
  (\<exists>Inv' c' P'. w = {Inv'} WHILE b DO c' {P'} \<and> c \<sqsubseteq> c' \<and> Inv \<sqsubseteq> Inv' \<and> P \<sqsubseteq> P')"
by (cases w) auto

instance
proof
  case goal1 thus ?case by (induct x) auto
next
  case goal2 thus ?case
  apply(induct x y arbitrary: z rule: le_acom.induct)
  apply (auto intro: le_trans)
  done
qed

end


subsubsection "Lifting"

instantiation option :: (SL_top)SL_top
begin

fun le_option where
"Some x \<sqsubseteq> Some y = (x \<sqsubseteq> y)" |
"None \<sqsubseteq> y = True" |
"Some _ \<sqsubseteq> None = False"

lemma [simp]: "(x \<sqsubseteq> None) = (x = None)"
by (cases x) simp_all

lemma [simp]: "(Some x \<sqsubseteq> u) = (\<exists>y. u = Some y & x \<sqsubseteq> y)"
by (cases u) auto

fun join_option where
"Some x \<squnion> Some y = Some(x \<squnion> y)" |
"None \<squnion> y = y" |
"x \<squnion> None = x"

lemma join_None2[simp]: "x \<squnion> None = x"
by (cases x) simp_all

definition "\<top> = Some \<top>"

instance proof
  case goal1 show ?case by(cases x, simp_all)
next
  case goal2 thus ?case
    by(cases z, simp, cases y, simp, cases x, auto intro: le_trans)
next
  case goal3 thus ?case by(cases x, simp, cases y, simp_all)
next
  case goal4 thus ?case by(cases y, simp, cases x, simp_all)
next
  case goal5 thus ?case by(cases z, simp, cases y, simp, cases x, simp_all)
next
  case goal6 thus ?case by(cases x, simp_all add: Top_option_def)
qed

end

definition bot_acom :: "com \<Rightarrow> ('a::SL_top)option acom" ("\<bottom>\<^sub>c") where
"\<bottom>\<^sub>c = anno None"

lemma strip_bot_acom[simp]: "strip(\<bottom>\<^sub>c c) = c"
by(simp add: bot_acom_def)

lemma bot_acom[rule_format]: "strip c' = c \<longrightarrow> \<bottom>\<^sub>c c \<sqsubseteq> c'"
apply(induct c arbitrary: c')
apply (simp_all add: bot_acom_def)
 apply(induct_tac c')
  apply simp_all
 apply(induct_tac c')
  apply simp_all
 apply(induct_tac c')
  apply simp_all
 apply(induct_tac c')
  apply simp_all
 apply(induct_tac c')
  apply simp_all
done


subsubsection "Post-fixed point iteration"

definition
  pfp :: "(('a::preord) \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option" where
"pfp f = while_option (\<lambda>x. \<not> f x \<sqsubseteq> x) f"

lemma pfp_pfp: assumes "pfp f x0 = Some x" shows "f x \<sqsubseteq> x"
using while_option_stop[OF assms[simplified pfp_def]] by simp

lemma pfp_least:
assumes mono: "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
and "f p \<sqsubseteq> p" and "x0 \<sqsubseteq> p" and "pfp f x0 = Some x" shows "x \<sqsubseteq> p"
proof-
  { fix x assume "x \<sqsubseteq> p"
    hence  "f x \<sqsubseteq> f p" by(rule mono)
    from this `f p \<sqsubseteq> p` have "f x \<sqsubseteq> p" by(rule le_trans)
  }
  thus "x \<sqsubseteq> p" using assms(2-) while_option_rule[where P = "%x. x \<sqsubseteq> p"]
    unfolding pfp_def by blast
qed

definition
 lpfp\<^isub>c :: "(('a::SL_top)option acom \<Rightarrow> 'a option acom) \<Rightarrow> com \<Rightarrow> 'a option acom option" where
"lpfp\<^isub>c f c = pfp f (\<bottom>\<^sub>c c)"

lemma lpfpc_pfp: "lpfp\<^isub>c f c0 = Some c \<Longrightarrow> f c \<sqsubseteq> c"
by(simp add: pfp_pfp lpfp\<^isub>c_def)

lemma strip_pfp:
assumes "\<And>x. g(f x) = g x" and "pfp f x0 = Some x" shows "g x = g x0"
using assms while_option_rule[where P = "%x. g x = g x0" and c = f]
unfolding pfp_def by metis

lemma strip_lpfpc: assumes "\<And>c. strip(f c) = strip c" and "lpfp\<^isub>c f c = Some c'"
shows "strip c' = c"
using assms(1) strip_pfp[OF _ assms(2)[simplified lpfp\<^isub>c_def]]
by(metis strip_bot_acom)

lemma lpfpc_least:
assumes mono: "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
and "strip p = c0" and "f p \<sqsubseteq> p" and lp: "lpfp\<^isub>c f c0 = Some c" shows "c \<sqsubseteq> p"
using pfp_least[OF _ _ bot_acom[OF `strip p = c0`] lp[simplified lpfp\<^isub>c_def]]
  mono `f p \<sqsubseteq> p`
by blast


subsection "Abstract Interpretation"

definition \<gamma>_fun :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b)set" where
"\<gamma>_fun \<gamma> F = {f. \<forall>x. f x \<in> \<gamma>(F x)}"

fun \<gamma>_option :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a option \<Rightarrow> 'b set" where
"\<gamma>_option \<gamma> None = {}" |
"\<gamma>_option \<gamma> (Some a) = \<gamma> a"

text{* The interface for abstract values: *}

locale Val_abs =
fixes \<gamma> :: "'av::SL_top \<Rightarrow> val set"
  assumes mono_gamma: "a \<sqsubseteq> b \<Longrightarrow> \<gamma> a \<subseteq> \<gamma> b"
  and gamma_Top[simp]: "\<gamma> \<top> = UNIV"
fixes num' :: "val \<Rightarrow> 'av"
and plus' :: "'av \<Rightarrow> 'av \<Rightarrow> 'av"
  assumes gamma_num': "n : \<gamma>(num' n)"
  and gamma_plus':
 "n1 : \<gamma> a1 \<Longrightarrow> n2 : \<gamma> a2 \<Longrightarrow> n1+n2 : \<gamma>(plus' a1 a2)"

type_synonym 'av st = "(vname \<Rightarrow> 'av)"

locale Abs_Int_Fun = Val_abs \<gamma> for \<gamma> :: "'av::SL_top \<Rightarrow> val set"
begin

fun aval' :: "aexp \<Rightarrow> 'av st \<Rightarrow> 'av" where
"aval' (N n) S = num' n" |
"aval' (V x) S = S x" |
"aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

fun step' :: "'av st option \<Rightarrow> 'av st option acom \<Rightarrow> 'av st option acom"
 where
"step' S (SKIP {P}) = (SKIP {S})" |
"step' S (x ::= e {P}) =
  x ::= e {case S of None \<Rightarrow> None | Some S \<Rightarrow> Some(S(x := aval' e S))}" |
"step' S (c1; c2) = step' S c1; step' (post c1) c2" |
"step' S (IF b THEN c1 ELSE c2 {P}) =
   IF b THEN step' S c1 ELSE step' S c2 {post c1 \<squnion> post c2}" |
"step' S ({Inv} WHILE b DO c {P}) =
  {S \<squnion> post c} WHILE b DO (step' Inv c) {Inv}"

definition AI :: "com \<Rightarrow> 'av st option acom option" where
"AI = lpfp\<^isub>c (step' \<top>)"


lemma strip_step'[simp]: "strip(step' S c) = strip c"
by(induct c arbitrary: S) (simp_all add: Let_def)


abbreviation \<gamma>\<^isub>f :: "'av st \<Rightarrow> state set"
where "\<gamma>\<^isub>f == \<gamma>_fun \<gamma>"

abbreviation \<gamma>\<^isub>o :: "'av st option \<Rightarrow> state set"
where "\<gamma>\<^isub>o == \<gamma>_option \<gamma>\<^isub>f"

abbreviation \<gamma>\<^isub>c :: "'av st option acom \<Rightarrow> state set acom"
where "\<gamma>\<^isub>c == map_acom \<gamma>\<^isub>o"

lemma gamma_f_Top[simp]: "\<gamma>\<^isub>f Top = UNIV"
by(simp add: Top_fun_def \<gamma>_fun_def)

lemma gamma_o_Top[simp]: "\<gamma>\<^isub>o Top = UNIV"
by (simp add: Top_option_def)

(* FIXME (maybe also le \<rightarrow> sqle?) *)

lemma mono_gamma_f: "f \<sqsubseteq> g \<Longrightarrow> \<gamma>\<^isub>f f \<subseteq> \<gamma>\<^isub>f g"
by(auto simp: le_fun_def \<gamma>_fun_def dest: mono_gamma)

lemma mono_gamma_o:
  "sa \<sqsubseteq> sa' \<Longrightarrow> \<gamma>\<^isub>o sa \<subseteq> \<gamma>\<^isub>o sa'"
by(induction sa sa' rule: le_option.induct)(simp_all add: mono_gamma_f)

lemma mono_gamma_c: "ca \<sqsubseteq> ca' \<Longrightarrow> \<gamma>\<^isub>c ca \<le> \<gamma>\<^isub>c ca'"
by (induction ca ca' rule: le_acom.induct) (simp_all add:mono_gamma_o)

text{* Soundness: *}

lemma aval'_sound: "s : \<gamma>\<^isub>f S \<Longrightarrow> aval a s : \<gamma>(aval' a S)"
by (induct a) (auto simp: gamma_num' gamma_plus' \<gamma>_fun_def)

lemma in_gamma_update:
  "\<lbrakk> s : \<gamma>\<^isub>f S; i : \<gamma> a \<rbrakk> \<Longrightarrow> s(x := i) : \<gamma>\<^isub>f(S(x := a))"
by(simp add: \<gamma>_fun_def)

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
  ultimately show ?case using `S \<subseteq> \<gamma>\<^isub>o sa` by (simp add: If.IH subset_iff)
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
  ultimately show ?case by (simp add: While.IH subset_iff)
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

locale Abs_Int_Fun_mono = Abs_Int_Fun +
assumes mono_plus': "a1 \<sqsubseteq> b1 \<Longrightarrow> a2 \<sqsubseteq> b2 \<Longrightarrow> plus' a1 a2 \<sqsubseteq> plus' b1 b2"
begin

lemma mono_aval': "S \<sqsubseteq> S' \<Longrightarrow> aval' e S \<sqsubseteq> aval' e S'"
by(induction e)(auto simp: le_fun_def mono_plus')

lemma mono_update: "a \<sqsubseteq> a' \<Longrightarrow> S \<sqsubseteq> S' \<Longrightarrow> S(x := a) \<sqsubseteq> S'(x := a')"
by(simp add: le_fun_def)

lemma step'_mono: "S \<sqsubseteq> S' \<Longrightarrow> step' S c \<sqsubseteq> step' S' c"
apply(induction c arbitrary: S S')
apply (auto simp: Let_def mono_update mono_aval' le_join_disj split: option.split)
done

end

text{* Problem: not executable because of the comparison of abstract states,
i.e. functions, in the post-fixedpoint computation. *}

end
