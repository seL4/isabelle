(* Author: Tobias Nipkow *)

theory Abs_Int0
imports Abs_Int_init
begin

subsection "Orderings"

class preord =
fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
assumes le_refl[simp]: "x \<sqsubseteq> x"
and le_trans: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
begin

definition mono where "mono f = (\<forall>x y. x \<sqsubseteq> y \<longrightarrow> f x \<sqsubseteq> f y)"

declare le_trans[trans]

end

text{* Note: no antisymmetry. Allows implementations where some abstract
element is implemented by two different values @{prop "x \<noteq> y"}
such that @{prop"x \<sqsubseteq> y"} and @{prop"y \<sqsubseteq> x"}. Antisymmetry is not
needed because we never compare elements for equality but only for @{text"\<sqsubseteq>"}.
*}

class join = preord +
fixes join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)

class SL_top = join +
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

instantiation "fun" :: (type, preord) preord
begin

definition "f \<sqsubseteq> g = (\<forall>x. f x \<sqsubseteq> g x)"

instance
proof
  case goal2 thus ?case by (metis le_fun_def preord_class.le_trans)
qed (simp_all add: le_fun_def)

end


instantiation "fun" :: (type, SL_top) SL_top
begin

definition "f \<squnion> g = (\<lambda>x. f x \<squnion> g x)"
definition "\<top> = (\<lambda>x. \<top>)"

lemma join_apply[simp]: "(f \<squnion> g) x = f x \<squnion> g x"
by (simp add: join_fun_def)

instance
proof
qed (simp_all add: le_fun_def Top_fun_def)

end


instantiation acom :: (preord) preord
begin

fun le_acom :: "('a::preord)acom \<Rightarrow> 'a acom \<Rightarrow> bool" where
"le_acom (SKIP {S}) (SKIP {S'}) = (S \<sqsubseteq> S')" |
"le_acom (x ::= e {S}) (x' ::= e' {S'}) = (x=x' \<and> e=e' \<and> S \<sqsubseteq> S')" |
"le_acom (C1;C2) (D1;D2) = (C1 \<sqsubseteq> D1 \<and> C2 \<sqsubseteq> D2)" |
"le_acom (IF b THEN C1 ELSE C2 {S}) (IF b' THEN D1 ELSE D2 {S'}) =
  (b=b' \<and> C1 \<sqsubseteq> D1 \<and> C2 \<sqsubseteq> D2 \<and> S \<sqsubseteq> S')" |
"le_acom ({I} WHILE b DO C {P}) ({I'} WHILE b' DO C' {P'}) =
  (b=b' \<and> C \<sqsubseteq> C' \<and> I \<sqsubseteq> I' \<and> P \<sqsubseteq> P')" |
"le_acom _ _ = False"

lemma [simp]: "SKIP {S} \<sqsubseteq> C \<longleftrightarrow> (\<exists>S'. C = SKIP {S'} \<and> S \<sqsubseteq> S')"
by (cases C) auto

lemma [simp]: "x ::= e {S} \<sqsubseteq> C \<longleftrightarrow> (\<exists>S'. C = x ::= e {S'} \<and> S \<sqsubseteq> S')"
by (cases C) auto

lemma [simp]: "C1;C2 \<sqsubseteq> C \<longleftrightarrow> (\<exists>D1 D2. C = D1;D2 \<and> C1 \<sqsubseteq> D1 \<and> C2 \<sqsubseteq> D2)"
by (cases C) auto

lemma [simp]: "IF b THEN C1 ELSE C2 {S} \<sqsubseteq> C \<longleftrightarrow>
  (\<exists>D1 D2 S'. C = IF b THEN D1 ELSE D2 {S'} \<and> C1 \<sqsubseteq> D1 \<and> C2 \<sqsubseteq> D2 \<and> S \<sqsubseteq> S')"
by (cases C) auto

lemma [simp]: "{I} WHILE b DO C {P} \<sqsubseteq> W \<longleftrightarrow>
  (\<exists>I' C' P'. W = {I'} WHILE b DO C' {P'} \<and> C \<sqsubseteq> C' \<and> I \<sqsubseteq> I' \<and> P \<sqsubseteq> P')"
by (cases W) auto

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


instantiation option :: (preord)preord
begin

fun le_option where
"Some x \<sqsubseteq> Some y = (x \<sqsubseteq> y)" |
"None \<sqsubseteq> y = True" |
"Some _ \<sqsubseteq> None = False"

lemma [simp]: "(x \<sqsubseteq> None) = (x = None)"
by (cases x) simp_all

lemma [simp]: "(Some x \<sqsubseteq> u) = (\<exists>y. u = Some y \<and> x \<sqsubseteq> y)"
by (cases u) auto

instance proof
  case goal1 show ?case by(cases x, simp_all)
next
  case goal2 thus ?case
    by(cases z, simp, cases y, simp, cases x, auto intro: le_trans)
qed

end

instantiation option :: (join)join
begin

fun join_option where
"Some x \<squnion> Some y = Some(x \<squnion> y)" |
"None \<squnion> y = y" |
"x \<squnion> None = x"

lemma join_None2[simp]: "x \<squnion> None = x"
by (cases x) simp_all

instance ..

end

instantiation option :: (SL_top)SL_top
begin

definition "\<top> = Some \<top>"

instance proof
  case goal1 thus ?case by(cases x, simp, cases y, simp_all)
next
  case goal2 thus ?case by(cases y, simp, cases x, simp_all)
next
  case goal3 thus ?case by(cases z, simp, cases y, simp, cases x, simp_all)
next
  case goal4 thus ?case by(cases x, simp_all add: Top_option_def)
qed

end

class Bot = preord +
fixes Bot :: "'a" ("\<bottom>")
assumes Bot[simp]: "\<bottom> \<sqsubseteq> x"

instantiation option :: (preord)Bot
begin

definition Bot_option :: "'a option" where
"\<bottom> = None"

instance
proof
  case goal1 thus ?case by(auto simp: Bot_option_def)
qed

end


definition bot :: "com \<Rightarrow> 'a option acom" where
"bot c = anno None c"

lemma bot_least: "strip C = c \<Longrightarrow> bot c \<sqsubseteq> C"
by(induct C arbitrary: c)(auto simp: bot_def)

lemma strip_bot[simp]: "strip(bot c) = c"
by(simp add: bot_def)


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
 lpfp :: "('a::preord option acom \<Rightarrow> 'a option acom) \<Rightarrow> com \<Rightarrow> 'a option acom option"
where "lpfp f c = pfp f (bot c)"

lemma lpfpc_pfp: "lpfp f c = Some p \<Longrightarrow> f p \<sqsubseteq> p"
by(simp add: pfp_pfp lpfp_def)

lemma strip_pfp:
assumes "\<And>x. g(f x) = g x" and "pfp f x0 = Some x" shows "g x = g x0"
using assms while_option_rule[where P = "%x. g x = g x0" and c = f]
unfolding pfp_def by metis

lemma strip_lpfp: assumes "\<And>C. strip(f C) = strip C" and "lpfp f c = Some C"
shows "strip C = c"
using assms(1) strip_pfp[OF _ assms(2)[simplified lpfp_def]]
by(metis strip_bot)


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
"step' S (C1; C2) = step' S C1; step' (post C1) C2" |
"step' S (IF b THEN C1 ELSE C2 {P}) =
   IF b THEN step' S C1 ELSE step' S C2 {post C1 \<squnion> post C2}" |
"step' S ({Inv} WHILE b DO C {P}) =
  {S \<squnion> post C} WHILE b DO (step' Inv C) {Inv}"

definition AI :: "com \<Rightarrow> 'av st option acom option" where
"AI = lpfp (step' \<top>)"


lemma strip_step'[simp]: "strip(step' S C) = strip C"
by(induct C arbitrary: S) (simp_all add: Let_def)


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

lemma mono_gamma_f: "f1 \<sqsubseteq> f2 \<Longrightarrow> \<gamma>\<^isub>f f1 \<subseteq> \<gamma>\<^isub>f f2"
by(auto simp: le_fun_def \<gamma>_fun_def dest: mono_gamma)

lemma mono_gamma_o:
  "S1 \<sqsubseteq> S2 \<Longrightarrow> \<gamma>\<^isub>o S1 \<subseteq> \<gamma>\<^isub>o S2"
by(induction S1 S2 rule: le_option.induct)(simp_all add: mono_gamma_f)

lemma mono_gamma_c: "C1 \<sqsubseteq> C2 \<Longrightarrow> \<gamma>\<^isub>c C1 \<le> \<gamma>\<^isub>c C2"
by (induction C1 C2 rule: le_acom.induct) (simp_all add:mono_gamma_o)

text{* Soundness: *}

lemma aval'_sound: "s : \<gamma>\<^isub>f S \<Longrightarrow> aval a s : \<gamma>(aval' a S)"
by (induct a) (auto simp: gamma_num' gamma_plus' \<gamma>_fun_def)

lemma in_gamma_update:
  "\<lbrakk> s : \<gamma>\<^isub>f S; i : \<gamma> a \<rbrakk> \<Longrightarrow> s(x := i) : \<gamma>\<^isub>f(S(x := a))"
by(simp add: \<gamma>_fun_def)

lemma step_preserves_le:
  "\<lbrakk> S \<subseteq> \<gamma>\<^isub>o S'; C \<le> \<gamma>\<^isub>c C' \<rbrakk> \<Longrightarrow> step S C \<le> \<gamma>\<^isub>c (step' S' C')"
proof(induction C arbitrary: C' S S')
  case SKIP thus ?case by(auto simp:SKIP_le map_acom_SKIP)
next
  case Assign thus ?case
    by (fastforce simp: Assign_le  map_acom_Assign intro: aval'_sound in_gamma_update
      split: option.splits del:subsetD)
next
  case Seq thus ?case apply (auto simp: Seq_le map_acom_Seq)
    by (metis le_post post_map_acom)
next
  case (If b C1 C2 P)
  then obtain D1 D2 P' where
      "C' = IF b THEN D1 ELSE D2 {P'}"
      "P \<subseteq> \<gamma>\<^isub>o P'" "C1 \<le> \<gamma>\<^isub>c D1" "C2 \<le> \<gamma>\<^isub>c D2"
    by (fastforce simp: If_le map_acom_If)
  moreover have "post C1 \<subseteq> \<gamma>\<^isub>o(post D1 \<squnion> post D2)"
    by (metis (no_types) `C1 \<le> \<gamma>\<^isub>c D1` join_ge1 le_post mono_gamma_o order_trans post_map_acom)
  moreover have "post C2 \<subseteq> \<gamma>\<^isub>o(post D1 \<squnion> post D2)"
    by (metis (no_types) `C2 \<le> \<gamma>\<^isub>c D2` join_ge2 le_post mono_gamma_o order_trans post_map_acom)
  ultimately show ?case using `S \<subseteq> \<gamma>\<^isub>o S'` by (simp add: If.IH subset_iff)
next
  case (While I b C1 P)
  then obtain D1 I' P' where
    "C' = {I'} WHILE b DO D1 {P'}"
    "I \<subseteq> \<gamma>\<^isub>o I'" "P \<subseteq> \<gamma>\<^isub>o P'" "C1 \<le> \<gamma>\<^isub>c D1"
    by (fastforce simp: map_acom_While While_le)
  moreover have "S \<union> post C1 \<subseteq> \<gamma>\<^isub>o (S' \<squnion> post D1)"
    using `S \<subseteq> \<gamma>\<^isub>o S'` le_post[OF `C1 \<le> \<gamma>\<^isub>c D1`, simplified]
    by (metis (no_types) join_ge1 join_ge2 le_sup_iff mono_gamma_o order_trans)
  ultimately show ?case by (simp add: While.IH subset_iff)
qed

lemma AI_sound: "AI c = Some C \<Longrightarrow> CS c \<le> \<gamma>\<^isub>c C"
proof(simp add: CS_def AI_def)
  assume 1: "lpfp (step' \<top>) c = Some C"
  have 2: "step' \<top> C \<sqsubseteq> C" by(rule lpfpc_pfp[OF 1])
  have 3: "strip (\<gamma>\<^isub>c (step' \<top> C)) = c"
    by(simp add: strip_lpfp[OF _ 1])
  have "lfp c (step UNIV) \<le> \<gamma>\<^isub>c (step' \<top> C)"
  proof(rule lfp_lowerbound[simplified,OF 3])
    show "step UNIV (\<gamma>\<^isub>c (step' \<top> C)) \<le> \<gamma>\<^isub>c (step' \<top> C)"
    proof(rule step_preserves_le[OF _ _])
      show "UNIV \<subseteq> \<gamma>\<^isub>o \<top>" by simp
      show "\<gamma>\<^isub>c (step' \<top> C) \<le> \<gamma>\<^isub>c C" by(rule mono_gamma_c[OF 2])
    qed
  qed
  with 2 show "lfp c (step UNIV) \<le> \<gamma>\<^isub>c C"
    by (blast intro: mono_gamma_c order_trans)
qed

end


subsubsection "Monotonicity"

lemma mono_post: "C1 \<sqsubseteq> C2 \<Longrightarrow> post C1 \<sqsubseteq> post C2"
by(induction C1 C2 rule: le_acom.induct) (auto)

locale Abs_Int_Fun_mono = Abs_Int_Fun +
assumes mono_plus': "a1 \<sqsubseteq> b1 \<Longrightarrow> a2 \<sqsubseteq> b2 \<Longrightarrow> plus' a1 a2 \<sqsubseteq> plus' b1 b2"
begin

lemma mono_aval': "S \<sqsubseteq> S' \<Longrightarrow> aval' e S \<sqsubseteq> aval' e S'"
by(induction e)(auto simp: le_fun_def mono_plus')

lemma mono_update: "a \<sqsubseteq> a' \<Longrightarrow> S \<sqsubseteq> S' \<Longrightarrow> S(x := a) \<sqsubseteq> S'(x := a')"
by(simp add: le_fun_def)

lemma mono_step': "S1 \<sqsubseteq> S2 \<Longrightarrow> C1 \<sqsubseteq> C2 \<Longrightarrow> step' S1 C1 \<sqsubseteq> step' S2 C2"
apply(induction C1 C2 arbitrary: S1 S2 rule: le_acom.induct)
apply (auto simp: Let_def mono_update mono_aval' mono_post le_join_disj
            split: option.split)
done

end

text{* Problem: not executable because of the comparison of abstract states,
i.e. functions, in the post-fixedpoint computation. *}

end
