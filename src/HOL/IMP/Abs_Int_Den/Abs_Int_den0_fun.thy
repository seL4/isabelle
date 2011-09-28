(* Author: Tobias Nipkow *)

header "Denotational Abstract Interpretation"

theory Abs_Int_den0_fun
imports "~~/src/HOL/ex/Interpretation_with_Defs" Big_Step
begin

subsection "Orderings"

class preord =
fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
assumes le_refl[simp]: "x \<sqsubseteq> x"
and le_trans: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"

text{* Note: no antisymmetry. Allows implementations where some abstract
element is implemented by two different values @{prop "x \<noteq> y"}
such that @{prop"x \<sqsubseteq> y"} and @{prop"y \<sqsubseteq> x"}. Antisymmetry is not
needed because we never compare elements for equality but only for @{text"\<sqsubseteq>"}.
*}

class SL_top = preord +
fixes join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
fixes Top :: "'a"
assumes join_ge1 [simp]: "x \<sqsubseteq> x \<squnion> y"
and join_ge2 [simp]: "y \<sqsubseteq> x \<squnion> y"
and join_least: "x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<squnion> y \<sqsubseteq> z"
and top[simp]: "x \<sqsubseteq> Top"
begin

lemma join_le_iff[simp]: "x \<squnion> y \<sqsubseteq> z \<longleftrightarrow> x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
by (metis join_ge1 join_ge2 join_least le_trans)

fun iter :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
"iter 0 f _ = Top" |
"iter (Suc n) f x = (if f x \<sqsubseteq> x then x else iter n f (f x))"

lemma iter_pfp: "f(iter n f x) \<sqsubseteq> iter n f x"
apply (induction n arbitrary: x)
 apply (simp)
apply (simp)
done

abbreviation iter' :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
"iter' n f x0 == iter n (\<lambda>x. x0 \<squnion> f x) x0"

lemma iter'_pfp_above:
  "f(iter' n f x0) \<sqsubseteq> iter' n f x0"  "x0 \<sqsubseteq> iter' n f x0"
using iter_pfp[of "\<lambda>x. x0 \<squnion> f x"] by auto

text{* So much for soundness. But how good an approximation of the post-fixed
point does @{const iter} yield? *}

lemma iter_funpow: "iter n f x \<noteq> Top \<Longrightarrow> \<exists>k. iter n f x = (f^^k) x"
apply(induction n arbitrary: x)
 apply simp
apply (auto)
 apply(metis funpow.simps(1) id_def)
by (metis funpow.simps(2) funpow_swap1 o_apply)

text{* For monotone @{text f}, @{term "iter f n x0"} yields the least
post-fixed point above @{text x0}, unless it yields @{text Top}. *}

lemma iter_least_pfp:
assumes mono: "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y" and "iter n f x0 \<noteq> Top"
and "f p \<sqsubseteq> p" and "x0 \<sqsubseteq> p" shows "iter n f x0 \<sqsubseteq> p"
proof-
  obtain k where "iter n f x0 = (f^^k) x0"
    using iter_funpow[OF `iter n f x0 \<noteq> Top`] by blast
  moreover
  { fix n have "(f^^n) x0 \<sqsubseteq> p"
    proof(induction n)
      case 0 show ?case by(simp add: `x0 \<sqsubseteq> p`)
    next
      case (Suc n) thus ?case
        by (simp add: `x0 \<sqsubseteq> p`)(metis Suc assms(3) le_trans mono)
    qed
  } ultimately show ?thesis by simp
qed

end

text{* The interface of abstract values: *}

locale Rep =
fixes rep :: "'a::SL_top \<Rightarrow> 'b set"
assumes le_rep: "a \<sqsubseteq> b \<Longrightarrow> rep a \<subseteq> rep b"
begin

abbreviation in_rep (infix "<:" 50) where "x <: a == x : rep a"

lemma in_rep_join: "x <: a1 \<or> x <: a2 \<Longrightarrow> x <: a1 \<squnion> a2"
by (metis SL_top_class.join_ge1 SL_top_class.join_ge2 le_rep subsetD)

end

locale Val_abs = Rep rep
  for rep :: "'a::SL_top \<Rightarrow> val set" +
fixes num' :: "val \<Rightarrow> 'a"
and plus' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
assumes rep_num': "rep(num' n) = {n}"
and rep_plus': "n1 <: a1 \<Longrightarrow> n2 <: a2 \<Longrightarrow> n1+n2 <: plus' a1 a2"


instantiation "fun" :: (type, SL_top) SL_top
begin

definition "f \<sqsubseteq> g = (ALL x. f x \<sqsubseteq> g x)"
definition "f \<squnion> g = (\<lambda>x. f x \<squnion> g x)"
definition "Top = (\<lambda>x. Top)"

lemma join_apply[simp]:
  "(f \<squnion> g) x = f x \<squnion> g x"
by (simp add: join_fun_def)

instance
proof
  case goal2 thus ?case by (metis le_fun_def preord_class.le_trans)
qed (simp_all add: le_fun_def Top_fun_def)

end

subsection "Abstract Interpretation Abstractly"

text{* Abstract interpretation over abstract values. Abstract states are
simply functions. The post-fixed point finder is parameterized over. *}

type_synonym 'a st = "name \<Rightarrow> 'a"

locale Abs_Int_Fun = Val_abs +
fixes pfp :: "('a st \<Rightarrow> 'a st) \<Rightarrow> 'a st \<Rightarrow> 'a st"
assumes pfp: "f(pfp f x) \<sqsubseteq> pfp f x"
assumes above: "x \<sqsubseteq> pfp f x"
begin

fun aval' :: "aexp \<Rightarrow> (name \<Rightarrow> 'a) \<Rightarrow> 'a" where
"aval' (N n) _ = num' n" |
"aval' (V x) S = S x" |
"aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

abbreviation fun_in_rep (infix "<:" 50) where
"f <: F == \<forall>x. f x <: F x"

lemma fun_in_rep_le: "(s::state) <: S \<Longrightarrow> S \<sqsubseteq> T \<Longrightarrow> s <: T"
by (metis le_fun_def le_rep subsetD)

lemma aval'_sound: "s <: S \<Longrightarrow> aval a s <: aval' a S"
by (induct a) (auto simp: rep_num' rep_plus')

fun AI :: "com \<Rightarrow> (name \<Rightarrow> 'a) \<Rightarrow> (name \<Rightarrow> 'a)" where
"AI SKIP S = S" |
"AI (x ::= a) S = S(x := aval' a S)" |
"AI (c1;c2) S = AI c2 (AI c1 S)" |
"AI (IF b THEN c1 ELSE c2) S = (AI c1 S) \<squnion> (AI c2 S)" |
"AI (WHILE b DO c) S = pfp (AI c) S"

lemma AI_sound: "(c,s) \<Rightarrow> t \<Longrightarrow> s <: S0 \<Longrightarrow> t <: AI c S0"
proof(induction c arbitrary: s t S0)
  case SKIP thus ?case by fastforce
next
  case Assign thus ?case by (auto simp: aval'_sound)
next
  case Semi thus ?case by auto
next
  case If thus ?case by(auto simp: in_rep_join)
next
  case (While b c)
  let ?P = "pfp (AI c) S0"
  { fix s t have "(WHILE b DO c,s) \<Rightarrow> t \<Longrightarrow> s <: ?P \<Longrightarrow> t <: ?P"
    proof(induction "WHILE b DO c" s t rule: big_step_induct)
      case WhileFalse thus ?case by simp
    next
      case WhileTrue thus ?case by(metis While.IH pfp fun_in_rep_le)
    qed
  }
  with fun_in_rep_le[OF `s <: S0` above]
  show ?case by (metis While(2) AI.simps(5))
qed

end


text{* Problem: not executable because of the comparison of abstract states,
i.e. functions, in the post-fixedpoint computation. Need to implement
abstract states concretely. *}

end
