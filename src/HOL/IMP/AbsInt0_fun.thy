(* Author: Tobias Nipkow *)

header "Abstract Interpretation"

theory AbsInt0_fun
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

fun bpfp where
"bpfp f 0 _ = Top" |
"bpfp f (Suc n) x = (if f x \<sqsubseteq> x then x else bpfp f n (f x))"

definition "pfp f = bpfp f 3"

lemma postfixedpoint: "f(bpfp f n x) \<sqsubseteq> bpfp f n x"
apply (induct n arbitrary: x)
 apply (simp)
apply (simp)
done

lemma bpfp_funpow: "bpfp f n x \<noteq> Top \<Longrightarrow> EX k. bpfp f n x = (f^^k) x"
apply(induct n arbitrary: x)
apply simp
apply simp
apply (auto)
apply(rule_tac x=0 in exI)
apply simp
by (metis funpow.simps(2) funpow_swap1 o_apply)

lemma pfp_funpow: "pfp f x \<noteq> Top \<Longrightarrow> EX k. pfp f x = (f^^k) x"
by(simp add: pfp_def bpfp_funpow)

abbreviation (input) lift (infix "\<up>" 65) where "f\<up>x0 == (%x. x0 \<squnion> f x)"

definition "pfp_above f x0 = pfp (f\<up>x0) x0"

lemma pfp_above_pfp:
shows "f(pfp_above f x0) \<sqsubseteq> pfp_above f x0" and "x0 \<sqsubseteq> pfp_above f x0"
using postfixedpoint[of "lift f x0"]
by(auto simp add: pfp_above_def pfp_def)

lemma least_pfp:
assumes mono: "!!x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y" and "pfp_above f x0 \<noteq> Top"
and "f p \<sqsubseteq> p" and "x0 \<sqsubseteq> p" shows "pfp_above f x0 \<sqsubseteq> p"
proof-
  let ?F = "lift f x0"
  obtain k where "pfp_above f x0 = (?F^^k) x0"
    using pfp_funpow `pfp_above f x0 \<noteq> Top`
    by(fastsimp simp add: pfp_above_def)
  moreover
  { fix n have "(?F^^n) x0 \<sqsubseteq> p"
    proof(induct n)
      case 0 show ?case by(simp add: `x0 \<sqsubseteq> p`)
    next
      case (Suc n) thus ?case
        by (simp add: `x0 \<sqsubseteq> p`)(metis Suc assms(3) le_trans mono)
    qed
  } ultimately show ?thesis by simp
qed

lemma chain: assumes "!!x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
shows "((f\<up>x0)^^i) x0 \<sqsubseteq> ((f\<up>x0)^^(i+1)) x0"
apply(induct i)
 apply simp
apply simp
by (metis assms join_ge2 le_trans)

lemma pfp_almost_fp:
assumes mono: "!!x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y" and "pfp_above f x0 \<noteq> Top"
shows "pfp_above f x0 \<sqsubseteq> x0 \<squnion> f(pfp_above f x0)"
proof-
  let ?p = "pfp_above f x0"
  obtain k where 1: "?p = ((f\<up>x0)^^k) x0"
    using pfp_funpow `?p \<noteq> Top`
    by(fastsimp simp add: pfp_above_def)
  thus ?thesis using chain mono by simp
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
fixes num' :: "val \<Rightarrow> 'a"  ("num\<^isup>#")
and plus' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("plus\<^isup>#")
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

text{* Abstract interpretation over abstract values.
Abstract states are simply functions. *}

locale Abs_Int_Fun = Val_abs
begin

fun aval' :: "aexp \<Rightarrow> (name \<Rightarrow> 'a) \<Rightarrow> 'a" ("aval\<^isup>#") where
"aval' (N n) _ = num' n" |
"aval' (V x) S = S x" |
"aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

abbreviation fun_in_rep (infix "<:" 50) where
"f <: F == ALL x. f x <: F x"

lemma fun_in_rep_le: "(s::state) <: S \<Longrightarrow> S \<sqsubseteq> T \<Longrightarrow> s <: T"
by (metis le_fun_def le_rep subsetD)

lemma aval'_sound: "s <: S \<Longrightarrow> aval a s <: aval' a S"
by (induct a) (auto simp: rep_num' rep_plus')

fun AI :: "com \<Rightarrow> (name \<Rightarrow> 'a) \<Rightarrow> (name \<Rightarrow> 'a)" where
"AI SKIP S = S" |
"AI (x ::= a) S = S(x := aval' a S)" |
"AI (c1;c2) S = AI c2 (AI c1 S)" |
"AI (IF b THEN c1 ELSE c2) S = (AI c1 S) \<squnion> (AI c2 S)" |
"AI (WHILE b DO c) S = pfp_above (AI c) S"

lemma AI_sound: "(c,s) \<Rightarrow> t \<Longrightarrow> s <: S0 \<Longrightarrow> t <: AI c S0"
proof(induct c arbitrary: s t S0)
  case SKIP thus ?case by fastsimp
next
  case Assign thus ?case by (auto simp: aval'_sound)
next
  case Semi thus ?case by auto
next
  case If thus ?case by(auto simp: in_rep_join)
next
  case (While b c)
  let ?P = "pfp_above (AI c) S0"
  have pfp: "AI c ?P \<sqsubseteq> ?P" and "S0 \<sqsubseteq> ?P"
    by(simp_all add: SL_top_class.pfp_above_pfp)
  { fix s t have "(WHILE b DO c,s) \<Rightarrow> t \<Longrightarrow> s <: ?P \<Longrightarrow> t <: ?P"
    proof(induct "WHILE b DO c" s t rule: big_step_induct)
      case WhileFalse thus ?case by simp
    next
      case WhileTrue thus ?case using While.hyps pfp fun_in_rep_le by metis
    qed
  }
  with fun_in_rep_le[OF `s <: S0` `S0 \<sqsubseteq> ?P`]
  show ?case by (metis While(2) AI.simps(5))
qed

end


text{* Problem: not executable because of the comparison of abstract states,
i.e. functions, in the post-fixedpoint computation. Need to implement
abstract states concretely. *}


(* Exercises: show that <= is a preorder if
1. v1 <= v2  =  rep v1 <= rep v2
2. v1 <= v2  =  ALL x. lookup v1 x <= lookup v2 x
*)

end
