(* Author: Tobias Nipkow *)

theory Abs_Int0
imports Abs_State
begin

subsection "Computable Abstract Interpretation"

text{* Abstract interpretation over type @{text astate} instead of
functions. *}

locale Abs_Int = Val_abs +
fixes pfp :: "('a st up acom \<Rightarrow> 'a st up acom) \<Rightarrow> 'a st up acom \<Rightarrow> 'a st up acom"
assumes pfp: "\<forall>c. strip(f c) = strip c \<Longrightarrow> f(pfp f c) \<sqsubseteq> pfp f c"
and strip_pfp: "\<forall>c. strip(f c) = strip c \<Longrightarrow> strip(pfp f c) = strip c"
begin

fun aval' :: "aexp \<Rightarrow> 'a st \<Rightarrow> 'a" where
"aval' (N n) _ = num' n" |
"aval' (V x) S = lookup S x" |
"aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

fun step :: "'a st up \<Rightarrow> 'a st up acom \<Rightarrow> 'a st up acom" where
"step S (SKIP {P}) = (SKIP {S})" |
"step S (x ::= e {P}) =
  x ::= e {case S of Bot \<Rightarrow> Bot | Up S \<Rightarrow> Up(update S x (aval' e S))}" |
"step S (c1; c2) = step S c1; step (post c1) c2" |
"step S (IF b THEN c1 ELSE c2 {P}) =
  (let c1' = step S c1; c2' = step S c2
   in IF b THEN c1' ELSE c2' {post c1 \<squnion> post c2})" |
"step S ({Inv} WHILE b DO c {P}) =
   {S \<squnion> post c} WHILE b DO step Inv c {Inv}"

lemma strip_step[simp]: "strip(step S c) = strip c"
by(induct c arbitrary: S) (simp_all add: Let_def)

definition AI :: "com \<Rightarrow> 'a st up acom" where
"AI c = pfp (step Top) (bot_acom c)"


subsubsection "Monotonicity"

lemma mono_aval': "S \<sqsubseteq> S' \<Longrightarrow> aval' e S \<sqsubseteq> aval' e S'"
by(induction e) (auto simp: le_st_def lookup_def mono_plus')

lemma mono_update: "a \<sqsubseteq> a' \<Longrightarrow> S \<sqsubseteq> S' \<Longrightarrow> update S x a \<sqsubseteq> update S' x a'"
by(auto simp add: le_st_def lookup_def update_def)

lemma step_mono: "S \<sqsubseteq> S' \<Longrightarrow> step S c \<sqsubseteq> step S' c"
apply(induction c arbitrary: S S')
apply (auto simp: Let_def mono_update mono_aval' le_join_disj split: up.split)
done

subsubsection "Soundness"

lemma aval'_sound: "s <:f S \<Longrightarrow> aval a s <: aval' a S"
by (induct a) (auto simp: rep_num' rep_plus' rep_st_def lookup_def)

lemma in_rep_update: "\<lbrakk> s <:f S; i <: a \<rbrakk> \<Longrightarrow> s(x := i) <:f update S x a"
by(simp add: rep_st_def lookup_update)

lemma step_sound:
  "step S c \<sqsubseteq> c \<Longrightarrow> (strip c,s) \<Rightarrow> t \<Longrightarrow> s <:up S \<Longrightarrow> t <:up post c"
proof(induction c arbitrary: S s t)
  case SKIP thus ?case
    by simp (metis skipE up_fun_in_rep_le)
next
  case Assign thus ?case
    apply (auto simp del: fun_upd_apply simp: split: up.splits)
    by (metis aval'_sound fun_in_rep_le in_rep_update)
next
  case Semi thus ?case by simp blast
next
  case (If b c1 c2 S0) thus ?case
    apply(auto simp: Let_def)
    apply (metis up_fun_in_rep_le)+
    done
next
  case (While Inv b c P)
  from While.prems have inv: "step Inv c \<sqsubseteq> c"
    and "post c \<sqsubseteq> Inv" and "S \<sqsubseteq> Inv" and "Inv \<sqsubseteq> P" by(auto simp: Let_def)
  { fix s t have "(WHILE b DO strip c,s) \<Rightarrow> t \<Longrightarrow> s <:up Inv \<Longrightarrow> t <:up Inv"
    proof(induction "WHILE b DO strip c" s t rule: big_step_induct)
      case WhileFalse thus ?case by simp
    next
      case (WhileTrue s1 s2 s3)
      from WhileTrue.hyps(5)[OF up_fun_in_rep_le[OF While.IH[OF inv `(strip c, s1) \<Rightarrow> s2` `s1 <:up Inv`] `post c \<sqsubseteq> Inv`]]
      show ?case .
    qed
  }
  thus ?case using While.prems(2)
    by simp (metis `s <:up S` `S \<sqsubseteq> Inv` `Inv \<sqsubseteq> P` up_fun_in_rep_le)
qed

lemma AI_sound: "(c,s) \<Rightarrow> t \<Longrightarrow> t <:up post(AI c)"
by(fastforce simp: AI_def strip_pfp in_rep_Top_up intro: step_sound pfp)

end


end
