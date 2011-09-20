(* Author: Tobias Nipkow *)

theory AbsInt0
imports Astate
begin

subsection "Computable Abstract Interpretation"

text{* Abstract interpretation over type @{text astate} instead of
functions. *}

locale Abs_Int = Val_abs +
fixes pfp :: "('a astate \<Rightarrow> 'a astate) \<Rightarrow> 'a astate \<Rightarrow> 'a astate"
assumes pfp: "f(pfp f x0) \<sqsubseteq> pfp f x0"
assumes above: "x0 \<sqsubseteq> pfp f x0"
begin

fun aval' :: "aexp \<Rightarrow> 'a astate \<Rightarrow> 'a" where
"aval' (N n) _ = num' n" |
"aval' (V x) S = lookup S x" |
"aval' (Plus e1 e2) S = plus' (aval' e1 S) (aval' e2 S)"

abbreviation astate_in_rep (infix "<:" 50) where
"s <: S == ALL x. s x <: lookup S x"

lemma astate_in_rep_le: "(s::state) <: S \<Longrightarrow> S \<sqsubseteq> T \<Longrightarrow> s <: T"
by (metis in_mono le_astate_def le_rep lookup_def top)

lemma aval'_sound: "s <: S \<Longrightarrow> aval a s <: aval' a S"
by (induct a) (auto simp: rep_num' rep_plus')


fun AI :: "com \<Rightarrow> 'a astate \<Rightarrow> 'a astate" where
"AI SKIP S = S" |
"AI (x ::= a) S = update S x (aval' a S)" |
"AI (c1;c2) S = AI c2 (AI c1 S)" |
"AI (IF b THEN c1 ELSE c2) S = (AI c1 S) \<squnion> (AI c2 S)" |
"AI (WHILE b DO c) S = pfp (AI c) S"

lemma AI_sound: "(c,s) \<Rightarrow> t \<Longrightarrow> s <: S0 \<Longrightarrow> t <: AI c S0"
proof(induction c arbitrary: s t S0)
  case SKIP thus ?case by fastforce
next
  case Assign thus ?case
    by (auto simp: lookup_update aval'_sound)
next
  case Semi thus ?case by auto
next
  case If thus ?case
    by (metis AI.simps(4) IfE astate_in_rep_le join_ge1 join_ge2)
next
  case (While b c)
  let ?P = "pfp (AI c) S0"
  { fix s t have "(WHILE b DO c,s) \<Rightarrow> t \<Longrightarrow> s <: ?P \<Longrightarrow> t <: ?P"
    proof(induction "WHILE b DO c" s t rule: big_step_induct)
      case WhileFalse thus ?case by simp
    next
      case WhileTrue thus ?case using While.IH pfp astate_in_rep_le by metis
    qed
  }
  with astate_in_rep_le[OF `s <: S0` above]
  show ?case by (metis While(2) AI.simps(5))
qed

end

end
