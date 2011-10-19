(* Author: Tobias Nipkow *)

theory Abs_Int1
imports Abs_Int0_const
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


locale Val_abs1_rep =
  Val_abs rep num' plus'
  for rep :: "'a::L_top_bot \<Rightarrow> val set" and num' plus' +
assumes inter_rep_subset_rep_meet:
  "rep a1 \<inter> rep a2 \<subseteq> rep(a1 \<sqinter> a2)"
and rep_Bot: "rep \<bottom> = {}"
begin

lemma in_rep_meet: "x <: a1 \<Longrightarrow> x <: a2 \<Longrightarrow> x <: a1 \<sqinter> a2"
by (metis IntI inter_rep_subset_rep_meet set_mp)

lemma rep_meet[simp]: "rep(a1 \<sqinter> a2) = rep a1 \<inter> rep a2"
by (metis equalityI inter_rep_subset_rep_meet le_inf_iff le_rep meet_le1 meet_le2)

end


locale Val_abs1 = Val_abs1_rep +
fixes filter_plus' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a * 'a"
and filter_less' :: "bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a * 'a"
assumes filter_plus': "filter_plus' a a1 a2 = (a1',a2') \<Longrightarrow>
  n1 <: a1 \<Longrightarrow> n2 <: a2 \<Longrightarrow> n1+n2 <: a \<Longrightarrow> n1 <: a1' \<and> n2 <: a2'"
and filter_less': "filter_less' (n1<n2) a1 a2 = (a1',a2') \<Longrightarrow>
  n1 <: a1 \<Longrightarrow> n2 <: a2 \<Longrightarrow> n1 <: a1' \<and> n2 <: a2'"


locale Abs_Int1 = Val_abs1
begin

lemma in_rep_join_UpI: "s <:up S1 | s <:up S2 \<Longrightarrow> s <:up S1 \<squnion> S2"
by (metis join_ge1 join_ge2 up_fun_in_rep_le)

fun aval' :: "aexp \<Rightarrow> 'a st up \<Rightarrow> 'a" where
"aval' _ Bot = \<bottom>" |
"aval' (N n) _ = num' n" |
"aval' (V x) (Up S) = lookup S x" |
"aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

lemma aval'_sound: "s <:up S \<Longrightarrow> aval a s <: aval' a S"
by(induct a)(auto simp: rep_num' rep_plus' in_rep_up_iff lookup_def rep_st_def)

subsubsection "Backward analysis"

fun afilter :: "aexp \<Rightarrow> 'a \<Rightarrow> 'a st up \<Rightarrow> 'a st up" where
"afilter (N n) a S = (if n <: a then S else Bot)" |
"afilter (V x) a S = (case S of Bot \<Rightarrow> Bot | Up S \<Rightarrow>
  let a' = lookup S x \<sqinter> a in
  if a' \<sqsubseteq> \<bottom> then Bot else Up(update S x a'))" |
"afilter (Plus e1 e2) a S =
 (let (a1,a2) = filter_plus' a (aval' e1 S) (aval' e2 S)
  in afilter e1 a1 (afilter e2 a2 S))"

text{* The test for @{const Bot} in the @{const V}-case is important: @{const
Bot} indicates that a variable has no possible values, i.e.\ that the current
program point is unreachable. But then the abstract state should collapse to
@{const bot}. Put differently, we maintain the invariant that in an abstract
state all variables are mapped to non-@{const Bot} values. Otherwise the
(pointwise) join of two abstract states, one of which contains @{const Bot}
values, may produce too large a result, thus making the analysis less
precise. *}


fun bfilter :: "bexp \<Rightarrow> bool \<Rightarrow> 'a st up \<Rightarrow> 'a st up" where
"bfilter (Bc v) res S = (if v=res then S else Bot)" |
"bfilter (Not b) res S = bfilter b (\<not> res) S" |
"bfilter (And b1 b2) res S =
  (if res then bfilter b1 True (bfilter b2 True S)
   else bfilter b1 False S \<squnion> bfilter b2 False S)" |
"bfilter (Less e1 e2) res S =
  (let (res1,res2) = filter_less' res (aval' e1 S) (aval' e2 S)
   in afilter e1 res1 (afilter e2 res2 S))"

lemma afilter_sound: "s <:up S \<Longrightarrow> aval e s <: a \<Longrightarrow> s <:up afilter e a S"
proof(induction e arbitrary: a S)
  case N thus ?case by simp
next
  case (V x)
  obtain S' where "S = Up S'" and "s <:f S'" using `s <:up S`
    by(auto simp: in_rep_up_iff)
  moreover hence "s x <: lookup S' x" by(simp add: rep_st_def)
  moreover have "s x <: a" using V by simp
  ultimately show ?case using V(1)
    by(simp add: lookup_update Let_def rep_st_def)
      (metis le_rep emptyE in_rep_meet rep_Bot subset_empty)
next
  case (Plus e1 e2) thus ?case
    using filter_plus'[OF _ aval'_sound[OF Plus(3)] aval'_sound[OF Plus(3)]]
    by (auto split: prod.split)
qed

lemma bfilter_sound: "s <:up S \<Longrightarrow> bv = bval b s \<Longrightarrow> s <:up bfilter b bv S"
proof(induction b arbitrary: S bv)
  case Bc thus ?case by simp
next
  case (Not b) thus ?case by simp
next
  case (And b1 b2) thus ?case by(fastforce simp: in_rep_join_UpI)
next
  case (Less e1 e2) thus ?case
    by (auto split: prod.split)
       (metis afilter_sound filter_less' aval'_sound Less)
qed


fun step :: "'a st up \<Rightarrow> 'a st up acom \<Rightarrow> 'a st up acom"
 where
"step S (SKIP {P}) = (SKIP {S})" |
"step S (x ::= e {P}) =
  x ::= e {case S of Bot \<Rightarrow> Bot
           | Up S \<Rightarrow> Up(update S x (aval' e (Up S)))}" |
"step S (c1; c2) = step S c1; step (post c1) c2" |
"step S (IF b THEN c1 ELSE c2 {P}) =
  (let c1' = step (bfilter b True S) c1; c2' = step (bfilter b False S) c2
   in IF b THEN c1' ELSE c2' {post c1 \<squnion> post c2})" |
"step S ({Inv} WHILE b DO c {P}) =
   {S \<squnion> post c}
   WHILE b DO step (bfilter b True Inv) c
   {bfilter b False Inv}"

definition AI :: "com \<Rightarrow> 'a st up acom option" where
"AI = lpfp\<^isub>c (step \<top>)"

lemma strip_step[simp]: "strip(step S c) = strip c"
by(induct c arbitrary: S) (simp_all add: Let_def)


subsubsection "Soundness"

lemma in_rep_update: "\<lbrakk> s <:f S; i <: a \<rbrakk> \<Longrightarrow> s(x := i) <:f update S x a"
by(simp add: rep_st_def lookup_update)

lemma While_final_False: "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> \<not> bval b t"
by(induct "WHILE b DO c" s t rule: big_step_induct) simp_all

lemma step_sound:
  "step S c \<sqsubseteq> c \<Longrightarrow> (strip c,s) \<Rightarrow> t \<Longrightarrow> s <:up S \<Longrightarrow> t <:up post c"
proof(induction c arbitrary: S s t)
  case SKIP thus ?case
    by simp (metis skipE up_fun_in_rep_le)
next
  case Assign thus ?case
    apply (auto simp del: fun_upd_apply split: up.splits)
    by (metis aval'_sound fun_in_rep_le in_rep_update rep_up.simps(2))
next
  case Semi thus ?case by simp blast
next
  case (If b c1 c2 S0)
  show ?case
  proof cases
    assume "bval b s"
    with If.prems have 1: "step (bfilter b True S) c1 \<sqsubseteq> c1"
      and 2: "(strip c1, s) \<Rightarrow> t" and 3: "post c1 \<sqsubseteq> S0" by(auto simp: Let_def)
    from If.IH(1)[OF 1 2 bfilter_sound[OF `s <:up S`]] `bval b s` 3
    show ?thesis by simp (metis up_fun_in_rep_le)
  next
    assume "\<not> bval b s"
    with If.prems have 1: "step (bfilter b False S) c2 \<sqsubseteq> c2"
      and 2: "(strip c2, s) \<Rightarrow> t" and 3: "post c2 \<sqsubseteq> S0" by(auto simp: Let_def)
    from If.IH(2)[OF 1 2 bfilter_sound[OF `s <:up S`]] `\<not> bval b s` 3
    show ?thesis by simp (metis up_fun_in_rep_le)
  qed
next
  case (While Inv b c P)
  from While.prems have inv: "step (bfilter b True Inv) c \<sqsubseteq> c"
    and "post c \<sqsubseteq> Inv" and "S \<sqsubseteq> Inv" and "bfilter b False Inv \<sqsubseteq> P"
    by(auto simp: Let_def)
  { fix s t have "(WHILE b DO strip c,s) \<Rightarrow> t \<Longrightarrow> s <:up Inv \<Longrightarrow> t <:up Inv"
    proof(induction "WHILE b DO strip c" s t rule: big_step_induct)
      case WhileFalse thus ?case by simp
    next
      case (WhileTrue s1 s2 s3)
      from WhileTrue.hyps(5)[OF up_fun_in_rep_le[OF While.IH[OF inv `(strip c, s1) \<Rightarrow> s2` bfilter_sound[OF `s1 <:up Inv`]] `post c \<sqsubseteq> Inv`]] `bval b s1`
      show ?case by simp
    qed
  } note Inv = this
  from  While.prems(2) have "(WHILE b DO strip c, s) \<Rightarrow> t" and "\<not> bval b t"
    by(auto dest: While_final_False)
  from Inv[OF this(1) up_fun_in_rep_le[OF `s <:up S` `S \<sqsubseteq> Inv`]]
  have "t <:up Inv" .
  from up_fun_in_rep_le[OF bfilter_sound[OF this]  `bfilter b False Inv \<sqsubseteq> P`]
  show ?case using `\<not> bval b t` by simp
qed

lemma AI_sound: "\<lbrakk> AI c = Some c';  (c,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> t <:up post c'"
unfolding AI_def
by (metis in_rep_Top_up lpfpc_pfp step_sound strip_lpfpc strip_step)
(*
by(metis step_sound[of "\<top>" c' s t] strip_lpfp strip_step
  lpfp_pfp mono_def mono_step[OF le_refl] in_rep_Top_up)
*)
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
apply(cases S)
 apply simp
apply(cases S')
 apply simp
apply simp
by(induction e) (auto simp: le_st_def lookup_def mono_plus')

lemma mono_afilter: "r \<sqsubseteq> r' \<Longrightarrow> S \<sqsubseteq> S' \<Longrightarrow> afilter e r S \<sqsubseteq> afilter e r' S'"
apply(induction e arbitrary: r r' S S')
apply(auto simp: Let_def split: up.splits prod.splits)
apply (metis le_rep subsetD)
apply(drule_tac x = "list" in mono_lookup)
apply (metis mono_meet le_trans)
apply (metis mono_meet mono_lookup mono_update le_trans)
apply(metis mono_aval' mono_filter_plus'[simplified le_prod_def] fst_conv snd_conv)
done

lemma mono_bfilter: "S \<sqsubseteq> S' \<Longrightarrow> bfilter b r S \<sqsubseteq> bfilter b r S'"
apply(induction b arbitrary: r S S')
apply(auto simp: le_trans[OF _ join_ge1] le_trans[OF _ join_ge2] split: prod.splits)
apply(metis mono_aval' mono_afilter mono_filter_less'[simplified le_prod_def] fst_conv snd_conv)
done


lemma post_le_post: "c \<sqsubseteq> c' \<Longrightarrow> post c \<sqsubseteq> post c'"
by (induction c c' rule: le_acom.induct) simp_all

lemma mono_step: "S \<sqsubseteq> S' \<Longrightarrow> c \<sqsubseteq> c' \<Longrightarrow> step S c \<sqsubseteq> step S' c'"
apply(induction c c' arbitrary: S S' rule: le_acom.induct)
apply (auto simp: post_le_post Let_def mono_bfilter mono_update mono_aval' le_join_disj
  split: up.split)
done

end

end
