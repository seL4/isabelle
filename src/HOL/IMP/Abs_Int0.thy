(* Author: Tobias Nipkow *)

theory Abs_Int0
imports Abs_State
begin

subsection "Computable Abstract Interpretation"

text{* Abstract interpretation over type @{text st} instead of
functions. *}

context Val_abs
begin

fun aval' :: "aexp \<Rightarrow> 'a st \<Rightarrow> 'a" where
"aval' (N n) _ = num' n" |
"aval' (V x) S = lookup S x" |
"aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

lemma aval'_sound: "s : \<gamma>\<^isub>f S \<Longrightarrow> aval a s : \<gamma>(aval' a S)"
by (induct a) (auto simp: rep_num' rep_plus' rep_st_def lookup_def)

end

locale Abs_Int = Val_abs
begin

fun step :: "'a st option \<Rightarrow> 'a st option acom \<Rightarrow> 'a st option acom" where
"step S (SKIP {P}) = (SKIP {S})" |
"step S (x ::= e {P}) =
  x ::= e {case S of None \<Rightarrow> None | Some S \<Rightarrow> Some(update S x (aval' e S))}" |
"step S (c1; c2) = step S c1; step (post c1) c2" |
"step S (IF b THEN c1 ELSE c2 {P}) =
  (let c1' = step S c1; c2' = step S c2
   in IF b THEN c1' ELSE c2' {post c1 \<squnion> post c2})" |
"step S ({Inv} WHILE b DO c {P}) =
   {S \<squnion> post c} WHILE b DO step Inv c {Inv}"

definition AI :: "com \<Rightarrow> 'a st option acom option" where
"AI = lpfp\<^isub>c (step \<top>)"


lemma strip_step[simp]: "strip(step S c) = strip c"
by(induct c arbitrary: S) (simp_all add: Let_def)


text{* Soundness: *}

lemma in_rep_update:
  "\<lbrakk> s : \<gamma>\<^isub>f S; i : \<gamma> a \<rbrakk> \<Longrightarrow> s(x := i) : \<gamma>\<^isub>f(update S x a)"
by(simp add: rep_st_def lookup_update)

text{* The soundness proofs are textually identical to the ones for the step
function operating on states as functions. *}

lemma step_preserves_le2:
  "\<lbrakk> S \<subseteq> \<gamma>\<^isub>u sa; cs \<le> \<gamma>\<^isub>c ca; strip cs = c; strip ca = c \<rbrakk>
   \<Longrightarrow> step_cs S cs \<le> \<gamma>\<^isub>c (step sa ca)"
proof(induction c arbitrary: cs ca S sa)
  case SKIP thus ?case
    by(auto simp:strip_eq_SKIP)
next
  case Assign thus ?case
    by (fastforce simp: strip_eq_Assign intro: aval'_sound in_rep_update
      split: option.splits del:subsetD)
next
  case Semi thus ?case apply (auto simp: strip_eq_Semi)
    by (metis le_post post_map_acom)
next
  case (If b c1 c2)
  then obtain cs1 cs2 ca1 ca2 P Pa where
      "cs = IF b THEN cs1 ELSE cs2 {P}" "ca = IF b THEN ca1 ELSE ca2 {Pa}"
      "P \<subseteq> \<gamma>\<^isub>u Pa" "cs1 \<le> \<gamma>\<^isub>c ca1" "cs2 \<le> \<gamma>\<^isub>c ca2"
      "strip cs1 = c1" "strip ca1 = c1" "strip cs2 = c2" "strip ca2 = c2"
    by (fastforce simp: strip_eq_If)
  moreover have "post cs1 \<subseteq> \<gamma>\<^isub>u(post ca1 \<squnion> post ca2)"
    by (metis (no_types) `cs1 \<le> \<gamma>\<^isub>c ca1` join_ge1 le_post mono_rep_u order_trans post_map_acom)
  moreover have "post cs2 \<subseteq> \<gamma>\<^isub>u(post ca1 \<squnion> post ca2)"
    by (metis (no_types) `cs2 \<le> \<gamma>\<^isub>c ca2` join_ge2 le_post mono_rep_u order_trans post_map_acom)
  ultimately show ?case using If.prems(1) by (simp add: If.IH subset_iff)
next
  case (While b c1)
  then obtain cs1 ca1 I P Ia Pa where
    "cs = {I} WHILE b DO cs1 {P}" "ca = {Ia} WHILE b DO ca1 {Pa}"
    "I \<subseteq> \<gamma>\<^isub>u Ia" "P \<subseteq> \<gamma>\<^isub>u Pa" "cs1 \<le> \<gamma>\<^isub>c ca1"
    "strip cs1 = c1" "strip ca1 = c1"
    by (fastforce simp: strip_eq_While)
  moreover have "S \<union> post cs1 \<subseteq> \<gamma>\<^isub>u (sa \<squnion> post ca1)"
    using `S \<subseteq> \<gamma>\<^isub>u sa` le_post[OF `cs1 \<le> \<gamma>\<^isub>c ca1`, simplified]
    by (metis (no_types) join_ge1 join_ge2 le_sup_iff mono_rep_u order_trans)
  ultimately show ?case by (simp add: While.IH subset_iff)
qed

lemma step_preserves_le:
  "\<lbrakk> S \<subseteq> \<gamma>\<^isub>u sa; cs \<le> \<gamma>\<^isub>c ca; strip cs = c \<rbrakk>
   \<Longrightarrow> step_cs S cs \<le> \<gamma>\<^isub>c(step sa ca)"
by (metis le_strip step_preserves_le2 strip_acom)

lemma AI_sound: "AI c = Some c' \<Longrightarrow> CS UNIV c \<le> \<gamma>\<^isub>c c'"
proof(simp add: CS_def AI_def)
  assume 1: "lpfp\<^isub>c (step \<top>) c = Some c'"
  have 2: "step \<top> c' \<sqsubseteq> c'" by(rule lpfpc_pfp[OF 1])
  have 3: "strip (\<gamma>\<^isub>c (step \<top> c')) = c"
    by(simp add: strip_lpfpc[OF _ 1])
  have "lfp c (step_cs UNIV) \<le> \<gamma>\<^isub>c (step \<top> c')"
  proof(rule lfp_lowerbound[OF 3])
    show "step_cs UNIV (\<gamma>\<^isub>c (step \<top> c')) \<le> \<gamma>\<^isub>c (step \<top> c')"
    proof(rule step_preserves_le[OF _ _ 3])
      show "UNIV \<subseteq> \<gamma>\<^isub>u \<top>" by simp
      show "\<gamma>\<^isub>c (step \<top> c') \<le> \<gamma>\<^isub>c c'" by(rule mono_rep_c[OF 2])
    qed
  qed
  from this 2 show "lfp c (step_cs UNIV) \<le> \<gamma>\<^isub>c c'"
    by (blast intro: mono_rep_c order_trans)
qed

end


subsubsection "Monotonicity"

locale Abs_Int_mono = Abs_Int +
assumes mono_plus': "a1 \<sqsubseteq> b1 \<Longrightarrow> a2 \<sqsubseteq> b2 \<Longrightarrow> plus' a1 a2 \<sqsubseteq> plus' b1 b2"
begin

lemma mono_aval': "S \<sqsubseteq> S' \<Longrightarrow> aval' e S \<sqsubseteq> aval' e S'"
by(induction e) (auto simp: le_st_def lookup_def mono_plus')

lemma mono_update: "a \<sqsubseteq> a' \<Longrightarrow> S \<sqsubseteq> S' \<Longrightarrow> update S x a \<sqsubseteq> update S' x a'"
by(auto simp add: le_st_def lookup_def update_def)

lemma step_mono: "S \<sqsubseteq> S' \<Longrightarrow> step S c \<sqsubseteq> step S' c"
apply(induction c arbitrary: S S')
apply (auto simp: Let_def mono_update mono_aval' le_join_disj split: option.split)
done

end

end
