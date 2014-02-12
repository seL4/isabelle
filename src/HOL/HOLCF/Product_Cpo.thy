(*  Title:      HOL/HOLCF/Product_Cpo.thy
    Author:     Franz Regensburger
*)

header {* The cpo of cartesian products *}

theory Product_Cpo
imports Adm
begin

default_sort cpo

subsection {* Unit type is a pcpo *}

instantiation unit :: discrete_cpo
begin

definition
  below_unit_def [simp]: "x \<sqsubseteq> (y::unit) \<longleftrightarrow> True"

instance proof
qed simp

end

instance unit :: pcpo
by intro_classes simp


subsection {* Product type is a partial order *}

instantiation prod :: (below, below) below
begin

definition
  below_prod_def: "(op \<sqsubseteq>) \<equiv> \<lambda>p1 p2. (fst p1 \<sqsubseteq> fst p2 \<and> snd p1 \<sqsubseteq> snd p2)"

instance ..
end

instance prod :: (po, po) po
proof
  fix x :: "'a \<times> 'b"
  show "x \<sqsubseteq> x"
    unfolding below_prod_def by simp
next
  fix x y :: "'a \<times> 'b"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> x" thus "x = y"
    unfolding below_prod_def prod_eq_iff
    by (fast intro: below_antisym)
next
  fix x y z :: "'a \<times> 'b"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> z" thus "x \<sqsubseteq> z"
    unfolding below_prod_def
    by (fast intro: below_trans)
qed

subsection {* Monotonicity of \emph{Pair}, \emph{fst}, \emph{snd} *}

lemma prod_belowI: "\<lbrakk>fst p \<sqsubseteq> fst q; snd p \<sqsubseteq> snd q\<rbrakk> \<Longrightarrow> p \<sqsubseteq> q"
unfolding below_prod_def by simp

lemma Pair_below_iff [simp]: "(a, b) \<sqsubseteq> (c, d) \<longleftrightarrow> a \<sqsubseteq> c \<and> b \<sqsubseteq> d"
unfolding below_prod_def by simp

text {* Pair @{text "(_,_)"}  is monotone in both arguments *}

lemma monofun_pair1: "monofun (\<lambda>x. (x, y))"
by (simp add: monofun_def)

lemma monofun_pair2: "monofun (\<lambda>y. (x, y))"
by (simp add: monofun_def)

lemma monofun_pair:
  "\<lbrakk>x1 \<sqsubseteq> x2; y1 \<sqsubseteq> y2\<rbrakk> \<Longrightarrow> (x1, y1) \<sqsubseteq> (x2, y2)"
by simp

lemma ch2ch_Pair [simp]:
  "chain X \<Longrightarrow> chain Y \<Longrightarrow> chain (\<lambda>i. (X i, Y i))"
by (rule chainI, simp add: chainE)

text {* @{term fst} and @{term snd} are monotone *}

lemma fst_monofun: "x \<sqsubseteq> y \<Longrightarrow> fst x \<sqsubseteq> fst y"
unfolding below_prod_def by simp

lemma snd_monofun: "x \<sqsubseteq> y \<Longrightarrow> snd x \<sqsubseteq> snd y"
unfolding below_prod_def by simp

lemma monofun_fst: "monofun fst"
by (simp add: monofun_def below_prod_def)

lemma monofun_snd: "monofun snd"
by (simp add: monofun_def below_prod_def)

lemmas ch2ch_fst [simp] = ch2ch_monofun [OF monofun_fst]

lemmas ch2ch_snd [simp] = ch2ch_monofun [OF monofun_snd]

lemma prod_chain_cases:
  assumes "chain Y"
  obtains A B
  where "chain A" and "chain B" and "Y = (\<lambda>i. (A i, B i))"
proof
  from `chain Y` show "chain (\<lambda>i. fst (Y i))" by (rule ch2ch_fst)
  from `chain Y` show "chain (\<lambda>i. snd (Y i))" by (rule ch2ch_snd)
  show "Y = (\<lambda>i. (fst (Y i), snd (Y i)))" by simp
qed

subsection {* Product type is a cpo *}

lemma is_lub_Pair:
  "\<lbrakk>range A <<| x; range B <<| y\<rbrakk> \<Longrightarrow> range (\<lambda>i. (A i, B i)) <<| (x, y)"
unfolding is_lub_def is_ub_def ball_simps below_prod_def by simp

lemma lub_Pair:
  "\<lbrakk>chain (A::nat \<Rightarrow> 'a::cpo); chain (B::nat \<Rightarrow> 'b::cpo)\<rbrakk>
    \<Longrightarrow> (\<Squnion>i. (A i, B i)) = (\<Squnion>i. A i, \<Squnion>i. B i)"
by (fast intro: lub_eqI is_lub_Pair elim: thelubE)

lemma is_lub_prod:
  fixes S :: "nat \<Rightarrow> ('a::cpo \<times> 'b::cpo)"
  assumes S: "chain S"
  shows "range S <<| (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
using S by (auto elim: prod_chain_cases simp add: is_lub_Pair cpo_lubI)

lemma lub_prod:
  "chain (S::nat \<Rightarrow> 'a::cpo \<times> 'b::cpo)
    \<Longrightarrow> (\<Squnion>i. S i) = (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
by (rule is_lub_prod [THEN lub_eqI])

instance prod :: (cpo, cpo) cpo
proof
  fix S :: "nat \<Rightarrow> ('a \<times> 'b)"
  assume "chain S"
  hence "range S <<| (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
    by (rule is_lub_prod)
  thus "\<exists>x. range S <<| x" ..
qed

instance prod :: (discrete_cpo, discrete_cpo) discrete_cpo
proof
  fix x y :: "'a \<times> 'b"
  show "x \<sqsubseteq> y \<longleftrightarrow> x = y"
    unfolding below_prod_def prod_eq_iff
    by simp
qed

subsection {* Product type is pointed *}

lemma minimal_prod: "(\<bottom>, \<bottom>) \<sqsubseteq> p"
by (simp add: below_prod_def)

instance prod :: (pcpo, pcpo) pcpo
by intro_classes (fast intro: minimal_prod)

lemma inst_prod_pcpo: "\<bottom> = (\<bottom>, \<bottom>)"
by (rule minimal_prod [THEN bottomI, symmetric])

lemma Pair_bottom_iff [simp]: "(x, y) = \<bottom> \<longleftrightarrow> x = \<bottom> \<and> y = \<bottom>"
unfolding inst_prod_pcpo by simp

lemma fst_strict [simp]: "fst \<bottom> = \<bottom>"
unfolding inst_prod_pcpo by (rule fst_conv)

lemma snd_strict [simp]: "snd \<bottom> = \<bottom>"
unfolding inst_prod_pcpo by (rule snd_conv)

lemma Pair_strict [simp]: "(\<bottom>, \<bottom>) = \<bottom>"
by simp

lemma split_strict [simp]: "split f \<bottom> = f \<bottom> \<bottom>"
unfolding split_def by simp

subsection {* Continuity of \emph{Pair}, \emph{fst}, \emph{snd} *}

lemma cont_pair1: "cont (\<lambda>x. (x, y))"
apply (rule contI)
apply (rule is_lub_Pair)
apply (erule cpo_lubI)
apply (rule is_lub_const)
done

lemma cont_pair2: "cont (\<lambda>y. (x, y))"
apply (rule contI)
apply (rule is_lub_Pair)
apply (rule is_lub_const)
apply (erule cpo_lubI)
done

lemma cont_fst: "cont fst"
apply (rule contI)
apply (simp add: lub_prod)
apply (erule cpo_lubI [OF ch2ch_fst])
done

lemma cont_snd: "cont snd"
apply (rule contI)
apply (simp add: lub_prod)
apply (erule cpo_lubI [OF ch2ch_snd])
done

lemma cont2cont_Pair [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. (f x, g x))"
apply (rule cont_apply [OF f cont_pair1])
apply (rule cont_apply [OF g cont_pair2])
apply (rule cont_const)
done

lemmas cont2cont_fst [simp, cont2cont] = cont_compose [OF cont_fst]

lemmas cont2cont_snd [simp, cont2cont] = cont_compose [OF cont_snd]

lemma cont2cont_case_prod:
  assumes f1: "\<And>a b. cont (\<lambda>x. f x a b)"
  assumes f2: "\<And>x b. cont (\<lambda>a. f x a b)"
  assumes f3: "\<And>x a. cont (\<lambda>b. f x a b)"
  assumes g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. case g x of (a, b) \<Rightarrow> f x a b)"
unfolding split_def
apply (rule cont_apply [OF g])
apply (rule cont_apply [OF cont_fst f2])
apply (rule cont_apply [OF cont_snd f3])
apply (rule cont_const)
apply (rule f1)
done

lemma prod_contI:
  assumes f1: "\<And>y. cont (\<lambda>x. f (x, y))"
  assumes f2: "\<And>x. cont (\<lambda>y. f (x, y))"
  shows "cont f"
proof -
  have "cont (\<lambda>(x, y). f (x, y))"
    by (intro cont2cont_case_prod f1 f2 cont2cont)
  thus "cont f"
    by (simp only: split_eta)
qed

lemma prod_cont_iff:
  "cont f \<longleftrightarrow> (\<forall>y. cont (\<lambda>x. f (x, y))) \<and> (\<forall>x. cont (\<lambda>y. f (x, y)))"
apply safe
apply (erule cont_compose [OF _ cont_pair1])
apply (erule cont_compose [OF _ cont_pair2])
apply (simp only: prod_contI)
done

lemma cont2cont_case_prod' [simp, cont2cont]:
  assumes f: "cont (\<lambda>p. f (fst p) (fst (snd p)) (snd (snd p)))"
  assumes g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. case_prod (f x) (g x))"
using assms by (simp add: cont2cont_case_prod prod_cont_iff)

text {* The simple version (due to Joachim Breitner) is needed if
  either element type of the pair is not a cpo. *}

lemma cont2cont_split_simple [simp, cont2cont]:
 assumes "\<And>a b. cont (\<lambda>x. f x a b)"
 shows "cont (\<lambda>x. case p of (a, b) \<Rightarrow> f x a b)"
using assms by (cases p) auto

text {* Admissibility of predicates on product types. *}

lemma adm_case_prod [simp]:
  assumes "adm (\<lambda>x. P x (fst (f x)) (snd (f x)))"
  shows "adm (\<lambda>x. case f x of (a, b) \<Rightarrow> P x a b)"
unfolding case_prod_beta using assms .

subsection {* Compactness and chain-finiteness *}

lemma fst_below_iff: "fst (x::'a \<times> 'b) \<sqsubseteq> y \<longleftrightarrow> x \<sqsubseteq> (y, snd x)"
unfolding below_prod_def by simp

lemma snd_below_iff: "snd (x::'a \<times> 'b) \<sqsubseteq> y \<longleftrightarrow> x \<sqsubseteq> (fst x, y)"
unfolding below_prod_def by simp

lemma compact_fst: "compact x \<Longrightarrow> compact (fst x)"
by (rule compactI, simp add: fst_below_iff)

lemma compact_snd: "compact x \<Longrightarrow> compact (snd x)"
by (rule compactI, simp add: snd_below_iff)

lemma compact_Pair: "\<lbrakk>compact x; compact y\<rbrakk> \<Longrightarrow> compact (x, y)"
by (rule compactI, simp add: below_prod_def)

lemma compact_Pair_iff [simp]: "compact (x, y) \<longleftrightarrow> compact x \<and> compact y"
apply (safe intro!: compact_Pair)
apply (drule compact_fst, simp)
apply (drule compact_snd, simp)
done

instance prod :: (chfin, chfin) chfin
apply intro_classes
apply (erule compact_imp_max_in_chain)
apply (case_tac "\<Squnion>i. Y i", simp)
done

end
