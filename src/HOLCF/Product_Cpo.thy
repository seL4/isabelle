(*  Title:      HOLCF/Product_Cpo.thy
    Author:     Franz Regensburger
*)

header {* The cpo of cartesian products *}

theory Product_Cpo
imports Adm
begin

defaultsort cpo

subsection {* Type @{typ unit} is a pcpo *}

instantiation unit :: sq_ord
begin

definition
  less_unit_def [simp]: "x \<sqsubseteq> (y::unit) \<equiv> True"

instance ..
end

instance unit :: discrete_cpo
by intro_classes simp

instance unit :: finite_po ..

instance unit :: pcpo
by intro_classes simp


subsection {* Product type is a partial order *}

instantiation "*" :: (sq_ord, sq_ord) sq_ord
begin

definition
  less_cprod_def: "(op \<sqsubseteq>) \<equiv> \<lambda>p1 p2. (fst p1 \<sqsubseteq> fst p2 \<and> snd p1 \<sqsubseteq> snd p2)"

instance ..
end

instance "*" :: (po, po) po
proof
  fix x :: "'a \<times> 'b"
  show "x \<sqsubseteq> x"
    unfolding less_cprod_def by simp
next
  fix x y :: "'a \<times> 'b"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> x" thus "x = y"
    unfolding less_cprod_def Pair_fst_snd_eq
    by (fast intro: antisym_less)
next
  fix x y z :: "'a \<times> 'b"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> z" thus "x \<sqsubseteq> z"
    unfolding less_cprod_def
    by (fast intro: trans_less)
qed

subsection {* Monotonicity of @{text "(_,_)"}, @{term fst}, @{term snd} *}

lemma prod_lessI: "\<lbrakk>fst p \<sqsubseteq> fst q; snd p \<sqsubseteq> snd q\<rbrakk> \<Longrightarrow> p \<sqsubseteq> q"
unfolding less_cprod_def by simp

lemma Pair_less_iff [simp]: "(a, b) \<sqsubseteq> (c, d) \<longleftrightarrow> a \<sqsubseteq> c \<and> b \<sqsubseteq> d"
unfolding less_cprod_def by simp

text {* Pair @{text "(_,_)"}  is monotone in both arguments *}

lemma monofun_pair1: "monofun (\<lambda>x. (x, y))"
by (simp add: monofun_def)

lemma monofun_pair2: "monofun (\<lambda>y. (x, y))"
by (simp add: monofun_def)

lemma monofun_pair:
  "\<lbrakk>x1 \<sqsubseteq> x2; y1 \<sqsubseteq> y2\<rbrakk> \<Longrightarrow> (x1, y1) \<sqsubseteq> (x2, y2)"
by simp

text {* @{term fst} and @{term snd} are monotone *}

lemma monofun_fst: "monofun fst"
by (simp add: monofun_def less_cprod_def)

lemma monofun_snd: "monofun snd"
by (simp add: monofun_def less_cprod_def)

subsection {* Product type is a cpo *}

lemma is_lub_Pair:
  "\<lbrakk>range X <<| x; range Y <<| y\<rbrakk> \<Longrightarrow> range (\<lambda>i. (X i, Y i)) <<| (x, y)"
apply (rule is_lubI [OF ub_rangeI])
apply (simp add: less_cprod_def is_ub_lub)
apply (frule ub2ub_monofun [OF monofun_fst])
apply (drule ub2ub_monofun [OF monofun_snd])
apply (simp add: less_cprod_def is_lub_lub)
done

lemma lub_cprod:
  fixes S :: "nat \<Rightarrow> ('a::cpo \<times> 'b::cpo)"
  assumes S: "chain S"
  shows "range S <<| (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
proof -
  have "chain (\<lambda>i. fst (S i))"
    using monofun_fst S by (rule ch2ch_monofun)
  hence 1: "range (\<lambda>i. fst (S i)) <<| (\<Squnion>i. fst (S i))"
    by (rule cpo_lubI)
  have "chain (\<lambda>i. snd (S i))"
    using monofun_snd S by (rule ch2ch_monofun)
  hence 2: "range (\<lambda>i. snd (S i)) <<| (\<Squnion>i. snd (S i))"
    by (rule cpo_lubI)
  show "range S <<| (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
    using is_lub_Pair [OF 1 2] by simp
qed

lemma thelub_cprod:
  "chain (S::nat \<Rightarrow> 'a::cpo \<times> 'b::cpo)
    \<Longrightarrow> (\<Squnion>i. S i) = (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
by (rule lub_cprod [THEN thelubI])

instance "*" :: (cpo, cpo) cpo
proof
  fix S :: "nat \<Rightarrow> ('a \<times> 'b)"
  assume "chain S"
  hence "range S <<| (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
    by (rule lub_cprod)
  thus "\<exists>x. range S <<| x" ..
qed

instance "*" :: (finite_po, finite_po) finite_po ..

instance "*" :: (discrete_cpo, discrete_cpo) discrete_cpo
proof
  fix x y :: "'a \<times> 'b"
  show "x \<sqsubseteq> y \<longleftrightarrow> x = y"
    unfolding less_cprod_def Pair_fst_snd_eq
    by simp
qed

subsection {* Product type is pointed *}

lemma minimal_cprod: "(\<bottom>, \<bottom>) \<sqsubseteq> p"
by (simp add: less_cprod_def)

instance "*" :: (pcpo, pcpo) pcpo
by intro_classes (fast intro: minimal_cprod)

lemma inst_cprod_pcpo: "\<bottom> = (\<bottom>, \<bottom>)"
by (rule minimal_cprod [THEN UU_I, symmetric])

lemma Pair_defined_iff [simp]: "(x, y) = \<bottom> \<longleftrightarrow> x = \<bottom> \<and> y = \<bottom>"
unfolding inst_cprod_pcpo by simp

lemma fst_strict [simp]: "fst \<bottom> = \<bottom>"
unfolding inst_cprod_pcpo by (rule fst_conv)

lemma csnd_strict [simp]: "snd \<bottom> = \<bottom>"
unfolding inst_cprod_pcpo by (rule snd_conv)

lemma Pair_strict [simp]: "(\<bottom>, \<bottom>) = \<bottom>"
by simp

lemma split_strict [simp]: "split f \<bottom> = f \<bottom> \<bottom>"
unfolding split_def by simp

subsection {* Continuity of @{text "(_,_)"}, @{term fst}, @{term snd} *}

lemma cont_pair1: "cont (\<lambda>x. (x, y))"
apply (rule contI)
apply (rule is_lub_Pair)
apply (erule cpo_lubI)
apply (rule lub_const)
done

lemma cont_pair2: "cont (\<lambda>y. (x, y))"
apply (rule contI)
apply (rule is_lub_Pair)
apply (rule lub_const)
apply (erule cpo_lubI)
done

lemma contlub_fst: "contlub fst"
apply (rule contlubI)
apply (simp add: thelub_cprod)
done

lemma contlub_snd: "contlub snd"
apply (rule contlubI)
apply (simp add: thelub_cprod)
done

lemma cont_fst: "cont fst"
apply (rule monocontlub2cont)
apply (rule monofun_fst)
apply (rule contlub_fst)
done

lemma cont_snd: "cont snd"
apply (rule monocontlub2cont)
apply (rule monofun_snd)
apply (rule contlub_snd)
done

lemma cont2cont_Pair [cont2cont]:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. (f x, g x))"
apply (rule cont_apply [OF f cont_pair1])
apply (rule cont_apply [OF g cont_pair2])
apply (rule cont_const)
done

lemmas cont2cont_fst [cont2cont] = cont_compose [OF cont_fst]

lemmas cont2cont_snd [cont2cont] = cont_compose [OF cont_snd]

lemma cont2cont_split:
  assumes f1: "\<And>a b. cont (\<lambda>x. f x a b)"
  assumes f2: "\<And>x b. cont (\<lambda>a. f x a b)"
  assumes f3: "\<And>x a. cont (\<lambda>b. f x a b)"
  assumes g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. split (\<lambda>a b. f x a b) (g x))"
unfolding split_def
apply (rule cont_apply [OF g])
apply (rule cont_apply [OF cont_fst f2])
apply (rule cont_apply [OF cont_snd f3])
apply (rule cont_const)
apply (rule f1)
done

lemma cont_fst_snd_D1:
  "cont (\<lambda>p. f (fst p) (snd p)) \<Longrightarrow> cont (\<lambda>x. f x y)"
by (drule cont_compose [OF _ cont_pair1], simp)

lemma cont_fst_snd_D2:
  "cont (\<lambda>p. f (fst p) (snd p)) \<Longrightarrow> cont (\<lambda>y. f x y)"
by (drule cont_compose [OF _ cont_pair2], simp)

lemma cont2cont_split' [cont2cont]:
  assumes f: "cont (\<lambda>p. f (fst p) (fst (snd p)) (snd (snd p)))"
  assumes g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. split (f x) (g x))"
proof -
  note f1 = f [THEN cont_fst_snd_D1]
  note f2 = f [THEN cont_fst_snd_D2, THEN cont_fst_snd_D1]
  note f3 = f [THEN cont_fst_snd_D2, THEN cont_fst_snd_D2]
  show ?thesis
    unfolding split_def
    apply (rule cont_apply [OF g])
    apply (rule cont_apply [OF cont_fst f2])
    apply (rule cont_apply [OF cont_snd f3])
    apply (rule cont_const)
    apply (rule f1)
    done
qed

subsection {* Compactness and chain-finiteness *}

lemma fst_less_iff: "fst (x::'a \<times> 'b) \<sqsubseteq> y \<longleftrightarrow> x \<sqsubseteq> (y, snd x)"
unfolding less_cprod_def by simp

lemma snd_less_iff: "snd (x::'a \<times> 'b) \<sqsubseteq> y = x \<sqsubseteq> (fst x, y)"
unfolding less_cprod_def by simp

lemma compact_fst: "compact x \<Longrightarrow> compact (fst x)"
by (rule compactI, simp add: fst_less_iff)

lemma compact_snd: "compact x \<Longrightarrow> compact (snd x)"
by (rule compactI, simp add: snd_less_iff)

lemma compact_Pair: "\<lbrakk>compact x; compact y\<rbrakk> \<Longrightarrow> compact (x, y)"
by (rule compactI, simp add: less_cprod_def)

lemma compact_Pair_iff [simp]: "compact (x, y) \<longleftrightarrow> compact x \<and> compact y"
apply (safe intro!: compact_Pair)
apply (drule compact_fst, simp)
apply (drule compact_snd, simp)
done

instance "*" :: (chfin, chfin) chfin
apply intro_classes
apply (erule compact_imp_max_in_chain)
apply (case_tac "\<Squnion>i. Y i", simp)
done

end
