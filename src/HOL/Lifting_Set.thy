(*  Title:      HOL/Lifting_Set.thy
    Author:     Brian Huffman and Ondrej Kuncar
*)

section \<open>Setup for Lifting/Transfer for the set type\<close>

theory Lifting_Set
imports Lifting
begin

subsection \<open>Relator and predicator properties\<close>

lemma rel_setD1: "\<lbrakk> rel_set R A B; x \<in> A \<rbrakk> \<Longrightarrow> \<exists>y \<in> B. R x y"
  and rel_setD2: "\<lbrakk> rel_set R A B; y \<in> B \<rbrakk> \<Longrightarrow> \<exists>x \<in> A. R x y"
  by (simp_all add: rel_set_def)

lemma rel_set_conversep [simp]: "rel_set A\<inverse>\<inverse> = (rel_set A)\<inverse>\<inverse>"
  unfolding rel_set_def by auto

lemma rel_set_eq [relator_eq]: "rel_set (=) = (=)"
  unfolding rel_set_def fun_eq_iff by auto

lemma rel_set_mono[relator_mono]:
  assumes "A \<le> B"
  shows "rel_set A \<le> rel_set B"
  using assms unfolding rel_set_def by blast

lemma rel_set_OO[relator_distr]: "rel_set R OO rel_set S = rel_set (R OO S)"
  apply (rule sym)
  apply (intro ext)
  subgoal for X Z
    apply (rule iffI)
    apply (rule relcomppI [where b="{y. (\<exists>x\<in>X. R x y) \<and> (\<exists>z\<in>Z. S y z)}"])
    apply (simp add: rel_set_def, fast)+
    done
  done

lemma Domainp_set[relator_domain]:
  "Domainp (rel_set T) = (\<lambda>A. Ball A (Domainp T))"
  unfolding rel_set_def Domainp_iff[abs_def]
  apply (intro ext)
  apply (rule iffI) 
  apply blast
  subgoal for A by (rule exI [where x="{y. \<exists>x\<in>A. T x y}"]) fast
  done

lemma left_total_rel_set[transfer_rule]: 
  "left_total A \<Longrightarrow> left_total (rel_set A)"
  unfolding left_total_def rel_set_def
  apply safe
  subgoal for X by (rule exI [where x="{y. \<exists>x\<in>X. A x y}"]) fast
  done

lemma left_unique_rel_set[transfer_rule]: 
  "left_unique A \<Longrightarrow> left_unique (rel_set A)"
  unfolding left_unique_def rel_set_def
  by fast

lemma right_total_rel_set [transfer_rule]:
  "right_total A \<Longrightarrow> right_total (rel_set A)"
  using left_total_rel_set[of "A\<inverse>\<inverse>"] by simp

lemma right_unique_rel_set [transfer_rule]:
  "right_unique A \<Longrightarrow> right_unique (rel_set A)"
  unfolding right_unique_def rel_set_def by fast

lemma bi_total_rel_set [transfer_rule]:
  "bi_total A \<Longrightarrow> bi_total (rel_set A)"
  by(simp add: bi_total_alt_def left_total_rel_set right_total_rel_set)

lemma bi_unique_rel_set [transfer_rule]:
  "bi_unique A \<Longrightarrow> bi_unique (rel_set A)"
  unfolding bi_unique_def rel_set_def by fast

lemma set_relator_eq_onp [relator_eq_onp]:
  "rel_set (eq_onp P) = eq_onp (\<lambda>A. Ball A P)"
  unfolding fun_eq_iff rel_set_def eq_onp_def Ball_def by fast

lemma bi_unique_rel_set_lemma:
  assumes "bi_unique R" and "rel_set R X Y"
  obtains f where "Y = image f X" and "inj_on f X" and "\<forall>x\<in>X. R x (f x)"
proof
  define f where "f x = (THE y. R x y)" for x
  { fix x assume "x \<in> X"
    with \<open>rel_set R X Y\<close> \<open>bi_unique R\<close> have "R x (f x)"
      by (simp add: bi_unique_def rel_set_def f_def) (metis theI)
    with assms \<open>x \<in> X\<close> 
    have  "R x (f x)" "\<forall>x'\<in>X. R x' (f x) \<longrightarrow> x = x'" "\<forall>y\<in>Y. R x y \<longrightarrow> y = f x" "f x \<in> Y"
      by (fastforce simp add: bi_unique_def rel_set_def)+ }
  note * = this
  moreover
  { fix y assume "y \<in> Y"
    with \<open>rel_set R X Y\<close> *(3) \<open>y \<in> Y\<close> have "\<exists>x\<in>X. y = f x"
      by (fastforce simp: rel_set_def) }
  ultimately show "\<forall>x\<in>X. R x (f x)" "Y = image f X" "inj_on f X"
    by (auto simp: inj_on_def image_iff)
qed

subsection \<open>Quotient theorem for the Lifting package\<close>

lemma Quotient_set[quot_map]:
  assumes "Quotient R Abs Rep T"
  shows "Quotient (rel_set R) (image Abs) (image Rep) (rel_set T)"
  using assms unfolding Quotient_alt_def4
  apply (simp add: rel_set_OO[symmetric])
  apply (simp add: rel_set_def)
  apply fast
  done


subsection \<open>Transfer rules for the Transfer package\<close>

subsubsection \<open>Unconditional transfer rules\<close>

context includes lifting_syntax
begin

lemma empty_transfer [transfer_rule]: "(rel_set A) {} {}"
  unfolding rel_set_def by simp

lemma insert_transfer [transfer_rule]:
  "(A ===> rel_set A ===> rel_set A) insert insert"
  unfolding rel_fun_def rel_set_def by auto

lemma union_transfer [transfer_rule]:
  "(rel_set A ===> rel_set A ===> rel_set A) union union"
  unfolding rel_fun_def rel_set_def by auto

lemma Union_transfer [transfer_rule]:
  "(rel_set (rel_set A) ===> rel_set A) Union Union"
  unfolding rel_fun_def rel_set_def by simp fast

lemma image_transfer [transfer_rule]:
  "((A ===> B) ===> rel_set A ===> rel_set B) image image"
  unfolding rel_fun_def rel_set_def by simp fast

lemma UNION_transfer [transfer_rule]: \<comment> \<open>TODO deletion candidate\<close>
  "(rel_set A ===> (A ===> rel_set B) ===> rel_set B) (\<lambda>A f. \<Union>(f ` A)) (\<lambda>A f. \<Union>(f ` A))"
  by transfer_prover

lemma Ball_transfer [transfer_rule]:
  "(rel_set A ===> (A ===> (=)) ===> (=)) Ball Ball"
  unfolding rel_set_def rel_fun_def by fast

lemma Bex_transfer [transfer_rule]:
  "(rel_set A ===> (A ===> (=)) ===> (=)) Bex Bex"
  unfolding rel_set_def rel_fun_def by fast

lemma Pow_transfer [transfer_rule]:
  "(rel_set A ===> rel_set (rel_set A)) Pow Pow"
  apply (rule rel_funI)
  apply (rule rel_setI)
  subgoal for X Y X'
    apply (rule rev_bexI [where x="{y\<in>Y. \<exists>x\<in>X'. A x y}"])
    apply clarsimp
    apply (simp add: rel_set_def)
    apply fast
    done
  subgoal for X Y Y'
    apply (rule rev_bexI [where x="{x\<in>X. \<exists>y\<in>Y'. A x y}"])
    apply clarsimp
    apply (simp add: rel_set_def)
    apply fast
    done
  done

lemma rel_set_transfer [transfer_rule]:
  "((A ===> B ===> (=)) ===> rel_set A ===> rel_set B ===> (=)) rel_set rel_set"
  unfolding rel_fun_def rel_set_def by fast

lemma bind_transfer [transfer_rule]:
  "(rel_set A ===> (A ===> rel_set B) ===> rel_set B) Set.bind Set.bind"
  unfolding bind_UNION [abs_def] by transfer_prover

lemma INF_parametric [transfer_rule]: \<comment> \<open>TODO deletion candidate\<close>
  "(rel_set A ===> (A ===> HOL.eq) ===> HOL.eq) (\<lambda>A f. Inf (f ` A)) (\<lambda>A f. Inf (f ` A))"
  by transfer_prover

lemma SUP_parametric [transfer_rule]: \<comment> \<open>TODO deletion candidate\<close>
  "(rel_set R ===> (R ===> HOL.eq) ===> HOL.eq) (\<lambda>A f. Sup (f ` A)) (\<lambda>A f. Sup (f ` A))"
  by transfer_prover


subsubsection \<open>Rules requiring bi-unique, bi-total or right-total relations\<close>

lemma member_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(A ===> rel_set A ===> (=)) (\<in>) (\<in>)"
  using assms unfolding rel_fun_def rel_set_def bi_unique_def by fast

lemma right_total_Collect_transfer[transfer_rule]:
  assumes "right_total A"
  shows "((A ===> (=)) ===> rel_set A) (\<lambda>P. Collect (\<lambda>x. P x \<and> Domainp A x)) Collect"
  using assms unfolding right_total_def rel_set_def rel_fun_def Domainp_iff by fast

lemma Collect_transfer [transfer_rule]:
  assumes "bi_total A"
  shows "((A ===> (=)) ===> rel_set A) Collect Collect"
  using assms unfolding rel_fun_def rel_set_def bi_total_def by fast

lemma inter_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(rel_set A ===> rel_set A ===> rel_set A) inter inter"
  using assms unfolding rel_fun_def rel_set_def bi_unique_def by fast

lemma Diff_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(rel_set A ===> rel_set A ===> rel_set A) (-) (-)"
  using assms unfolding rel_fun_def rel_set_def bi_unique_def
  unfolding Ball_def Bex_def Diff_eq
  by (safe, simp, metis, simp, metis)

lemma subset_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(rel_set A ===> rel_set A ===> (=)) (\<subseteq>) (\<subseteq>)"
  unfolding subset_eq [abs_def] by transfer_prover

context
  includes lifting_syntax
begin

lemma strict_subset_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(rel_set A ===> rel_set A ===> (=)) (\<subset>) (\<subset>)"
  unfolding subset_not_subset_eq by transfer_prover

end

declare right_total_UNIV_transfer[transfer_rule]

lemma UNIV_transfer [transfer_rule]:
  assumes "bi_total A"
  shows "(rel_set A) UNIV UNIV"
  using assms unfolding rel_set_def bi_total_def by simp

lemma right_total_Compl_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "right_total A"
  shows "(rel_set A ===> rel_set A) (\<lambda>S. uminus S \<inter> Collect (Domainp A)) uminus"
  unfolding Compl_eq [abs_def]
  by (subst Collect_conj_eq[symmetric]) transfer_prover

lemma Compl_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "bi_total A"
  shows "(rel_set A ===> rel_set A) uminus uminus"
  unfolding Compl_eq [abs_def] by transfer_prover

lemma right_total_Inter_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "right_total A"
  shows "(rel_set (rel_set A) ===> rel_set A) (\<lambda>S. \<Inter>S \<inter> Collect (Domainp A)) Inter"
  unfolding Inter_eq[abs_def]
  by (subst Collect_conj_eq[symmetric]) transfer_prover

lemma Inter_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "bi_total A"
  shows "(rel_set (rel_set A) ===> rel_set A) Inter Inter"
  unfolding Inter_eq [abs_def] by transfer_prover

lemma filter_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "((A ===> (=)) ===> rel_set A ===> rel_set A) Set.filter Set.filter"
  unfolding Set.filter_def[abs_def] rel_fun_def rel_set_def by blast

lemma finite_transfer [transfer_rule]:
  "bi_unique A \<Longrightarrow> (rel_set A ===> (=)) finite finite"
  by (rule rel_funI, erule (1) bi_unique_rel_set_lemma)
     (auto dest: finite_imageD)

lemma card_transfer [transfer_rule]:
  "bi_unique A \<Longrightarrow> (rel_set A ===> (=)) card card"
  by (rule rel_funI, erule (1) bi_unique_rel_set_lemma)
     (simp add: card_image)

context
  includes lifting_syntax
begin

lemma vimage_right_total_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique B" "right_total A"
  shows "((A ===> B) ===> rel_set B ===> rel_set A) (\<lambda>f X. f -` X \<inter> Collect (Domainp A)) vimage"
proof -
  let ?vimage = "(\<lambda>f B. {x. f x \<in> B \<and> Domainp A x})"
  have "((A ===> B) ===> rel_set B ===> rel_set A) ?vimage vimage"
    unfolding vimage_def
    by transfer_prover
  also have "?vimage = (\<lambda>f X. f -` X \<inter> Collect (Domainp A))"
    by auto
  finally show ?thesis .
qed

end

lemma vimage_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total A" "bi_unique B"
  shows "((A ===> B) ===> rel_set B ===> rel_set A) vimage vimage"
  unfolding vimage_def[abs_def] by transfer_prover

lemma Image_parametric [transfer_rule]:
  assumes "bi_unique A"
  shows "(rel_set (rel_prod A B) ===> rel_set A ===> rel_set B) (``) (``)"
  by (intro rel_funI rel_setI)
    (force dest: rel_setD1 bi_uniqueDr[OF assms], force dest: rel_setD2 bi_uniqueDl[OF assms])

lemma inj_on_transfer[transfer_rule]:
  "((A ===> B) ===> rel_set A ===> (=)) inj_on inj_on"
  if [transfer_rule]: "bi_unique A" "bi_unique B"
  unfolding inj_on_def
  by transfer_prover

end

lemma (in comm_monoid_set) F_parametric [transfer_rule]:
  fixes A :: "'b \<Rightarrow> 'c \<Rightarrow> bool"
  assumes "bi_unique A"
  shows "rel_fun (rel_fun A (=)) (rel_fun (rel_set A) (=)) F F"
proof (rule rel_funI)+
  fix f :: "'b \<Rightarrow> 'a" and g S T
  assume "rel_fun A (=) f g" "rel_set A S T"
  with \<open>bi_unique A\<close> obtain i where "bij_betw i S T" "\<And>x. x \<in> S \<Longrightarrow> f x = g (i x)"
    by (auto elim: bi_unique_rel_set_lemma simp: rel_fun_def bij_betw_def)
  then show "F f S = F g T"
    by (simp add: reindex_bij_betw)
qed

lemmas sum_parametric = sum.F_parametric
lemmas prod_parametric = prod.F_parametric

lemma rel_set_UNION:
  assumes [transfer_rule]: "rel_set Q A B" "rel_fun Q (rel_set R) f g"
  shows "rel_set R (\<Union>(f ` A)) (\<Union>(g ` B))"
  by transfer_prover

context
  includes lifting_syntax
begin

lemma fold_graph_transfer[transfer_rule]:
  assumes "bi_unique R" "right_total R"
  shows "((R ===> (=) ===> (=)) ===> (=) ===> rel_set R ===> (=) ===> (=)) fold_graph fold_graph"
proof(intro rel_funI)
  fix f1 :: "'a \<Rightarrow> 'c \<Rightarrow> 'c" and f2 :: "'b \<Rightarrow> 'c \<Rightarrow> 'c"
  assume rel_f: "(R ===> (=) ===> (=)) f1 f2"
  fix z1 z2 :: 'c assume [simp]: "z1 = z2"
  fix A1 A2 assume rel_A: "rel_set R A1 A2"
  fix y1 y2 :: 'c assume [simp]: "y1 = y2"

  from \<open>bi_unique R\<close> \<open>right_total R\<close> have The_y: "\<forall>y. \<exists>!x. R x y"
    unfolding bi_unique_def right_total_def by auto
  define r where "r \<equiv> \<lambda>y. THE x. R x y"
  
  from The_y have r_y: "R (r y) y" for y
    unfolding r_def using the_equality by fastforce
  with assms rel_A have "inj_on r A2" "A1 = r ` A2"
    unfolding r_def rel_set_def inj_on_def bi_unique_def
      apply(auto simp: image_iff) by metis+
  with \<open>bi_unique R\<close> rel_f r_y have "(f1 o r) y = f2 y" for y
    unfolding bi_unique_def rel_fun_def by auto
  then have "(f1 o r) = f2"
    by blast
  then show "fold_graph f1 z1 A1 y1 = fold_graph f2 z2 A2 y2"
    by (fastforce simp: fold_graph_image[OF \<open>inj_on r A2\<close>] \<open>A1 = r ` A2\<close>)
qed

lemma fold_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique R" "right_total R"
  shows "((R ===> (=) ===> (=)) ===> (=) ===> rel_set R ===> (=)) Finite_Set.fold Finite_Set.fold"
  unfolding Finite_Set.fold_def
  by transfer_prover

end


end
