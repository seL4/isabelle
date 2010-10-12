(*  Title:      HOLCF/Completion.thy
    Author:     Brian Huffman
*)

header {* Defining algebraic domains by ideal completion *}

theory Completion
imports Cfun
begin

subsection {* Ideals over a preorder *}

locale preorder =
  fixes r :: "'a::type \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50)
  assumes r_refl: "x \<preceq> x"
  assumes r_trans: "\<lbrakk>x \<preceq> y; y \<preceq> z\<rbrakk> \<Longrightarrow> x \<preceq> z"
begin

definition
  ideal :: "'a set \<Rightarrow> bool" where
  "ideal A = ((\<exists>x. x \<in> A) \<and> (\<forall>x\<in>A. \<forall>y\<in>A. \<exists>z\<in>A. x \<preceq> z \<and> y \<preceq> z) \<and>
    (\<forall>x y. x \<preceq> y \<longrightarrow> y \<in> A \<longrightarrow> x \<in> A))"

lemma idealI:
  assumes "\<exists>x. x \<in> A"
  assumes "\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> \<exists>z\<in>A. x \<preceq> z \<and> y \<preceq> z"
  assumes "\<And>x y. \<lbrakk>x \<preceq> y; y \<in> A\<rbrakk> \<Longrightarrow> x \<in> A"
  shows "ideal A"
unfolding ideal_def using prems by fast

lemma idealD1:
  "ideal A \<Longrightarrow> \<exists>x. x \<in> A"
unfolding ideal_def by fast

lemma idealD2:
  "\<lbrakk>ideal A; x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> \<exists>z\<in>A. x \<preceq> z \<and> y \<preceq> z"
unfolding ideal_def by fast

lemma idealD3:
  "\<lbrakk>ideal A; x \<preceq> y; y \<in> A\<rbrakk> \<Longrightarrow> x \<in> A"
unfolding ideal_def by fast

lemma ideal_principal: "ideal {x. x \<preceq> z}"
apply (rule idealI)
apply (rule_tac x=z in exI)
apply (fast intro: r_refl)
apply (rule_tac x=z in bexI, fast)
apply (fast intro: r_refl)
apply (fast intro: r_trans)
done

lemma ex_ideal: "\<exists>A. ideal A"
by (rule exI, rule ideal_principal)

lemma lub_image_principal:
  assumes f: "\<And>x y. x \<preceq> y \<Longrightarrow> f x \<sqsubseteq> f y"
  shows "(\<Squnion>x\<in>{x. x \<preceq> y}. f x) = f y"
apply (rule thelubI)
apply (rule is_lub_maximal)
apply (rule ub_imageI)
apply (simp add: f)
apply (rule imageI)
apply (simp add: r_refl)
done

text {* The set of ideals is a cpo *}

lemma ideal_UN:
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes ideal_A: "\<And>i. ideal (A i)"
  assumes chain_A: "\<And>i j. i \<le> j \<Longrightarrow> A i \<subseteq> A j"
  shows "ideal (\<Union>i. A i)"
 apply (rule idealI)
   apply (cut_tac idealD1 [OF ideal_A], fast)
  apply (clarify, rename_tac i j)
  apply (drule subsetD [OF chain_A [OF le_maxI1]])
  apply (drule subsetD [OF chain_A [OF le_maxI2]])
  apply (drule (1) idealD2 [OF ideal_A])
  apply blast
 apply clarify
 apply (drule (1) idealD3 [OF ideal_A])
 apply fast
done

lemma typedef_ideal_po:
  fixes Abs :: "'a set \<Rightarrow> 'b::below"
  assumes type: "type_definition Rep Abs {S. ideal S}"
  assumes below: "\<And>x y. x \<sqsubseteq> y \<longleftrightarrow> Rep x \<subseteq> Rep y"
  shows "OFCLASS('b, po_class)"
 apply (intro_classes, unfold below)
   apply (rule subset_refl)
  apply (erule (1) subset_trans)
 apply (rule type_definition.Rep_inject [OF type, THEN iffD1])
 apply (erule (1) subset_antisym)
done

lemma
  fixes Abs :: "'a set \<Rightarrow> 'b::po"
  assumes type: "type_definition Rep Abs {S. ideal S}"
  assumes below: "\<And>x y. x \<sqsubseteq> y \<longleftrightarrow> Rep x \<subseteq> Rep y"
  assumes S: "chain S"
  shows typedef_ideal_lub: "range S <<| Abs (\<Union>i. Rep (S i))"
    and typedef_ideal_rep_contlub: "Rep (\<Squnion>i. S i) = (\<Union>i. Rep (S i))"
proof -
  have 1: "ideal (\<Union>i. Rep (S i))"
    apply (rule ideal_UN)
     apply (rule type_definition.Rep [OF type, unfolded mem_Collect_eq])
    apply (subst below [symmetric])
    apply (erule chain_mono [OF S])
    done
  hence 2: "Rep (Abs (\<Union>i. Rep (S i))) = (\<Union>i. Rep (S i))"
    by (simp add: type_definition.Abs_inverse [OF type])
  show 3: "range S <<| Abs (\<Union>i. Rep (S i))"
    apply (rule is_lubI)
     apply (rule is_ubI)
     apply (simp add: below 2, fast)
    apply (simp add: below 2 is_ub_def, fast)
    done
  hence 4: "(\<Squnion>i. S i) = Abs (\<Union>i. Rep (S i))"
    by (rule thelubI)
  show 5: "Rep (\<Squnion>i. S i) = (\<Union>i. Rep (S i))"
    by (simp add: 4 2)
qed

lemma typedef_ideal_cpo:
  fixes Abs :: "'a set \<Rightarrow> 'b::po"
  assumes type: "type_definition Rep Abs {S. ideal S}"
  assumes below: "\<And>x y. x \<sqsubseteq> y \<longleftrightarrow> Rep x \<subseteq> Rep y"
  shows "OFCLASS('b, cpo_class)"
by (default, rule exI, erule typedef_ideal_lub [OF type below])

end

interpretation below: preorder "below :: 'a::po \<Rightarrow> 'a \<Rightarrow> bool"
apply unfold_locales
apply (rule below_refl)
apply (erule (1) below_trans)
done

subsection {* Lemmas about least upper bounds *}

lemma is_ub_thelub_ex: "\<lbrakk>\<exists>u. S <<| u; x \<in> S\<rbrakk> \<Longrightarrow> x \<sqsubseteq> lub S"
apply (erule exE, drule lubI)
apply (drule is_lubD1)
apply (erule (1) is_ubD)
done

lemma is_lub_thelub_ex: "\<lbrakk>\<exists>u. S <<| u; S <| x\<rbrakk> \<Longrightarrow> lub S \<sqsubseteq> x"
by (erule exE, drule lubI, erule is_lub_lub)

subsection {* Locale for ideal completion *}

locale ideal_completion = preorder +
  fixes principal :: "'a::type \<Rightarrow> 'b::cpo"
  fixes rep :: "'b::cpo \<Rightarrow> 'a::type set"
  assumes ideal_rep: "\<And>x. ideal (rep x)"
  assumes rep_contlub: "\<And>Y. chain Y \<Longrightarrow> rep (\<Squnion>i. Y i) = (\<Union>i. rep (Y i))"
  assumes rep_principal: "\<And>a. rep (principal a) = {b. b \<preceq> a}"
  assumes subset_repD: "\<And>x y. rep x \<subseteq> rep y \<Longrightarrow> x \<sqsubseteq> y"
  assumes countable: "\<exists>f::'a \<Rightarrow> nat. inj f"
begin

lemma rep_mono: "x \<sqsubseteq> y \<Longrightarrow> rep x \<subseteq> rep y"
apply (frule bin_chain)
apply (drule rep_contlub)
apply (simp only: thelubI [OF lub_bin_chain])
apply (rule subsetI, rule UN_I [where a=0], simp_all)
done

lemma below_def: "x \<sqsubseteq> y \<longleftrightarrow> rep x \<subseteq> rep y"
by (rule iffI [OF rep_mono subset_repD])

lemma rep_eq: "rep x = {a. principal a \<sqsubseteq> x}"
unfolding below_def rep_principal
apply safe
apply (erule (1) idealD3 [OF ideal_rep])
apply (erule subsetD, simp add: r_refl)
done

lemma mem_rep_iff_principal_below: "a \<in> rep x \<longleftrightarrow> principal a \<sqsubseteq> x"
by (simp add: rep_eq)

lemma principal_below_iff_mem_rep: "principal a \<sqsubseteq> x \<longleftrightarrow> a \<in> rep x"
by (simp add: rep_eq)

lemma principal_below_iff [simp]: "principal a \<sqsubseteq> principal b \<longleftrightarrow> a \<preceq> b"
by (simp add: principal_below_iff_mem_rep rep_principal)

lemma principal_eq_iff: "principal a = principal b \<longleftrightarrow> a \<preceq> b \<and> b \<preceq> a"
unfolding po_eq_conv [where 'a='b] principal_below_iff ..

lemma eq_iff: "x = y \<longleftrightarrow> rep x = rep y"
unfolding po_eq_conv below_def by auto

lemma repD: "a \<in> rep x \<Longrightarrow> principal a \<sqsubseteq> x"
by (simp add: rep_eq)

lemma principal_mono: "a \<preceq> b \<Longrightarrow> principal a \<sqsubseteq> principal b"
by (simp only: principal_below_iff)

lemma ch2ch_principal [simp]:
  "\<forall>i. Y i \<preceq> Y (Suc i) \<Longrightarrow> chain (\<lambda>i. principal (Y i))"
by (simp add: chainI principal_mono)

lemma lub_principal_rep: "principal ` rep x <<| x"
apply (rule is_lubI)
apply (rule ub_imageI)
apply (erule repD)
apply (subst below_def)
apply (rule subsetI)
apply (drule (1) ub_imageD)
apply (simp add: rep_eq)
done

subsubsection {* Principal ideals approximate all elements *}

lemma compact_principal [simp]: "compact (principal a)"
by (rule compactI2, simp add: principal_below_iff_mem_rep rep_contlub)

text {* Construct a chain whose lub is the same as a given ideal *}

lemma obtain_principal_chain:
  obtains Y where "\<forall>i. Y i \<preceq> Y (Suc i)" and "x = (\<Squnion>i. principal (Y i))"
proof -
  obtain count :: "'a \<Rightarrow> nat" where inj: "inj count"
    using countable ..
  def enum \<equiv> "\<lambda>i. THE a. count a = i"
  have enum_count [simp]: "\<And>x. enum (count x) = x"
    unfolding enum_def by (simp add: inj_eq [OF inj])
  def a \<equiv> "LEAST i. enum i \<in> rep x"
  def b \<equiv> "\<lambda>i. LEAST j. enum j \<in> rep x \<and> \<not> enum j \<preceq> enum i"
  def c \<equiv> "\<lambda>i j. LEAST k. enum k \<in> rep x \<and> enum i \<preceq> enum k \<and> enum j \<preceq> enum k"
  def P \<equiv> "\<lambda>i. \<exists>j. enum j \<in> rep x \<and> \<not> enum j \<preceq> enum i"
  def X \<equiv> "nat_rec a (\<lambda>n i. if P i then c i (b i) else i)"
  have X_0: "X 0 = a" unfolding X_def by simp
  have X_Suc: "\<And>n. X (Suc n) = (if P (X n) then c (X n) (b (X n)) else X n)"
    unfolding X_def by simp
  have a_mem: "enum a \<in> rep x"
    unfolding a_def
    apply (rule LeastI_ex)
    apply (cut_tac ideal_rep [of x])
    apply (drule idealD1)
    apply (clarify, rename_tac a)
    apply (rule_tac x="count a" in exI, simp)
    done
  have b: "\<And>i. P i \<Longrightarrow> enum i \<in> rep x
    \<Longrightarrow> enum (b i) \<in> rep x \<and> \<not> enum (b i) \<preceq> enum i"
    unfolding P_def b_def by (erule LeastI2_ex, simp)
  have c: "\<And>i j. enum i \<in> rep x \<Longrightarrow> enum j \<in> rep x
    \<Longrightarrow> enum (c i j) \<in> rep x \<and> enum i \<preceq> enum (c i j) \<and> enum j \<preceq> enum (c i j)"
    unfolding c_def
    apply (drule (1) idealD2 [OF ideal_rep], clarify)
    apply (rule_tac a="count z" in LeastI2, simp, simp)
    done
  have X_mem: "\<And>n. enum (X n) \<in> rep x"
    apply (induct_tac n)
    apply (simp add: X_0 a_mem)
    apply (clarsimp simp add: X_Suc, rename_tac n)
    apply (simp add: b c)
    done
  have X_chain: "\<And>n. enum (X n) \<preceq> enum (X (Suc n))"
    apply (clarsimp simp add: X_Suc r_refl)
    apply (simp add: b c X_mem)
    done
  have less_b: "\<And>n i. n < b i \<Longrightarrow> enum n \<in> rep x \<Longrightarrow> enum n \<preceq> enum i"
    unfolding b_def by (drule not_less_Least, simp)
  have X_covers: "\<And>n. \<forall>k\<le>n. enum k \<in> rep x \<longrightarrow> enum k \<preceq> enum (X n)"
    apply (induct_tac n)
    apply (clarsimp simp add: X_0 a_def)
    apply (drule_tac k=0 in Least_le, simp add: r_refl)
    apply (clarsimp, rename_tac n k)
    apply (erule le_SucE)
    apply (rule r_trans [OF _ X_chain], simp)
    apply (case_tac "P (X n)", simp add: X_Suc)
    apply (rule_tac x="b (X n)" and y="Suc n" in linorder_cases)
    apply (simp only: less_Suc_eq_le)
    apply (drule spec, drule (1) mp, simp add: b X_mem)
    apply (simp add: c X_mem)
    apply (drule (1) less_b)
    apply (erule r_trans)
    apply (simp add: b c X_mem)
    apply (simp add: X_Suc)
    apply (simp add: P_def)
    done
  have 1: "\<forall>i. enum (X i) \<preceq> enum (X (Suc i))"
    by (simp add: X_chain)
  have 2: "x = (\<Squnion>n. principal (enum (X n)))"
    apply (simp add: eq_iff rep_contlub 1 rep_principal)
    apply (auto, rename_tac a)
    apply (subgoal_tac "\<exists>i. a = enum i", erule exE)
    apply (rule_tac x=i in exI, simp add: X_covers)
    apply (rule_tac x="count a" in exI, simp)
    apply (erule idealD3 [OF ideal_rep])
    apply (rule X_mem)
    done
  from 1 2 show ?thesis ..
qed

lemma principal_induct:
  assumes adm: "adm P"
  assumes P: "\<And>a. P (principal a)"
  shows "P x"
apply (rule obtain_principal_chain [of x])
apply (simp add: admD [OF adm] P)
done

lemma principal_induct2:
  "\<lbrakk>\<And>y. adm (\<lambda>x. P x y); \<And>x. adm (\<lambda>y. P x y);
    \<And>a b. P (principal a) (principal b)\<rbrakk> \<Longrightarrow> P x y"
apply (rule_tac x=y in spec)
apply (rule_tac x=x in principal_induct, simp)
apply (rule allI, rename_tac y)
apply (rule_tac x=y in principal_induct, simp)
apply simp
done

lemma compact_imp_principal: "compact x \<Longrightarrow> \<exists>a. x = principal a"
apply (rule obtain_principal_chain [of x])
apply (drule adm_compact_neq [OF _ cont_id])
apply (subgoal_tac "chain (\<lambda>i. principal (Y i))")
apply (drule (2) admD2, fast, simp)
done

lemma obtain_compact_chain:
  obtains Y :: "nat \<Rightarrow> 'b"
  where "chain Y" and "\<forall>i. compact (Y i)" and "x = (\<Squnion>i. Y i)"
apply (rule obtain_principal_chain [of x])
apply (rule_tac Y="\<lambda>i. principal (Y i)" in that, simp_all)
done

subsection {* Defining functions in terms of basis elements *}

definition
  basis_fun :: "('a::type \<Rightarrow> 'c::cpo) \<Rightarrow> 'b \<rightarrow> 'c" where
  "basis_fun = (\<lambda>f. (\<Lambda> x. lub (f ` rep x)))"

lemma basis_fun_lemma:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "\<exists>u. f ` rep x <<| u"
proof -
  obtain Y where Y: "\<forall>i. Y i \<preceq> Y (Suc i)"
  and x: "x = (\<Squnion>i. principal (Y i))"
    by (rule obtain_principal_chain [of x])
  have chain: "chain (\<lambda>i. f (Y i))"
    by (rule chainI, simp add: f_mono Y)
  have rep_x: "rep x = (\<Union>n. {a. a \<preceq> Y n})"
    by (simp add: x rep_contlub Y rep_principal)
  have "f ` rep x <<| (\<Squnion>n. f (Y n))"
    apply (rule is_lubI)
    apply (rule ub_imageI, rename_tac a)
    apply (clarsimp simp add: rep_x)
    apply (drule f_mono)
    apply (erule below_trans)
    apply (rule is_ub_thelub [OF chain])
    apply (rule is_lub_thelub [OF chain])
    apply (rule ub_rangeI)
    apply (drule_tac x="Y i" in ub_imageD)
    apply (simp add: rep_x, fast intro: r_refl)
    apply assumption
    done
  thus ?thesis ..
qed

lemma basis_fun_beta:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "basis_fun f\<cdot>x = lub (f ` rep x)"
unfolding basis_fun_def
proof (rule beta_cfun)
  have lub: "\<And>x. \<exists>u. f ` rep x <<| u"
    using f_mono by (rule basis_fun_lemma)
  show cont: "cont (\<lambda>x. lub (f ` rep x))"
    apply (rule contI2)
     apply (rule monofunI)
     apply (rule is_lub_thelub_ex [OF lub ub_imageI])
     apply (rule is_ub_thelub_ex [OF lub imageI])
     apply (erule (1) subsetD [OF rep_mono])
    apply (rule is_lub_thelub_ex [OF lub ub_imageI])
    apply (simp add: rep_contlub, clarify)
    apply (erule rev_below_trans [OF is_ub_thelub])
    apply (erule is_ub_thelub_ex [OF lub imageI])
    done
qed

lemma basis_fun_principal:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "basis_fun f\<cdot>(principal a) = f a"
apply (subst basis_fun_beta, erule f_mono)
apply (subst rep_principal)
apply (rule lub_image_principal, erule f_mono)
done

lemma basis_fun_mono:
  assumes f_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  assumes g_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> g a \<sqsubseteq> g b"
  assumes below: "\<And>a. f a \<sqsubseteq> g a"
  shows "basis_fun f \<sqsubseteq> basis_fun g"
 apply (rule cfun_belowI)
 apply (simp only: basis_fun_beta f_mono g_mono)
 apply (rule is_lub_thelub_ex)
  apply (rule basis_fun_lemma, erule f_mono)
 apply (rule ub_imageI, rename_tac a)
 apply (rule below_trans [OF below])
 apply (rule is_ub_thelub_ex)
  apply (rule basis_fun_lemma, erule g_mono)
 apply (erule imageI)
done

end

lemma (in preorder) typedef_ideal_completion:
  fixes Abs :: "'a set \<Rightarrow> 'b::cpo"
  assumes type: "type_definition Rep Abs {S. ideal S}"
  assumes below: "\<And>x y. x \<sqsubseteq> y \<longleftrightarrow> Rep x \<subseteq> Rep y"
  assumes principal: "\<And>a. principal a = Abs {b. b \<preceq> a}"
  assumes countable: "\<exists>f::'a \<Rightarrow> nat. inj f"
  shows "ideal_completion r principal Rep"
proof
  interpret type_definition Rep Abs "{S. ideal S}" by fact
  fix a b :: 'a and x y :: 'b and Y :: "nat \<Rightarrow> 'b"
  show "ideal (Rep x)"
    using Rep [of x] by simp
  show "chain Y \<Longrightarrow> Rep (\<Squnion>i. Y i) = (\<Union>i. Rep (Y i))"
    using type below by (rule typedef_ideal_rep_contlub)
  show "Rep (principal a) = {b. b \<preceq> a}"
    by (simp add: principal Abs_inverse ideal_principal)
  show "Rep x \<subseteq> Rep y \<Longrightarrow> x \<sqsubseteq> y"
    by (simp only: below)
  show "\<exists>f::'a \<Rightarrow> nat. inj f"
    by (rule countable)
qed

end
