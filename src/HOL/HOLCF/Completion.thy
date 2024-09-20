(*  Title:      HOL/HOLCF/Completion.thy
    Author:     Brian Huffman
*)

section \<open>Defining algebraic domains by ideal completion\<close>

theory Completion
imports Cfun
begin

subsection \<open>Ideals over a preorder\<close>

locale preorder =
  fixes r :: "'a::type \<Rightarrow> 'a \<Rightarrow> bool" (infix \<open>\<preceq>\<close> 50)
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
unfolding ideal_def using assms by fast

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
    apply (rule exI [where x = z])
    apply (fast intro: r_refl)
   apply (rule bexI [where x = z], fast)
   apply (fast intro: r_refl)
  apply (fast intro: r_trans)
  done

lemma ex_ideal: "\<exists>A. A \<in> {A. ideal A}"
by (fast intro: ideal_principal)

text \<open>The set of ideals is a cpo\<close>

lemma ideal_UN:
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes ideal_A: "\<And>i. ideal (A i)"
  assumes chain_A: "\<And>i j. i \<le> j \<Longrightarrow> A i \<subseteq> A j"
  shows "ideal (\<Union>i. A i)"
  apply (rule idealI)
  using idealD1 [OF ideal_A] apply fast
   apply (clarify)
  subgoal for i j
    apply (drule subsetD [OF chain_A [OF max.cobounded1]])
    apply (drule subsetD [OF chain_A [OF max.cobounded2]])
    apply (drule (1) idealD2 [OF ideal_A])
    apply blast
    done
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
    and typedef_ideal_rep_lub: "Rep (\<Squnion>i. S i) = (\<Union>i. Rep (S i))"
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
    by (rule lub_eqI)
  show 5: "Rep (\<Squnion>i. S i) = (\<Union>i. Rep (S i))"
    by (simp add: 4 2)
qed

lemma typedef_ideal_cpo:
  fixes Abs :: "'a set \<Rightarrow> 'b::po"
  assumes type: "type_definition Rep Abs {S. ideal S}"
  assumes below: "\<And>x y. x \<sqsubseteq> y \<longleftrightarrow> Rep x \<subseteq> Rep y"
  shows "OFCLASS('b, cpo_class)"
  by standard (rule exI, erule typedef_ideal_lub [OF type below])

end

interpretation below: preorder "below :: 'a::po \<Rightarrow> 'a \<Rightarrow> bool"
apply unfold_locales
apply (rule below_refl)
apply (erule (1) below_trans)
done

subsection \<open>Lemmas about least upper bounds\<close>

lemma is_ub_thelub_ex: "\<lbrakk>\<exists>u. S <<| u; x \<in> S\<rbrakk> \<Longrightarrow> x \<sqsubseteq> lub S"
apply (erule exE, drule is_lub_lub)
apply (drule is_lubD1)
apply (erule (1) is_ubD)
done

lemma is_lub_thelub_ex: "\<lbrakk>\<exists>u. S <<| u; S <| x\<rbrakk> \<Longrightarrow> lub S \<sqsubseteq> x"
by (erule exE, drule is_lub_lub, erule is_lubD2)


subsection \<open>Locale for ideal completion\<close>

hide_const (open) Filter.principal

locale ideal_completion = preorder +
  fixes principal :: "'a::type \<Rightarrow> 'b::cpo"
  fixes rep :: "'b::cpo \<Rightarrow> 'a::type set"
  assumes ideal_rep: "\<And>x. ideal (rep x)"
  assumes rep_lub: "\<And>Y. chain Y \<Longrightarrow> rep (\<Squnion>i. Y i) = (\<Union>i. rep (Y i))"
  assumes rep_principal: "\<And>a. rep (principal a) = {b. b \<preceq> a}"
  assumes belowI: "\<And>x y. rep x \<subseteq> rep y \<Longrightarrow> x \<sqsubseteq> y"
  assumes countable: "\<exists>f::'a \<Rightarrow> nat. inj f"
begin

lemma rep_mono: "x \<sqsubseteq> y \<Longrightarrow> rep x \<subseteq> rep y"
apply (frule bin_chain)
apply (drule rep_lub)
apply (simp only: lub_eqI [OF is_lub_bin_chain])
apply (rule subsetI, rule UN_I [where a=0], simp_all)
done

lemma below_def: "x \<sqsubseteq> y \<longleftrightarrow> rep x \<subseteq> rep y"
by (rule iffI [OF rep_mono belowI])

lemma principal_below_iff_mem_rep: "principal a \<sqsubseteq> x \<longleftrightarrow> a \<in> rep x"
unfolding below_def rep_principal
by (auto intro: r_refl elim: idealD3 [OF ideal_rep])

lemma principal_below_iff [simp]: "principal a \<sqsubseteq> principal b \<longleftrightarrow> a \<preceq> b"
by (simp add: principal_below_iff_mem_rep rep_principal)

lemma principal_eq_iff: "principal a = principal b \<longleftrightarrow> a \<preceq> b \<and> b \<preceq> a"
unfolding po_eq_conv [where 'a='b] principal_below_iff ..

lemma eq_iff: "x = y \<longleftrightarrow> rep x = rep y"
unfolding po_eq_conv below_def by auto

lemma principal_mono: "a \<preceq> b \<Longrightarrow> principal a \<sqsubseteq> principal b"
by (simp only: principal_below_iff)

lemma ch2ch_principal [simp]:
  "\<forall>i. Y i \<preceq> Y (Suc i) \<Longrightarrow> chain (\<lambda>i. principal (Y i))"
by (simp add: chainI principal_mono)

subsubsection \<open>Principal ideals approximate all elements\<close>

lemma compact_principal [simp]: "compact (principal a)"
by (rule compactI2, simp add: principal_below_iff_mem_rep rep_lub)

text \<open>Construct a chain whose lub is the same as a given ideal\<close>

lemma obtain_principal_chain:
  obtains Y where "\<forall>i. Y i \<preceq> Y (Suc i)" and "x = (\<Squnion>i. principal (Y i))"
proof -
  obtain count :: "'a \<Rightarrow> nat" where inj: "inj count"
    using countable ..
  define enum where "enum i = (THE a. count a = i)" for i
  have enum_count [simp]: "\<And>x. enum (count x) = x"
    unfolding enum_def by (simp add: inj_eq [OF inj])
  define a where "a = (LEAST i. enum i \<in> rep x)"
  define b where "b i = (LEAST j. enum j \<in> rep x \<and> \<not> enum j \<preceq> enum i)" for i
  define c where "c i j = (LEAST k. enum k \<in> rep x \<and> enum i \<preceq> enum k \<and> enum j \<preceq> enum k)" for i j
  define P where "P i \<longleftrightarrow> (\<exists>j. enum j \<in> rep x \<and> \<not> enum j \<preceq> enum i)" for i
  define X where "X = rec_nat a (\<lambda>n i. if P i then c i (b i) else i)"
  have X_0: "X 0 = a" unfolding X_def by simp
  have X_Suc: "\<And>n. X (Suc n) = (if P (X n) then c (X n) (b (X n)) else X n)"
    unfolding X_def by simp
  have a_mem: "enum a \<in> rep x"
    unfolding a_def
    apply (rule LeastI_ex)
    apply (insert ideal_rep [of x])
    apply (drule idealD1)
    apply (clarify)
    subgoal for a by (rule exI [where x="count a"]) simp
    done
  have b: "\<And>i. P i \<Longrightarrow> enum i \<in> rep x
    \<Longrightarrow> enum (b i) \<in> rep x \<and> \<not> enum (b i) \<preceq> enum i"
    unfolding P_def b_def by (erule LeastI2_ex, simp)
  have c: "\<And>i j. enum i \<in> rep x \<Longrightarrow> enum j \<in> rep x
    \<Longrightarrow> enum (c i j) \<in> rep x \<and> enum i \<preceq> enum (c i j) \<and> enum j \<preceq> enum (c i j)"
    unfolding c_def
    apply (drule (1) idealD2 [OF ideal_rep], clarify)
    subgoal for \<dots> z by (rule LeastI2 [where a="count z"], simp, simp)
    done
  have X_mem: "enum (X n) \<in> rep x" for n
  proof (induct n)
    case 0
    then show ?case by (simp add: X_0 a_mem)
  next
    case (Suc n)
    with b c show ?case by (auto simp: X_Suc)
  qed
  have X_chain: "\<And>n. enum (X n) \<preceq> enum (X (Suc n))"
    apply (clarsimp simp add: X_Suc r_refl)
    apply (simp add: b c X_mem)
    done
  have less_b: "\<And>n i. n < b i \<Longrightarrow> enum n \<in> rep x \<Longrightarrow> enum n \<preceq> enum i"
    unfolding b_def by (drule not_less_Least, simp)
  have X_covers: "\<forall>k\<le>n. enum k \<in> rep x \<longrightarrow> enum k \<preceq> enum (X n)" for n
  proof (induct n)
    case 0
    then show ?case
      apply (clarsimp simp add: X_0 a_def)
      apply (drule Least_le [where k=0], simp add: r_refl)
      done
  next
    case (Suc n)
    then show ?case
      apply clarsimp
      apply (erule le_SucE)
       apply (rule r_trans [OF _ X_chain], simp)
      apply (cases "P (X n)", simp add: X_Suc)
       apply (rule linorder_cases [where x="b (X n)" and y="Suc n"])
         apply (simp only: less_Suc_eq_le)
         apply (drule spec, drule (1) mp, simp add: b X_mem)
        apply (simp add: c X_mem)
       apply (drule (1) less_b)
       apply (erule r_trans)
       apply (simp add: b c X_mem)
      apply (simp add: X_Suc)
      apply (simp add: P_def)
      done
  qed
  have 1: "\<forall>i. enum (X i) \<preceq> enum (X (Suc i))"
    by (simp add: X_chain)
  have "x = (\<Squnion>n. principal (enum (X n)))"
    apply (simp add: eq_iff rep_lub 1 rep_principal)
    apply auto
    subgoal for a
      apply (subgoal_tac "\<exists>i. a = enum i", erule exE)
       apply (rule_tac x=i in exI, simp add: X_covers)
      apply (rule_tac x="count a" in exI, simp)
      done
    subgoal
      apply (erule idealD3 [OF ideal_rep])
      apply (rule X_mem)
      done
    done
  with 1 show ?thesis ..
qed

lemma principal_induct:
  assumes adm: "adm P"
  assumes P: "\<And>a. P (principal a)"
  shows "P x"
apply (rule obtain_principal_chain [of x])
apply (simp add: admD [OF adm] P)
done

lemma compact_imp_principal: "compact x \<Longrightarrow> \<exists>a. x = principal a"
apply (rule obtain_principal_chain [of x])
apply (drule adm_compact_neq [OF _ cont_id])
apply (subgoal_tac "chain (\<lambda>i. principal (Y i))")
apply (drule (2) admD2, fast, simp)
done

subsection \<open>Defining functions in terms of basis elements\<close>

definition
  extension :: "('a::type \<Rightarrow> 'c::cpo) \<Rightarrow> 'b \<rightarrow> 'c" where
  "extension = (\<lambda>f. (\<Lambda> x. lub (f ` rep x)))"

lemma extension_lemma:
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
    by (simp add: x rep_lub Y rep_principal)
  have "f ` rep x <<| (\<Squnion>n. f (Y n))"
    apply (rule is_lubI)
     apply (rule ub_imageI)
    subgoal for a
      apply (clarsimp simp add: rep_x)
      apply (drule f_mono)
      apply (erule below_lub [OF chain])
      done
    apply (rule lub_below [OF chain])
    subgoal for \<dots> n
      apply (drule ub_imageD [where x="Y n"])
       apply (simp add: rep_x, fast intro: r_refl)
      apply assumption
      done
    done
  then show ?thesis ..
qed

lemma extension_beta:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "extension f\<cdot>x = lub (f ` rep x)"
unfolding extension_def
proof (rule beta_cfun)
  have lub: "\<And>x. \<exists>u. f ` rep x <<| u"
    using f_mono by (rule extension_lemma)
  show cont: "cont (\<lambda>x. lub (f ` rep x))"
    apply (rule contI2)
     apply (rule monofunI)
     apply (rule is_lub_thelub_ex [OF lub ub_imageI])
     apply (rule is_ub_thelub_ex [OF lub imageI])
     apply (erule (1) subsetD [OF rep_mono])
    apply (rule is_lub_thelub_ex [OF lub ub_imageI])
    apply (simp add: rep_lub, clarify)
    apply (erule rev_below_trans [OF is_ub_thelub])
    apply (erule is_ub_thelub_ex [OF lub imageI])
    done
qed

lemma extension_principal:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "extension f\<cdot>(principal a) = f a"
apply (subst extension_beta, erule f_mono)
apply (subst rep_principal)
apply (rule lub_eqI)
apply (rule is_lub_maximal)
apply (rule ub_imageI)
apply (simp add: f_mono)
apply (rule imageI)
apply (simp add: r_refl)
done

lemma extension_mono:
  assumes f_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  assumes g_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> g a \<sqsubseteq> g b"
  assumes below: "\<And>a. f a \<sqsubseteq> g a"
  shows "extension f \<sqsubseteq> extension g"
  apply (rule cfun_belowI)
  apply (simp only: extension_beta f_mono g_mono)
  apply (rule is_lub_thelub_ex)
   apply (rule extension_lemma, erule f_mono)
  apply (rule ub_imageI)
  subgoal for x a
    apply (rule below_trans [OF below])
    apply (rule is_ub_thelub_ex)
     apply (rule extension_lemma, erule g_mono)
    apply (erule imageI)
    done
  done

lemma cont_extension:
  assumes f_mono: "\<And>a b x. a \<preceq> b \<Longrightarrow> f x a \<sqsubseteq> f x b"
  assumes f_cont: "\<And>a. cont (\<lambda>x. f x a)"
  shows "cont (\<lambda>x. extension (\<lambda>a. f x a))"
 apply (rule contI2)
  apply (rule monofunI)
  apply (rule extension_mono, erule f_mono, erule f_mono)
  apply (erule cont2monofunE [OF f_cont])
 apply (rule cfun_belowI)
 apply (rule principal_induct, simp)
 apply (simp only: contlub_cfun_fun)
 apply (simp only: extension_principal f_mono)
 apply (simp add: cont2contlubE [OF f_cont])
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
    using type below by (rule typedef_ideal_rep_lub)
  show "Rep (principal a) = {b. b \<preceq> a}"
    by (simp add: principal Abs_inverse ideal_principal)
  show "Rep x \<subseteq> Rep y \<Longrightarrow> x \<sqsubseteq> y"
    by (simp only: below)
  show "\<exists>f::'a \<Rightarrow> nat. inj f"
    by (rule countable)
qed

end
