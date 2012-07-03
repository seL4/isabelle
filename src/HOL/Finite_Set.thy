(*  Title:      HOL/Finite_Set.thy
    Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel
                with contributions by Jeremy Avigad
*)

header {* Finite sets *}

theory Finite_Set
imports Option Power
uses ("Tools/set_comprehension_pointfree.ML")
begin

subsection {* Predicate for finite sets *}

inductive finite :: "'a set \<Rightarrow> bool"
  where
    emptyI [simp, intro!]: "finite {}"
  | insertI [simp, intro!]: "finite A \<Longrightarrow> finite (insert a A)"

(* FIXME: move to Set theory *)
use "Tools/set_comprehension_pointfree.ML"

simproc_setup finite_Collect ("finite (Collect P)") =
  {* K Set_Comprehension_Pointfree.simproc *}

(* FIXME: move to Set theory*)
setup {*
  Code_Preproc.map_pre (fn ss => ss addsimprocs
    [Raw_Simplifier.make_simproc {name = "set comprehension", lhss = [@{cpat "Collect ?P"}],
    proc = K Set_Comprehension_Pointfree.code_simproc, identifier = []}])
*}

lemma finite_induct [case_names empty insert, induct set: finite]:
  -- {* Discharging @{text "x \<notin> F"} entails extra work. *}
  assumes "finite F"
  assumes "P {}"
    and insert: "\<And>x F. finite F \<Longrightarrow> x \<notin> F \<Longrightarrow> P F \<Longrightarrow> P (insert x F)"
  shows "P F"
using `finite F`
proof induct
  show "P {}" by fact
  fix x F assume F: "finite F" and P: "P F"
  show "P (insert x F)"
  proof cases
    assume "x \<in> F"
    hence "insert x F = F" by (rule insert_absorb)
    with P show ?thesis by (simp only:)
  next
    assume "x \<notin> F"
    from F this P show ?thesis by (rule insert)
  qed
qed


subsubsection {* Choice principles *}

lemma ex_new_if_finite: -- "does not depend on def of finite at all"
  assumes "\<not> finite (UNIV :: 'a set)" and "finite A"
  shows "\<exists>a::'a. a \<notin> A"
proof -
  from assms have "A \<noteq> UNIV" by blast
  then show ?thesis by blast
qed

text {* A finite choice principle. Does not need the SOME choice operator. *}

lemma finite_set_choice:
  "finite A \<Longrightarrow> \<forall>x\<in>A. \<exists>y. P x y \<Longrightarrow> \<exists>f. \<forall>x\<in>A. P x (f x)"
proof (induct rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert a A)
  then obtain f b where f: "ALL x:A. P x (f x)" and ab: "P a b" by auto
  show ?case (is "EX f. ?P f")
  proof
    show "?P(%x. if x = a then b else f x)" using f ab by auto
  qed
qed


subsubsection {* Finite sets are the images of initial segments of natural numbers *}

lemma finite_imp_nat_seg_image_inj_on:
  assumes "finite A" 
  shows "\<exists>(n::nat) f. A = f ` {i. i < n} \<and> inj_on f {i. i < n}"
using assms
proof induct
  case empty
  show ?case
  proof
    show "\<exists>f. {} = f ` {i::nat. i < 0} \<and> inj_on f {i. i < 0}" by simp 
  qed
next
  case (insert a A)
  have notinA: "a \<notin> A" by fact
  from insert.hyps obtain n f
    where "A = f ` {i::nat. i < n}" "inj_on f {i. i < n}" by blast
  hence "insert a A = f(n:=a) ` {i. i < Suc n}"
        "inj_on (f(n:=a)) {i. i < Suc n}" using notinA
    by (auto simp add: image_def Ball_def inj_on_def less_Suc_eq)
  thus ?case by blast
qed

lemma nat_seg_image_imp_finite:
  "A = f ` {i::nat. i < n} \<Longrightarrow> finite A"
proof (induct n arbitrary: A)
  case 0 thus ?case by simp
next
  case (Suc n)
  let ?B = "f ` {i. i < n}"
  have finB: "finite ?B" by(rule Suc.hyps[OF refl])
  show ?case
  proof cases
    assume "\<exists>k<n. f n = f k"
    hence "A = ?B" using Suc.prems by(auto simp:less_Suc_eq)
    thus ?thesis using finB by simp
  next
    assume "\<not>(\<exists> k<n. f n = f k)"
    hence "A = insert (f n) ?B" using Suc.prems by(auto simp:less_Suc_eq)
    thus ?thesis using finB by simp
  qed
qed

lemma finite_conv_nat_seg_image:
  "finite A \<longleftrightarrow> (\<exists>(n::nat) f. A = f ` {i::nat. i < n})"
  by (blast intro: nat_seg_image_imp_finite dest: finite_imp_nat_seg_image_inj_on)

lemma finite_imp_inj_to_nat_seg:
  assumes "finite A"
  shows "\<exists>f n::nat. f ` A = {i. i < n} \<and> inj_on f A"
proof -
  from finite_imp_nat_seg_image_inj_on[OF `finite A`]
  obtain f and n::nat where bij: "bij_betw f {i. i<n} A"
    by (auto simp:bij_betw_def)
  let ?f = "the_inv_into {i. i<n} f"
  have "inj_on ?f A & ?f ` A = {i. i<n}"
    by (fold bij_betw_def) (rule bij_betw_the_inv_into[OF bij])
  thus ?thesis by blast
qed

lemma finite_Collect_less_nat [iff]:
  "finite {n::nat. n < k}"
  by (fastforce simp: finite_conv_nat_seg_image)

lemma finite_Collect_le_nat [iff]:
  "finite {n::nat. n \<le> k}"
  by (simp add: le_eq_less_or_eq Collect_disj_eq)


subsubsection {* Finiteness and common set operations *}

lemma rev_finite_subset:
  "finite B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> finite A"
proof (induct arbitrary: A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F A)
  have A: "A \<subseteq> insert x F" and r: "A - {x} \<subseteq> F \<Longrightarrow> finite (A - {x})" by fact+
  show "finite A"
  proof cases
    assume x: "x \<in> A"
    with A have "A - {x} \<subseteq> F" by (simp add: subset_insert_iff)
    with r have "finite (A - {x})" .
    hence "finite (insert x (A - {x}))" ..
    also have "insert x (A - {x}) = A" using x by (rule insert_Diff)
    finally show ?thesis .
  next
    show "A \<subseteq> F ==> ?thesis" by fact
    assume "x \<notin> A"
    with A show "A \<subseteq> F" by (simp add: subset_insert_iff)
  qed
qed

lemma finite_subset:
  "A \<subseteq> B \<Longrightarrow> finite B \<Longrightarrow> finite A"
  by (rule rev_finite_subset)

lemma finite_UnI:
  assumes "finite F" and "finite G"
  shows "finite (F \<union> G)"
  using assms by induct simp_all

lemma finite_Un [iff]:
  "finite (F \<union> G) \<longleftrightarrow> finite F \<and> finite G"
  by (blast intro: finite_UnI finite_subset [of _ "F \<union> G"])

lemma finite_insert [simp]: "finite (insert a A) \<longleftrightarrow> finite A"
proof -
  have "finite {a} \<and> finite A \<longleftrightarrow> finite A" by simp
  then have "finite ({a} \<union> A) \<longleftrightarrow> finite A" by (simp only: finite_Un)
  then show ?thesis by simp
qed

lemma finite_Int [simp, intro]:
  "finite F \<or> finite G \<Longrightarrow> finite (F \<inter> G)"
  by (blast intro: finite_subset)

lemma finite_Collect_conjI [simp, intro]:
  "finite {x. P x} \<or> finite {x. Q x} \<Longrightarrow> finite {x. P x \<and> Q x}"
  by (simp add: Collect_conj_eq)

lemma finite_Collect_disjI [simp]:
  "finite {x. P x \<or> Q x} \<longleftrightarrow> finite {x. P x} \<and> finite {x. Q x}"
  by (simp add: Collect_disj_eq)

lemma finite_Diff [simp, intro]:
  "finite A \<Longrightarrow> finite (A - B)"
  by (rule finite_subset, rule Diff_subset)

lemma finite_Diff2 [simp]:
  assumes "finite B"
  shows "finite (A - B) \<longleftrightarrow> finite A"
proof -
  have "finite A \<longleftrightarrow> finite((A - B) \<union> (A \<inter> B))" by (simp add: Un_Diff_Int)
  also have "\<dots> \<longleftrightarrow> finite (A - B)" using `finite B` by simp
  finally show ?thesis ..
qed

lemma finite_Diff_insert [iff]:
  "finite (A - insert a B) \<longleftrightarrow> finite (A - B)"
proof -
  have "finite (A - B) \<longleftrightarrow> finite (A - B - {a})" by simp
  moreover have "A - insert a B = A - B - {a}" by auto
  ultimately show ?thesis by simp
qed

lemma finite_compl[simp]:
  "finite (A :: 'a set) \<Longrightarrow> finite (- A) \<longleftrightarrow> finite (UNIV :: 'a set)"
  by (simp add: Compl_eq_Diff_UNIV)

lemma finite_Collect_not[simp]:
  "finite {x :: 'a. P x} \<Longrightarrow> finite {x. \<not> P x} \<longleftrightarrow> finite (UNIV :: 'a set)"
  by (simp add: Collect_neg_eq)

lemma finite_Union [simp, intro]:
  "finite A \<Longrightarrow> (\<And>M. M \<in> A \<Longrightarrow> finite M) \<Longrightarrow> finite(\<Union>A)"
  by (induct rule: finite_induct) simp_all

lemma finite_UN_I [intro]:
  "finite A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> finite (B a)) \<Longrightarrow> finite (\<Union>a\<in>A. B a)"
  by (induct rule: finite_induct) simp_all

lemma finite_UN [simp]:
  "finite A \<Longrightarrow> finite (UNION A B) \<longleftrightarrow> (\<forall>x\<in>A. finite (B x))"
  by (blast intro: finite_subset)

lemma finite_Inter [intro]:
  "\<exists>A\<in>M. finite A \<Longrightarrow> finite (\<Inter>M)"
  by (blast intro: Inter_lower finite_subset)

lemma finite_INT [intro]:
  "\<exists>x\<in>I. finite (A x) \<Longrightarrow> finite (\<Inter>x\<in>I. A x)"
  by (blast intro: INT_lower finite_subset)

lemma finite_imageI [simp, intro]:
  "finite F \<Longrightarrow> finite (h ` F)"
  by (induct rule: finite_induct) simp_all

lemma finite_image_set [simp]:
  "finite {x. P x} \<Longrightarrow> finite { f x | x. P x }"
  by (simp add: image_Collect [symmetric])

lemma finite_imageD:
  assumes "finite (f ` A)" and "inj_on f A"
  shows "finite A"
using assms
proof (induct "f ` A" arbitrary: A)
  case empty then show ?case by simp
next
  case (insert x B)
  then have B_A: "insert x B = f ` A" by simp
  then obtain y where "x = f y" and "y \<in> A" by blast
  from B_A `x \<notin> B` have "B = f ` A - {x}" by blast
  with B_A `x \<notin> B` `x = f y` `inj_on f A` `y \<in> A` have "B = f ` (A - {y})" by (simp add: inj_on_image_set_diff)
  moreover from `inj_on f A` have "inj_on f (A - {y})" by (rule inj_on_diff)
  ultimately have "finite (A - {y})" by (rule insert.hyps)
  then show "finite A" by simp
qed

lemma finite_surj:
  "finite A \<Longrightarrow> B \<subseteq> f ` A \<Longrightarrow> finite B"
  by (erule finite_subset) (rule finite_imageI)

lemma finite_range_imageI:
  "finite (range g) \<Longrightarrow> finite (range (\<lambda>x. f (g x)))"
  by (drule finite_imageI) (simp add: range_composition)

lemma finite_subset_image:
  assumes "finite B"
  shows "B \<subseteq> f ` A \<Longrightarrow> \<exists>C\<subseteq>A. finite C \<and> B = f ` C"
using assms
proof induct
  case empty then show ?case by simp
next
  case insert then show ?case
    by (clarsimp simp del: image_insert simp add: image_insert [symmetric])
       blast
qed

lemma finite_vimage_IntI:
  "finite F \<Longrightarrow> inj_on h A \<Longrightarrow> finite (h -` F \<inter> A)"
  apply (induct rule: finite_induct)
   apply simp_all
  apply (subst vimage_insert)
  apply (simp add: finite_subset [OF inj_on_vimage_singleton] Int_Un_distrib2)
  done

lemma finite_vimageI:
  "finite F \<Longrightarrow> inj h \<Longrightarrow> finite (h -` F)"
  using finite_vimage_IntI[of F h UNIV] by auto

lemma finite_vimageD:
  assumes fin: "finite (h -` F)" and surj: "surj h"
  shows "finite F"
proof -
  have "finite (h ` (h -` F))" using fin by (rule finite_imageI)
  also have "h ` (h -` F) = F" using surj by (rule surj_image_vimage_eq)
  finally show "finite F" .
qed

lemma finite_vimage_iff: "bij h \<Longrightarrow> finite (h -` F) \<longleftrightarrow> finite F"
  unfolding bij_def by (auto elim: finite_vimageD finite_vimageI)

lemma finite_Collect_bex [simp]:
  assumes "finite A"
  shows "finite {x. \<exists>y\<in>A. Q x y} \<longleftrightarrow> (\<forall>y\<in>A. finite {x. Q x y})"
proof -
  have "{x. \<exists>y\<in>A. Q x y} = (\<Union>y\<in>A. {x. Q x y})" by auto
  with assms show ?thesis by simp
qed

lemma finite_Collect_bounded_ex [simp]:
  assumes "finite {y. P y}"
  shows "finite {x. \<exists>y. P y \<and> Q x y} \<longleftrightarrow> (\<forall>y. P y \<longrightarrow> finite {x. Q x y})"
proof -
  have "{x. EX y. P y & Q x y} = (\<Union>y\<in>{y. P y}. {x. Q x y})" by auto
  with assms show ?thesis by simp
qed

lemma finite_Plus:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite (A <+> B)"
  by (simp add: Plus_def)

lemma finite_PlusD: 
  fixes A :: "'a set" and B :: "'b set"
  assumes fin: "finite (A <+> B)"
  shows "finite A" "finite B"
proof -
  have "Inl ` A \<subseteq> A <+> B" by auto
  then have "finite (Inl ` A :: ('a + 'b) set)" using fin by (rule finite_subset)
  then show "finite A" by (rule finite_imageD) (auto intro: inj_onI)
next
  have "Inr ` B \<subseteq> A <+> B" by auto
  then have "finite (Inr ` B :: ('a + 'b) set)" using fin by (rule finite_subset)
  then show "finite B" by (rule finite_imageD) (auto intro: inj_onI)
qed

lemma finite_Plus_iff [simp]:
  "finite (A <+> B) \<longleftrightarrow> finite A \<and> finite B"
  by (auto intro: finite_PlusD finite_Plus)

lemma finite_Plus_UNIV_iff [simp]:
  "finite (UNIV :: ('a + 'b) set) \<longleftrightarrow> finite (UNIV :: 'a set) \<and> finite (UNIV :: 'b set)"
  by (subst UNIV_Plus_UNIV [symmetric]) (rule finite_Plus_iff)

lemma finite_SigmaI [simp, intro]:
  "finite A \<Longrightarrow> (\<And>a. a\<in>A \<Longrightarrow> finite (B a)) ==> finite (SIGMA a:A. B a)"
  by (unfold Sigma_def) blast

lemma finite_cartesian_product:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite (A \<times> B)"
  by (rule finite_SigmaI)

lemma finite_Prod_UNIV:
  "finite (UNIV :: 'a set) \<Longrightarrow> finite (UNIV :: 'b set) \<Longrightarrow> finite (UNIV :: ('a \<times> 'b) set)"
  by (simp only: UNIV_Times_UNIV [symmetric] finite_cartesian_product)

lemma finite_cartesian_productD1:
  assumes "finite (A \<times> B)" and "B \<noteq> {}"
  shows "finite A"
proof -
  from assms obtain n f where "A \<times> B = f ` {i::nat. i < n}"
    by (auto simp add: finite_conv_nat_seg_image)
  then have "fst ` (A \<times> B) = fst ` f ` {i::nat. i < n}" by simp
  with `B \<noteq> {}` have "A = (fst \<circ> f) ` {i::nat. i < n}"
    by (simp add: image_compose)
  then have "\<exists>n f. A = f ` {i::nat. i < n}" by blast
  then show ?thesis
    by (auto simp add: finite_conv_nat_seg_image)
qed

lemma finite_cartesian_productD2:
  assumes "finite (A \<times> B)" and "A \<noteq> {}"
  shows "finite B"
proof -
  from assms obtain n f where "A \<times> B = f ` {i::nat. i < n}"
    by (auto simp add: finite_conv_nat_seg_image)
  then have "snd ` (A \<times> B) = snd ` f ` {i::nat. i < n}" by simp
  with `A \<noteq> {}` have "B = (snd \<circ> f) ` {i::nat. i < n}"
    by (simp add: image_compose)
  then have "\<exists>n f. B = f ` {i::nat. i < n}" by blast
  then show ?thesis
    by (auto simp add: finite_conv_nat_seg_image)
qed

lemma finite_prod: 
  "finite (UNIV :: ('a \<times> 'b) set) \<longleftrightarrow> finite (UNIV :: 'a set) \<and> finite (UNIV :: 'b set)"
by(auto simp add: UNIV_Times_UNIV[symmetric] simp del: UNIV_Times_UNIV 
   dest: finite_cartesian_productD1 finite_cartesian_productD2)

lemma finite_Pow_iff [iff]:
  "finite (Pow A) \<longleftrightarrow> finite A"
proof
  assume "finite (Pow A)"
  then have "finite ((%x. {x}) ` A)" by (blast intro: finite_subset)
  then show "finite A" by (rule finite_imageD [unfolded inj_on_def]) simp
next
  assume "finite A"
  then show "finite (Pow A)"
    by induct (simp_all add: Pow_insert)
qed

corollary finite_Collect_subsets [simp, intro]:
  "finite A \<Longrightarrow> finite {B. B \<subseteq> A}"
  by (simp add: Pow_def [symmetric])

lemma finite_set: "finite (UNIV :: 'a set set) \<longleftrightarrow> finite (UNIV :: 'a set)"
by(simp only: finite_Pow_iff Pow_UNIV[symmetric])

lemma finite_UnionD: "finite(\<Union>A) \<Longrightarrow> finite A"
  by (blast intro: finite_subset [OF subset_Pow_Union])


subsubsection {* Further induction rules on finite sets *}

lemma finite_ne_induct [case_names singleton insert, consumes 2]:
  assumes "finite F" and "F \<noteq> {}"
  assumes "\<And>x. P {x}"
    and "\<And>x F. finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> x \<notin> F \<Longrightarrow> P F  \<Longrightarrow> P (insert x F)"
  shows "P F"
using assms
proof induct
  case empty then show ?case by simp
next
  case (insert x F) then show ?case by cases auto
qed

lemma finite_subset_induct [consumes 2, case_names empty insert]:
  assumes "finite F" and "F \<subseteq> A"
  assumes empty: "P {}"
    and insert: "\<And>a F. finite F \<Longrightarrow> a \<in> A \<Longrightarrow> a \<notin> F \<Longrightarrow> P F \<Longrightarrow> P (insert a F)"
  shows "P F"
using `finite F` `F \<subseteq> A`
proof induct
  show "P {}" by fact
next
  fix x F
  assume "finite F" and "x \<notin> F" and
    P: "F \<subseteq> A \<Longrightarrow> P F" and i: "insert x F \<subseteq> A"
  show "P (insert x F)"
  proof (rule insert)
    from i show "x \<in> A" by blast
    from i have "F \<subseteq> A" by blast
    with P show "P F" .
    show "finite F" by fact
    show "x \<notin> F" by fact
  qed
qed

lemma finite_empty_induct:
  assumes "finite A"
  assumes "P A"
    and remove: "\<And>a A. finite A \<Longrightarrow> a \<in> A \<Longrightarrow> P A \<Longrightarrow> P (A - {a})"
  shows "P {}"
proof -
  have "\<And>B. B \<subseteq> A \<Longrightarrow> P (A - B)"
  proof -
    fix B :: "'a set"
    assume "B \<subseteq> A"
    with `finite A` have "finite B" by (rule rev_finite_subset)
    from this `B \<subseteq> A` show "P (A - B)"
    proof induct
      case empty
      from `P A` show ?case by simp
    next
      case (insert b B)
      have "P (A - B - {b})"
      proof (rule remove)
        from `finite A` show "finite (A - B)" by induct auto
        from insert show "b \<in> A - B" by simp
        from insert show "P (A - B)" by simp
      qed
      also have "A - B - {b} = A - insert b B" by (rule Diff_insert [symmetric])
      finally show ?case .
    qed
  qed
  then have "P (A - A)" by blast
  then show ?thesis by simp
qed


subsection {* Class @{text finite}  *}

class finite =
  assumes finite_UNIV: "finite (UNIV \<Colon> 'a set)"
begin

lemma finite [simp]: "finite (A \<Colon> 'a set)"
  by (rule subset_UNIV finite_UNIV finite_subset)+

lemma finite_code [code]: "finite (A \<Colon> 'a set) \<longleftrightarrow> True"
  by simp

end

instance prod :: (finite, finite) finite
  by default (simp only: UNIV_Times_UNIV [symmetric] finite_cartesian_product finite)

lemma inj_graph: "inj (%f. {(x, y). y = f x})"
  by (rule inj_onI, auto simp add: set_eq_iff fun_eq_iff)

instance "fun" :: (finite, finite) finite
proof
  show "finite (UNIV :: ('a => 'b) set)"
  proof (rule finite_imageD)
    let ?graph = "%f::'a => 'b. {(x, y). y = f x}"
    have "range ?graph \<subseteq> Pow UNIV" by simp
    moreover have "finite (Pow (UNIV :: ('a * 'b) set))"
      by (simp only: finite_Pow_iff finite)
    ultimately show "finite (range ?graph)"
      by (rule finite_subset)
    show "inj ?graph" by (rule inj_graph)
  qed
qed

instance bool :: finite
  by default (simp add: UNIV_bool)

instance set :: (finite) finite
  by default (simp only: Pow_UNIV [symmetric] finite_Pow_iff finite)

instance unit :: finite
  by default (simp add: UNIV_unit)

instance sum :: (finite, finite) finite
  by default (simp only: UNIV_Plus_UNIV [symmetric] finite_Plus finite)

lemma finite_option_UNIV [simp]:
  "finite (UNIV :: 'a option set) = finite (UNIV :: 'a set)"
  by (auto simp add: UNIV_option_conv elim: finite_imageD intro: inj_Some)

instance option :: (finite) finite
  by default (simp add: UNIV_option_conv)


subsection {* A basic fold functional for finite sets *}

text {* The intended behaviour is
@{text "fold f z {x\<^isub>1, ..., x\<^isub>n} = f x\<^isub>1 (\<dots> (f x\<^isub>n z)\<dots>)"}
if @{text f} is ``left-commutative'':
*}

locale comp_fun_commute =
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes comp_fun_commute: "f y \<circ> f x = f x \<circ> f y"
begin

lemma fun_left_comm: "f x (f y z) = f y (f x z)"
  using comp_fun_commute by (simp add: fun_eq_iff)

end

inductive fold_graph :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool"
for f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and z :: 'b where
  emptyI [intro]: "fold_graph f z {} z" |
  insertI [intro]: "x \<notin> A \<Longrightarrow> fold_graph f z A y
      \<Longrightarrow> fold_graph f z (insert x A) (f x y)"

inductive_cases empty_fold_graphE [elim!]: "fold_graph f z {} x"

definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b" where
  "fold f z A = (THE y. fold_graph f z A y)"

text{*A tempting alternative for the definiens is
@{term "if finite A then THE y. fold_graph f z A y else e"}.
It allows the removal of finiteness assumptions from the theorems
@{text fold_comm}, @{text fold_reindex} and @{text fold_distrib}.
The proofs become ugly. It is not worth the effort. (???) *}

lemma finite_imp_fold_graph: "finite A \<Longrightarrow> \<exists>x. fold_graph f z A x"
by (induct rule: finite_induct) auto


subsubsection{*From @{const fold_graph} to @{term fold}*}

context comp_fun_commute
begin

lemma fold_graph_insertE_aux:
  "fold_graph f z A y \<Longrightarrow> a \<in> A \<Longrightarrow> \<exists>y'. y = f a y' \<and> fold_graph f z (A - {a}) y'"
proof (induct set: fold_graph)
  case (insertI x A y) show ?case
  proof (cases "x = a")
    assume "x = a" with insertI show ?case by auto
  next
    assume "x \<noteq> a"
    then obtain y' where y: "y = f a y'" and y': "fold_graph f z (A - {a}) y'"
      using insertI by auto
    have "f x y = f a (f x y')"
      unfolding y by (rule fun_left_comm)
    moreover have "fold_graph f z (insert x A - {a}) (f x y')"
      using y' and `x \<noteq> a` and `x \<notin> A`
      by (simp add: insert_Diff_if fold_graph.insertI)
    ultimately show ?case by fast
  qed
qed simp

lemma fold_graph_insertE:
  assumes "fold_graph f z (insert x A) v" and "x \<notin> A"
  obtains y where "v = f x y" and "fold_graph f z A y"
using assms by (auto dest: fold_graph_insertE_aux [OF _ insertI1])

lemma fold_graph_determ:
  "fold_graph f z A x \<Longrightarrow> fold_graph f z A y \<Longrightarrow> y = x"
proof (induct arbitrary: y set: fold_graph)
  case (insertI x A y v)
  from `fold_graph f z (insert x A) v` and `x \<notin> A`
  obtain y' where "v = f x y'" and "fold_graph f z A y'"
    by (rule fold_graph_insertE)
  from `fold_graph f z A y'` have "y' = y" by (rule insertI)
  with `v = f x y'` show "v = f x y" by simp
qed fast

lemma fold_equality:
  "fold_graph f z A y \<Longrightarrow> fold f z A = y"
by (unfold fold_def) (blast intro: fold_graph_determ)

lemma fold_graph_fold:
  assumes "finite A"
  shows "fold_graph f z A (fold f z A)"
proof -
  from assms have "\<exists>x. fold_graph f z A x" by (rule finite_imp_fold_graph)
  moreover note fold_graph_determ
  ultimately have "\<exists>!x. fold_graph f z A x" by (rule ex_ex1I)
  then have "fold_graph f z A (The (fold_graph f z A))" by (rule theI')
  then show ?thesis by (unfold fold_def)
qed

text{* The base case for @{text fold}: *}

lemma (in -) fold_empty [simp]: "fold f z {} = z"
by (unfold fold_def) blast

text{* The various recursion equations for @{const fold}: *}

lemma fold_insert [simp]:
  assumes "finite A" and "x \<notin> A"
  shows "fold f z (insert x A) = f x (fold f z A)"
proof (rule fold_equality)
  from `finite A` have "fold_graph f z A (fold f z A)" by (rule fold_graph_fold)
  with `x \<notin> A`show "fold_graph f z (insert x A) (f x (fold f z A))" by (rule fold_graph.insertI)
qed

lemma fold_fun_comm:
  "finite A \<Longrightarrow> f x (fold f z A) = fold f (f x z) A"
proof (induct rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert y A) then show ?case
    by (simp add: fun_left_comm[of x])
qed

lemma fold_insert2:
  "finite A \<Longrightarrow> x \<notin> A \<Longrightarrow> fold f z (insert x A) = fold f (f x z) A"
by (simp add: fold_fun_comm)

lemma fold_rec:
  assumes "finite A" and "x \<in> A"
  shows "fold f z A = f x (fold f z (A - {x}))"
proof -
  have A: "A = insert x (A - {x})" using `x \<in> A` by blast
  then have "fold f z A = fold f z (insert x (A - {x}))" by simp
  also have "\<dots> = f x (fold f z (A - {x}))"
    by (rule fold_insert) (simp add: `finite A`)+
  finally show ?thesis .
qed

lemma fold_insert_remove:
  assumes "finite A"
  shows "fold f z (insert x A) = f x (fold f z (A - {x}))"
proof -
  from `finite A` have "finite (insert x A)" by auto
  moreover have "x \<in> insert x A" by auto
  ultimately have "fold f z (insert x A) = f x (fold f z (insert x A - {x}))"
    by (rule fold_rec)
  then show ?thesis by simp
qed

end

text{* A simplified version for idempotent functions: *}

locale comp_fun_idem = comp_fun_commute +
  assumes comp_fun_idem: "f x o f x = f x"
begin

lemma fun_left_idem: "f x (f x z) = f x z"
  using comp_fun_idem by (simp add: fun_eq_iff)

lemma fold_insert_idem:
  assumes fin: "finite A"
  shows "fold f z (insert x A) = f x (fold f z A)"
proof cases
  assume "x \<in> A"
  then obtain B where "A = insert x B" and "x \<notin> B" by (rule set_insert)
  then show ?thesis using assms by (simp add:fun_left_idem)
next
  assume "x \<notin> A" then show ?thesis using assms by simp
qed

declare fold_insert[simp del] fold_insert_idem[simp]

lemma fold_insert_idem2:
  "finite A \<Longrightarrow> fold f z (insert x A) = fold f (f x z) A"
by(simp add:fold_fun_comm)

end


subsubsection {* Expressing set operations via @{const fold} *}

lemma (in comp_fun_commute) comp_comp_fun_commute:
  "comp_fun_commute (f \<circ> g)"
proof
qed (simp_all add: comp_fun_commute)

lemma (in comp_fun_idem) comp_comp_fun_idem:
  "comp_fun_idem (f \<circ> g)"
  by (rule comp_fun_idem.intro, rule comp_comp_fun_commute, unfold_locales)
    (simp_all add: comp_fun_idem)

lemma comp_fun_idem_insert:
  "comp_fun_idem insert"
proof
qed auto

lemma comp_fun_idem_remove:
  "comp_fun_idem Set.remove"
proof
qed auto

lemma (in semilattice_inf) comp_fun_idem_inf:
  "comp_fun_idem inf"
proof
qed (auto simp add: inf_left_commute)

lemma (in semilattice_sup) comp_fun_idem_sup:
  "comp_fun_idem sup"
proof
qed (auto simp add: sup_left_commute)

lemma union_fold_insert:
  assumes "finite A"
  shows "A \<union> B = fold insert B A"
proof -
  interpret comp_fun_idem insert by (fact comp_fun_idem_insert)
  from `finite A` show ?thesis by (induct A arbitrary: B) simp_all
qed

lemma minus_fold_remove:
  assumes "finite A"
  shows "B - A = fold Set.remove B A"
proof -
  interpret comp_fun_idem Set.remove by (fact comp_fun_idem_remove)
  from `finite A` have "fold Set.remove B A = B - A" by (induct A arbitrary: B) auto
  then show ?thesis ..
qed

context complete_lattice
begin

lemma inf_Inf_fold_inf:
  assumes "finite A"
  shows "inf B (Inf A) = fold inf B A"
proof -
  interpret comp_fun_idem inf by (fact comp_fun_idem_inf)
  from `finite A` show ?thesis by (induct A arbitrary: B)
    (simp_all add: inf_commute fold_fun_comm)
qed

lemma sup_Sup_fold_sup:
  assumes "finite A"
  shows "sup B (Sup A) = fold sup B A"
proof -
  interpret comp_fun_idem sup by (fact comp_fun_idem_sup)
  from `finite A` show ?thesis by (induct A arbitrary: B)
    (simp_all add: sup_commute fold_fun_comm)
qed

lemma Inf_fold_inf:
  assumes "finite A"
  shows "Inf A = fold inf top A"
  using assms inf_Inf_fold_inf [of A top] by (simp add: inf_absorb2)

lemma Sup_fold_sup:
  assumes "finite A"
  shows "Sup A = fold sup bot A"
  using assms sup_Sup_fold_sup [of A bot] by (simp add: sup_absorb2)

lemma inf_INF_fold_inf:
  assumes "finite A"
  shows "inf B (INFI A f) = fold (inf \<circ> f) B A" (is "?inf = ?fold") 
proof (rule sym)
  interpret comp_fun_idem inf by (fact comp_fun_idem_inf)
  interpret comp_fun_idem "inf \<circ> f" by (fact comp_comp_fun_idem)
  from `finite A` show "?fold = ?inf"
    by (induct A arbitrary: B)
      (simp_all add: INF_def inf_left_commute)
qed

lemma sup_SUP_fold_sup:
  assumes "finite A"
  shows "sup B (SUPR A f) = fold (sup \<circ> f) B A" (is "?sup = ?fold") 
proof (rule sym)
  interpret comp_fun_idem sup by (fact comp_fun_idem_sup)
  interpret comp_fun_idem "sup \<circ> f" by (fact comp_comp_fun_idem)
  from `finite A` show "?fold = ?sup"
    by (induct A arbitrary: B)
      (simp_all add: SUP_def sup_left_commute)
qed

lemma INF_fold_inf:
  assumes "finite A"
  shows "INFI A f = fold (inf \<circ> f) top A"
  using assms inf_INF_fold_inf [of A top] by simp

lemma SUP_fold_sup:
  assumes "finite A"
  shows "SUPR A f = fold (sup \<circ> f) bot A"
  using assms sup_SUP_fold_sup [of A bot] by simp

end


subsection {* The derived combinator @{text fold_image} *}

definition fold_image :: "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b"
  where "fold_image f g = fold (\<lambda>x y. f (g x) y)"

lemma fold_image_empty[simp]: "fold_image f g z {} = z"
  by (simp add:fold_image_def)

context ab_semigroup_mult
begin

lemma fold_image_insert[simp]:
  assumes "finite A" and "a \<notin> A"
  shows "fold_image times g z (insert a A) = g a * (fold_image times g z A)"
proof -
  interpret comp_fun_commute "%x y. (g x) * y"
    by default (simp add: fun_eq_iff mult_ac)
  from assms show ?thesis by (simp add: fold_image_def)
qed

lemma fold_image_reindex:
  assumes "finite A"
  shows "inj_on h A \<Longrightarrow> fold_image times g z (h ` A) = fold_image times (g \<circ> h) z A"
  using assms by induct auto

lemma fold_image_cong:
  assumes "finite A" and g_h: "\<And>x. x\<in>A \<Longrightarrow> g x = h x"
  shows "fold_image times g z A = fold_image times h z A"
proof -
  from `finite A`
  have "\<And>C. C <= A --> (ALL x:C. g x = h x) --> fold_image times g z C = fold_image times h z C"
  proof (induct arbitrary: C)
    case empty then show ?case by simp
  next
    case (insert x F) then show ?case apply -
    apply (simp add: subset_insert_iff, clarify)
    apply (subgoal_tac "finite C")
      prefer 2 apply (blast dest: finite_subset [rotated])
    apply (subgoal_tac "C = insert x (C - {x})")
      prefer 2 apply blast
    apply (erule ssubst)
    apply (simp add: Ball_def del: insert_Diff_single)
    done
  qed
  with g_h show ?thesis by simp
qed

end

context comm_monoid_mult
begin

lemma fold_image_1:
  "finite S \<Longrightarrow> (\<forall>x\<in>S. f x = 1) \<Longrightarrow> fold_image op * f 1 S = 1"
  apply (induct rule: finite_induct)
  apply simp by auto

lemma fold_image_Un_Int:
  "finite A ==> finite B ==>
    fold_image times g 1 A * fold_image times g 1 B =
    fold_image times g 1 (A Un B) * fold_image times g 1 (A Int B)"
  apply (induct rule: finite_induct)
by (induct set: finite) 
   (auto simp add: mult_ac insert_absorb Int_insert_left)

lemma fold_image_Un_one:
  assumes fS: "finite S" and fT: "finite T"
  and I0: "\<forall>x \<in> S\<inter>T. f x = 1"
  shows "fold_image (op *) f 1 (S \<union> T) = fold_image (op *) f 1 S * fold_image (op *) f 1 T"
proof-
  have "fold_image op * f 1 (S \<inter> T) = 1" 
    apply (rule fold_image_1)
    using fS fT I0 by auto 
  with fold_image_Un_Int[OF fS fT] show ?thesis by simp
qed

corollary fold_Un_disjoint:
  "finite A ==> finite B ==> A Int B = {} ==>
   fold_image times g 1 (A Un B) =
   fold_image times g 1 A * fold_image times g 1 B"
by (simp add: fold_image_Un_Int)

lemma fold_image_UN_disjoint:
  "\<lbrakk> finite I; ALL i:I. finite (A i);
     ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {} \<rbrakk>
   \<Longrightarrow> fold_image times g 1 (UNION I A) =
       fold_image times (%i. fold_image times g 1 (A i)) 1 I"
apply (induct rule: finite_induct)
apply simp
apply atomize
apply (subgoal_tac "ALL i:F. x \<noteq> i")
 prefer 2 apply blast
apply (subgoal_tac "A x Int UNION F A = {}")
 prefer 2 apply blast
apply (simp add: fold_Un_disjoint)
done

lemma fold_image_Sigma: "finite A ==> ALL x:A. finite (B x) ==>
  fold_image times (%x. fold_image times (g x) 1 (B x)) 1 A =
  fold_image times (split g) 1 (SIGMA x:A. B x)"
apply (subst Sigma_def)
apply (subst fold_image_UN_disjoint, assumption, simp)
 apply blast
apply (erule fold_image_cong)
apply (subst fold_image_UN_disjoint, simp, simp)
 apply blast
apply simp
done

lemma fold_image_distrib: "finite A \<Longrightarrow>
   fold_image times (%x. g x * h x) 1 A =
   fold_image times g 1 A *  fold_image times h 1 A"
by (erule finite_induct) (simp_all add: mult_ac)

lemma fold_image_related: 
  assumes Re: "R e e" 
  and Rop: "\<forall>x1 y1 x2 y2. R x1 x2 \<and> R y1 y2 \<longrightarrow> R (x1 * y1) (x2 * y2)" 
  and fS: "finite S" and Rfg: "\<forall>x\<in>S. R (h x) (g x)"
  shows "R (fold_image (op *) h e S) (fold_image (op *) g e S)"
  using fS by (rule finite_subset_induct) (insert assms, auto)

lemma  fold_image_eq_general:
  assumes fS: "finite S"
  and h: "\<forall>y\<in>S'. \<exists>!x. x\<in> S \<and> h(x) = y" 
  and f12:  "\<forall>x\<in>S. h x \<in> S' \<and> f2(h x) = f1 x"
  shows "fold_image (op *) f1 e S = fold_image (op *) f2 e S'"
proof-
  from h f12 have hS: "h ` S = S'" by auto
  {fix x y assume H: "x \<in> S" "y \<in> S" "h x = h y"
    from f12 h H  have "x = y" by auto }
  hence hinj: "inj_on h S" unfolding inj_on_def Ex1_def by blast
  from f12 have th: "\<And>x. x \<in> S \<Longrightarrow> (f2 \<circ> h) x = f1 x" by auto 
  from hS have "fold_image (op *) f2 e S' = fold_image (op *) f2 e (h ` S)" by simp
  also have "\<dots> = fold_image (op *) (f2 o h) e S" 
    using fold_image_reindex[OF fS hinj, of f2 e] .
  also have "\<dots> = fold_image (op *) f1 e S " using th fold_image_cong[OF fS, of "f2 o h" f1 e]
    by blast
  finally show ?thesis ..
qed

lemma fold_image_eq_general_inverses:
  assumes fS: "finite S" 
  and kh: "\<And>y. y \<in> T \<Longrightarrow> k y \<in> S \<and> h (k y) = y"
  and hk: "\<And>x. x \<in> S \<Longrightarrow> h x \<in> T \<and> k (h x) = x  \<and> g (h x) = f x"
  shows "fold_image (op *) f e S = fold_image (op *) g e T"
  (* metis solves it, but not yet available here *)
  apply (rule fold_image_eq_general[OF fS, of T h g f e])
  apply (rule ballI)
  apply (frule kh)
  apply (rule ex1I[])
  apply blast
  apply clarsimp
  apply (drule hk) apply simp
  apply (rule sym)
  apply (erule conjunct1[OF conjunct2[OF hk]])
  apply (rule ballI)
  apply (drule  hk)
  apply blast
  done

end


subsection {* A fold functional for non-empty sets *}

text{* Does not require start value. *}

inductive
  fold1Set :: "('a => 'a => 'a) => 'a set => 'a => bool"
  for f :: "'a => 'a => 'a"
where
  fold1Set_insertI [intro]:
   "\<lbrakk> fold_graph f a A x; a \<notin> A \<rbrakk> \<Longrightarrow> fold1Set f (insert a A) x"

definition fold1 :: "('a => 'a => 'a) => 'a set => 'a" where
  "fold1 f A == THE x. fold1Set f A x"

lemma fold1Set_nonempty:
  "fold1Set f A x \<Longrightarrow> A \<noteq> {}"
by(erule fold1Set.cases, simp_all)

inductive_cases empty_fold1SetE [elim!]: "fold1Set f {} x"

inductive_cases insert_fold1SetE [elim!]: "fold1Set f (insert a X) x"


lemma fold1Set_sing [iff]: "(fold1Set f {a} b) = (a = b)"
by (blast elim: fold_graph.cases)

lemma fold1_singleton [simp]: "fold1 f {a} = a"
by (unfold fold1_def) blast

lemma finite_nonempty_imp_fold1Set:
  "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> EX x. fold1Set f A x"
apply (induct A rule: finite_induct)
apply (auto dest: finite_imp_fold_graph [of _ f])
done

text{*First, some lemmas about @{const fold_graph}.*}

context ab_semigroup_mult
begin

lemma comp_fun_commute: "comp_fun_commute (op *)"
  by default (simp add: fun_eq_iff mult_ac)

lemma fold_graph_insert_swap:
assumes fold: "fold_graph times (b::'a) A y" and "b \<notin> A"
shows "fold_graph times z (insert b A) (z * y)"
proof -
  interpret comp_fun_commute "op *::'a \<Rightarrow> 'a \<Rightarrow> 'a" by (rule comp_fun_commute)
from assms show ?thesis
proof (induct rule: fold_graph.induct)
  case emptyI show ?case by (subst mult_commute [of z b], fast)
next
  case (insertI x A y)
    have "fold_graph times z (insert x (insert b A)) (x * (z * y))"
      using insertI by force  --{*how does @{term id} get unfolded?*}
    thus ?case by (simp add: insert_commute mult_ac)
qed
qed

lemma fold_graph_permute_diff:
assumes fold: "fold_graph times b A x"
shows "!!a. \<lbrakk>a \<in> A; b \<notin> A\<rbrakk> \<Longrightarrow> fold_graph times a (insert b (A-{a})) x"
using fold
proof (induct rule: fold_graph.induct)
  case emptyI thus ?case by simp
next
  case (insertI x A y)
  have "a = x \<or> a \<in> A" using insertI by simp
  thus ?case
  proof
    assume "a = x"
    with insertI show ?thesis
      by (simp add: id_def [symmetric], blast intro: fold_graph_insert_swap)
  next
    assume ainA: "a \<in> A"
    hence "fold_graph times a (insert x (insert b (A - {a}))) (x * y)"
      using insertI by force
    moreover
    have "insert x (insert b (A - {a})) = insert b (insert x A - {a})"
      using ainA insertI by blast
    ultimately show ?thesis by simp
  qed
qed

lemma fold1_eq_fold:
assumes "finite A" "a \<notin> A" shows "fold1 times (insert a A) = fold times a A"
proof -
  interpret comp_fun_commute "op *::'a \<Rightarrow> 'a \<Rightarrow> 'a" by (rule comp_fun_commute)
  from assms show ?thesis
apply (simp add: fold1_def fold_def)
apply (rule the_equality)
apply (best intro: fold_graph_determ theI dest: finite_imp_fold_graph [of _ times])
apply (rule sym, clarify)
apply (case_tac "Aa=A")
 apply (best intro: fold_graph_determ)
apply (subgoal_tac "fold_graph times a A x")
 apply (best intro: fold_graph_determ)
apply (subgoal_tac "insert aa (Aa - {a}) = A")
 prefer 2 apply (blast elim: equalityE)
apply (auto dest: fold_graph_permute_diff [where a=a])
done
qed

lemma nonempty_iff: "(A \<noteq> {}) = (\<exists>x B. A = insert x B & x \<notin> B)"
apply safe
 apply simp
 apply (drule_tac x=x in spec)
 apply (drule_tac x="A-{x}" in spec, auto)
done

lemma fold1_insert:
  assumes nonempty: "A \<noteq> {}" and A: "finite A" "x \<notin> A"
  shows "fold1 times (insert x A) = x * fold1 times A"
proof -
  interpret comp_fun_commute "op *::'a \<Rightarrow> 'a \<Rightarrow> 'a" by (rule comp_fun_commute)
  from nonempty obtain a A' where "A = insert a A' & a ~: A'"
    by (auto simp add: nonempty_iff)
  with A show ?thesis
    by (simp add: insert_commute [of x] fold1_eq_fold eq_commute)
qed

end

context ab_semigroup_idem_mult
begin

lemma comp_fun_idem: "comp_fun_idem (op *)"
  by default (simp_all add: fun_eq_iff mult_left_commute)

lemma fold1_insert_idem [simp]:
  assumes nonempty: "A \<noteq> {}" and A: "finite A" 
  shows "fold1 times (insert x A) = x * fold1 times A"
proof -
  interpret comp_fun_idem "op *::'a \<Rightarrow> 'a \<Rightarrow> 'a"
    by (rule comp_fun_idem)
  from nonempty obtain a A' where A': "A = insert a A' & a ~: A'"
    by (auto simp add: nonempty_iff)
  show ?thesis
  proof cases
    assume a: "a = x"
    show ?thesis
    proof cases
      assume "A' = {}"
      with A' a show ?thesis by simp
    next
      assume "A' \<noteq> {}"
      with A A' a show ?thesis
        by (simp add: fold1_insert mult_assoc [symmetric])
    qed
  next
    assume "a \<noteq> x"
    with A A' show ?thesis
      by (simp add: insert_commute fold1_eq_fold)
  qed
qed

lemma hom_fold1_commute:
assumes hom: "!!x y. h (x * y) = h x * h y"
and N: "finite N" "N \<noteq> {}" shows "h (fold1 times N) = fold1 times (h ` N)"
using N
proof (induct rule: finite_ne_induct)
  case singleton thus ?case by simp
next
  case (insert n N)
  then have "h (fold1 times (insert n N)) = h (n * fold1 times N)" by simp
  also have "\<dots> = h n * h (fold1 times N)" by(rule hom)
  also have "h (fold1 times N) = fold1 times (h ` N)" by(rule insert)
  also have "times (h n) \<dots> = fold1 times (insert (h n) (h ` N))"
    using insert by(simp)
  also have "insert (h n) (h ` N) = h ` insert n N" by simp
  finally show ?case .
qed

lemma fold1_eq_fold_idem:
  assumes "finite A"
  shows "fold1 times (insert a A) = fold times a A"
proof (cases "a \<in> A")
  case False
  with assms show ?thesis by (simp add: fold1_eq_fold)
next
  interpret comp_fun_idem times by (fact comp_fun_idem)
  case True then obtain b B
    where A: "A = insert a B" and "a \<notin> B" by (rule set_insert)
  with assms have "finite B" by auto
  then have "fold times a (insert a B) = fold times (a * a) B"
    using `a \<notin> B` by (rule fold_insert2)
  then show ?thesis
    using `a \<notin> B` `finite B` by (simp add: fold1_eq_fold A)
qed

end


text{* Now the recursion rules for definitions: *}

lemma fold1_singleton_def: "g = fold1 f \<Longrightarrow> g {a} = a"
by simp

lemma (in ab_semigroup_mult) fold1_insert_def:
  "\<lbrakk> g = fold1 times; finite A; x \<notin> A; A \<noteq> {} \<rbrakk> \<Longrightarrow> g (insert x A) = x * g A"
by (simp add:fold1_insert)

lemma (in ab_semigroup_idem_mult) fold1_insert_idem_def:
  "\<lbrakk> g = fold1 times; finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> g (insert x A) = x * g A"
by simp

subsubsection{* Determinacy for @{term fold1Set} *}

(*Not actually used!!*)
(*
context ab_semigroup_mult
begin

lemma fold_graph_permute:
  "[|fold_graph times id b (insert a A) x; a \<notin> A; b \<notin> A|]
   ==> fold_graph times id a (insert b A) x"
apply (cases "a=b") 
apply (auto dest: fold_graph_permute_diff) 
done

lemma fold1Set_determ:
  "fold1Set times A x ==> fold1Set times A y ==> y = x"
proof (clarify elim!: fold1Set.cases)
  fix A x B y a b
  assume Ax: "fold_graph times id a A x"
  assume By: "fold_graph times id b B y"
  assume anotA:  "a \<notin> A"
  assume bnotB:  "b \<notin> B"
  assume eq: "insert a A = insert b B"
  show "y=x"
  proof cases
    assume same: "a=b"
    hence "A=B" using anotA bnotB eq by (blast elim!: equalityE)
    thus ?thesis using Ax By same by (blast intro: fold_graph_determ)
  next
    assume diff: "a\<noteq>b"
    let ?D = "B - {a}"
    have B: "B = insert a ?D" and A: "A = insert b ?D"
     and aB: "a \<in> B" and bA: "b \<in> A"
      using eq anotA bnotB diff by (blast elim!:equalityE)+
    with aB bnotB By
    have "fold_graph times id a (insert b ?D) y" 
      by (auto intro: fold_graph_permute simp add: insert_absorb)
    moreover
    have "fold_graph times id a (insert b ?D) x"
      by (simp add: A [symmetric] Ax) 
    ultimately show ?thesis by (blast intro: fold_graph_determ) 
  qed
qed

lemma fold1Set_equality: "fold1Set times A y ==> fold1 times A = y"
  by (unfold fold1_def) (blast intro: fold1Set_determ)

end
*)

declare
  empty_fold_graphE [rule del]  fold_graph.intros [rule del]
  empty_fold1SetE [rule del]  insert_fold1SetE [rule del]
  -- {* No more proofs involve these relations. *}

subsubsection {* Lemmas about @{text fold1} *}

context ab_semigroup_mult
begin

lemma fold1_Un:
assumes A: "finite A" "A \<noteq> {}"
shows "finite B \<Longrightarrow> B \<noteq> {} \<Longrightarrow> A Int B = {} \<Longrightarrow>
       fold1 times (A Un B) = fold1 times A * fold1 times B"
using A by (induct rule: finite_ne_induct)
  (simp_all add: fold1_insert mult_assoc)

lemma fold1_in:
  assumes A: "finite (A)" "A \<noteq> {}" and elem: "\<And>x y. x * y \<in> {x,y}"
  shows "fold1 times A \<in> A"
using A
proof (induct rule:finite_ne_induct)
  case singleton thus ?case by simp
next
  case insert thus ?case using elem by (force simp add:fold1_insert)
qed

end

lemma (in ab_semigroup_idem_mult) fold1_Un2:
assumes A: "finite A" "A \<noteq> {}"
shows "finite B \<Longrightarrow> B \<noteq> {} \<Longrightarrow>
       fold1 times (A Un B) = fold1 times A * fold1 times B"
using A
proof(induct rule:finite_ne_induct)
  case singleton thus ?case by simp
next
  case insert thus ?case by (simp add: mult_assoc)
qed


subsection {* Locales as mini-packages for fold operations *}

subsubsection {* The natural case *}

locale folding =
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes F :: "'a set \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes comp_fun_commute: "f y \<circ> f x = f x \<circ> f y"
  assumes eq_fold: "finite A \<Longrightarrow> F A s = fold f s A"
begin

lemma empty [simp]:
  "F {} = id"
  by (simp add: eq_fold fun_eq_iff)

lemma insert [simp]:
  assumes "finite A" and "x \<notin> A"
  shows "F (insert x A) = F A \<circ> f x"
proof -
  interpret comp_fun_commute f
    by default (insert comp_fun_commute, simp add: fun_eq_iff)
  from fold_insert2 assms
  have "\<And>s. fold f s (insert x A) = fold f (f x s) A" .
  with `finite A` show ?thesis by (simp add: eq_fold fun_eq_iff)
qed

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "F A = F (A - {x}) \<circ> f x"
proof -
  from `x \<in> A` obtain B where A: "A = insert x B" and "x \<notin> B"
    by (auto dest: mk_disjoint_insert)
  moreover from `finite A` this have "finite B" by simp
  ultimately show ?thesis by simp
qed

lemma insert_remove:
  assumes "finite A"
  shows "F (insert x A) = F (A - {x}) \<circ> f x"
  using assms by (cases "x \<in> A") (simp_all add: remove insert_absorb)

lemma commute_left_comp:
  "f y \<circ> (f x \<circ> g) = f x \<circ> (f y \<circ> g)"
  by (simp add: o_assoc comp_fun_commute)

lemma comp_fun_commute':
  assumes "finite A"
  shows "f x \<circ> F A = F A \<circ> f x"
  using assms by (induct A)
    (simp, simp del: o_apply add: o_assoc, simp del: o_apply add: o_assoc [symmetric] comp_fun_commute)

lemma commute_left_comp':
  assumes "finite A"
  shows "f x \<circ> (F A \<circ> g) = F A \<circ> (f x \<circ> g)"
  using assms by (simp add: o_assoc comp_fun_commute')

lemma comp_fun_commute'':
  assumes "finite A" and "finite B"
  shows "F B \<circ> F A = F A \<circ> F B"
  using assms by (induct A)
    (simp_all add: o_assoc, simp add: o_assoc [symmetric] comp_fun_commute')

lemma commute_left_comp'':
  assumes "finite A" and "finite B"
  shows "F B \<circ> (F A \<circ> g) = F A \<circ> (F B \<circ> g)"
  using assms by (simp add: o_assoc comp_fun_commute'')

lemmas comp_fun_commutes = o_assoc [symmetric] comp_fun_commute commute_left_comp
  comp_fun_commute' commute_left_comp' comp_fun_commute'' commute_left_comp''

lemma union_inter:
  assumes "finite A" and "finite B"
  shows "F (A \<union> B) \<circ> F (A \<inter> B) = F A \<circ> F B"
  using assms by (induct A)
    (simp_all del: o_apply add: insert_absorb Int_insert_left comp_fun_commutes,
      simp add: o_assoc)

lemma union:
  assumes "finite A" and "finite B"
  and "A \<inter> B = {}"
  shows "F (A \<union> B) = F A \<circ> F B"
proof -
  from union_inter `finite A` `finite B` have "F (A \<union> B) \<circ> F (A \<inter> B) = F A \<circ> F B" .
  with `A \<inter> B = {}` show ?thesis by simp
qed

end


subsubsection {* The natural case with idempotency *}

locale folding_idem = folding +
  assumes idem_comp: "f x \<circ> f x = f x"
begin

lemma idem_left_comp:
  "f x \<circ> (f x \<circ> g) = f x \<circ> g"
  by (simp add: o_assoc idem_comp)

lemma in_comp_idem:
  assumes "finite A" and "x \<in> A"
  shows "F A \<circ> f x = F A"
using assms by (induct A)
  (auto simp add: comp_fun_commutes idem_comp, simp add: commute_left_comp' [symmetric] comp_fun_commute')

lemma subset_comp_idem:
  assumes "finite A" and "B \<subseteq> A"
  shows "F A \<circ> F B = F A"
proof -
  from assms have "finite B" by (blast dest: finite_subset)
  then show ?thesis using `B \<subseteq> A` by (induct B)
    (simp_all add: o_assoc in_comp_idem `finite A`)
qed

declare insert [simp del]

lemma insert_idem [simp]:
  assumes "finite A"
  shows "F (insert x A) = F A \<circ> f x"
  using assms by (cases "x \<in> A") (simp_all add: insert in_comp_idem insert_absorb)

lemma union_idem:
  assumes "finite A" and "finite B"
  shows "F (A \<union> B) = F A \<circ> F B"
proof -
  from assms have "finite (A \<union> B)" and "A \<inter> B \<subseteq> A \<union> B" by auto
  then have "F (A \<union> B) \<circ> F (A \<inter> B) = F (A \<union> B)" by (rule subset_comp_idem)
  with assms show ?thesis by (simp add: union_inter)
qed

end


subsubsection {* The image case with fixed function *}

no_notation times (infixl "*" 70)
no_notation Groups.one ("1")

locale folding_image_simple = comm_monoid +
  fixes g :: "('b \<Rightarrow> 'a)"
  fixes F :: "'b set \<Rightarrow> 'a"
  assumes eq_fold_g: "finite A \<Longrightarrow> F A = fold_image f g 1 A"
begin

lemma empty [simp]:
  "F {} = 1"
  by (simp add: eq_fold_g)

lemma insert [simp]:
  assumes "finite A" and "x \<notin> A"
  shows "F (insert x A) = g x * F A"
proof -
  interpret comp_fun_commute "%x y. (g x) * y"
    by default (simp add: ac_simps fun_eq_iff)
  from assms have "fold_image (op *) g 1 (insert x A) = g x * fold_image (op *) g 1 A"
    by (simp add: fold_image_def)
  with `finite A` show ?thesis by (simp add: eq_fold_g)
qed

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "F A = g x * F (A - {x})"
proof -
  from `x \<in> A` obtain B where A: "A = insert x B" and "x \<notin> B"
    by (auto dest: mk_disjoint_insert)
  moreover from `finite A` this have "finite B" by simp
  ultimately show ?thesis by simp
qed

lemma insert_remove:
  assumes "finite A"
  shows "F (insert x A) = g x * F (A - {x})"
  using assms by (cases "x \<in> A") (simp_all add: remove insert_absorb)

lemma neutral:
  assumes "finite A" and "\<forall>x\<in>A. g x = 1"
  shows "F A = 1"
  using assms by (induct A) simp_all

lemma union_inter:
  assumes "finite A" and "finite B"
  shows "F (A \<union> B) * F (A \<inter> B) = F A * F B"
using assms proof (induct A)
  case empty then show ?case by simp
next
  case (insert x A) then show ?case
    by (auto simp add: insert_absorb Int_insert_left commute [of _ "g x"] assoc left_commute)
qed

corollary union_inter_neutral:
  assumes "finite A" and "finite B"
  and I0: "\<forall>x \<in> A\<inter>B. g x = 1"
  shows "F (A \<union> B) = F A * F B"
  using assms by (simp add: union_inter [symmetric] neutral)

corollary union_disjoint:
  assumes "finite A" and "finite B"
  assumes "A \<inter> B = {}"
  shows "F (A \<union> B) = F A * F B"
  using assms by (simp add: union_inter_neutral)

end


subsubsection {* The image case with flexible function *}

locale folding_image = comm_monoid +
  fixes F :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'a"
  assumes eq_fold: "\<And>g. finite A \<Longrightarrow> F g A = fold_image f g 1 A"

sublocale folding_image < folding_image_simple "op *" 1 g "F g" proof
qed (fact eq_fold)

context folding_image
begin

lemma reindex: (* FIXME polymorhism *)
  assumes "finite A" and "inj_on h A"
  shows "F g (h ` A) = F (g \<circ> h) A"
  using assms by (induct A) auto

lemma cong:
  assumes "finite A" and "\<And>x. x \<in> A \<Longrightarrow> g x = h x"
  shows "F g A = F h A"
proof -
  from assms have "ALL C. C <= A --> (ALL x:C. g x = h x) --> F g C = F h C"
  apply - apply (erule finite_induct) apply simp
  apply (simp add: subset_insert_iff, clarify)
  apply (subgoal_tac "finite C")
  prefer 2 apply (blast dest: finite_subset [rotated])
  apply (subgoal_tac "C = insert x (C - {x})")
  prefer 2 apply blast
  apply (erule ssubst)
  apply (drule spec)
  apply (erule (1) notE impE)
  apply (simp add: Ball_def del: insert_Diff_single)
  done
  with assms show ?thesis by simp
qed

lemma UNION_disjoint:
  assumes "finite I" and "\<forall>i\<in>I. finite (A i)"
  and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
  shows "F g (UNION I A) = F (F g \<circ> A) I"
apply (insert assms)
apply (induct rule: finite_induct)
apply simp
apply atomize
apply (subgoal_tac "\<forall>i\<in>Fa. x \<noteq> i")
 prefer 2 apply blast
apply (subgoal_tac "A x Int UNION Fa A = {}")
 prefer 2 apply blast
apply (simp add: union_disjoint)
done

lemma distrib:
  assumes "finite A"
  shows "F (\<lambda>x. g x * h x) A = F g A * F h A"
  using assms by (rule finite_induct) (simp_all add: assoc commute left_commute)

lemma related: 
  assumes Re: "R 1 1" 
  and Rop: "\<forall>x1 y1 x2 y2. R x1 x2 \<and> R y1 y2 \<longrightarrow> R (x1 * y1) (x2 * y2)" 
  and fS: "finite S" and Rfg: "\<forall>x\<in>S. R (h x) (g x)"
  shows "R (F h S) (F g S)"
  using fS by (rule finite_subset_induct) (insert assms, auto)

lemma eq_general:
  assumes fS: "finite S"
  and h: "\<forall>y\<in>S'. \<exists>!x. x \<in> S \<and> h x = y" 
  and f12:  "\<forall>x\<in>S. h x \<in> S' \<and> f2 (h x) = f1 x"
  shows "F f1 S = F f2 S'"
proof-
  from h f12 have hS: "h ` S = S'" by blast
  {fix x y assume H: "x \<in> S" "y \<in> S" "h x = h y"
    from f12 h H  have "x = y" by auto }
  hence hinj: "inj_on h S" unfolding inj_on_def Ex1_def by blast
  from f12 have th: "\<And>x. x \<in> S \<Longrightarrow> (f2 \<circ> h) x = f1 x" by auto 
  from hS have "F f2 S' = F f2 (h ` S)" by simp
  also have "\<dots> = F (f2 o h) S" using reindex [OF fS hinj, of f2] .
  also have "\<dots> = F f1 S " using th cong [OF fS, of "f2 o h" f1]
    by blast
  finally show ?thesis ..
qed

lemma eq_general_inverses:
  assumes fS: "finite S" 
  and kh: "\<And>y. y \<in> T \<Longrightarrow> k y \<in> S \<and> h (k y) = y"
  and hk: "\<And>x. x \<in> S \<Longrightarrow> h x \<in> T \<and> k (h x) = x \<and> g (h x) = j x"
  shows "F j S = F g T"
  (* metis solves it, but not yet available here *)
  apply (rule eq_general [OF fS, of T h g j])
  apply (rule ballI)
  apply (frule kh)
  apply (rule ex1I[])
  apply blast
  apply clarsimp
  apply (drule hk) apply simp
  apply (rule sym)
  apply (erule conjunct1[OF conjunct2[OF hk]])
  apply (rule ballI)
  apply (drule hk)
  apply blast
  done

end


subsubsection {* The image case with fixed function and idempotency *}

locale folding_image_simple_idem = folding_image_simple +
  assumes idem: "x * x = x"

sublocale folding_image_simple_idem < semilattice proof
qed (fact idem)

context folding_image_simple_idem
begin

lemma in_idem:
  assumes "finite A" and "x \<in> A"
  shows "g x * F A = F A"
  using assms by (induct A) (auto simp add: left_commute)

lemma subset_idem:
  assumes "finite A" and "B \<subseteq> A"
  shows "F B * F A = F A"
proof -
  from assms have "finite B" by (blast dest: finite_subset)
  then show ?thesis using `B \<subseteq> A` by (induct B)
    (auto simp add: assoc in_idem `finite A`)
qed

declare insert [simp del]

lemma insert_idem [simp]:
  assumes "finite A"
  shows "F (insert x A) = g x * F A"
  using assms by (cases "x \<in> A") (simp_all add: insert in_idem insert_absorb)

lemma union_idem:
  assumes "finite A" and "finite B"
  shows "F (A \<union> B) = F A * F B"
proof -
  from assms have "finite (A \<union> B)" and "A \<inter> B \<subseteq> A \<union> B" by auto
  then have "F (A \<inter> B) * F (A \<union> B) = F (A \<union> B)" by (rule subset_idem)
  with assms show ?thesis by (simp add: union_inter [of A B, symmetric] commute)
qed

end


subsubsection {* The image case with flexible function and idempotency *}

locale folding_image_idem = folding_image +
  assumes idem: "x * x = x"

sublocale folding_image_idem < folding_image_simple_idem "op *" 1 g "F g" proof
qed (fact idem)


subsubsection {* The neutral-less case *}

locale folding_one = abel_semigroup +
  fixes F :: "'a set \<Rightarrow> 'a"
  assumes eq_fold: "finite A \<Longrightarrow> F A = fold1 f A"
begin

lemma singleton [simp]:
  "F {x} = x"
  by (simp add: eq_fold)

lemma eq_fold':
  assumes "finite A" and "x \<notin> A"
  shows "F (insert x A) = fold (op *) x A"
proof -
  interpret ab_semigroup_mult "op *" by default (simp_all add: ac_simps)
  from assms show ?thesis by (simp add: eq_fold fold1_eq_fold)
qed

lemma insert [simp]:
  assumes "finite A" and "x \<notin> A" and "A \<noteq> {}"
  shows "F (insert x A) = x * F A"
proof -
  from `A \<noteq> {}` obtain b where "b \<in> A" by blast
  then obtain B where *: "A = insert b B" "b \<notin> B" by (blast dest: mk_disjoint_insert)
  with `finite A` have "finite B" by simp
  interpret fold: folding "op *" "\<lambda>a b. fold (op *) b a" proof
  qed (simp_all add: fun_eq_iff ac_simps)
  thm fold.comp_fun_commute' [of B b, simplified fun_eq_iff, simplified]
  from `finite B` fold.comp_fun_commute' [of B x]
    have "op * x \<circ> (\<lambda>b. fold op * b B) = (\<lambda>b. fold op * b B) \<circ> op * x" by simp
  then have A: "x * fold op * b B = fold op * (b * x) B" by (simp add: fun_eq_iff commute)
  from `finite B` * fold.insert [of B b]
    have "(\<lambda>x. fold op * x (insert b B)) = (\<lambda>x. fold op * x B) \<circ> op * b" by simp
  then have B: "fold op * x (insert b B) = fold op * (b * x) B" by (simp add: fun_eq_iff)
  from A B assms * show ?thesis by (simp add: eq_fold' del: fold.insert)
qed

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "F A = (if A - {x} = {} then x else x * F (A - {x}))"
proof -
  from assms obtain B where "A = insert x B" and "x \<notin> B" by (blast dest: mk_disjoint_insert)
  with assms show ?thesis by simp
qed

lemma insert_remove:
  assumes "finite A"
  shows "F (insert x A) = (if A - {x} = {} then x else x * F (A - {x}))"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb remove)

lemma union_disjoint:
  assumes "finite A" "A \<noteq> {}" and "finite B" "B \<noteq> {}" and "A \<inter> B = {}"
  shows "F (A \<union> B) = F A * F B"
  using assms by (induct A rule: finite_ne_induct) (simp_all add: ac_simps)

lemma union_inter:
  assumes "finite A" and "finite B" and "A \<inter> B \<noteq> {}"
  shows "F (A \<union> B) * F (A \<inter> B) = F A * F B"
proof -
  from assms have "A \<noteq> {}" and "B \<noteq> {}" by auto
  from `finite A` `A \<noteq> {}` `A \<inter> B \<noteq> {}` show ?thesis proof (induct A rule: finite_ne_induct)
    case (singleton x) then show ?case by (simp add: insert_absorb ac_simps)
  next
    case (insert x A) show ?case proof (cases "x \<in> B")
      case True then have "B \<noteq> {}" by auto
      with insert True `finite B` show ?thesis by (cases "A \<inter> B = {}")
        (simp_all add: insert_absorb ac_simps union_disjoint)
    next
      case False with insert have "F (A \<union> B) * F (A \<inter> B) = F A * F B" by simp
      moreover from False `finite B` insert have "finite (A \<union> B)" "x \<notin> A \<union> B" "A \<union> B \<noteq> {}"
        by auto
      ultimately show ?thesis using False `finite A` `x \<notin> A` `A \<noteq> {}` by (simp add: assoc)
    qed
  qed
qed

lemma closed:
  assumes "finite A" "A \<noteq> {}" and elem: "\<And>x y. x * y \<in> {x, y}"
  shows "F A \<in> A"
using `finite A` `A \<noteq> {}` proof (induct rule: finite_ne_induct)
  case singleton then show ?case by simp
next
  case insert with elem show ?case by force
qed

end


subsubsection {* The neutral-less case with idempotency *}

locale folding_one_idem = folding_one +
  assumes idem: "x * x = x"

sublocale folding_one_idem < semilattice proof
qed (fact idem)

context folding_one_idem
begin

lemma in_idem:
  assumes "finite A" and "x \<in> A"
  shows "x * F A = F A"
proof -
  from assms have "A \<noteq> {}" by auto
  with `finite A` show ?thesis using `x \<in> A` by (induct A rule: finite_ne_induct) (auto simp add: ac_simps)
qed

lemma subset_idem:
  assumes "finite A" "B \<noteq> {}" and "B \<subseteq> A"
  shows "F B * F A = F A"
proof -
  from assms have "finite B" by (blast dest: finite_subset)
  then show ?thesis using `B \<noteq> {}` `B \<subseteq> A` by (induct B rule: finite_ne_induct)
    (simp_all add: assoc in_idem `finite A`)
qed

lemma eq_fold_idem':
  assumes "finite A"
  shows "F (insert a A) = fold (op *) a A"
proof -
  interpret ab_semigroup_idem_mult "op *" by default (simp_all add: ac_simps)
  from assms show ?thesis by (simp add: eq_fold fold1_eq_fold_idem)
qed

lemma insert_idem [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "F (insert x A) = x * F A"
proof (cases "x \<in> A")
  case False from `finite A` `x \<notin> A` `A \<noteq> {}` show ?thesis by (rule insert)
next
  case True
  from `finite A` `A \<noteq> {}` show ?thesis by (simp add: in_idem insert_absorb True)
qed
  
lemma union_idem:
  assumes "finite A" "A \<noteq> {}" and "finite B" "B \<noteq> {}"
  shows "F (A \<union> B) = F A * F B"
proof (cases "A \<inter> B = {}")
  case True with assms show ?thesis by (simp add: union_disjoint)
next
  case False
  from assms have "finite (A \<union> B)" and "A \<inter> B \<subseteq> A \<union> B" by auto
  with False have "F (A \<inter> B) * F (A \<union> B) = F (A \<union> B)" by (auto intro: subset_idem)
  with assms False show ?thesis by (simp add: union_inter [of A B, symmetric] commute)
qed

lemma hom_commute:
  assumes hom: "\<And>x y. h (x * y) = h x * h y"
  and N: "finite N" "N \<noteq> {}" shows "h (F N) = F (h ` N)"
using N proof (induct rule: finite_ne_induct)
  case singleton thus ?case by simp
next
  case (insert n N)
  then have "h (F (insert n N)) = h (n * F N)" by simp
  also have "\<dots> = h n * h (F N)" by (rule hom)
  also have "h (F N) = F (h ` N)" by(rule insert)
  also have "h n * \<dots> = F (insert (h n) (h ` N))"
    using insert by(simp)
  also have "insert (h n) (h ` N) = h ` insert n N" by simp
  finally show ?case .
qed

end

notation times (infixl "*" 70)
notation Groups.one ("1")


subsection {* Finite cardinality *}

text {* This definition, although traditional, is ugly to work with:
@{text "card A == LEAST n. EX f. A = {f i | i. i < n}"}.
But now that we have @{text fold_image} things are easy:
*}

definition card :: "'a set \<Rightarrow> nat" where
  "card A = (if finite A then fold_image (op +) (\<lambda>x. 1) 0 A else 0)"

interpretation card: folding_image_simple "op +" 0 "\<lambda>x. 1" card proof
qed (simp add: card_def)

lemma card_infinite [simp]:
  "\<not> finite A \<Longrightarrow> card A = 0"
  by (simp add: card_def)

lemma card_empty:
  "card {} = 0"
  by (fact card.empty)

lemma card_insert_disjoint:
  "finite A ==> x \<notin> A ==> card (insert x A) = Suc (card A)"
  by simp

lemma card_insert_if:
  "finite A ==> card (insert x A) = (if x \<in> A then card A else Suc (card A))"
  by auto (simp add: card.insert_remove card.remove)

lemma card_ge_0_finite:
  "card A > 0 \<Longrightarrow> finite A"
  by (rule ccontr) simp

lemma card_0_eq [simp, no_atp]:
  "finite A \<Longrightarrow> card A = 0 \<longleftrightarrow> A = {}"
  by (auto dest: mk_disjoint_insert)

lemma finite_UNIV_card_ge_0:
  "finite (UNIV :: 'a set) \<Longrightarrow> card (UNIV :: 'a set) > 0"
  by (rule ccontr) simp

lemma card_eq_0_iff:
  "card A = 0 \<longleftrightarrow> A = {} \<or> \<not> finite A"
  by auto

lemma card_gt_0_iff:
  "0 < card A \<longleftrightarrow> A \<noteq> {} \<and> finite A"
  by (simp add: neq0_conv [symmetric] card_eq_0_iff) 

lemma card_Suc_Diff1: "finite A ==> x: A ==> Suc (card (A - {x})) = card A"
apply(rule_tac t = A in insert_Diff [THEN subst], assumption)
apply(simp del:insert_Diff_single)
done

lemma card_Diff_singleton:
  "finite A ==> x: A ==> card (A - {x}) = card A - 1"
by (simp add: card_Suc_Diff1 [symmetric])

lemma card_Diff_singleton_if:
  "finite A ==> card (A - {x}) = (if x : A then card A - 1 else card A)"
by (simp add: card_Diff_singleton)

lemma card_Diff_insert[simp]:
assumes "finite A" and "a:A" and "a ~: B"
shows "card(A - insert a B) = card(A - B) - 1"
proof -
  have "A - insert a B = (A - B) - {a}" using assms by blast
  then show ?thesis using assms by(simp add:card_Diff_singleton)
qed

lemma card_insert: "finite A ==> card (insert x A) = Suc (card (A - {x}))"
by (simp add: card_insert_if card_Suc_Diff1 del:card_Diff_insert)

lemma card_insert_le: "finite A ==> card A <= card (insert x A)"
by (simp add: card_insert_if)

lemma card_Collect_less_nat[simp]: "card{i::nat. i < n} = n"
by (induct n) (simp_all add:less_Suc_eq Collect_disj_eq)

lemma card_Collect_le_nat[simp]: "card{i::nat. i <= n} = Suc n"
using card_Collect_less_nat[of "Suc n"] by(simp add: less_Suc_eq_le)

lemma card_mono:
  assumes "finite B" and "A \<subseteq> B"
  shows "card A \<le> card B"
proof -
  from assms have "finite A" by (auto intro: finite_subset)
  then show ?thesis using assms proof (induct A arbitrary: B)
    case empty then show ?case by simp
  next
    case (insert x A)
    then have "x \<in> B" by simp
    from insert have "A \<subseteq> B - {x}" and "finite (B - {x})" by auto
    with insert.hyps have "card A \<le> card (B - {x})" by auto
    with `finite A` `x \<notin> A` `finite B` `x \<in> B` show ?case by simp (simp only: card.remove)
  qed
qed

lemma card_seteq: "finite B ==> (!!A. A <= B ==> card B <= card A ==> A = B)"
apply (induct rule: finite_induct)
apply simp
apply clarify
apply (subgoal_tac "finite A & A - {x} <= F")
 prefer 2 apply (blast intro: finite_subset, atomize)
apply (drule_tac x = "A - {x}" in spec)
apply (simp add: card_Diff_singleton_if split add: split_if_asm)
apply (case_tac "card A", auto)
done

lemma psubset_card_mono: "finite B ==> A < B ==> card A < card B"
apply (simp add: psubset_eq linorder_not_le [symmetric])
apply (blast dest: card_seteq)
done

lemma card_Un_Int: "finite A ==> finite B
    ==> card A + card B = card (A Un B) + card (A Int B)"
  by (fact card.union_inter [symmetric])

lemma card_Un_disjoint: "finite A ==> finite B
    ==> A Int B = {} ==> card (A Un B) = card A + card B"
  by (fact card.union_disjoint)

lemma card_Diff_subset:
  assumes "finite B" and "B \<subseteq> A"
  shows "card (A - B) = card A - card B"
proof (cases "finite A")
  case False with assms show ?thesis by simp
next
  case True with assms show ?thesis by (induct B arbitrary: A) simp_all
qed

lemma card_Diff_subset_Int:
  assumes AB: "finite (A \<inter> B)" shows "card (A - B) = card A - card (A \<inter> B)"
proof -
  have "A - B = A - A \<inter> B" by auto
  thus ?thesis
    by (simp add: card_Diff_subset AB) 
qed

lemma diff_card_le_card_Diff:
assumes "finite B" shows "card A - card B \<le> card(A - B)"
proof-
  have "card A - card B \<le> card A - card (A \<inter> B)"
    using card_mono[OF assms Int_lower2, of A] by arith
  also have "\<dots> = card(A-B)" using assms by(simp add: card_Diff_subset_Int)
  finally show ?thesis .
qed

lemma card_Diff1_less: "finite A ==> x: A ==> card (A - {x}) < card A"
apply (rule Suc_less_SucD)
apply (simp add: card_Suc_Diff1 del:card_Diff_insert)
done

lemma card_Diff2_less:
  "finite A ==> x: A ==> y: A ==> card (A - {x} - {y}) < card A"
apply (case_tac "x = y")
 apply (simp add: card_Diff1_less del:card_Diff_insert)
apply (rule less_trans)
 prefer 2 apply (auto intro!: card_Diff1_less simp del:card_Diff_insert)
done

lemma card_Diff1_le: "finite A ==> card (A - {x}) <= card A"
apply (case_tac "x : A")
 apply (simp_all add: card_Diff1_less less_imp_le)
done

lemma card_psubset: "finite B ==> A \<subseteq> B ==> card A < card B ==> A < B"
by (erule psubsetI, blast)

lemma insert_partition:
  "\<lbrakk> x \<notin> F; \<forall>c1 \<in> insert x F. \<forall>c2 \<in> insert x F. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {} \<rbrakk>
  \<Longrightarrow> x \<inter> \<Union> F = {}"
by auto

lemma finite_psubset_induct[consumes 1, case_names psubset]:
  assumes fin: "finite A" 
  and     major: "\<And>A. finite A \<Longrightarrow> (\<And>B. B \<subset> A \<Longrightarrow> P B) \<Longrightarrow> P A" 
  shows "P A"
using fin
proof (induct A taking: card rule: measure_induct_rule)
  case (less A)
  have fin: "finite A" by fact
  have ih: "\<And>B. \<lbrakk>card B < card A; finite B\<rbrakk> \<Longrightarrow> P B" by fact
  { fix B 
    assume asm: "B \<subset> A"
    from asm have "card B < card A" using psubset_card_mono fin by blast
    moreover
    from asm have "B \<subseteq> A" by auto
    then have "finite B" using fin finite_subset by blast
    ultimately 
    have "P B" using ih by simp
  }
  with fin show "P A" using major by blast
qed

text{* main cardinality theorem *}
lemma card_partition [rule_format]:
  "finite C ==>
     finite (\<Union> C) -->
     (\<forall>c\<in>C. card c = k) -->
     (\<forall>c1 \<in> C. \<forall>c2 \<in> C. c1 \<noteq> c2 --> c1 \<inter> c2 = {}) -->
     k * card(C) = card (\<Union> C)"
apply (erule finite_induct, simp)
apply (simp add: card_Un_disjoint insert_partition 
       finite_subset [of _ "\<Union> (insert x F)"])
done

lemma card_eq_UNIV_imp_eq_UNIV:
  assumes fin: "finite (UNIV :: 'a set)"
  and card: "card A = card (UNIV :: 'a set)"
  shows "A = (UNIV :: 'a set)"
proof
  show "A \<subseteq> UNIV" by simp
  show "UNIV \<subseteq> A"
  proof
    fix x
    show "x \<in> A"
    proof (rule ccontr)
      assume "x \<notin> A"
      then have "A \<subset> UNIV" by auto
      with fin have "card A < card (UNIV :: 'a set)" by (fact psubset_card_mono)
      with card show False by simp
    qed
  qed
qed

text{*The form of a finite set of given cardinality*}

lemma card_eq_SucD:
assumes "card A = Suc k"
shows "\<exists>b B. A = insert b B & b \<notin> B & card B = k & (k=0 \<longrightarrow> B={})"
proof -
  have fin: "finite A" using assms by (auto intro: ccontr)
  moreover have "card A \<noteq> 0" using assms by auto
  ultimately obtain b where b: "b \<in> A" by auto
  show ?thesis
  proof (intro exI conjI)
    show "A = insert b (A-{b})" using b by blast
    show "b \<notin> A - {b}" by blast
    show "card (A - {b}) = k" and "k = 0 \<longrightarrow> A - {b} = {}"
      using assms b fin by(fastforce dest:mk_disjoint_insert)+
  qed
qed

lemma card_Suc_eq:
  "(card A = Suc k) =
   (\<exists>b B. A = insert b B & b \<notin> B & card B = k & (k=0 \<longrightarrow> B={}))"
apply(rule iffI)
 apply(erule card_eq_SucD)
apply(auto)
apply(subst card_insert)
 apply(auto intro:ccontr)
done

lemma card_le_Suc_iff: "finite A \<Longrightarrow>
  Suc n \<le> card A = (\<exists>a B. A = insert a B \<and> a \<notin> B \<and> n \<le> card B \<and> finite B)"
by (fastforce simp: card_Suc_eq less_eq_nat.simps(2) insert_eq_iff
  dest: subset_singletonD split: nat.splits if_splits)

lemma finite_fun_UNIVD2:
  assumes fin: "finite (UNIV :: ('a \<Rightarrow> 'b) set)"
  shows "finite (UNIV :: 'b set)"
proof -
  from fin have "\<And>arbitrary. finite (range (\<lambda>f :: 'a \<Rightarrow> 'b. f arbitrary))"
    by (rule finite_imageI)
  moreover have "\<And>arbitrary. UNIV = range (\<lambda>f :: 'a \<Rightarrow> 'b. f arbitrary)"
    by (rule UNIV_eq_I) auto
  ultimately show "finite (UNIV :: 'b set)" by simp
qed

lemma card_UNIV_unit [simp]: "card (UNIV :: unit set) = 1"
  unfolding UNIV_unit by simp

lemma card_UNIV_bool [simp]: "card (UNIV :: bool set) = 2"
  unfolding UNIV_bool by simp


subsubsection {* Cardinality of image *}

lemma card_image_le: "finite A ==> card (f ` A) <= card A"
apply (induct rule: finite_induct)
 apply simp
apply (simp add: le_SucI card_insert_if)
done

lemma card_image:
  assumes "inj_on f A"
  shows "card (f ` A) = card A"
proof (cases "finite A")
  case True then show ?thesis using assms by (induct A) simp_all
next
  case False then have "\<not> finite (f ` A)" using assms by (auto dest: finite_imageD)
  with False show ?thesis by simp
qed

lemma bij_betw_same_card: "bij_betw f A B \<Longrightarrow> card A = card B"
by(auto simp: card_image bij_betw_def)

lemma endo_inj_surj: "finite A ==> f ` A \<subseteq> A ==> inj_on f A ==> f ` A = A"
by (simp add: card_seteq card_image)

lemma eq_card_imp_inj_on:
  "[| finite A; card(f ` A) = card A |] ==> inj_on f A"
apply (induct rule:finite_induct)
apply simp
apply(frule card_image_le[where f = f])
apply(simp add:card_insert_if split:if_splits)
done

lemma inj_on_iff_eq_card:
  "finite A ==> inj_on f A = (card(f ` A) = card A)"
by(blast intro: card_image eq_card_imp_inj_on)


lemma card_inj_on_le:
  "[|inj_on f A; f ` A \<subseteq> B; finite B |] ==> card A \<le> card B"
apply (subgoal_tac "finite A") 
 apply (force intro: card_mono simp add: card_image [symmetric])
apply (blast intro: finite_imageD dest: finite_subset) 
done

lemma card_bij_eq:
  "[|inj_on f A; f ` A \<subseteq> B; inj_on g B; g ` B \<subseteq> A;
     finite A; finite B |] ==> card A = card B"
by (auto intro: le_antisym card_inj_on_le)

lemma bij_betw_finite:
  assumes "bij_betw f A B"
  shows "finite A \<longleftrightarrow> finite B"
using assms unfolding bij_betw_def
using finite_imageD[of f A] by auto


subsubsection {* Pigeonhole Principles *}

lemma pigeonhole: "card A > card(f ` A) \<Longrightarrow> ~ inj_on f A "
by (auto dest: card_image less_irrefl_nat)

lemma pigeonhole_infinite:
assumes  "~ finite A" and "finite(f`A)"
shows "EX a0:A. ~finite{a:A. f a = f a0}"
proof -
  have "finite(f`A) \<Longrightarrow> ~ finite A \<Longrightarrow> EX a0:A. ~finite{a:A. f a = f a0}"
  proof(induct "f`A" arbitrary: A rule: finite_induct)
    case empty thus ?case by simp
  next
    case (insert b F)
    show ?case
    proof cases
      assume "finite{a:A. f a = b}"
      hence "~ finite(A - {a:A. f a = b})" using `\<not> finite A` by simp
      also have "A - {a:A. f a = b} = {a:A. f a \<noteq> b}" by blast
      finally have "~ finite({a:A. f a \<noteq> b})" .
      from insert(3)[OF _ this]
      show ?thesis using insert(2,4) by simp (blast intro: rev_finite_subset)
    next
      assume 1: "~finite{a:A. f a = b}"
      hence "{a \<in> A. f a = b} \<noteq> {}" by force
      thus ?thesis using 1 by blast
    qed
  qed
  from this[OF assms(2,1)] show ?thesis .
qed

lemma pigeonhole_infinite_rel:
assumes "~finite A" and "finite B" and "ALL a:A. EX b:B. R a b"
shows "EX b:B. ~finite{a:A. R a b}"
proof -
   let ?F = "%a. {b:B. R a b}"
   from finite_Pow_iff[THEN iffD2, OF `finite B`]
   have "finite(?F ` A)" by(blast intro: rev_finite_subset)
   from pigeonhole_infinite[where f = ?F, OF assms(1) this]
   obtain a0 where "a0\<in>A" and 1: "\<not> finite {a\<in>A. ?F a = ?F a0}" ..
   obtain b0 where "b0 : B" and "R a0 b0" using `a0:A` assms(3) by blast
   { assume "finite{a:A. R a b0}"
     then have "finite {a\<in>A. ?F a = ?F a0}"
       using `b0 : B` `R a0 b0` by(blast intro: rev_finite_subset)
   }
   with 1 `b0 : B` show ?thesis by blast
qed


subsubsection {* Cardinality of sums *}

lemma card_Plus:
  assumes "finite A" and "finite B"
  shows "card (A <+> B) = card A + card B"
proof -
  have "Inl`A \<inter> Inr`B = {}" by fast
  with assms show ?thesis
    unfolding Plus_def
    by (simp add: card_Un_disjoint card_image)
qed

lemma card_Plus_conv_if:
  "card (A <+> B) = (if finite A \<and> finite B then card A + card B else 0)"
  by (auto simp add: card_Plus)


subsubsection {* Cardinality of the Powerset *}

lemma card_Pow: "finite A ==> card (Pow A) = 2 ^ card A"
apply (induct rule: finite_induct)
 apply (simp_all add: Pow_insert)
apply (subst card_Un_disjoint, blast)
  apply (blast, blast)
apply (subgoal_tac "inj_on (insert x) (Pow F)")
 apply (subst mult_2)
 apply (simp add: card_image Pow_insert)
apply (unfold inj_on_def)
apply (blast elim!: equalityE)
done

text {* Relates to equivalence classes.  Based on a theorem of F. Kamm\"uller.  *}

lemma dvd_partition:
  "finite (Union C) ==>
    ALL c : C. k dvd card c ==>
    (ALL c1: C. ALL c2: C. c1 \<noteq> c2 --> c1 Int c2 = {}) ==>
  k dvd card (Union C)"
apply (frule finite_UnionD)
apply (rotate_tac -1)
apply (induct rule: finite_induct)
apply simp_all
apply clarify
apply (subst card_Un_disjoint)
   apply (auto simp add: disjoint_eq_subset_Compl)
done


subsubsection {* Relating injectivity and surjectivity *}

lemma finite_surj_inj: "finite A \<Longrightarrow> A \<subseteq> f ` A \<Longrightarrow> inj_on f A"
apply(rule eq_card_imp_inj_on, assumption)
apply(frule finite_imageI)
apply(drule (1) card_seteq)
 apply(erule card_image_le)
apply simp
done

lemma finite_UNIV_surj_inj: fixes f :: "'a \<Rightarrow> 'a"
shows "finite(UNIV:: 'a set) \<Longrightarrow> surj f \<Longrightarrow> inj f"
by (blast intro: finite_surj_inj subset_UNIV)

lemma finite_UNIV_inj_surj: fixes f :: "'a \<Rightarrow> 'a"
shows "finite(UNIV:: 'a set) \<Longrightarrow> inj f \<Longrightarrow> surj f"
by(fastforce simp:surj_def dest!: endo_inj_surj)

corollary infinite_UNIV_nat[iff]: "~finite(UNIV::nat set)"
proof
  assume "finite(UNIV::nat set)"
  with finite_UNIV_inj_surj[of Suc]
  show False by simp (blast dest: Suc_neq_Zero surjD)
qed

(* Often leads to bogus ATP proofs because of reduced type information, hence no_atp *)
lemma infinite_UNIV_char_0[no_atp]:
  "\<not> finite (UNIV::'a::semiring_char_0 set)"
proof
  assume "finite (UNIV::'a set)"
  with subset_UNIV have "finite (range of_nat::'a set)"
    by (rule finite_subset)
  moreover have "inj (of_nat::nat \<Rightarrow> 'a)"
    by (simp add: inj_on_def)
  ultimately have "finite (UNIV::nat set)"
    by (rule finite_imageD)
  then show "False"
    by simp
qed

hide_const (open) Finite_Set.fold

end
