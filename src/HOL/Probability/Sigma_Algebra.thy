(*  Title:      Sigma_Algebra.thy
    Author:     Stefan Richter, Markus Wenzel, TU Muenchen
    Plus material from the Hurd/Coble measure theory development, 
    translated by Lawrence Paulson.
*)

header {* Sigma Algebras *}

theory Sigma_Algebra imports Complex_Main begin

text {* Sigma algebras are an elementary concept in measure
  theory. To measure --- that is to integrate --- functions, we first have
  to measure sets. Unfortunately, when dealing with a large universe,
  it is often not possible to consistently assign a measure to every
  subset. Therefore it is necessary to define the set of measurable
  subsets of the universe. A sigma algebra is such a set that has
  three very natural and desirable properties. *}

subsection {* Algebras *}

record 'a algebra = 
  space :: "'a set" 
  sets :: "'a set set"

locale algebra =
  fixes M
  assumes space_closed: "sets M \<subseteq> Pow (space M)"
     and  empty_sets [iff]: "{} \<in> sets M"
     and  compl_sets [intro]: "!!a. a \<in> sets M \<Longrightarrow> space M - a \<in> sets M"
     and  Un [intro]: "!!a b. a \<in> sets M \<Longrightarrow> b \<in> sets M \<Longrightarrow> a \<union> b \<in> sets M"

lemma (in algebra) top [iff]: "space M \<in> sets M"
  by (metis Diff_empty compl_sets empty_sets)

lemma (in algebra) sets_into_space: "x \<in> sets M \<Longrightarrow> x \<subseteq> space M"
  by (metis PowD contra_subsetD space_closed)

lemma (in algebra) Int [intro]: 
  assumes a: "a \<in> sets M" and b: "b \<in> sets M" shows "a \<inter> b \<in> sets M"
proof -
  have "((space M - a) \<union> (space M - b)) \<in> sets M" 
    by (metis a b compl_sets Un)
  moreover
  have "a \<inter> b = space M - ((space M - a) \<union> (space M - b))" 
    using space_closed a b
    by blast
  ultimately show ?thesis
    by (metis compl_sets)
qed

lemma (in algebra) Diff [intro]: 
  assumes a: "a \<in> sets M" and b: "b \<in> sets M" shows "a - b \<in> sets M"
proof -
  have "(a \<inter> (space M - b)) \<in> sets M"
    by (metis a b compl_sets Int)
  moreover
  have "a - b = (a \<inter> (space M - b))"
    by (metis Int_Diff Int_absorb1 Int_commute a sets_into_space)
  ultimately show ?thesis
    by metis
qed

lemma (in algebra) finite_union [intro]: 
  "finite X \<Longrightarrow> X \<subseteq> sets M \<Longrightarrow> Union X \<in> sets M"
  by (induct set: finite) (auto simp add: Un) 


subsection {* Sigma Algebras *}

locale sigma_algebra = algebra +
  assumes countable_UN [intro]:
         "!!A. range A \<subseteq> sets M \<Longrightarrow> (\<Union>i::nat. A i) \<in> sets M"

lemma (in sigma_algebra) countable_INT [intro]:
  assumes a: "range a \<subseteq> sets M"
  shows "(\<Inter>i::nat. a i) \<in> sets M"
proof -
  have "space M - (\<Union>i. space M - a i) \<in> sets M" using a
    by (blast intro: countable_UN compl_sets a) 
  moreover
  have "(\<Inter>i. a i) = space M - (\<Union>i. space M - a i)" using space_closed a 
    by blast
  ultimately show ?thesis by metis
qed

lemma (in sigma_algebra) gen_countable_UN:
  fixes f :: "nat \<Rightarrow> 'c"
  shows  "I = range f \<Longrightarrow> range A \<subseteq> sets M \<Longrightarrow> (\<Union>x\<in>I. A x) \<in> sets M"
by auto

lemma (in sigma_algebra) gen_countable_INT:
  fixes f :: "nat \<Rightarrow> 'c"
  shows  "I = range f \<Longrightarrow> range A \<subseteq> sets M \<Longrightarrow> (\<Inter>x\<in>I. A x) \<in> sets M"
by auto

lemma algebra_Pow:
     "algebra (| space = sp, sets = Pow sp |)"
  by (auto simp add: algebra_def) 

lemma sigma_algebra_Pow:
     "sigma_algebra (| space = sp, sets = Pow sp |)"
  by (auto simp add: sigma_algebra_def sigma_algebra_axioms_def algebra_Pow) 

subsection {* Binary Unions *}

definition binary :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
  where "binary a b =  (\<lambda>\<^isup>x. b)(0 := a)"

lemma range_binary_eq: "range(binary a b) = {a,b}" 
  by (auto simp add: binary_def)  

lemma Un_range_binary: "a \<union> b = (\<Union>i::nat. binary a b i)" 
  by (simp add: UNION_eq_Union_image range_binary_eq) 

lemma Int_range_binary: "a \<inter> b = (\<Inter>i::nat. binary a b i)" 
  by (simp add: INTER_eq_Inter_image range_binary_eq) 

lemma sigma_algebra_iff: 
     "sigma_algebra M \<longleftrightarrow> 
      algebra M & (\<forall>A. range A \<subseteq> sets M \<longrightarrow> (\<Union>i::nat. A i) \<in> sets M)"
  by (simp add: sigma_algebra_def sigma_algebra_axioms_def) 

lemma sigma_algebra_iff2:
     "sigma_algebra M \<longleftrightarrow>
       sets M \<subseteq> Pow (space M) &
       {} \<in> sets M & (\<forall>s \<in> sets M. space M - s \<in> sets M) &
       (\<forall>A. range A \<subseteq> sets M \<longrightarrow> (\<Union>i::nat. A i) \<in> sets M)"
  by (force simp add: range_binary_eq sigma_algebra_def sigma_algebra_axioms_def
         algebra_def Un_range_binary) 


subsection {* Initial Sigma Algebra *}

text {*Sigma algebras can naturally be created as the closure of any set of
  sets with regard to the properties just postulated.  *}

inductive_set
  sigma_sets :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
  for sp :: "'a set" and A :: "'a set set"
  where
    Basic: "a \<in> A \<Longrightarrow> a \<in> sigma_sets sp A"
  | Empty: "{} \<in> sigma_sets sp A"
  | Compl: "a \<in> sigma_sets sp A \<Longrightarrow> sp - a \<in> sigma_sets sp A"
  | Union: "(\<And>i::nat. a i \<in> sigma_sets sp A) \<Longrightarrow> (\<Union>i. a i) \<in> sigma_sets sp A"


definition
  sigma  where
  "sigma sp A = (| space = sp, sets = sigma_sets sp A |)"


lemma space_sigma [simp]: "space (sigma X B) = X"
  by (simp add: sigma_def) 

lemma sigma_sets_top: "sp \<in> sigma_sets sp A"
  by (metis Diff_empty sigma_sets.Compl sigma_sets.Empty)

lemma sigma_sets_into_sp: "A \<subseteq> Pow sp \<Longrightarrow> x \<in> sigma_sets sp A \<Longrightarrow> x \<subseteq> sp"
  by (erule sigma_sets.induct, auto) 

lemma sigma_sets_Un: 
  "a \<in> sigma_sets sp A \<Longrightarrow> b \<in> sigma_sets sp A \<Longrightarrow> a \<union> b \<in> sigma_sets sp A"
apply (simp add: Un_range_binary range_binary_eq) 
apply (metis Union COMBK_def binary_def fun_upd_apply) 
done

lemma sigma_sets_Inter:
  assumes Asb: "A \<subseteq> Pow sp"
  shows "(\<And>i::nat. a i \<in> sigma_sets sp A) \<Longrightarrow> (\<Inter>i. a i) \<in> sigma_sets sp A"
proof -
  assume ai: "\<And>i::nat. a i \<in> sigma_sets sp A"
  hence "\<And>i::nat. sp-(a i) \<in> sigma_sets sp A" 
    by (rule sigma_sets.Compl)
  hence "(\<Union>i. sp-(a i)) \<in> sigma_sets sp A" 
    by (rule sigma_sets.Union)
  hence "sp-(\<Union>i. sp-(a i)) \<in> sigma_sets sp A" 
    by (rule sigma_sets.Compl)
  also have "sp-(\<Union>i. sp-(a i)) = sp Int (\<Inter>i. a i)" 
    by auto
  also have "... = (\<Inter>i. a i)" using ai
    by (blast dest: sigma_sets_into_sp [OF Asb]) 
  finally show ?thesis . 
qed

lemma sigma_sets_INTER:
  assumes Asb: "A \<subseteq> Pow sp" 
      and ai: "\<And>i::nat. i \<in> S \<Longrightarrow> a i \<in> sigma_sets sp A" and non: "S \<noteq> {}"
  shows "(\<Inter>i\<in>S. a i) \<in> sigma_sets sp A"
proof -
  from ai have "\<And>i. (if i\<in>S then a i else sp) \<in> sigma_sets sp A"
    by (simp add: sigma_sets.intros sigma_sets_top)
  hence "(\<Inter>i. (if i\<in>S then a i else sp)) \<in> sigma_sets sp A"
    by (rule sigma_sets_Inter [OF Asb])
  also have "(\<Inter>i. (if i\<in>S then a i else sp)) = (\<Inter>i\<in>S. a i)"
    by auto (metis ai non sigma_sets_into_sp subset_empty subset_iff Asb)+
  finally show ?thesis .
qed

lemma (in sigma_algebra) sigma_sets_subset:
  assumes a: "a \<subseteq> sets M" 
  shows "sigma_sets (space M) a \<subseteq> sets M"
proof
  fix x
  assume "x \<in> sigma_sets (space M) a"
  from this show "x \<in> sets M"
    by (induct rule: sigma_sets.induct, auto) (metis a subsetD) 
qed

lemma (in sigma_algebra) sigma_sets_eq:
     "sigma_sets (space M) (sets M) = sets M"
proof
  show "sets M \<subseteq> sigma_sets (space M) (sets M)"
    by (metis Set.subsetI sigma_sets.Basic space_closed)
  next
  show "sigma_sets (space M) (sets M) \<subseteq> sets M"
    by (metis sigma_sets_subset subset_refl)
qed

lemma sigma_algebra_sigma_sets:
     "a \<subseteq> Pow (space M) \<Longrightarrow> sets M = sigma_sets (space M) a \<Longrightarrow> sigma_algebra M"
  apply (auto simp add: sigma_algebra_def sigma_algebra_axioms_def
      algebra_def sigma_sets.Empty sigma_sets.Compl sigma_sets_Un) 
  apply (blast dest: sigma_sets_into_sp)
  apply (blast intro: sigma_sets.intros) 
  done

lemma sigma_algebra_sigma:
     "a \<subseteq> Pow X \<Longrightarrow> sigma_algebra (sigma X a)"
  apply (rule sigma_algebra_sigma_sets) 
  apply (auto simp add: sigma_def) 
  done

lemma (in sigma_algebra) sigma_subset:
     "a \<subseteq> sets M ==> sets (sigma (space M) a) \<subseteq> (sets M)"
  by (simp add: sigma_def sigma_sets_subset)

end
