(*  Title:      Sigma_Algebra.thy
    Author:     Stefan Richter, Markus Wenzel, TU Muenchen
    Plus material from the Hurd/Coble measure theory development,
    translated by Lawrence Paulson.
*)

header {* Sigma Algebras *}

theory Sigma_Algebra imports Main Countable FuncSet begin

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

lemma algebra_iff_Int:
     "algebra M \<longleftrightarrow>
       sets M \<subseteq> Pow (space M) & {} \<in> sets M &
       (\<forall>a \<in> sets M. space M - a \<in> sets M) &
       (\<forall>a \<in> sets M. \<forall> b \<in> sets M. a \<inter> b \<in> sets M)"
proof (auto simp add: algebra.Int, auto simp add: algebra_def)
  fix a b
  assume ab: "sets M \<subseteq> Pow (space M)"
             "\<forall>a\<in>sets M. space M - a \<in> sets M"
             "\<forall>a\<in>sets M. \<forall>b\<in>sets M. a \<inter> b \<in> sets M"
             "a \<in> sets M" "b \<in> sets M"
  hence "a \<union> b = space M - ((space M - a) \<inter> (space M - b))"
    by blast
  also have "... \<in> sets M"
    by (metis ab)
  finally show "a \<union> b \<in> sets M" .
qed

lemma (in algebra) insert_in_sets:
  assumes "{x} \<in> sets M" "A \<in> sets M" shows "insert x A \<in> sets M"
proof -
  have "{x} \<union> A \<in> sets M" using assms by (rule Un)
  thus ?thesis by auto
qed

lemma (in algebra) Int_space_eq1 [simp]: "x \<in> sets M \<Longrightarrow> space M \<inter> x = x"
  by (metis Int_absorb1 sets_into_space)

lemma (in algebra) Int_space_eq2 [simp]: "x \<in> sets M \<Longrightarrow> x \<inter> space M = x"
  by (metis Int_absorb2 sets_into_space)

lemma (in algebra) restricted_algebra:
  assumes "S \<in> sets M"
  shows "algebra (M\<lparr> space := S, sets := (\<lambda>A. S \<inter> A) ` sets M \<rparr>)"
    (is "algebra ?r")
  using assms by unfold_locales auto

subsection {* Sigma Algebras *}

locale sigma_algebra = algebra +
  assumes countable_nat_UN [intro]:
         "!!A. range A \<subseteq> sets M \<Longrightarrow> (\<Union>i::nat. A i) \<in> sets M"

lemma countable_UN_eq:
  fixes A :: "'i::countable \<Rightarrow> 'a set"
  shows "(range A \<subseteq> sets M \<longrightarrow> (\<Union>i. A i) \<in> sets M) \<longleftrightarrow>
    (range (A \<circ> from_nat) \<subseteq> sets M \<longrightarrow> (\<Union>i. (A \<circ> from_nat) i) \<in> sets M)"
proof -
  let ?A' = "A \<circ> from_nat"
  have *: "(\<Union>i. ?A' i) = (\<Union>i. A i)" (is "?l = ?r")
  proof safe
    fix x i assume "x \<in> A i" thus "x \<in> ?l"
      by (auto intro!: exI[of _ "to_nat i"])
  next
    fix x i assume "x \<in> ?A' i" thus "x \<in> ?r"
      by (auto intro!: exI[of _ "from_nat i"])
  qed
  have **: "range ?A' = range A"
    using surj_range[OF surj_from_nat]
    by (auto simp: image_compose intro!: imageI)
  show ?thesis unfolding * ** ..
qed

lemma (in sigma_algebra) countable_UN[intro]:
  fixes A :: "'i::countable \<Rightarrow> 'a set"
  assumes "A`X \<subseteq> sets M"
  shows  "(\<Union>x\<in>X. A x) \<in> sets M"
proof -
  let "?A i" = "if i \<in> X then A i else {}"
  from assms have "range ?A \<subseteq> sets M" by auto
  with countable_nat_UN[of "?A \<circ> from_nat"] countable_UN_eq[of ?A M]
  have "(\<Union>x. ?A x) \<in> sets M" by auto
  moreover have "(\<Union>x. ?A x) = (\<Union>x\<in>X. A x)" by (auto split: split_if_asm)
  ultimately show ?thesis by simp
qed

lemma (in sigma_algebra) finite_UN:
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M"
  shows "(\<Union>i\<in>I. A i) \<in> sets M"
  using assms by induct auto

lemma (in sigma_algebra) countable_INT [intro]:
  fixes A :: "'i::countable \<Rightarrow> 'a set"
  assumes A: "A`X \<subseteq> sets M" "X \<noteq> {}"
  shows "(\<Inter>i\<in>X. A i) \<in> sets M"
proof -
  from A have "\<forall>i\<in>X. A i \<in> sets M" by fast
  hence "space M - (\<Union>i\<in>X. space M - A i) \<in> sets M" by blast
  moreover
  have "(\<Inter>i\<in>X. A i) = space M - (\<Union>i\<in>X. space M - A i)" using space_closed A
    by blast
  ultimately show ?thesis by metis
qed

lemma (in sigma_algebra) finite_INT:
  assumes "finite I" "I \<noteq> {}" "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M"
  shows "(\<Inter>i\<in>I. A i) \<in> sets M"
  using assms by (induct rule: finite_ne_induct) auto

lemma algebra_Pow:
     "algebra \<lparr> space = sp, sets = Pow sp, \<dots> = X \<rparr>"
  by (auto simp add: algebra_def)

lemma sigma_algebra_Pow:
     "sigma_algebra \<lparr> space = sp, sets = Pow sp, \<dots> = X \<rparr>"
  by (auto simp add: sigma_algebra_def sigma_algebra_axioms_def algebra_Pow)

lemma sigma_algebra_iff:
     "sigma_algebra M \<longleftrightarrow>
      algebra M \<and> (\<forall>A. range A \<subseteq> sets M \<longrightarrow> (\<Union>i::nat. A i) \<in> sets M)"
  by (simp add: sigma_algebra_def sigma_algebra_axioms_def)

subsection {* Binary Unions *}

definition binary :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
  where "binary a b =  (\<lambda>\<^isup>x. b)(0 := a)"

lemma range_binary_eq: "range(binary a b) = {a,b}"
  by (auto simp add: binary_def)

lemma Un_range_binary: "a \<union> b = (\<Union>i::nat. binary a b i)"
  by (simp add: UNION_eq_Union_image range_binary_eq)

lemma Int_range_binary: "a \<inter> b = (\<Inter>i::nat. binary a b i)"
  by (simp add: INTER_eq_Inter_image range_binary_eq)

lemma sigma_algebra_iff2:
     "sigma_algebra M \<longleftrightarrow>
       sets M \<subseteq> Pow (space M) \<and>
       {} \<in> sets M \<and> (\<forall>s \<in> sets M. space M - s \<in> sets M) \<and>
       (\<forall>A. range A \<subseteq> sets M \<longrightarrow> (\<Union>i::nat. A i) \<in> sets M)"
  by (auto simp add: range_binary_eq sigma_algebra_def sigma_algebra_axioms_def
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

lemma sets_sigma: "sets (sigma A B) = sigma_sets A B"
  unfolding sigma_def by simp

lemma space_sigma [simp]: "space (sigma X B) = X"
  by (simp add: sigma_def)

lemma sigma_sets_top: "sp \<in> sigma_sets sp A"
  by (metis Diff_empty sigma_sets.Compl sigma_sets.Empty)

lemma sigma_sets_into_sp: "A \<subseteq> Pow sp \<Longrightarrow> x \<in> sigma_sets sp A \<Longrightarrow> x \<subseteq> sp"
  by (erule sigma_sets.induct, auto)

lemma sigma_sets_Un:
  "a \<in> sigma_sets sp A \<Longrightarrow> b \<in> sigma_sets sp A \<Longrightarrow> a \<union> b \<in> sigma_sets sp A"
apply (simp add: Un_range_binary range_binary_eq)
apply (rule Union, simp add: binary_def COMBK_def fun_upd_apply)
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
    by (metis Set.subsetI sigma_sets.Basic)
  next
  show "sigma_sets (space M) (sets M) \<subseteq> sets M"
    by (metis sigma_sets_subset subset_refl)
qed

lemma sigma_algebra_sigma_sets:
     "a \<subseteq> Pow (space M) \<Longrightarrow> sets M = sigma_sets (space M) a \<Longrightarrow> sigma_algebra M"
  apply (auto simp add: sigma_algebra_def sigma_algebra_axioms_def
      algebra_def sigma_sets.Empty sigma_sets.Compl sigma_sets_Un)
  apply (blast dest: sigma_sets_into_sp)
  apply (rule sigma_sets.Union, fast)
  done

lemma sigma_algebra_sigma:
     "a \<subseteq> Pow X \<Longrightarrow> sigma_algebra (sigma X a)"
  apply (rule sigma_algebra_sigma_sets)
  apply (auto simp add: sigma_def)
  done

lemma (in sigma_algebra) sigma_subset:
     "a \<subseteq> sets M ==> sets (sigma (space M) a) \<subseteq> (sets M)"
  by (simp add: sigma_def sigma_sets_subset)

lemma (in sigma_algebra) restriction_in_sets:
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes "S \<in> sets M"
  and *: "range A \<subseteq> (\<lambda>A. S \<inter> A) ` sets M" (is "_ \<subseteq> ?r")
  shows "range A \<subseteq> sets M" "(\<Union>i. A i) \<in> (\<lambda>A. S \<inter> A) ` sets M"
proof -
  { fix i have "A i \<in> ?r" using * by auto
    hence "\<exists>B. A i = B \<inter> S \<and> B \<in> sets M" by auto
    hence "A i \<subseteq> S" "A i \<in> sets M" using `S \<in> sets M` by auto }
  thus "range A \<subseteq> sets M" "(\<Union>i. A i) \<in> (\<lambda>A. S \<inter> A) ` sets M"
    by (auto intro!: image_eqI[of _ _ "(\<Union>i. A i)"])
qed

lemma (in sigma_algebra) restricted_sigma_algebra:
  assumes "S \<in> sets M"
  shows "sigma_algebra (M\<lparr> space := S, sets := (\<lambda>A. S \<inter> A) ` sets M \<rparr>)"
    (is "sigma_algebra ?r")
  unfolding sigma_algebra_def sigma_algebra_axioms_def
proof safe
  show "algebra ?r" using restricted_algebra[OF assms] .
next
  fix A :: "nat \<Rightarrow> 'a set" assume "range A \<subseteq> sets ?r"
  from restriction_in_sets[OF assms this[simplified]]
  show "(\<Union>i. A i) \<in> sets ?r" by simp
qed

section {* Measurable functions *}

definition
  "measurable A B = {f \<in> space A -> space B. \<forall>y \<in> sets B. f -` y \<inter> space A \<in> sets A}"

lemma (in sigma_algebra) measurable_sigma:
  assumes B: "B \<subseteq> Pow X"
      and f: "f \<in> space M -> X"
      and ba: "\<And>y. y \<in> B \<Longrightarrow> (f -` y) \<inter> space M \<in> sets M"
  shows "f \<in> measurable M (sigma X B)"
proof -
  have "sigma_sets X B \<subseteq> {y . (f -` y) \<inter> space M \<in> sets M & y \<subseteq> X}"
    proof clarify
      fix x
      assume "x \<in> sigma_sets X B"
      thus "f -` x \<inter> space M \<in> sets M \<and> x \<subseteq> X"
        proof induct
          case (Basic a)
          thus ?case
            by (auto simp add: ba) (metis B subsetD PowD)
        next
          case Empty
          thus ?case
            by auto
        next
          case (Compl a)
          have [simp]: "f -` X \<inter> space M = space M"
            by (auto simp add: funcset_mem [OF f])
          thus ?case
            by (auto simp add: vimage_Diff Diff_Int_distrib2 compl_sets Compl)
        next
          case (Union a)
          thus ?case
            by (simp add: vimage_UN, simp only: UN_extend_simps(4))
               (blast intro: countable_UN)
        qed
    qed
  thus ?thesis
    by (simp add: measurable_def sigma_algebra_axioms sigma_algebra_sigma B f)
       (auto simp add: sigma_def)
qed

lemma measurable_cong:
  assumes "\<And> w. w \<in> space M \<Longrightarrow> f w = g w"
  shows "f \<in> measurable M M' \<longleftrightarrow> g \<in> measurable M M'"
  unfolding measurable_def using assms
  by (simp cong: vimage_inter_cong Pi_cong)

lemma measurable_space:
  "f \<in> measurable M A \<Longrightarrow> x \<in> space M \<Longrightarrow> f x \<in> space A"
   unfolding measurable_def by auto

lemma measurable_sets:
  "f \<in> measurable M A \<Longrightarrow> S \<in> sets A \<Longrightarrow> f -` S \<inter> space M \<in> sets M"
   unfolding measurable_def by auto

lemma (in sigma_algebra) measurable_subset:
     "(\<And>S. S \<in> sets A \<Longrightarrow> S \<subseteq> space A) \<Longrightarrow> measurable M A \<subseteq> measurable M (sigma (space A) (sets A))"
  by (auto intro: measurable_sigma measurable_sets measurable_space)

lemma measurable_eqI:
     "\<lbrakk> space m1 = space m1' ; space m2 = space m2' ;
        sets m1 = sets m1' ; sets m2 = sets m2' \<rbrakk>
      \<Longrightarrow> measurable m1 m2 = measurable m1' m2'"
  by (simp add: measurable_def sigma_algebra_iff2)

lemma (in sigma_algebra) measurable_const[intro, simp]:
  assumes "c \<in> space M'"
  shows "(\<lambda>x. c) \<in> measurable M M'"
  using assms by (auto simp add: measurable_def)

lemma (in sigma_algebra) measurable_If:
  assumes measure: "f \<in> measurable M M'" "g \<in> measurable M M'"
  assumes P: "{x\<in>space M. P x} \<in> sets M"
  shows "(\<lambda>x. if P x then f x else g x) \<in> measurable M M'"
  unfolding measurable_def
proof safe
  fix x assume "x \<in> space M"
  thus "(if P x then f x else g x) \<in> space M'"
    using measure unfolding measurable_def by auto
next
  fix A assume "A \<in> sets M'"
  hence *: "(\<lambda>x. if P x then f x else g x) -` A \<inter> space M =
    ((f -` A \<inter> space M) \<inter> {x\<in>space M. P x}) \<union>
    ((g -` A \<inter> space M) \<inter> (space M - {x\<in>space M. P x}))"
    using measure unfolding measurable_def by (auto split: split_if_asm)
  show "(\<lambda>x. if P x then f x else g x) -` A \<inter> space M \<in> sets M"
    using `A \<in> sets M'` measure P unfolding * measurable_def
    by (auto intro!: Un)
qed

lemma (in sigma_algebra) measurable_If_set:
  assumes measure: "f \<in> measurable M M'" "g \<in> measurable M M'"
  assumes P: "A \<in> sets M"
  shows "(\<lambda>x. if x \<in> A then f x else g x) \<in> measurable M M'"
proof (rule measurable_If[OF measure])
  have "{x \<in> space M. x \<in> A} = A" using `A \<in> sets M` sets_into_space by auto
  thus "{x \<in> space M. x \<in> A} \<in> sets M" using `A \<in> sets M` by auto
qed

lemma (in algebra) measurable_ident[intro, simp]: "id \<in> measurable M M"
  by (auto simp add: measurable_def)

lemma measurable_comp[intro]:
  fixes f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'c"
  shows "f \<in> measurable a b \<Longrightarrow> g \<in> measurable b c \<Longrightarrow> (g o f) \<in> measurable a c"
  apply (auto simp add: measurable_def vimage_compose)
  apply (subgoal_tac "f -` g -` y \<inter> space a = f -` (g -` y \<inter> space b) \<inter> space a")
  apply force+
  done

lemma measurable_strong:
  fixes f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'c"
  assumes f: "f \<in> measurable a b" and g: "g \<in> (space b -> space c)"
      and a: "sigma_algebra a" and b: "sigma_algebra b" and c: "sigma_algebra c"
      and t: "f ` (space a) \<subseteq> t"
      and cb: "\<And>s. s \<in> sets c \<Longrightarrow> (g -` s) \<inter> t \<in> sets b"
  shows "(g o f) \<in> measurable a c"
proof -
  have fab: "f \<in> (space a -> space b)"
   and ba: "\<And>y. y \<in> sets b \<Longrightarrow> (f -` y) \<inter> (space a) \<in> sets a" using f
     by (auto simp add: measurable_def)
  have eq: "f -` g -` y \<inter> space a = f -` (g -` y \<inter> t) \<inter> space a" using t
    by force
  show ?thesis
    apply (auto simp add: measurable_def vimage_compose a c)
    apply (metis funcset_mem fab g)
    apply (subst eq, metis ba cb)
    done
qed

lemma measurable_mono1:
     "a \<subseteq> b \<Longrightarrow> sigma_algebra \<lparr>space = X, sets = b\<rparr>
      \<Longrightarrow> measurable \<lparr>space = X, sets = a\<rparr> c \<subseteq> measurable \<lparr>space = X, sets = b\<rparr> c"
  by (auto simp add: measurable_def)

lemma measurable_up_sigma:
  "measurable A M \<subseteq> measurable (sigma (space A) (sets A)) M"
  unfolding measurable_def
  by (auto simp: sigma_def intro: sigma_sets.Basic)

lemma (in sigma_algebra) measurable_range_reduce:
   "\<lbrakk> f \<in> measurable M \<lparr>space = s, sets = Pow s\<rparr> ; s \<noteq> {} \<rbrakk>
    \<Longrightarrow> f \<in> measurable M \<lparr>space = s \<inter> (f ` space M), sets = Pow (s \<inter> (f ` space M))\<rparr>"
  by (simp add: measurable_def sigma_algebra_Pow del: Pow_Int_eq) blast

lemma (in sigma_algebra) measurable_Pow_to_Pow:
   "(sets M = Pow (space M)) \<Longrightarrow> f \<in> measurable M \<lparr>space = UNIV, sets = Pow UNIV\<rparr>"
  by (auto simp add: measurable_def sigma_algebra_def sigma_algebra_axioms_def algebra_def)

lemma (in sigma_algebra) measurable_Pow_to_Pow_image:
   "sets M = Pow (space M)
    \<Longrightarrow> f \<in> measurable M \<lparr>space = f ` space M, sets = Pow (f ` space M)\<rparr>"
  by (simp add: measurable_def sigma_algebra_Pow) intro_locales

lemma (in sigma_algebra) sigma_algebra_preimages:
  fixes f :: "'x \<Rightarrow> 'a"
  assumes "f \<in> A \<rightarrow> space M"
  shows "sigma_algebra \<lparr> space = A, sets = (\<lambda>M. f -` M \<inter> A) ` sets M \<rparr>"
    (is "sigma_algebra \<lparr> space = _, sets = ?F ` sets M \<rparr>")
proof (simp add: sigma_algebra_iff2, safe)
  show "{} \<in> ?F ` sets M" by blast
next
  fix S assume "S \<in> sets M"
  moreover have "A - ?F S = ?F (space M - S)"
    using assms by auto
  ultimately show "A - ?F S \<in> ?F ` sets M"
    by blast
next
  fix S :: "nat \<Rightarrow> 'x set" assume *: "range S \<subseteq> ?F ` sets M"
  have "\<forall>i. \<exists>b. b \<in> sets M \<and> S i = ?F b"
  proof safe
    fix i
    have "S i \<in> ?F ` sets M" using * by auto
    then show "\<exists>b. b \<in> sets M \<and> S i = ?F b" by auto
  qed
  from choice[OF this] obtain b where b: "range b \<subseteq> sets M" "\<And>i. S i = ?F (b i)"
    by auto
  then have "(\<Union>i. S i) = ?F (\<Union>i. b i)" by auto
  then show "(\<Union>i. S i) \<in> ?F ` sets M" using b(1) by blast
qed

section "Disjoint families"

definition
  disjoint_family_on  where
  "disjoint_family_on A S \<longleftrightarrow> (\<forall>m\<in>S. \<forall>n\<in>S. m \<noteq> n \<longrightarrow> A m \<inter> A n = {})"

abbreviation
  "disjoint_family A \<equiv> disjoint_family_on A UNIV"

lemma range_subsetD: "range f \<subseteq> B \<Longrightarrow> f i \<in> B"
  by blast

lemma Int_Diff_disjoint: "A \<inter> B \<inter> (A - B) = {}"
  by blast

lemma Int_Diff_Un: "A \<inter> B \<union> (A - B) = A"
  by blast

lemma disjoint_family_subset:
     "disjoint_family A \<Longrightarrow> (!!x. B x \<subseteq> A x) \<Longrightarrow> disjoint_family B"
  by (force simp add: disjoint_family_on_def)

lemma disjoint_family_on_mono:
  "A \<subseteq> B \<Longrightarrow> disjoint_family_on f B \<Longrightarrow> disjoint_family_on f A"
  unfolding disjoint_family_on_def by auto

lemma disjoint_family_Suc:
  assumes Suc: "!!n. A n \<subseteq> A (Suc n)"
  shows "disjoint_family (\<lambda>i. A (Suc i) - A i)"
proof -
  {
    fix m
    have "!!n. A n \<subseteq> A (m+n)"
    proof (induct m)
      case 0 show ?case by simp
    next
      case (Suc m) thus ?case
        by (metis Suc_eq_plus1 assms nat_add_commute nat_add_left_commute subset_trans)
    qed
  }
  hence "!!m n. m < n \<Longrightarrow> A m \<subseteq> A n"
    by (metis add_commute le_add_diff_inverse nat_less_le)
  thus ?thesis
    by (auto simp add: disjoint_family_on_def)
      (metis insert_absorb insert_subset le_SucE le_antisym not_leE)
qed

definition disjointed :: "(nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> 'a set "
  where "disjointed A n = A n - (\<Union>i\<in>{0..<n}. A i)"

lemma finite_UN_disjointed_eq: "(\<Union>i\<in>{0..<n}. disjointed A i) = (\<Union>i\<in>{0..<n}. A i)"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  thus ?case by (simp add: atLeastLessThanSuc disjointed_def)
qed

lemma UN_disjointed_eq: "(\<Union>i. disjointed A i) = (\<Union>i. A i)"
  apply (rule UN_finite2_eq [where k=0])
  apply (simp add: finite_UN_disjointed_eq)
  done

lemma less_disjoint_disjointed: "m<n \<Longrightarrow> disjointed A m \<inter> disjointed A n = {}"
  by (auto simp add: disjointed_def)

lemma disjoint_family_disjointed: "disjoint_family (disjointed A)"
  by (simp add: disjoint_family_on_def)
     (metis neq_iff Int_commute less_disjoint_disjointed)

lemma disjointed_subset: "disjointed A n \<subseteq> A n"
  by (auto simp add: disjointed_def)

lemma (in algebra) UNION_in_sets:
  fixes A:: "nat \<Rightarrow> 'a set"
  assumes A: "range A \<subseteq> sets M "
  shows  "(\<Union>i\<in>{0..<n}. A i) \<in> sets M"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  thus ?case
    by (simp add: atLeastLessThanSuc) (metis A Un UNIV_I image_subset_iff)
qed

lemma (in algebra) range_disjointed_sets:
  assumes A: "range A \<subseteq> sets M "
  shows  "range (disjointed A) \<subseteq> sets M"
proof (auto simp add: disjointed_def)
  fix n
  show "A n - (\<Union>i\<in>{0..<n}. A i) \<in> sets M" using UNION_in_sets
    by (metis A Diff UNIV_I image_subset_iff)
qed

lemma sigma_algebra_disjoint_iff:
     "sigma_algebra M \<longleftrightarrow>
      algebra M &
      (\<forall>A. range A \<subseteq> sets M \<longrightarrow> disjoint_family A \<longrightarrow>
           (\<Union>i::nat. A i) \<in> sets M)"
proof (auto simp add: sigma_algebra_iff)
  fix A :: "nat \<Rightarrow> 'a set"
  assume M: "algebra M"
     and A: "range A \<subseteq> sets M"
     and UnA: "\<forall>A. range A \<subseteq> sets M \<longrightarrow>
               disjoint_family A \<longrightarrow> (\<Union>i::nat. A i) \<in> sets M"
  hence "range (disjointed A) \<subseteq> sets M \<longrightarrow>
         disjoint_family (disjointed A) \<longrightarrow>
         (\<Union>i. disjointed A i) \<in> sets M" by blast
  hence "(\<Union>i. disjointed A i) \<in> sets M"
    by (simp add: algebra.range_disjointed_sets M A disjoint_family_disjointed)
  thus "(\<Union>i::nat. A i) \<in> sets M" by (simp add: UN_disjointed_eq)
qed

subsection {* Sigma algebra generated by function preimages *}

definition (in sigma_algebra)
  "vimage_algebra S f = \<lparr> space = S, sets = (\<lambda>A. f -` A \<inter> S) ` sets M \<rparr>"

lemma (in sigma_algebra) in_vimage_algebra[simp]:
  "A \<in> sets (vimage_algebra S f) \<longleftrightarrow> (\<exists>B\<in>sets M. A = f -` B \<inter> S)"
  by (simp add: vimage_algebra_def image_iff)

lemma (in sigma_algebra) space_vimage_algebra[simp]:
  "space (vimage_algebra S f) = S"
  by (simp add: vimage_algebra_def)

lemma (in sigma_algebra) sigma_algebra_vimage:
  fixes S :: "'c set" assumes "f \<in> S \<rightarrow> space M"
  shows "sigma_algebra (vimage_algebra S f)"
proof
  fix A assume "A \<in> sets (vimage_algebra S f)"
  then guess B unfolding in_vimage_algebra ..
  then show "space (vimage_algebra S f) - A \<in> sets (vimage_algebra S f)"
    using sets_into_space assms
    by (auto intro!: bexI[of _ "space M - B"])
next
  fix A assume "A \<in> sets (vimage_algebra S f)"
  then guess A' unfolding in_vimage_algebra .. note A' = this
  fix B assume "B \<in> sets (vimage_algebra S f)"
  then guess B' unfolding in_vimage_algebra .. note B' = this
  then show "A \<union> B \<in> sets (vimage_algebra S f)"
    using sets_into_space assms A' B'
    by (auto intro!: bexI[of _ "A' \<union> B'"])
next
  fix A::"nat \<Rightarrow> 'c set" assume "range A \<subseteq> sets (vimage_algebra S f)"
  then have "\<forall>i. \<exists>B. A i = f -` B \<inter> S \<and> B \<in> sets M"
    by (simp add: subset_eq) blast
  from this[THEN choice] obtain B
    where B: "\<And>i. A i = f -` B i \<inter> S" "range B \<subseteq> sets M" by auto
  show "(\<Union>i. A i) \<in> sets (vimage_algebra S f)"
    using B by (auto intro!: bexI[of _ "\<Union>i. B i"])
qed auto

lemma (in sigma_algebra) measurable_vimage_algebra:
  fixes S :: "'c set" assumes "f \<in> S \<rightarrow> space M"
  shows "f \<in> measurable (vimage_algebra S f) M"
    unfolding measurable_def using assms by force

subsection {* A Two-Element Series *}

definition binaryset :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a set "
  where "binaryset A B = (\<lambda>\<^isup>x. {})(0 := A, Suc 0 := B)"

lemma range_binaryset_eq: "range(binaryset A B) = {A,B,{}}"
  apply (simp add: binaryset_def)
  apply (rule set_ext)
  apply (auto simp add: image_iff)
  done

lemma UN_binaryset_eq: "(\<Union>i. binaryset A B i) = A \<union> B"
  by (simp add: UNION_eq_Union_image range_binaryset_eq)

section {* Closed CDI *}

definition
  closed_cdi  where
  "closed_cdi M \<longleftrightarrow>
   sets M \<subseteq> Pow (space M) &
   (\<forall>s \<in> sets M. space M - s \<in> sets M) &
   (\<forall>A. (range A \<subseteq> sets M) & (A 0 = {}) & (\<forall>n. A n \<subseteq> A (Suc n)) \<longrightarrow>
        (\<Union>i. A i) \<in> sets M) &
   (\<forall>A. (range A \<subseteq> sets M) & disjoint_family A \<longrightarrow> (\<Union>i::nat. A i) \<in> sets M)"


inductive_set
  smallest_ccdi_sets :: "('a, 'b) algebra_scheme \<Rightarrow> 'a set set"
  for M
  where
    Basic [intro]:
      "a \<in> sets M \<Longrightarrow> a \<in> smallest_ccdi_sets M"
  | Compl [intro]:
      "a \<in> smallest_ccdi_sets M \<Longrightarrow> space M - a \<in> smallest_ccdi_sets M"
  | Inc:
      "range A \<in> Pow(smallest_ccdi_sets M) \<Longrightarrow> A 0 = {} \<Longrightarrow> (\<And>n. A n \<subseteq> A (Suc n))
       \<Longrightarrow> (\<Union>i. A i) \<in> smallest_ccdi_sets M"
  | Disj:
      "range A \<in> Pow(smallest_ccdi_sets M) \<Longrightarrow> disjoint_family A
       \<Longrightarrow> (\<Union>i::nat. A i) \<in> smallest_ccdi_sets M"
  monos Pow_mono


definition
  smallest_closed_cdi  where
  "smallest_closed_cdi M = (|space = space M, sets = smallest_ccdi_sets M|)"

lemma space_smallest_closed_cdi [simp]:
     "space (smallest_closed_cdi M) = space M"
  by (simp add: smallest_closed_cdi_def)

lemma (in algebra) smallest_closed_cdi1: "sets M \<subseteq> sets (smallest_closed_cdi M)"
  by (auto simp add: smallest_closed_cdi_def)

lemma (in algebra) smallest_ccdi_sets:
     "smallest_ccdi_sets M \<subseteq> Pow (space M)"
  apply (rule subsetI)
  apply (erule smallest_ccdi_sets.induct)
  apply (auto intro: range_subsetD dest: sets_into_space)
  done

lemma (in algebra) smallest_closed_cdi2: "closed_cdi (smallest_closed_cdi M)"
  apply (auto simp add: closed_cdi_def smallest_closed_cdi_def smallest_ccdi_sets)
  apply (blast intro: smallest_ccdi_sets.Inc smallest_ccdi_sets.Disj) +
  done

lemma (in algebra) smallest_closed_cdi3:
     "sets (smallest_closed_cdi M) \<subseteq> Pow (space M)"
  by (simp add: smallest_closed_cdi_def smallest_ccdi_sets)

lemma closed_cdi_subset: "closed_cdi M \<Longrightarrow> sets M \<subseteq> Pow (space M)"
  by (simp add: closed_cdi_def)

lemma closed_cdi_Compl: "closed_cdi M \<Longrightarrow> s \<in> sets M \<Longrightarrow> space M - s \<in> sets M"
  by (simp add: closed_cdi_def)

lemma closed_cdi_Inc:
     "closed_cdi M \<Longrightarrow> range A \<subseteq> sets M \<Longrightarrow> A 0 = {} \<Longrightarrow> (!!n. A n \<subseteq> A (Suc n)) \<Longrightarrow>
        (\<Union>i. A i) \<in> sets M"
  by (simp add: closed_cdi_def)

lemma closed_cdi_Disj:
     "closed_cdi M \<Longrightarrow> range A \<subseteq> sets M \<Longrightarrow> disjoint_family A \<Longrightarrow> (\<Union>i::nat. A i) \<in> sets M"
  by (simp add: closed_cdi_def)

lemma closed_cdi_Un:
  assumes cdi: "closed_cdi M" and empty: "{} \<in> sets M"
      and A: "A \<in> sets M" and B: "B \<in> sets M"
      and disj: "A \<inter> B = {}"
    shows "A \<union> B \<in> sets M"
proof -
  have ra: "range (binaryset A B) \<subseteq> sets M"
   by (simp add: range_binaryset_eq empty A B)
 have di:  "disjoint_family (binaryset A B)" using disj
   by (simp add: disjoint_family_on_def binaryset_def Int_commute)
 from closed_cdi_Disj [OF cdi ra di]
 show ?thesis
   by (simp add: UN_binaryset_eq)
qed

lemma (in algebra) smallest_ccdi_sets_Un:
  assumes A: "A \<in> smallest_ccdi_sets M" and B: "B \<in> smallest_ccdi_sets M"
      and disj: "A \<inter> B = {}"
    shows "A \<union> B \<in> smallest_ccdi_sets M"
proof -
  have ra: "range (binaryset A B) \<in> Pow (smallest_ccdi_sets M)"
    by (simp add: range_binaryset_eq  A B smallest_ccdi_sets.Basic)
  have di:  "disjoint_family (binaryset A B)" using disj
    by (simp add: disjoint_family_on_def binaryset_def Int_commute)
  from Disj [OF ra di]
  show ?thesis
    by (simp add: UN_binaryset_eq)
qed

lemma (in algebra) smallest_ccdi_sets_Int1:
  assumes a: "a \<in> sets M"
  shows "b \<in> smallest_ccdi_sets M \<Longrightarrow> a \<inter> b \<in> smallest_ccdi_sets M"
proof (induct rule: smallest_ccdi_sets.induct)
  case (Basic x)
  thus ?case
    by (metis a Int smallest_ccdi_sets.Basic)
next
  case (Compl x)
  have "a \<inter> (space M - x) = space M - ((space M - a) \<union> (a \<inter> x))"
    by blast
  also have "... \<in> smallest_ccdi_sets M"
    by (metis smallest_ccdi_sets.Compl a Compl(2) Diff_Int2 Diff_Int_distrib2
           Diff_disjoint Int_Diff Int_empty_right Un_commute
           smallest_ccdi_sets.Basic smallest_ccdi_sets.Compl
           smallest_ccdi_sets_Un)
  finally show ?case .
next
  case (Inc A)
  have 1: "(\<Union>i. (\<lambda>i. a \<inter> A i) i) = a \<inter> (\<Union>i. A i)"
    by blast
  have "range (\<lambda>i. a \<inter> A i) \<in> Pow(smallest_ccdi_sets M)" using Inc
    by blast
  moreover have "(\<lambda>i. a \<inter> A i) 0 = {}"
    by (simp add: Inc)
  moreover have "!!n. (\<lambda>i. a \<inter> A i) n \<subseteq> (\<lambda>i. a \<inter> A i) (Suc n)" using Inc
    by blast
  ultimately have 2: "(\<Union>i. (\<lambda>i. a \<inter> A i) i) \<in> smallest_ccdi_sets M"
    by (rule smallest_ccdi_sets.Inc)
  show ?case
    by (metis 1 2)
next
  case (Disj A)
  have 1: "(\<Union>i. (\<lambda>i. a \<inter> A i) i) = a \<inter> (\<Union>i. A i)"
    by blast
  have "range (\<lambda>i. a \<inter> A i) \<in> Pow(smallest_ccdi_sets M)" using Disj
    by blast
  moreover have "disjoint_family (\<lambda>i. a \<inter> A i)" using Disj
    by (auto simp add: disjoint_family_on_def)
  ultimately have 2: "(\<Union>i. (\<lambda>i. a \<inter> A i) i) \<in> smallest_ccdi_sets M"
    by (rule smallest_ccdi_sets.Disj)
  show ?case
    by (metis 1 2)
qed


lemma (in algebra) smallest_ccdi_sets_Int:
  assumes b: "b \<in> smallest_ccdi_sets M"
  shows "a \<in> smallest_ccdi_sets M \<Longrightarrow> a \<inter> b \<in> smallest_ccdi_sets M"
proof (induct rule: smallest_ccdi_sets.induct)
  case (Basic x)
  thus ?case
    by (metis b smallest_ccdi_sets_Int1)
next
  case (Compl x)
  have "(space M - x) \<inter> b = space M - (x \<inter> b \<union> (space M - b))"
    by blast
  also have "... \<in> smallest_ccdi_sets M"
    by (metis Compl(2) Diff_disjoint Int_Diff Int_commute Int_empty_right b
           smallest_ccdi_sets.Compl smallest_ccdi_sets_Un)
  finally show ?case .
next
  case (Inc A)
  have 1: "(\<Union>i. (\<lambda>i. A i \<inter> b) i) = (\<Union>i. A i) \<inter> b"
    by blast
  have "range (\<lambda>i. A i \<inter> b) \<in> Pow(smallest_ccdi_sets M)" using Inc
    by blast
  moreover have "(\<lambda>i. A i \<inter> b) 0 = {}"
    by (simp add: Inc)
  moreover have "!!n. (\<lambda>i. A i \<inter> b) n \<subseteq> (\<lambda>i. A i \<inter> b) (Suc n)" using Inc
    by blast
  ultimately have 2: "(\<Union>i. (\<lambda>i. A i \<inter> b) i) \<in> smallest_ccdi_sets M"
    by (rule smallest_ccdi_sets.Inc)
  show ?case
    by (metis 1 2)
next
  case (Disj A)
  have 1: "(\<Union>i. (\<lambda>i. A i \<inter> b) i) = (\<Union>i. A i) \<inter> b"
    by blast
  have "range (\<lambda>i. A i \<inter> b) \<in> Pow(smallest_ccdi_sets M)" using Disj
    by blast
  moreover have "disjoint_family (\<lambda>i. A i \<inter> b)" using Disj
    by (auto simp add: disjoint_family_on_def)
  ultimately have 2: "(\<Union>i. (\<lambda>i. A i \<inter> b) i) \<in> smallest_ccdi_sets M"
    by (rule smallest_ccdi_sets.Disj)
  show ?case
    by (metis 1 2)
qed

lemma (in algebra) sets_smallest_closed_cdi_Int:
   "a \<in> sets (smallest_closed_cdi M) \<Longrightarrow> b \<in> sets (smallest_closed_cdi M)
    \<Longrightarrow> a \<inter> b \<in> sets (smallest_closed_cdi M)"
  by (simp add: smallest_ccdi_sets_Int smallest_closed_cdi_def)

lemma (in algebra) sigma_property_disjoint_lemma:
  assumes sbC: "sets M \<subseteq> C"
      and ccdi: "closed_cdi (|space = space M, sets = C|)"
  shows "sigma_sets (space M) (sets M) \<subseteq> C"
proof -
  have "smallest_ccdi_sets M \<in> {B . sets M \<subseteq> B \<and> sigma_algebra (|space = space M, sets = B|)}"
    apply (auto simp add: sigma_algebra_disjoint_iff algebra_iff_Int
            smallest_ccdi_sets_Int)
    apply (metis Union_Pow_eq Union_upper subsetD smallest_ccdi_sets)
    apply (blast intro: smallest_ccdi_sets.Disj)
    done
  hence "sigma_sets (space M) (sets M) \<subseteq> smallest_ccdi_sets M"
    by clarsimp
       (drule sigma_algebra.sigma_sets_subset [where a="sets M"], auto)
  also have "...  \<subseteq> C"
    proof
      fix x
      assume x: "x \<in> smallest_ccdi_sets M"
      thus "x \<in> C"
        proof (induct rule: smallest_ccdi_sets.induct)
          case (Basic x)
          thus ?case
            by (metis Basic subsetD sbC)
        next
          case (Compl x)
          thus ?case
            by (blast intro: closed_cdi_Compl [OF ccdi, simplified])
        next
          case (Inc A)
          thus ?case
               by (auto intro: closed_cdi_Inc [OF ccdi, simplified])
        next
          case (Disj A)
          thus ?case
               by (auto intro: closed_cdi_Disj [OF ccdi, simplified])
        qed
    qed
  finally show ?thesis .
qed

lemma (in algebra) sigma_property_disjoint:
  assumes sbC: "sets M \<subseteq> C"
      and compl: "!!s. s \<in> C \<inter> sigma_sets (space M) (sets M) \<Longrightarrow> space M - s \<in> C"
      and inc: "!!A. range A \<subseteq> C \<inter> sigma_sets (space M) (sets M)
                     \<Longrightarrow> A 0 = {} \<Longrightarrow> (!!n. A n \<subseteq> A (Suc n))
                     \<Longrightarrow> (\<Union>i. A i) \<in> C"
      and disj: "!!A. range A \<subseteq> C \<inter> sigma_sets (space M) (sets M)
                      \<Longrightarrow> disjoint_family A \<Longrightarrow> (\<Union>i::nat. A i) \<in> C"
  shows "sigma_sets (space M) (sets M) \<subseteq> C"
proof -
  have "sigma_sets (space M) (sets M) \<subseteq> C \<inter> sigma_sets (space M) (sets M)"
    proof (rule sigma_property_disjoint_lemma)
      show "sets M \<subseteq> C \<inter> sigma_sets (space M) (sets M)"
        by (metis Int_greatest Set.subsetI sbC sigma_sets.Basic)
    next
      show "closed_cdi \<lparr>space = space M, sets = C \<inter> sigma_sets (space M) (sets M)\<rparr>"
        by (simp add: closed_cdi_def compl inc disj)
           (metis PowI Set.subsetI le_infI2 sigma_sets_into_sp space_closed
             IntE sigma_sets.Compl range_subsetD sigma_sets.Union)
    qed
  thus ?thesis
    by blast
qed

end
