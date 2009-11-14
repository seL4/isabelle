header {*Measures*}

theory Measure
  imports Caratheodory FuncSet
begin

text{*From the Hurd/Coble measure theory development, translated by Lawrence Paulson.*}

definition prod_sets where
  "prod_sets A B = {z. \<exists>x \<in> A. \<exists>y \<in> B. z = x \<times> y}"

lemma prod_setsI: "x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> (x \<times> y) \<in> prod_sets A B"
  by (auto simp add: prod_sets_def) 

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

definition
  measurable  where
  "measurable a b = {f . sigma_algebra a & sigma_algebra b &
                         f \<in> (space a -> space b) &
                         (\<forall>y \<in> sets b. (f -` y) \<inter> (space a) \<in> sets a)}"

definition
  measure_preserving  where
  "measure_preserving m1 m2 =
     measurable m1 m2 \<inter> 
     {f . measure_space m1 & measure_space m2 &
          (\<forall>y \<in> sets m2. measure m1 ((f -` y) \<inter> (space m1)) = measure m2 y)}"

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
   by (simp add: disjoint_family_def binaryset_def Int_commute) 
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
    by (simp add: range_binaryset_eq  A B empty_sets smallest_ccdi_sets.Basic)
  have di:  "disjoint_family (binaryset A B)" using disj
    by (simp add: disjoint_family_def binaryset_def Int_commute) 
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
    by (auto simp add: disjoint_family_def) 
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
    by (auto simp add: disjoint_family_def) 
  ultimately have 2: "(\<Union>i. (\<lambda>i. A i \<inter> b) i) \<in> smallest_ccdi_sets M"
    by (rule smallest_ccdi_sets.Disj) 
  show ?case
    by (metis 1 2)
qed

lemma (in algebra) sets_smallest_closed_cdi_Int:
   "a \<in> sets (smallest_closed_cdi M) \<Longrightarrow> b \<in> sets (smallest_closed_cdi M)
    \<Longrightarrow> a \<inter> b \<in> sets (smallest_closed_cdi M)"
  by (simp add: smallest_ccdi_sets_Int smallest_closed_cdi_def) 

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
    by auto 
       (metis sigma_algebra.sigma_sets_subset algebra.simps(1) 
          algebra.simps(2) subsetD) 
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


(* or just countably_additiveD [OF measure_space.ca] *)
lemma (in measure_space) measure_countably_additive:
    "range A \<subseteq> sets M
     \<Longrightarrow> disjoint_family A \<Longrightarrow> (\<Union>i. A i) \<in> sets M
     \<Longrightarrow> (measure M o A)  sums  measure M (\<Union>i. A i)"
  by (insert ca) (simp add: countably_additive_def o_def) 

lemma (in measure_space) additive:
     "additive M (measure M)"
proof (rule algebra.countably_additive_additive [OF _ _ ca]) 
  show "algebra M"
    by (blast intro: sigma_algebra.axioms local.sigma_algebra_axioms)
  show "positive M (measure M)"
    by (simp add: positive_def empty_measure positive) 
qed
 
lemma (in measure_space) measure_additive:
     "a \<in> sets M \<Longrightarrow> b \<in> sets M \<Longrightarrow> a \<inter> b = {} 
      \<Longrightarrow> measure M a + measure M b = measure M (a \<union> b)"
  by (metis additiveD additive)

lemma (in measure_space) measure_compl:
  assumes s: "s \<in> sets M"
  shows "measure M (space M - s) = measure M (space M) - measure M s"
proof -
  have "measure M (space M) = measure M (s \<union> (space M - s))" using s
    by (metis Un_Diff_cancel Un_absorb1 s sets_into_space)
  also have "... = measure M s + measure M (space M - s)"
    by (rule additiveD [OF additive]) (auto simp add: s) 
  finally have "measure M (space M) = measure M s + measure M (space M - s)" .
  thus ?thesis
    by arith
qed

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
    by (auto simp add: disjoint_family_def)
      (metis insert_absorb insert_subset le_SucE le_antisym not_leE) 
qed


lemma (in measure_space) measure_countable_increasing:
  assumes A: "range A \<subseteq> sets M"
      and A0: "A 0 = {}"
      and ASuc: "!!n.  A n \<subseteq> A (Suc n)"
  shows "(measure M o A) ----> measure M (\<Union>i. A i)"
proof -
  {
    fix n
    have "(measure M \<circ> A) n =
          setsum (measure M \<circ> (\<lambda>i. A (Suc i) - A i)) {0..<n}"
      proof (induct n)
        case 0 thus ?case by (auto simp add: A0 empty_measure)
      next
        case (Suc m) 
        have "A (Suc m) = A m \<union> (A (Suc m) - A m)"
          by (metis ASuc Un_Diff_cancel Un_absorb1)
        hence "measure M (A (Suc m)) =
               measure M (A m) + measure M (A (Suc m) - A m)" 
          by (subst measure_additive) 
             (auto simp add: measure_additive range_subsetD [OF A]) 
        with Suc show ?case
          by simp
      qed
  }
  hence Meq: "measure M o A = (\<lambda>n. setsum (measure M o (\<lambda>i. A(Suc i) - A i)) {0..<n})"
    by (blast intro: ext) 
  have Aeq: "(\<Union>i. A (Suc i) - A i) = (\<Union>i. A i)"
    proof (rule UN_finite2_eq [where k=1], simp) 
      fix i
      show "(\<Union>i\<in>{0..<i}. A (Suc i) - A i) = (\<Union>i\<in>{0..<Suc i}. A i)"
        proof (induct i)
          case 0 thus ?case by (simp add: A0)
        next
          case (Suc i) 
          thus ?case
            by (auto simp add: atLeastLessThanSuc intro: subsetD [OF ASuc])
        qed
    qed
  have A1: "\<And>i. A (Suc i) - A i \<in> sets M"
    by (metis A Diff range_subsetD)
  have A2: "(\<Union>i. A (Suc i) - A i) \<in> sets M"
    by (blast intro: countable_UN range_subsetD [OF A])  
  have "(measure M o (\<lambda>i. A (Suc i) - A i)) sums measure M (\<Union>i. A (Suc i) - A i)"
    by (rule measure_countably_additive) 
       (auto simp add: disjoint_family_Suc ASuc A1 A2)
  also have "... =  measure M (\<Union>i. A i)"
    by (simp add: Aeq) 
  finally have "(measure M o (\<lambda>i. A (Suc i) - A i)) sums measure M (\<Union>i. A i)" .
  thus ?thesis
    by (auto simp add: sums_iff Meq dest: summable_sumr_LIMSEQ_suminf) 
qed

lemma (in measure_space) monotone_convergence:
  assumes A: "range A \<subseteq> sets M"
      and ASuc: "!!n.  A n \<subseteq> A (Suc n)"
  shows "(measure M \<circ> A) ----> measure M (\<Union>i. A i)"
proof -
  have ueq: "(\<Union>i. nat_case {} A i) = (\<Union>i. A i)" 
    by (auto simp add: split: nat.splits) 
  have meq: "measure M \<circ> A = (\<lambda>n. (measure M \<circ> nat_case {} A) (Suc n))"
    by (rule ext) simp
  have "(measure M \<circ> nat_case {} A) ----> measure M (\<Union>i. nat_case {} A i)" 
    by (rule measure_countable_increasing) 
       (auto simp add: range_subsetD [OF A] subsetD [OF ASuc] split: nat.splits) 
  also have "... = measure M (\<Union>i. A i)" 
    by (simp add: ueq) 
  finally have "(measure M \<circ> nat_case {} A) ---->  measure M (\<Union>i. A i)" .
  thus ?thesis using meq
    by (metis LIMSEQ_Suc)
qed

lemma measurable_sigma_preimages:
  assumes a: "sigma_algebra a" and b: "sigma_algebra b"
      and f: "f \<in> space a -> space b"
      and ba: "!!y. y \<in> sets b ==> f -` y \<in> sets a"
  shows "sigma_algebra (|space = space a, sets = (vimage f) ` (sets b) |)"
proof (simp add: sigma_algebra_iff2, intro conjI) 
  show "op -` f ` sets b \<subseteq> Pow (space a)"
    by auto (metis IntE a algebra.Int_space_eq1 ba sigma_algebra_iff vimageI) 
next
  show "{} \<in> op -` f ` sets b"
    by (metis algebra.empty_sets b image_iff sigma_algebra_iff vimage_empty)
next
  { fix y
    assume y: "y \<in> sets b"
    with a b f
    have "space a - f -` y = f -` (space b - y)"
      by (auto simp add: sigma_algebra_iff2) (blast intro: ba) 
    hence "space a - (f -` y) \<in> (vimage f) ` sets b"
      by auto
         (metis b y subsetD equalityE imageI sigma_algebra.sigma_sets_eq
                sigma_sets.Compl) 
  } 
  thus "\<forall>s\<in>sets b. space a - f -` s \<in> (vimage f) ` sets b"
    by blast
next
  {
    fix A:: "nat \<Rightarrow> 'a set"
    assume A: "range A \<subseteq> (vimage f) ` (sets b)"
    have  "(\<Union>i. A i) \<in> (vimage f) ` (sets b)"
      proof -
        def B \<equiv> "\<lambda>i. @v. v \<in> sets b \<and> f -` v = A i"
        { 
          fix i
          have "A i \<in> (vimage f) ` (sets b)" using A
            by blast
          hence "\<exists>v. v \<in> sets b \<and> f -` v = A i"
            by blast
          hence "B i \<in> sets b \<and> f -` B i = A i" 
            by (simp add: B_def) (erule someI_ex)
        } note B = this
        show ?thesis
          proof
            show "(\<Union>i. A i) = f -` (\<Union>i. B i)"
              by (simp add: vimage_UN B) 
           show "(\<Union>i. B i) \<in> sets b" using B
             by (auto intro: sigma_algebra.countable_UN [OF b]) 
          qed
      qed
  }
  thus "\<forall>A::nat \<Rightarrow> 'a set.
           range A \<subseteq> (vimage f) ` sets b \<longrightarrow> (\<Union>i. A i) \<in> (vimage f) ` sets b"
    by blast
qed

lemma (in sigma_algebra) measurable_sigma:
  assumes B: "B \<subseteq> Pow X" 
      and f: "f \<in> space M -> X"
      and ba: "!!y. y \<in> B ==> (f -` y) \<inter> space M \<in> sets M"
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

lemma measurable_subset:
     "measurable a b \<subseteq> measurable a (sigma (space b) (sets b))"
  apply clarify
  apply (rule sigma_algebra.measurable_sigma) 
  apply (auto simp add: measurable_def)
  apply (metis algebra.sets_into_space subsetD sigma_algebra_iff) 
  done

lemma measurable_eqI: 
     "space m1 = space m1' \<Longrightarrow> space m2 = space m2'
      \<Longrightarrow> sets m1 = sets m1' \<Longrightarrow> sets m2 = sets m2'
      \<Longrightarrow> measurable m1 m2 = measurable m1' m2'"
  by (simp add: measurable_def sigma_algebra_iff2) 

lemma measure_preserving_lift:
  fixes f :: "'a1 \<Rightarrow> 'a2" 
    and m1 :: "('a1, 'b1) measure_space_scheme"
    and m2 :: "('a2, 'b2) measure_space_scheme"
  assumes m1: "measure_space m1" and m2: "measure_space m2" 
  defines "m x \<equiv> (|space = space m2, sets = x, measure = measure m2, ... = more m2|)"
  assumes setsm2: "sets m2 = sigma_sets (space m2) a"
      and fmp: "f \<in> measure_preserving m1 (m a)"
  shows "f \<in> measure_preserving m1 m2"
proof -
  have [simp]: "!!x. space (m x) = space m2 & sets (m x) = x & measure (m x) = measure m2"
    by (simp add: m_def) 
  have sa1: "sigma_algebra m1" using m1 
    by (simp add: measure_space_def) 
  show ?thesis using fmp
    proof (clarsimp simp add: measure_preserving_def m1 m2) 
      assume fm: "f \<in> measurable m1 (m a)" 
         and mam: "measure_space (m a)"
         and meq: "\<forall>y\<in>a. measure m1 (f -` y \<inter> space m1) = measure m2 y"
      have "f \<in> measurable m1 (sigma (space (m a)) (sets (m a)))"
        by (rule subsetD [OF measurable_subset fm]) 
      also have "... = measurable m1 m2"
        by (rule measurable_eqI) (simp_all add: m_def setsm2 sigma_def) 
      finally have f12: "f \<in> measurable m1 m2" .
      hence ffn: "f \<in> space m1 \<rightarrow> space m2"
        by (simp add: measurable_def) 
      have "space m1 \<subseteq> f -` (space m2)"
        by auto (metis PiE ffn)
      hence fveq [simp]: "(f -` (space m2)) \<inter> space m1 = space m1"
        by blast
      {
        fix y
        assume y: "y \<in> sets m2" 
        have ama: "algebra (m a)"  using mam
          by (simp add: measure_space_def sigma_algebra_iff) 
        have spa: "space m2 \<in> a" using algebra.top [OF ama]
          by (simp add: m_def) 
        have "sigma_sets (space m2) a = sigma_sets (space (m a)) (sets (m a))"
          by (simp add: m_def) 
        also have "... \<subseteq> {s . measure m1 ((f -` s) \<inter> space m1) = measure m2 s}"
          proof (rule algebra.sigma_property_disjoint, auto simp add: ama) 
            fix x
            assume x: "x \<in> a"
            thus "measure m1 (f -` x \<inter> space m1) = measure m2 x"
              by (simp add: meq)
          next
            fix s
            assume eq: "measure m1 (f -` s \<inter> space m1) = measure m2 s"
               and s: "s \<in> sigma_sets (space m2) a"
            hence s2: "s \<in> sets m2"
              by (simp add: setsm2) 
            thus "measure m1 (f -` (space m2 - s) \<inter> space m1) =
                  measure m2 (space m2 - s)" using f12
              by (simp add: vimage_Diff Diff_Int_distrib2 eq m1 m2
                    measure_space.measure_compl measurable_def)  
                 (metis fveq meq spa) 
          next
            fix A
              assume A0: "A 0 = {}"
                 and ASuc: "!!n.  A n \<subseteq> A (Suc n)"
                 and rA1: "range A \<subseteq> 
                           {s. measure m1 (f -` s \<inter> space m1) = measure m2 s}"
                 and "range A \<subseteq> sigma_sets (space m2) a"
              hence rA2: "range A \<subseteq> sets m2" by (metis setsm2)
              have eq1: "!!i. measure m1 (f -` A i \<inter> space m1) = measure m2 (A i)"
                using rA1 by blast
              have "(measure m2 \<circ> A) = measure m1 o (\<lambda>i. (f -` A i \<inter> space m1))" 
                by (simp add: o_def eq1) 
              also have "... ----> measure m1 (\<Union>i. f -` A i \<inter> space m1)"
                proof (rule measure_space.measure_countable_increasing [OF m1])
                  show "range (\<lambda>i. f -` A i \<inter> space m1) \<subseteq> sets m1"
                    using f12 rA2 by (auto simp add: measurable_def)
                  show "f -` A 0 \<inter> space m1 = {}" using A0
                    by blast
                  show "\<And>n. f -` A n \<inter> space m1 \<subseteq> f -` A (Suc n) \<inter> space m1"
                    using ASuc by auto
                qed
              also have "... = measure m1 (f -` (\<Union>i. A i) \<inter> space m1)"
                by (simp add: vimage_UN)
              finally have "(measure m2 \<circ> A) ----> measure m1 (f -` (\<Union>i. A i) \<inter> space m1)" .
              moreover
              have "(measure m2 \<circ> A) ----> measure m2 (\<Union>i. A i)"
                by (rule measure_space.measure_countable_increasing 
                          [OF m2 rA2, OF A0 ASuc])
              ultimately 
              show "measure m1 (f -` (\<Union>i. A i) \<inter> space m1) =
                    measure m2 (\<Union>i. A i)"
                by (rule LIMSEQ_unique) 
          next
            fix A :: "nat => 'a2 set"
              assume dA: "disjoint_family A"
                 and rA1: "range A \<subseteq> 
                           {s. measure m1 (f -` s \<inter> space m1) = measure m2 s}"
                 and "range A \<subseteq> sigma_sets (space m2) a"
              hence rA2: "range A \<subseteq> sets m2" by (metis setsm2)
              hence Um2: "(\<Union>i. A i) \<in> sets m2"
                by (metis range_subsetD setsm2 sigma_sets.Union)
              have "!!i. measure m1 (f -` A i \<inter> space m1) = measure m2 (A i)"
                using rA1 by blast
              hence "measure m2 o A = measure m1 o (\<lambda>i. f -` A i \<inter> space m1)"
                by (simp add: o_def) 
              also have "... sums measure m1 (\<Union>i. f -` A i \<inter> space m1)" 
                proof (rule measure_space.measure_countably_additive [OF m1] )
                  show "range (\<lambda>i. f -` A i \<inter> space m1) \<subseteq> sets m1"
                    using f12 rA2 by (auto simp add: measurable_def)
                  show "disjoint_family (\<lambda>i. f -` A i \<inter> space m1)" using dA
                    by (auto simp add: disjoint_family_def) 
                  show "(\<Union>i. f -` A i \<inter> space m1) \<in> sets m1"
                    proof (rule sigma_algebra.countable_UN [OF sa1])
                      show "range (\<lambda>i. f -` A i \<inter> space m1) \<subseteq> sets m1" using f12 rA2
                        by (auto simp add: measurable_def) 
                    qed
                qed
              finally have "(measure m2 o A) sums measure m1 (\<Union>i. f -` A i \<inter> space m1)" .
              with measure_space.measure_countably_additive [OF m2 rA2 dA Um2] 
              have "measure m1 (\<Union>i. f -` A i \<inter> space m1) = measure m2 (\<Union>i. A i)"
                by (metis sums_unique) 

              moreover have "measure m1 (f -` (\<Union>i. A i) \<inter> space m1) = measure m1 (\<Union>i. f -` A i \<inter> space m1)"
                by (simp add: vimage_UN)
              ultimately show "measure m1 (f -` (\<Union>i. A i) \<inter> space m1) =
                    measure m2 (\<Union>i. A i)" 
                by metis
          qed
        finally have "sigma_sets (space m2) a 
              \<subseteq> {s . measure m1 ((f -` s) \<inter> space m1) = measure m2 s}" .
        hence "measure m1 (f -` y \<inter> space m1) = measure m2 y" using y
          by (force simp add: setsm2) 
      }
      thus "f \<in> measurable m1 m2 \<and>
       (\<forall>y\<in>sets m2.
           measure m1 (f -` y \<inter> space m1) = measure m2 y)"
        by (blast intro: f12) 
    qed
qed

lemma measurable_ident:
     "sigma_algebra M ==> id \<in> measurable M M"
  apply (simp add: measurable_def)
  apply (auto simp add: sigma_algebra_def algebra.Int algebra.top)
  done

lemma measurable_comp:
  fixes f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'c" 
  shows "f \<in> measurable a b \<Longrightarrow> g \<in> measurable b c \<Longrightarrow> (g o f) \<in> measurable a c"
  apply (auto simp add: measurable_def vimage_compose) 
  apply (subgoal_tac "f -` g -` y \<inter> space a = f -` (g -` y \<inter> space b) \<inter> space a")
  apply force+
  done

 lemma measurable_strong:
  fixes f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'c" 
  assumes f: "f \<in> measurable a b" and g: "g \<in> (space b -> space c)"
      and c: "sigma_algebra c"
      and t: "f ` (space a) \<subseteq> t"
      and cb: "\<And>s. s \<in> sets c \<Longrightarrow> (g -` s) \<inter> t \<in> sets b"
  shows "(g o f) \<in> measurable a c"
proof -
  have a: "sigma_algebra a" and b: "sigma_algebra b"
   and fab: "f \<in> (space a -> space b)"
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
   "measurable a b \<subseteq> measurable (sigma (space a) (sets a)) b"
  apply (auto simp add: measurable_def) 
  apply (metis sigma_algebra_iff2 sigma_algebra_sigma)
  apply (metis algebra.simps(2) sigma_algebra.sigma_sets_eq sigma_def) 
  done

lemma measure_preserving_up:
   "f \<in> measure_preserving \<lparr>space = space m1, sets = a, measure = measure m1\<rparr> m2 \<Longrightarrow>
    measure_space m1 \<Longrightarrow> sigma_algebra m1 \<Longrightarrow> a \<subseteq> sets m1 
    \<Longrightarrow> f \<in> measure_preserving m1 m2"
  by (auto simp add: measure_preserving_def measurable_def) 

lemma measure_preserving_up_sigma:
   "measure_space m1 \<Longrightarrow> (sets m1 = sets (sigma (space m1) a))
    \<Longrightarrow> measure_preserving \<lparr>space = space m1, sets = a, measure = measure m1\<rparr> m2 
        \<subseteq> measure_preserving m1 m2"
  apply (rule subsetI) 
  apply (rule measure_preserving_up) 
  apply (simp_all add: measure_space_def sigma_def) 
  apply (metis sigma_algebra.sigma_sets_eq subsetI sigma_sets.Basic) 
  done

lemma (in sigma_algebra) measurable_prod_sigma:
  assumes 1: "(fst o f) \<in> measurable M a1" and 2: "(snd o f) \<in> measurable M a2"
  shows "f \<in> measurable M (sigma ((space a1) \<times> (space a2)) 
                          (prod_sets (sets a1) (sets a2)))"
proof -
  from 1 have sa1: "sigma_algebra a1" and fn1: "fst \<circ> f \<in> space M \<rightarrow> space a1"
     and q1: "\<forall>y\<in>sets a1. (fst \<circ> f) -` y \<inter> space M \<in> sets M"
    by (auto simp add: measurable_def) 
  from 2 have sa2: "sigma_algebra a2" and fn2: "snd \<circ> f \<in> space M \<rightarrow> space a2"
     and q2: "\<forall>y\<in>sets a2. (snd \<circ> f) -` y \<inter> space M \<in> sets M"
    by (auto simp add: measurable_def) 
  show ?thesis
    proof (rule measurable_sigma) 
      show "prod_sets (sets a1) (sets a2) \<subseteq> Pow (space a1 \<times> space a2)" using sa1 sa2
        by (force simp add: prod_sets_def sigma_algebra_iff algebra_def) 
    next
      show "f \<in> space M \<rightarrow> space a1 \<times> space a2" 
        by (rule prod_final [OF fn1 fn2])
    next
      fix z
      assume z: "z \<in> prod_sets (sets a1) (sets a2)" 
      thus "f -` z \<inter> space M \<in> sets M"
        proof (auto simp add: prod_sets_def vimage_Times) 
          fix x y
          assume x: "x \<in> sets a1" and y: "y \<in> sets a2"
          have "(fst \<circ> f) -` x \<inter> (snd \<circ> f) -` y \<inter> space M = 
                ((fst \<circ> f) -` x \<inter> space M) \<inter> ((snd \<circ> f) -` y \<inter> space M)"
            by blast
          also have "...  \<in> sets M" using x y q1 q2
            by blast
          finally show "(fst \<circ> f) -` x \<inter> (snd \<circ> f) -` y \<inter> space M \<in> sets M" .
        qed
    qed
qed


lemma (in measure_space) measurable_range_reduce:
   "f \<in> measurable M \<lparr>space = s, sets = Pow s\<rparr> \<Longrightarrow>
    s \<noteq> {} 
    \<Longrightarrow> f \<in> measurable M \<lparr>space = s \<inter> (f ` space M), sets = Pow (s \<inter> (f ` space M))\<rparr>"
  by (simp add: measurable_def sigma_algebra_Pow del: Pow_Int_eq) blast

lemma (in measure_space) measurable_Pow_to_Pow:
   "(sets M = Pow (space M)) \<Longrightarrow> f \<in> measurable M \<lparr>space = UNIV, sets = Pow UNIV\<rparr>"
  by (auto simp add: measurable_def sigma_algebra_def sigma_algebra_axioms_def algebra_def)

lemma (in measure_space) measurable_Pow_to_Pow_image:
   "sets M = Pow (space M)
    \<Longrightarrow> f \<in> measurable M \<lparr>space = f ` space M, sets = Pow (f ` space M)\<rparr>"
  by (simp add: measurable_def sigma_algebra_Pow) intro_locales

lemma (in measure_space) measure_real_sum_image:
  assumes s: "s \<in> sets M"
      and ssets: "\<And>x. x \<in> s ==> {x} \<in> sets M"
      and fin: "finite s"
  shows "measure M s = (\<Sum>x\<in>s. measure M {x})"
proof -
  {
    fix u
    assume u: "u \<subseteq> s & u \<in> sets M"
    hence "finite u"
      by (metis fin finite_subset) 
    hence "measure M u = (\<Sum>x\<in>u. measure M {x})" using u
      proof (induct u)
        case empty
        thus ?case by simp
      next
        case (insert x t)
        hence x: "x \<in> s" and t: "t \<subseteq> s" 
          by (simp_all add: insert_subset) 
        hence ts: "t \<in> sets M"  using insert
          by (metis Diff_insert_absorb Diff ssets)
        have "measure M (insert x t) = measure M ({x} \<union> t)"
          by simp
        also have "... = measure M {x} + measure M t" 
          by (simp add: measure_additive insert insert_disjoint ssets x ts 
                  del: Un_insert_left)
        also have "... = (\<Sum>x\<in>insert x t. measure M {x})" 
          by (simp add: x t ts insert) 
        finally show ?case .
      qed
    }
  thus ?thesis
    by (metis subset_refl s)
qed
  
lemma (in sigma_algebra) sigma_algebra_extend:
     "sigma_algebra \<lparr>space = space M, sets = sets M, measure_space.measure = f\<rparr>"
   by unfold_locales (auto intro!: space_closed)

lemma (in sigma_algebra) finite_additivity_sufficient:
  assumes fin: "finite (space M)"
      and posf: "positive M f" and addf: "additive M f" 
  defines "Mf \<equiv> \<lparr>space = space M, sets = sets M, measure = f\<rparr>"
  shows "measure_space Mf" 
proof -
  have [simp]: "f {} = 0" using posf
    by (simp add: positive_def) 
  have "countably_additive Mf f"
    proof (auto simp add: countably_additive_def positive_def) 
      fix A :: "nat \<Rightarrow> 'a set"
      assume A: "range A \<subseteq> sets Mf"
         and disj: "disjoint_family A"
         and UnA: "(\<Union>i. A i) \<in> sets Mf"
      def I \<equiv> "{i. A i \<noteq> {}}"
      have "Union (A ` I) \<subseteq> space M" using A
        by (auto simp add: Mf_def) (metis range_subsetD subsetD sets_into_space) 
      hence "finite (A ` I)"
        by (metis finite_UnionD finite_subset fin) 
      moreover have "inj_on A I" using disj
        by (auto simp add: I_def disjoint_family_def inj_on_def) 
      ultimately have finI: "finite I"
        by (metis finite_imageD)
      hence "\<exists>N. \<forall>m\<ge>N. A m = {}"
        proof (cases "I = {}")
          case True thus ?thesis by (simp add: I_def) 
        next
          case False
          hence "\<forall>i\<in>I. i < Suc(Max I)"
            by (simp add: Max_less_iff [symmetric] finI) 
          hence "\<forall>m \<ge> Suc(Max I). A m = {}"
            by (simp add: I_def) (metis less_le_not_le) 
          thus ?thesis
            by blast
        qed
      then obtain N where N: "\<forall>m\<ge>N. A m = {}" by blast
      hence "\<forall>m\<ge>N. (f o A) m = 0"
        by simp 
      hence "(\<lambda>n. f (A n)) sums setsum (f o A) {0..<N}" 
        by (simp add: series_zero o_def) 
      also have "... = f (\<Union>i<N. A i)"
        proof (induct N)
          case 0 thus ?case by simp
        next
          case (Suc n) 
          have "f (A n \<union> (\<Union> x<n. A x)) = f (A n) + f (\<Union> i<n. A i)"
            proof (rule Caratheodory.additiveD [OF addf])
              show "A n \<inter> (\<Union> x<n. A x) = {}" using disj
                by (auto simp add: disjoint_family_def nat_less_le) blast
              show "A n \<in> sets M" using A 
                by (force simp add: Mf_def) 
              show "(\<Union>i<n. A i) \<in> sets M"
                proof (induct n)
                  case 0 thus ?case by simp
                next
                  case (Suc n) thus ?case using A
                    by (simp add: lessThan_Suc Mf_def Un range_subsetD) 
                qed
            qed
          thus ?case using Suc
            by (simp add: lessThan_Suc) 
        qed
      also have "... = f (\<Union>i. A i)" 
        proof -
          have "(\<Union> i<N. A i) = (\<Union>i. A i)" using N
            by auto (metis Int_absorb N disjoint_iff_not_equal lessThan_iff not_leE)
          thus ?thesis by simp
        qed
      finally show "(\<lambda>n. f (A n)) sums f (\<Union>i. A i)" .
    qed
  thus ?thesis using posf 
    by (simp add: Mf_def measure_space_def measure_space_axioms_def sigma_algebra_extend positive_def) 
qed

lemma finite_additivity_sufficient:
     "sigma_algebra M 
      \<Longrightarrow> finite (space M) 
      \<Longrightarrow> positive M (measure M) \<Longrightarrow> additive M (measure M) 
      \<Longrightarrow> measure_space M"
  by (rule measure_down [OF sigma_algebra.finite_additivity_sufficient], auto) 

end

