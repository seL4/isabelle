(*  Title:      HOL/Probability/Fin_Map.thy
    Author:     Fabian Immler, TU München
*)

section \<open>Finite Maps\<close>

theory Fin_Map
  imports "HOL-Analysis.Finite_Product_Measure" "HOL-Library.Finite_Map"
begin

text \<open>The \<^type>\<open>fmap\<close> type can be instantiated to \<^class>\<open>polish_space\<close>, needed for the proof of
  projective limit. \<^const>\<open>extensional\<close> functions are used for the representation in order to
  stay close to the developments of (finite) products \<^const>\<open>Pi\<^sub>E\<close> and their sigma-algebra
  \<^const>\<open>Pi\<^sub>M\<close>.\<close>

type_notation fmap ("(_ \<Rightarrow>\<^sub>F /_)" [22, 21] 21)

unbundle fmap.lifting


subsection \<open>Domain and Application\<close>

lift_definition domain::"('i \<Rightarrow>\<^sub>F 'a) \<Rightarrow> 'i set" is dom .

lemma finite_domain[simp, intro]: "finite (domain P)"
  by transfer simp

lift_definition proj :: "('i \<Rightarrow>\<^sub>F 'a) \<Rightarrow> 'i \<Rightarrow> 'a" ("'((_)')\<^sub>F" [0] 1000) is
  "\<lambda>f x. if x \<in> dom f then the (f x) else undefined" .

declare [[coercion proj]]

lemma extensional_proj[simp, intro]: "(P)\<^sub>F \<in> extensional (domain P)"
  by transfer (auto simp: extensional_def)

lemma proj_undefined[simp, intro]: "i \<notin> domain P \<Longrightarrow> P i = undefined"
  using extensional_proj[of P] unfolding extensional_def by auto

lemma finmap_eq_iff: "P = Q \<longleftrightarrow> (domain P = domain Q \<and> (\<forall>i\<in>domain P. P i = Q i))"
  apply transfer
  apply (safe intro!: ext)
  subgoal for P Q x
    by (cases "x \<in> dom P"; cases "P x") (auto dest!: bspec[where x=x])
  done


subsection \<open>Constructor of Finite Maps\<close>

lift_definition finmap_of::"'i set \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow>\<^sub>F 'a)" is
  "\<lambda>I f x. if x \<in> I \<and> finite I then Some (f x) else None"
  by (simp add: dom_def)

lemma proj_finmap_of[simp]:
  assumes "finite inds"
  shows "(finmap_of inds f)\<^sub>F = restrict f inds"
  using assms
  by transfer force

lemma domain_finmap_of[simp]:
  assumes "finite inds"
  shows "domain (finmap_of inds f) = inds"
  using assms
  by transfer (auto split: if_splits)

lemma finmap_of_eq_iff[simp]:
  assumes "finite i" "finite j"
  shows "finmap_of i m = finmap_of j n \<longleftrightarrow> i = j \<and> (\<forall>k\<in>i. m k= n k)"
  using assms by (auto simp: finmap_eq_iff)

lemma finmap_of_inj_on_extensional_finite:
  assumes "finite K"
  assumes "S \<subseteq> extensional K"
  shows "inj_on (finmap_of K) S"
proof (rule inj_onI)
  fix x y::"'a \<Rightarrow> 'b"
  assume "finmap_of K x = finmap_of K y"
  hence "(finmap_of K x)\<^sub>F = (finmap_of K y)\<^sub>F" by simp
  moreover
  assume "x \<in> S" "y \<in> S" hence "x \<in> extensional K" "y \<in> extensional K" using assms by auto
  ultimately
  show "x = y" using assms by (simp add: extensional_restrict)
qed

subsection \<open>Product set of Finite Maps\<close>

text \<open>This is \<^term>\<open>Pi\<close> for Finite Maps, most of this is copied\<close>

definition Pi' :: "'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<Rightarrow>\<^sub>F 'a) set" where
  "Pi' I A = { P. domain P = I \<and> (\<forall>i. i \<in> I \<longrightarrow> (P)\<^sub>F i \<in> A i) } "

syntax
  "_Pi'" :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3\<Pi>'' _\<in>_./ _)"   10)
translations
  "\<Pi>' x\<in>A. B" == "CONST Pi' A (\<lambda>x. B)"

subsubsection\<open>Basic Properties of \<^term>\<open>Pi'\<close>\<close>

lemma Pi'_I[intro!]: "domain f = A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<in> B x) \<Longrightarrow> f \<in> Pi' A B"
  by (simp add: Pi'_def)

lemma Pi'_I'[simp]: "domain f = A \<Longrightarrow> (\<And>x. x \<in> A \<longrightarrow> f x \<in> B x) \<Longrightarrow> f \<in> Pi' A B"
  by (simp add:Pi'_def)

lemma Pi'_mem: "f\<in> Pi' A B \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<in> B x"
  by (simp add: Pi'_def)

lemma Pi'_iff: "f \<in> Pi' I X \<longleftrightarrow> domain f = I \<and> (\<forall>i\<in>I. f i \<in> X i)"
  unfolding Pi'_def by auto

lemma Pi'E [elim]:
  "f \<in> Pi' A B \<Longrightarrow> (f x \<in> B x \<Longrightarrow> domain f = A \<Longrightarrow> Q) \<Longrightarrow> (x \<notin> A \<Longrightarrow> Q) \<Longrightarrow> Q"
  by(auto simp: Pi'_def)

lemma in_Pi'_cong:
  "domain f = domain g \<Longrightarrow> (\<And> w. w \<in> A \<Longrightarrow> f w = g w) \<Longrightarrow> f \<in> Pi' A B \<longleftrightarrow> g \<in> Pi' A B"
  by (auto simp: Pi'_def)

lemma Pi'_eq_empty[simp]:
  assumes "finite A" shows "(Pi' A B) = {} \<longleftrightarrow> (\<exists>x\<in>A. B x = {})"
  using assms
  apply (simp add: Pi'_def, auto)
  apply (drule_tac x = "finmap_of A (\<lambda>u. SOME y. y \<in> B u)" in spec, auto)
  apply (cut_tac P= "%y. y \<in> B i" in some_eq_ex, auto)
  done

lemma Pi'_mono: "(\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x) \<Longrightarrow> Pi' A B \<subseteq> Pi' A C"
  by (auto simp: Pi'_def)

lemma Pi_Pi': "finite A \<Longrightarrow> (Pi\<^sub>E A B) = proj ` Pi' A B"
  apply (auto simp: Pi'_def Pi_def extensional_def)
  apply (rule_tac x = "finmap_of A (restrict x A)" in image_eqI)
  apply auto
  done

subsection \<open>Topological Space of Finite Maps\<close>

instantiation fmap :: (type, topological_space) topological_space
begin

definition open_fmap :: "('a \<Rightarrow>\<^sub>F 'b) set \<Rightarrow> bool" where
   [code del]: "open_fmap = generate_topology {Pi' a b|a b. \<forall>i\<in>a. open (b i)}"

lemma open_Pi'I: "(\<And>i. i \<in> I \<Longrightarrow> open (A i)) \<Longrightarrow> open (Pi' I A)"
  by (auto intro: generate_topology.Basis simp: open_fmap_def)

instance using topological_space_generate_topology
  by intro_classes (auto simp: open_fmap_def class.topological_space_def)

end

lemma open_restricted_space:
  shows "open {m. P (domain m)}"
proof -
  have "{m. P (domain m)} = (\<Union>i \<in> Collect P. {m. domain m = i})" by auto
  also have "open \<dots>"
  proof (rule, safe, cases)
    fix i::"'a set"
    assume "finite i"
    hence "{m. domain m = i} = Pi' i (\<lambda>_. UNIV)" by (auto simp: Pi'_def)
    also have "open \<dots>" by (auto intro: open_Pi'I simp: \<open>finite i\<close>)
    finally show "open {m. domain m = i}" .
  next
    fix i::"'a set"
    assume "\<not> finite i" hence "{m. domain m = i} = {}" by auto
    also have "open \<dots>" by simp
    finally show "open {m. domain m = i}" .
  qed
  finally show ?thesis .
qed

lemma closed_restricted_space:
  shows "closed {m. P (domain m)}"
  using open_restricted_space[of "\<lambda>x. \<not> P x"]
  unfolding closed_def by (rule back_subst) auto

lemma tendsto_proj: "((\<lambda>x. x) \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. (x)\<^sub>F i) \<longlongrightarrow> (a)\<^sub>F i) F"
  unfolding tendsto_def
proof safe
  fix S::"'b set"
  let ?S = "Pi' (domain a) (\<lambda>x. if x = i then S else UNIV)"
  assume "open S" hence "open ?S" by (auto intro!: open_Pi'I)
  moreover assume "\<forall>S. open S \<longrightarrow> a \<in> S \<longrightarrow> eventually (\<lambda>x. x \<in> S) F" "a i \<in> S"
  ultimately have "eventually (\<lambda>x. x \<in> ?S) F" by auto
  thus "eventually (\<lambda>x. (x)\<^sub>F i \<in> S) F"
    by eventually_elim (insert \<open>a i \<in> S\<close>, force simp: Pi'_iff split: if_split_asm)
qed

lemma continuous_proj:
  shows "continuous_on s (\<lambda>x. (x)\<^sub>F i)"
  unfolding continuous_on_def by (safe intro!: tendsto_proj tendsto_ident_at)

instance fmap :: (type, first_countable_topology) first_countable_topology
proof
  fix x::"'a\<Rightarrow>\<^sub>F'b"
  have "\<forall>i. \<exists>A. countable A \<and> (\<forall>a\<in>A. x i \<in> a) \<and> (\<forall>a\<in>A. open a) \<and>
    (\<forall>S. open S \<and> x i \<in> S \<longrightarrow> (\<exists>a\<in>A. a \<subseteq> S)) \<and> (\<forall>a b. a \<in> A \<longrightarrow> b \<in> A \<longrightarrow> a \<inter> b \<in> A)" (is "\<forall>i. ?th i")
  proof
    fix i from first_countable_basis_Int_stableE[of "x i"]
    obtain A where
      "countable A"
      "\<And>C. C \<in> A \<Longrightarrow> (x)\<^sub>F i \<in> C"
      "\<And>C. C \<in> A \<Longrightarrow> open C"
      "\<And>S. open S \<Longrightarrow> (x)\<^sub>F i \<in> S \<Longrightarrow> \<exists>A\<in>A. A \<subseteq> S"
      "\<And>C D. C \<in> A \<Longrightarrow> D \<in> A \<Longrightarrow> C \<inter> D \<in> A"
      by auto
    thus "?th i" by (intro exI[where x=A]) simp
  qed
  then obtain A
    where A: "\<forall>i. countable (A i) \<and> Ball (A i) ((\<in>) ((x)\<^sub>F i)) \<and> Ball (A i) open \<and>
      (\<forall>S. open S \<and> (x)\<^sub>F i \<in> S \<longrightarrow> (\<exists>a\<in>A i. a \<subseteq> S)) \<and> (\<forall>a b. a \<in> A i \<longrightarrow> b \<in> A i \<longrightarrow> a \<inter> b \<in> A i)"
    by (auto simp: choice_iff)
  hence open_sub: "\<And>i S. i\<in>domain x \<Longrightarrow> open (S i) \<Longrightarrow> x i\<in>(S i) \<Longrightarrow> (\<exists>a\<in>A i. a\<subseteq>(S i))" by auto
  have A_notempty: "\<And>i. i \<in> domain x \<Longrightarrow> A i \<noteq> {}" using open_sub[of _ "\<lambda>_. UNIV"] by auto
  let ?A = "(\<lambda>f. Pi' (domain x) f) ` (Pi\<^sub>E (domain x) A)"
  show "\<exists>A::nat \<Rightarrow> ('a\<Rightarrow>\<^sub>F'b) set. (\<forall>i. x \<in> (A i) \<and> open (A i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. A i \<subseteq> S))"
  proof (rule first_countableI[of "?A"], safe)
    show "countable ?A" using A by (simp add: countable_PiE)
  next
    fix S::"('a \<Rightarrow>\<^sub>F 'b) set" assume "open S" "x \<in> S"
    thus "\<exists>a\<in>?A. a \<subseteq> S" unfolding open_fmap_def
    proof (induct rule: generate_topology.induct)
      case UNIV thus ?case by (auto simp add: ex_in_conv PiE_eq_empty_iff A_notempty)
    next
      case (Int a b)
      then obtain f g where
        "f \<in> Pi\<^sub>E (domain x) A" "Pi' (domain x) f \<subseteq> a" "g \<in> Pi\<^sub>E (domain x) A" "Pi' (domain x) g \<subseteq> b"
        by auto
      thus ?case using A
        by (auto simp: Pi'_iff PiE_iff extensional_def Int_stable_def
            intro!: bexI[where x="\<lambda>i. f i \<inter> g i"])
    next
      case (UN B)
      then obtain b where "x \<in> b" "b \<in> B" by auto
      hence "\<exists>a\<in>?A. a \<subseteq> b" using UN by simp
      thus ?case using \<open>b \<in> B\<close> by blast
    next
      case (Basis s)
      then obtain a b where xs: "x\<in> Pi' a b" "s = Pi' a b" "\<And>i. i\<in>a \<Longrightarrow> open (b i)" by auto
      have "\<forall>i. \<exists>a. (i \<in> domain x \<and> open (b i) \<and> (x)\<^sub>F i \<in> b i) \<longrightarrow> (a\<in>A i \<and> a \<subseteq> b i)"
        using open_sub[of _ b] by auto
      then obtain b'
        where "\<And>i. i \<in> domain x \<Longrightarrow> open (b i) \<Longrightarrow> (x)\<^sub>F i \<in> b i \<Longrightarrow> (b' i \<in>A i \<and> b' i \<subseteq> b i)"
          unfolding choice_iff by auto
      with xs have "\<And>i. i \<in> a \<Longrightarrow> (b' i \<in>A i \<and> b' i \<subseteq> b i)" "Pi' a b' \<subseteq> Pi' a b"
        by (auto simp: Pi'_iff intro!: Pi'_mono)
      thus ?case using xs
        by (intro bexI[where x="Pi' a b'"])
          (auto simp: Pi'_iff intro!: image_eqI[where x="restrict b' (domain x)"])
    qed
  qed (insert A,auto simp: PiE_iff intro!: open_Pi'I)
qed

subsection \<open>Metric Space of Finite Maps\<close>

(* TODO: Product of uniform spaces and compatibility with metric_spaces! *)

instantiation fmap :: (type, metric_space) dist
begin

definition dist_fmap where
  "dist P Q = Max (range (\<lambda>i. dist ((P)\<^sub>F i) ((Q)\<^sub>F i))) + (if domain P = domain Q then 0 else 1)"

instance ..
end

instantiation fmap :: (type, metric_space) uniformity_dist
begin

definition [code del]:
  "(uniformity :: (('a, 'b) fmap \<times> ('a \<Rightarrow>\<^sub>F 'b)) filter) =
    (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

instance
  by standard (rule uniformity_fmap_def)
end

declare uniformity_Abort[where 'a="('a \<Rightarrow>\<^sub>F 'b::metric_space)", code]

instantiation fmap :: (type, metric_space) metric_space
begin

lemma finite_proj_image': "x \<notin> domain P \<Longrightarrow> finite ((P)\<^sub>F ` S)"
  by (rule finite_subset[of _ "proj P ` (domain P \<inter> S \<union> {x})"]) auto

lemma finite_proj_image: "finite ((P)\<^sub>F ` S)"
 by (cases "\<exists>x. x \<notin> domain P") (auto intro: finite_proj_image' finite_subset[where B="domain P"])

lemma finite_proj_diag: "finite ((\<lambda>i. d ((P)\<^sub>F i) ((Q)\<^sub>F i)) ` S)"
proof -
  have "(\<lambda>i. d ((P)\<^sub>F i) ((Q)\<^sub>F i)) ` S = (\<lambda>(i, j). d i j) ` ((\<lambda>i. ((P)\<^sub>F i, (Q)\<^sub>F i)) ` S)" by auto
  moreover have "((\<lambda>i. ((P)\<^sub>F i, (Q)\<^sub>F i)) ` S) \<subseteq> (\<lambda>i. (P)\<^sub>F i) ` S \<times> (\<lambda>i. (Q)\<^sub>F i) ` S" by auto
  moreover have "finite \<dots>" using finite_proj_image[of P S] finite_proj_image[of Q S]
    by (intro finite_cartesian_product) simp_all
  ultimately show ?thesis by (simp add: finite_subset)
qed

lemma dist_le_1_imp_domain_eq:
  shows "dist P Q < 1 \<Longrightarrow> domain P = domain Q"
  by (simp add: dist_fmap_def finite_proj_diag split: if_split_asm)

lemma dist_proj:
  shows "dist ((x)\<^sub>F i) ((y)\<^sub>F i) \<le> dist x y"
proof -
  have "dist (x i) (y i) \<le> Max (range (\<lambda>i. dist (x i) (y i)))"
    by (simp add: Max_ge_iff finite_proj_diag)
  also have "\<dots> \<le> dist x y" by (simp add: dist_fmap_def)
  finally show ?thesis .
qed

lemma dist_finmap_lessI:
  assumes "domain P = domain Q"
  assumes "0 < e"
  assumes "\<And>i. i \<in> domain P \<Longrightarrow> dist (P i) (Q i) < e"
  shows "dist P Q < e"
proof -
  have "dist P Q = Max (range (\<lambda>i. dist (P i) (Q i)))"
    using assms by (simp add: dist_fmap_def finite_proj_diag)
  also have "\<dots> < e"
  proof (subst Max_less_iff, safe)
    fix i
    show "dist ((P)\<^sub>F i) ((Q)\<^sub>F i) < e" using assms
      by (cases "i \<in> domain P") simp_all
  qed (simp add: finite_proj_diag)
  finally show ?thesis .
qed

instance
proof
  fix S::"('a \<Rightarrow>\<^sub>F 'b) set"
  have *: "open S = (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)" (is "_ = ?od")
  proof
    assume "open S"
    thus ?od
      unfolding open_fmap_def
    proof (induct rule: generate_topology.induct)
      case UNIV thus ?case by (auto intro: zero_less_one)
    next
      case (Int a b)
      show ?case
      proof safe
        fix x assume x: "x \<in> a" "x \<in> b"
        with Int x obtain e1 e2 where
          "e1>0" "\<forall>y. dist y x < e1 \<longrightarrow> y \<in> a" "e2>0" "\<forall>y. dist y x < e2 \<longrightarrow> y \<in> b" by force
        thus "\<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> a \<inter> b"
          by (auto intro!: exI[where x="min e1 e2"])
      qed
    next
      case (UN K)
      show ?case
      proof safe
        fix x X assume "x \<in> X" and X: "X \<in> K"
        with UN obtain e where "e>0" "\<And>y. dist y x < e \<longrightarrow> y \<in> X" by force
        with X show "\<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> \<Union>K" by auto
      qed
    next
      case (Basis s) then obtain a b where s: "s = Pi' a b" and b: "\<And>i. i\<in>a \<Longrightarrow> open (b i)" by auto
      show ?case
      proof safe
        fix x assume "x \<in> s"
        hence [simp]: "finite a" and a_dom: "a = domain x" using s by (auto simp: Pi'_iff)
        obtain es where es: "\<forall>i \<in> a. es i > 0 \<and> (\<forall>y. dist y (proj x i) < es i \<longrightarrow> y \<in> b i)"
          using b \<open>x \<in> s\<close> by atomize_elim (intro bchoice, auto simp: open_dist s)
        hence in_b: "\<And>i y. i \<in> a \<Longrightarrow> dist y (proj x i) < es i \<Longrightarrow> y \<in> b i" by auto
        show "\<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> s"
        proof (cases, rule, safe)
          assume "a \<noteq> {}"
          show "0 < min 1 (Min (es ` a))" using es by (auto simp: \<open>a \<noteq> {}\<close>)
          fix y assume d: "dist y x < min 1 (Min (es ` a))"
          show "y \<in> s" unfolding s
          proof
            show "domain y = a" using d s \<open>a \<noteq> {}\<close> by (auto simp: dist_le_1_imp_domain_eq a_dom)
            fix i assume i: "i \<in> a"
            hence "dist ((y)\<^sub>F i) ((x)\<^sub>F i) < es i" using d
              by (auto simp: dist_fmap_def \<open>a \<noteq> {}\<close> intro!: le_less_trans[OF dist_proj])
            with i show "y i \<in> b i" by (rule in_b)
          qed
        next
          assume "\<not>a \<noteq> {}"
          thus "\<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> s"
            using s \<open>x \<in> s\<close> by (auto simp: Pi'_def dist_le_1_imp_domain_eq intro!: exI[where x=1])
        qed
      qed
    qed
  next
    assume "\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S"
    then obtain e where e_pos: "\<And>x. x \<in> S \<Longrightarrow> e x > 0" and
      e_in:  "\<And>x y . x \<in> S \<Longrightarrow> dist y x < e x \<Longrightarrow> y \<in> S"
      unfolding bchoice_iff
      by auto
    have S_eq: "S = \<Union>{Pi' a b| a b. \<exists>x\<in>S. domain x = a \<and> b = (\<lambda>i. ball (x i) (e x))}"
    proof safe
      fix x assume "x \<in> S"
      thus "x \<in> \<Union>{Pi' a b| a b. \<exists>x\<in>S. domain x = a \<and> b = (\<lambda>i. ball (x i) (e x))}"
        using e_pos by (auto intro!: exI[where x="Pi' (domain x) (\<lambda>i. ball (x i) (e x))"])
    next
      fix x y
      assume "y \<in> S"
      moreover
      assume "x \<in> (\<Pi>' i\<in>domain y. ball (y i) (e y))"
      hence "dist x y < e y" using e_pos \<open>y \<in> S\<close>
        by (auto simp: dist_fmap_def Pi'_iff finite_proj_diag dist_commute)
      ultimately show "x \<in> S" by (rule e_in)
    qed
    also have "open \<dots>"
      unfolding open_fmap_def
      by (intro generate_topology.UN) (auto intro: generate_topology.Basis)
    finally show "open S" .
  qed
  show "open S = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"
    unfolding * eventually_uniformity_metric
    by (simp del: split_paired_All add: dist_fmap_def dist_commute eq_commute)
next
  fix P Q::"'a \<Rightarrow>\<^sub>F 'b"
  have Max_eq_iff: "\<And>A m. finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (Max A = m) = (m \<in> A \<and> (\<forall>a\<in>A. a \<le> m))"
    by (auto intro: Max_in Max_eqI)
  show "dist P Q = 0 \<longleftrightarrow> P = Q"
    by (auto simp: finmap_eq_iff dist_fmap_def Max_ge_iff finite_proj_diag Max_eq_iff
        add_nonneg_eq_0_iff
      intro!: Max_eqI image_eqI[where x=undefined])
next
  fix P Q R::"'a \<Rightarrow>\<^sub>F 'b"
  let ?dists = "\<lambda>P Q i. dist ((P)\<^sub>F i) ((Q)\<^sub>F i)"
  let ?dpq = "?dists P Q" and ?dpr = "?dists P R" and ?dqr = "?dists Q R"
  let ?dom = "\<lambda>P Q. (if domain P = domain Q then 0 else 1::real)"
  have "dist P Q = Max (range ?dpq) + ?dom P Q"
    by (simp add: dist_fmap_def)
  also obtain t where "t \<in> range ?dpq" "t = Max (range ?dpq)" by (simp add: finite_proj_diag)
  then obtain i where "Max (range ?dpq) = ?dpq i" by auto
  also have "?dpq i \<le> ?dpr i + ?dqr i" by (rule dist_triangle2)
  also have "?dpr i \<le> Max (range ?dpr)" by (simp add: finite_proj_diag)
  also have "?dqr i \<le> Max (range ?dqr)" by (simp add: finite_proj_diag)
  also have "?dom P Q \<le> ?dom P R + ?dom Q R" by simp
  finally show "dist P Q \<le> dist P R + dist Q R" by (simp add: dist_fmap_def ac_simps)
qed

end

subsection \<open>Complete Space of Finite Maps\<close>

lemma tendsto_finmap:
  fixes f::"nat \<Rightarrow> ('i \<Rightarrow>\<^sub>F ('a::metric_space))"
  assumes ind_f:  "\<And>n. domain (f n) = domain g"
  assumes proj_g:  "\<And>i. i \<in> domain g \<Longrightarrow> (\<lambda>n. (f n) i) \<longlonglongrightarrow> g i"
  shows "f \<longlonglongrightarrow> g"
  unfolding tendsto_iff
proof safe
  fix e::real assume "0 < e"
  let ?dists = "\<lambda>x i. dist ((f x)\<^sub>F i) ((g)\<^sub>F i)"
  have "eventually (\<lambda>x. \<forall>i\<in>domain g. ?dists x i < e) sequentially"
    using finite_domain[of g] proj_g
  proof induct
    case (insert i G)
    with \<open>0 < e\<close> have "eventually (\<lambda>x. ?dists x i < e) sequentially" by (auto simp add: tendsto_iff)
    moreover
    from insert have "eventually (\<lambda>x. \<forall>i\<in>G. dist ((f x)\<^sub>F i) ((g)\<^sub>F i) < e) sequentially" by simp
    ultimately show ?case by eventually_elim auto
  qed simp
  thus "eventually (\<lambda>x. dist (f x) g < e) sequentially"
    by eventually_elim (auto simp add: dist_fmap_def finite_proj_diag ind_f \<open>0 < e\<close>)
qed

instance fmap :: (type, complete_space) complete_space
proof
  fix P::"nat \<Rightarrow> 'a \<Rightarrow>\<^sub>F 'b"
  assume "Cauchy P"
  then obtain Nd where Nd: "\<And>n. n \<ge> Nd \<Longrightarrow> dist (P n) (P Nd) < 1"
    by (force simp: Cauchy_altdef2)
  define d where "d = domain (P Nd)"
  with Nd have dim: "\<And>n. n \<ge> Nd \<Longrightarrow> domain (P n) = d" using dist_le_1_imp_domain_eq by auto
  have [simp]: "finite d" unfolding d_def by simp
  define p where "p i n = P n i" for i n
  define q where "q i = lim (p i)" for i
  define Q where "Q = finmap_of d q"
  have q: "\<And>i. i \<in> d \<Longrightarrow> q i = Q i" by (auto simp add: Q_def Abs_fmap_inverse)
  {
    fix i assume "i \<in> d"
    have "Cauchy (p i)" unfolding Cauchy_altdef2 p_def
    proof safe
      fix e::real assume "0 < e"
      with \<open>Cauchy P\<close> obtain N where N: "\<And>n. n\<ge>N \<Longrightarrow> dist (P n) (P N) < min e 1"
        by (force simp: Cauchy_altdef2 min_def)
      hence "\<And>n. n \<ge> N \<Longrightarrow> domain (P n) = domain (P N)" using dist_le_1_imp_domain_eq by auto
      with dim have dim: "\<And>n. n \<ge> N \<Longrightarrow> domain (P n) = d" by (metis nat_le_linear)
      show "\<exists>N. \<forall>n\<ge>N. dist ((P n) i) ((P N) i) < e"
      proof (safe intro!: exI[where x="N"])
        fix n assume "N \<le> n" have "N \<le> N" by simp
        have "dist ((P n) i) ((P N) i) \<le> dist (P n) (P N)"
          using dim[OF \<open>N \<le> n\<close>]  dim[OF \<open>N \<le> N\<close>] \<open>i \<in> d\<close>
          by (auto intro!: dist_proj)
        also have "\<dots> < e" using N[OF \<open>N \<le> n\<close>] by simp
        finally show "dist ((P n) i) ((P N) i) < e" .
      qed
    qed
    hence "convergent (p i)" by (metis Cauchy_convergent_iff)
    hence "p i \<longlonglongrightarrow> q i" unfolding q_def convergent_def by (metis limI)
  } note p = this
  have "P \<longlonglongrightarrow> Q"
  proof (rule metric_LIMSEQ_I)
    fix e::real assume "0 < e"
    have "\<exists>ni. \<forall>i\<in>d. \<forall>n\<ge>ni i. dist (p i n) (q i) < e"
    proof (safe intro!: bchoice)
      fix i assume "i \<in> d"
      from p[OF \<open>i \<in> d\<close>, THEN metric_LIMSEQ_D, OF \<open>0 < e\<close>]
      show "\<exists>no. \<forall>n\<ge>no. dist (p i n) (q i) < e" .
    qed
    then obtain ni where ni: "\<forall>i\<in>d. \<forall>n\<ge>ni i. dist (p i n) (q i) < e" ..
    define N where "N = max Nd (Max (ni ` d))"
    show "\<exists>N. \<forall>n\<ge>N. dist (P n) Q < e"
    proof (safe intro!: exI[where x="N"])
      fix n assume "N \<le> n"
      hence dom: "domain (P n) = d" "domain Q = d" "domain (P n) = domain Q"
        using dim by (simp_all add: N_def Q_def dim_def Abs_fmap_inverse)
      show "dist (P n) Q < e"
      proof (rule dist_finmap_lessI[OF dom(3) \<open>0 < e\<close>])
        fix i
        assume "i \<in> domain (P n)"
        hence "ni i \<le> Max (ni ` d)" using dom by simp
        also have "\<dots> \<le> N" by (simp add: N_def)
        finally show "dist ((P n)\<^sub>F i) ((Q)\<^sub>F i) < e" using ni \<open>i \<in> domain (P n)\<close> \<open>N \<le> n\<close> dom
          by (auto simp: p_def q N_def less_imp_le)
      qed
    qed
  qed
  thus "convergent P" by (auto simp: convergent_def)
qed

subsection \<open>Second Countable Space of Finite Maps\<close>

instantiation fmap :: (countable, second_countable_topology) second_countable_topology
begin

definition basis_proj::"'b set set"
  where "basis_proj = (SOME B. countable B \<and> topological_basis B)"

lemma countable_basis_proj: "countable basis_proj" and basis_proj: "topological_basis basis_proj"
  unfolding basis_proj_def by (intro is_basis countable_basis)+

definition basis_finmap::"('a \<Rightarrow>\<^sub>F 'b) set set"
  where "basis_finmap = {Pi' I S|I S. finite I \<and> (\<forall>i \<in> I. S i \<in> basis_proj)}"

lemma in_basis_finmapI:
  assumes "finite I" assumes "\<And>i. i \<in> I \<Longrightarrow> S i \<in> basis_proj"
  shows "Pi' I S \<in> basis_finmap"
  using assms unfolding basis_finmap_def by auto

lemma basis_finmap_eq:
  assumes "basis_proj \<noteq> {}"
  shows "basis_finmap = (\<lambda>f. Pi' (domain f) (\<lambda>i. from_nat_into basis_proj ((f)\<^sub>F i))) `
    (UNIV::('a \<Rightarrow>\<^sub>F nat) set)" (is "_ = ?f ` _")
  unfolding basis_finmap_def
proof safe
  fix I::"'a set" and S::"'a \<Rightarrow> 'b set"
  assume "finite I" "\<forall>i\<in>I. S i \<in> basis_proj"
  hence "Pi' I S = ?f (finmap_of I (\<lambda>x. to_nat_on basis_proj (S x)))"
    by (force simp: Pi'_def countable_basis_proj)
  thus "Pi' I S \<in> range ?f" by simp
next
  fix x and f::"'a \<Rightarrow>\<^sub>F nat"
  show "\<exists>I S. (\<Pi>' i\<in>domain f. from_nat_into basis_proj ((f)\<^sub>F i)) = Pi' I S \<and>
    finite I \<and> (\<forall>i\<in>I. S i \<in> basis_proj)"
    using assms by (auto intro: from_nat_into)
qed

lemma basis_finmap_eq_empty: "basis_proj = {} \<Longrightarrow> basis_finmap = {Pi' {} undefined}"
  by (auto simp: Pi'_iff basis_finmap_def)

lemma countable_basis_finmap: "countable basis_finmap"
  by (cases "basis_proj = {}") (auto simp: basis_finmap_eq basis_finmap_eq_empty)

lemma finmap_topological_basis:
  "topological_basis basis_finmap"
proof (subst topological_basis_iff, safe)
  fix B' assume "B' \<in> basis_finmap"
  thus "open B'"
    by (auto intro!: open_Pi'I topological_basis_open[OF basis_proj]
      simp: topological_basis_def basis_finmap_def Let_def)
next
  fix O'::"('a \<Rightarrow>\<^sub>F 'b) set" and x
  assume O': "open O'" "x \<in> O'"
  then obtain a where a:
    "x \<in> Pi' (domain x) a" "Pi' (domain x) a \<subseteq> O'" "\<And>i. i\<in>domain x \<Longrightarrow> open (a i)"
    unfolding open_fmap_def
  proof (atomize_elim, induct rule: generate_topology.induct)
    case (Int a b)
    let ?p="\<lambda>a f. x \<in> Pi' (domain x) f \<and> Pi' (domain x) f \<subseteq> a \<and> (\<forall>i. i \<in> domain x \<longrightarrow> open (f i))"
    from Int obtain f g where "?p a f" "?p b g" by auto
    thus ?case by (force intro!: exI[where x="\<lambda>i. f i \<inter> g i"] simp: Pi'_def)
  next
    case (UN k)
    then obtain kk a where "x \<in> kk" "kk \<in> k" "x \<in> Pi' (domain x) a" "Pi' (domain x) a \<subseteq> kk"
      "\<And>i. i\<in>domain x \<Longrightarrow> open (a i)"
      by force
    thus ?case by blast
  qed (auto simp: Pi'_def)
  have "\<exists>B.
    (\<forall>i\<in>domain x. x i \<in> B i \<and> B i \<subseteq> a i \<and> B i \<in> basis_proj)"
  proof (rule bchoice, safe)
    fix i assume "i \<in> domain x"
    hence "open (a i)" "x i \<in> a i" using a by auto
    from topological_basisE[OF basis_proj this] obtain b'
      where "b' \<in> basis_proj" "(x)\<^sub>F i \<in> b'" "b' \<subseteq> a i"
      by blast
    thus "\<exists>y. x i \<in> y \<and> y \<subseteq> a i \<and> y \<in> basis_proj" by auto
  qed
  then obtain B where B: "\<forall>i\<in>domain x. (x)\<^sub>F i \<in> B i \<and> B i \<subseteq> a i \<and> B i \<in> basis_proj"
    by auto
  define B' where "B' = Pi' (domain x) (\<lambda>i. (B i)::'b set)"
  have "B' \<subseteq> Pi' (domain x) a" using B by (auto intro!: Pi'_mono simp: B'_def)
  also note \<open>\<dots> \<subseteq> O'\<close>
  finally show "\<exists>B'\<in>basis_finmap. x \<in> B' \<and> B' \<subseteq> O'" using B
    by (auto intro!: bexI[where x=B'] Pi'_mono in_basis_finmapI simp: B'_def)
qed

lemma range_enum_basis_finmap_imp_open:
  assumes "x \<in> basis_finmap"
  shows "open x"
  using finmap_topological_basis assms by (auto simp: topological_basis_def)

instance proof qed (blast intro: finmap_topological_basis countable_basis_finmap topological_basis_imp_subbasis)

end

subsection \<open>Polish Space of Finite Maps\<close>

instance fmap :: (countable, polish_space) polish_space proof qed


subsection \<open>Product Measurable Space of Finite Maps\<close>

definition "PiF I M \<equiv>
  sigma (\<Union>J \<in> I. (\<Pi>' j\<in>J. space (M j))) {(\<Pi>' j\<in>J. X j) |X J. J \<in> I \<and> X \<in> (\<Pi> j\<in>J. sets (M j))}"

abbreviation
  "Pi\<^sub>F I M \<equiv> PiF I M"

syntax
  "_PiF" :: "pttrn \<Rightarrow> 'i set \<Rightarrow> 'a measure \<Rightarrow> ('i => 'a) measure"  ("(3\<Pi>\<^sub>F _\<in>_./ _)"  10)
translations
  "\<Pi>\<^sub>F x\<in>I. M" == "CONST PiF I (%x. M)"

lemma PiF_gen_subset: "{(\<Pi>' j\<in>J. X j) |X J. J \<in> I \<and> X \<in> (\<Pi> j\<in>J. sets (M j))} \<subseteq>
    Pow (\<Union>J \<in> I. (\<Pi>' j\<in>J. space (M j)))"
  by (auto simp: Pi'_def) (blast dest: sets.sets_into_space)

lemma space_PiF: "space (PiF I M) = (\<Union>J \<in> I. (\<Pi>' j\<in>J. space (M j)))"
  unfolding PiF_def using PiF_gen_subset by (rule space_measure_of)

lemma sets_PiF:
  "sets (PiF I M) = sigma_sets (\<Union>J \<in> I. (\<Pi>' j\<in>J. space (M j)))
    {(\<Pi>' j\<in>J. X j) |X J. J \<in> I \<and> X \<in> (\<Pi> j\<in>J. sets (M j))}"
  unfolding PiF_def using PiF_gen_subset by (rule sets_measure_of)

lemma sets_PiF_singleton:
  "sets (PiF {I} M) = sigma_sets (\<Pi>' j\<in>I. space (M j))
    {(\<Pi>' j\<in>I. X j) |X. X \<in> (\<Pi> j\<in>I. sets (M j))}"
  unfolding sets_PiF by simp

lemma in_sets_PiFI:
  assumes "X = (Pi' J S)" "J \<in> I" "\<And>i. i\<in>J \<Longrightarrow> S i \<in> sets (M i)"
  shows "X \<in> sets (PiF I M)"
  unfolding sets_PiF
  using assms by blast

lemma product_in_sets_PiFI:
  assumes "J \<in> I" "\<And>i. i\<in>J \<Longrightarrow> S i \<in> sets (M i)"
  shows "(Pi' J S) \<in> sets (PiF I M)"
  unfolding sets_PiF
  using assms by blast

lemma singleton_space_subset_in_sets:
  fixes J
  assumes "J \<in> I"
  assumes "finite J"
  shows "space (PiF {J} M) \<in> sets (PiF I M)"
  using assms
  by (intro in_sets_PiFI[where J=J and S="\<lambda>i. space (M i)"])
      (auto simp: product_def space_PiF)

lemma singleton_subspace_set_in_sets:
  assumes A: "A \<in> sets (PiF {J} M)"
  assumes "finite J"
  assumes "J \<in> I"
  shows "A \<in> sets (PiF I M)"
  using A[unfolded sets_PiF]
  apply (induct A)
  unfolding sets_PiF[symmetric] unfolding space_PiF[symmetric]
  using assms
  by (auto intro: in_sets_PiFI intro!: singleton_space_subset_in_sets)

lemma finite_measurable_singletonI:
  assumes "finite I"
  assumes "\<And>J. J \<in> I \<Longrightarrow> finite J"
  assumes MN: "\<And>J. J \<in> I \<Longrightarrow> A \<in> measurable (PiF {J} M) N"
  shows "A \<in> measurable (PiF I M) N"
  unfolding measurable_def
proof safe
  fix y assume "y \<in> sets N"
  have "A -` y \<inter> space (PiF I M) = (\<Union>J\<in>I. A -` y \<inter> space (PiF {J} M))"
    by (auto simp: space_PiF)
  also have "\<dots> \<in> sets (PiF I M)"
  proof (rule sets.finite_UN)
    show "finite I" by fact
    fix J assume "J \<in> I"
    with assms have "finite J" by simp
    show "A -` y \<inter> space (PiF {J} M) \<in> sets (PiF I M)"
      by (rule singleton_subspace_set_in_sets[OF measurable_sets[OF assms(3)]]) fact+
  qed
  finally show "A -` y \<inter> space (PiF I M) \<in> sets (PiF I M)" .
next
  fix x assume "x \<in> space (PiF I M)" thus "A x \<in> space N"
    using MN[of "domain x"]
    by (auto simp: space_PiF measurable_space Pi'_def)
qed

lemma countable_finite_comprehension:
  fixes f :: "'a::countable set \<Rightarrow> _"
  assumes "\<And>s. P s \<Longrightarrow> finite s"
  assumes "\<And>s. P s \<Longrightarrow> f s \<in> sets M"
  shows "\<Union>{f s|s. P s} \<in> sets M"
proof -
  have "\<Union>{f s|s. P s} = (\<Union>n::nat. let s = set (from_nat n) in if P s then f s else {})"
  proof safe
    fix x X s assume *: "x \<in> f s" "P s"
    with assms obtain l where "s = set l" using finite_list by blast
    with * show "x \<in> (\<Union>n. let s = set (from_nat n) in if P s then f s else {})" using \<open>P s\<close>
      by (auto intro!: exI[where x="to_nat l"])
  next
    fix x n assume "x \<in> (let s = set (from_nat n) in if P s then f s else {})"
    thus "x \<in> \<Union>{f s|s. P s}" using assms by (auto simp: Let_def split: if_split_asm)
  qed
  hence "\<Union>{f s|s. P s} = (\<Union>n. let s = set (from_nat n) in if P s then f s else {})" by simp
  also have "\<dots> \<in> sets M" using assms by (auto simp: Let_def)
  finally show ?thesis .
qed

lemma space_subset_in_sets:
  fixes J::"'a::countable set set"
  assumes "J \<subseteq> I"
  assumes "\<And>j. j \<in> J \<Longrightarrow> finite j"
  shows "space (PiF J M) \<in> sets (PiF I M)"
proof -
  have "space (PiF J M) = \<Union>{space (PiF {j} M)|j. j \<in> J}"
    unfolding space_PiF by blast
  also have "\<dots> \<in> sets (PiF I M)" using assms
    by (intro countable_finite_comprehension) (auto simp: singleton_space_subset_in_sets)
  finally show ?thesis .
qed

lemma subspace_set_in_sets:
  fixes J::"'a::countable set set"
  assumes A: "A \<in> sets (PiF J M)"
  assumes "J \<subseteq> I"
  assumes "\<And>j. j \<in> J \<Longrightarrow> finite j"
  shows "A \<in> sets (PiF I M)"
  using A[unfolded sets_PiF]
  apply (induct A)
  unfolding sets_PiF[symmetric] unfolding space_PiF[symmetric]
  using assms
  by (auto intro: in_sets_PiFI intro!: space_subset_in_sets)

lemma countable_measurable_PiFI:
  fixes I::"'a::countable set set"
  assumes MN: "\<And>J. J \<in> I \<Longrightarrow> finite J \<Longrightarrow> A \<in> measurable (PiF {J} M) N"
  shows "A \<in> measurable (PiF I M) N"
  unfolding measurable_def
proof safe
  fix y assume "y \<in> sets N"
  have "A -` y = (\<Union>{A -` y \<inter> {x. domain x = J}|J. finite J})" by auto
  { fix x::"'a \<Rightarrow>\<^sub>F 'b"
    from finite_list[of "domain x"] obtain xs where "set xs = domain x" by auto
    hence "\<exists>n. domain x = set (from_nat n)"
      by (intro exI[where x="to_nat xs"]) auto }
  hence "A -` y \<inter> space (PiF I M) = (\<Union>n. A -` y \<inter> space (PiF ({set (from_nat n)}\<inter>I) M))"
    by (auto simp: space_PiF Pi'_def)
  also have "\<dots> \<in> sets (PiF I M)"
    apply (intro sets.Int sets.countable_nat_UN subsetI, safe)
    apply (case_tac "set (from_nat i) \<in> I")
    apply simp_all
    apply (rule singleton_subspace_set_in_sets[OF measurable_sets[OF MN]])
    using assms \<open>y \<in> sets N\<close>
    apply (auto simp: space_PiF)
    done
  finally show "A -` y \<inter> space (PiF I M) \<in> sets (PiF I M)" .
next
  fix x assume "x \<in> space (PiF I M)" thus "A x \<in> space N"
    using MN[of "domain x"] by (auto simp: space_PiF measurable_space Pi'_def)
qed

lemma measurable_PiF:
  assumes f: "\<And>x. x \<in> space N \<Longrightarrow> domain (f x) \<in> I \<and> (\<forall>i\<in>domain (f x). (f x) i \<in> space (M i))"
  assumes S: "\<And>J S. J \<in> I \<Longrightarrow> (\<And>i. i \<in> J \<Longrightarrow> S i \<in> sets (M i)) \<Longrightarrow>
    f -` (Pi' J S) \<inter> space N \<in> sets N"
  shows "f \<in> measurable N (PiF I M)"
  unfolding PiF_def
  using PiF_gen_subset
  apply (rule measurable_measure_of)
  using f apply force
  apply (insert S, auto)
  done

lemma restrict_sets_measurable:
  assumes A: "A \<in> sets (PiF I M)" and "J \<subseteq> I"
  shows "A \<inter> {m. domain m \<in> J} \<in> sets (PiF J M)"
  using A[unfolded sets_PiF]
proof (induct A)
  case (Basic a)
  then obtain K S where S: "a = Pi' K S" "K \<in> I" "(\<forall>i\<in>K. S i \<in> sets (M i))"
    by auto
  show ?case
  proof cases
    assume "K \<in> J"
    hence "a \<inter> {m. domain m \<in> J} \<in> {Pi' K X |X K. K \<in> J \<and> X \<in> (\<Pi> j\<in>K. sets (M j))}" using S
      by (auto intro!: exI[where x=K] exI[where x=S] simp: Pi'_def)
    also have "\<dots> \<subseteq> sets (PiF J M)" unfolding sets_PiF by auto
    finally show ?thesis .
  next
    assume "K \<notin> J"
    hence "a \<inter> {m. domain m \<in> J} = {}" using S by (auto simp: Pi'_def)
    also have "\<dots> \<in> sets (PiF J M)" by simp
    finally show ?thesis .
  qed
next
  case (Union a)
  have "\<Union>(a ` UNIV) \<inter> {m. domain m \<in> J} = (\<Union>i. (a i \<inter> {m. domain m \<in> J}))"
    by simp
  also have "\<dots> \<in> sets (PiF J M)" using Union by (intro sets.countable_nat_UN) auto
  finally show ?case .
next
  case (Compl a)
  have "(space (PiF I M) - a) \<inter> {m. domain m \<in> J} = (space (PiF J M) - (a \<inter> {m. domain m \<in> J}))"
    using \<open>J \<subseteq> I\<close> by (auto simp: space_PiF Pi'_def)
  also have "\<dots> \<in> sets (PiF J M)" using Compl by auto
  finally show ?case by (simp add: space_PiF)
qed simp

lemma measurable_finmap_of:
  assumes f: "\<And>i. (\<exists>x \<in> space N. i \<in> J x) \<Longrightarrow> (\<lambda>x. f x i) \<in> measurable N (M i)"
  assumes J: "\<And>x. x \<in> space N \<Longrightarrow> J x \<in> I" "\<And>x. x \<in> space N \<Longrightarrow> finite (J x)"
  assumes JN: "\<And>S. {x. J x = S} \<inter> space N \<in> sets N"
  shows "(\<lambda>x. finmap_of (J x) (f x)) \<in> measurable N (PiF I M)"
proof (rule measurable_PiF)
  fix x assume "x \<in> space N"
  with J[of x] measurable_space[OF f]
  show "domain (finmap_of (J x) (f x)) \<in> I \<and>
        (\<forall>i\<in>domain (finmap_of (J x) (f x)). (finmap_of (J x) (f x)) i \<in> space (M i))"
    by auto
next
  fix K S assume "K \<in> I" and *: "\<And>i. i \<in> K \<Longrightarrow> S i \<in> sets (M i)"
  with J have eq: "(\<lambda>x. finmap_of (J x) (f x)) -` Pi' K S \<inter> space N =
    (if \<exists>x \<in> space N. K = J x \<and> finite K then if K = {} then {x \<in> space N. J x = K}
      else (\<Inter>i\<in>K. (\<lambda>x. f x i) -` S i \<inter> {x \<in> space N. J x = K}) else {})"
    by (auto simp: Pi'_def)
  have r: "{x \<in> space N. J x = K} = space N \<inter> ({x. J x = K} \<inter> space N)" by auto
  show "(\<lambda>x. finmap_of (J x) (f x)) -` Pi' K S \<inter> space N \<in> sets N"
    unfolding eq r
    apply (simp del: INT_simps add: )
    apply (intro conjI impI sets.finite_INT JN sets.Int[OF sets.top])
    apply simp apply assumption
    apply (subst Int_assoc[symmetric])
    apply (rule sets.Int)
    apply (intro measurable_sets[OF f] *) apply force apply assumption
    apply (intro JN)
    done
qed

lemma measurable_PiM_finmap_of:
  assumes "finite J"
  shows "finmap_of J \<in> measurable (Pi\<^sub>M J M) (PiF {J} M)"
  apply (rule measurable_finmap_of)
  apply (rule measurable_component_singleton)
  apply simp
  apply rule
  apply (rule \<open>finite J\<close>)
  apply simp
  done

lemma proj_measurable_singleton:
  assumes "A \<in> sets (M i)"
  shows "(\<lambda>x. (x)\<^sub>F i) -` A \<inter> space (PiF {I} M) \<in> sets (PiF {I} M)"
proof cases
  assume "i \<in> I"
  hence "(\<lambda>x. (x)\<^sub>F i) -` A \<inter> space (PiF {I} M) =
    Pi' I (\<lambda>x. if x = i then A else space (M x))"
    using sets.sets_into_space[OF ] \<open>A \<in> sets (M i)\<close> assms
    by (auto simp: space_PiF Pi'_def)
  thus ?thesis  using assms \<open>A \<in> sets (M i)\<close>
    by (intro in_sets_PiFI) auto
next
  assume "i \<notin> I"
  hence "(\<lambda>x. (x)\<^sub>F i) -` A \<inter> space (PiF {I} M) =
    (if undefined \<in> A then space (PiF {I} M) else {})" by (auto simp: space_PiF Pi'_def)
  thus ?thesis by simp
qed

lemma measurable_proj_singleton:
  assumes "i \<in> I"
  shows "(\<lambda>x. (x)\<^sub>F i) \<in> measurable (PiF {I} M) (M i)"
  by (unfold measurable_def, intro CollectI conjI ballI proj_measurable_singleton assms)
     (insert \<open>i \<in> I\<close>, auto simp: space_PiF)

lemma measurable_proj_countable:
  fixes I::"'a::countable set set"
  assumes "y \<in> space (M i)"
  shows "(\<lambda>x. if i \<in> domain x then (x)\<^sub>F i else y) \<in> measurable (PiF I M) (M i)"
proof (rule countable_measurable_PiFI)
  fix J assume "J \<in> I" "finite J"
  show "(\<lambda>x. if i \<in> domain x then x i else y) \<in> measurable (PiF {J} M) (M i)"
    unfolding measurable_def
  proof safe
    fix z assume "z \<in> sets (M i)"
    have "(\<lambda>x. if i \<in> domain x then x i else y) -` z \<inter> space (PiF {J} M) =
      (\<lambda>x. if i \<in> J then (x)\<^sub>F i else y) -` z \<inter> space (PiF {J} M)"
      by (auto simp: space_PiF Pi'_def)
    also have "\<dots> \<in> sets (PiF {J} M)" using \<open>z \<in> sets (M i)\<close> \<open>finite J\<close>
      by (cases "i \<in> J") (auto intro!: measurable_sets[OF measurable_proj_singleton])
    finally show "(\<lambda>x. if i \<in> domain x then x i else y) -` z \<inter> space (PiF {J} M) \<in>
      sets (PiF {J} M)" .
  qed (insert \<open>y \<in> space (M i)\<close>, auto simp: space_PiF Pi'_def)
qed

lemma measurable_restrict_proj:
  assumes "J \<in> II" "finite J"
  shows "finmap_of J \<in> measurable (PiM J M) (PiF II M)"
  using assms
  by (intro measurable_finmap_of measurable_component_singleton) auto

lemma measurable_proj_PiM:
  fixes J K ::"'a::countable set" and I::"'a set set"
  assumes "finite J" "J \<in> I"
  assumes "x \<in> space (PiM J M)"
  shows "proj \<in> measurable (PiF {J} M) (PiM J M)"
proof (rule measurable_PiM_single)
  show "proj \<in> space (PiF {J} M) \<rightarrow> (\<Pi>\<^sub>E i \<in> J. space (M i))"
    using assms by (auto simp add: space_PiM space_PiF extensional_def sets_PiF Pi'_def)
next
  fix A i assume A: "i \<in> J" "A \<in> sets (M i)"
  show "{\<omega> \<in> space (PiF {J} M). (\<omega>)\<^sub>F i \<in> A} \<in> sets (PiF {J} M)"
  proof
    have "{\<omega> \<in> space (PiF {J} M). (\<omega>)\<^sub>F i \<in> A} =
      (\<lambda>\<omega>. (\<omega>)\<^sub>F i) -` A \<inter> space (PiF {J} M)" by auto
    also have "\<dots> \<in> sets (PiF {J} M)"
      using assms A by (auto intro: measurable_sets[OF measurable_proj_singleton] simp: space_PiM)
    finally show ?thesis .
  qed simp
qed

lemma space_PiF_singleton_eq_product:
  assumes "finite I"
  shows "space (PiF {I} M) = (\<Pi>' i\<in>I. space (M i))"
  by (auto simp: product_def space_PiF assms)

text \<open>adapted from @{thm sets_PiM_single}\<close>

lemma sets_PiF_single:
  assumes "finite I" "I \<noteq> {}"
  shows "sets (PiF {I} M) =
    sigma_sets (\<Pi>' i\<in>I. space (M i))
      {{f\<in>\<Pi>' i\<in>I. space (M i). f i \<in> A} | i A. i \<in> I \<and> A \<in> sets (M i)}"
    (is "_ = sigma_sets ?\<Omega> ?R")
  unfolding sets_PiF_singleton
proof (rule sigma_sets_eqI)
  interpret R: sigma_algebra ?\<Omega> "sigma_sets ?\<Omega> ?R" by (rule sigma_algebra_sigma_sets) auto
  fix A assume "A \<in> {Pi' I X |X. X \<in> (\<Pi> j\<in>I. sets (M j))}"
  then obtain X where X: "A = Pi' I X" "X \<in> (\<Pi> j\<in>I. sets (M j))" by auto
  show "A \<in> sigma_sets ?\<Omega> ?R"
  proof -
    from \<open>I \<noteq> {}\<close> X have "A = (\<Inter>j\<in>I. {f\<in>space (PiF {I} M). f j \<in> X j})"
      using sets.sets_into_space
      by (auto simp: space_PiF product_def) blast
    also have "\<dots> \<in> sigma_sets ?\<Omega> ?R"
      using X \<open>I \<noteq> {}\<close> assms by (intro R.finite_INT) (auto simp: space_PiF)
    finally show "A \<in> sigma_sets ?\<Omega> ?R" .
  qed
next
  fix A assume "A \<in> ?R"
  then obtain i B where A: "A = {f\<in>\<Pi>' i\<in>I. space (M i). f i \<in> B}" "i \<in> I" "B \<in> sets (M i)"
    by auto
  then have "A = (\<Pi>' j \<in> I. if j = i then B else space (M j))"
    using sets.sets_into_space[OF A(3)]
    apply (auto simp: Pi'_iff split: if_split_asm)
    apply blast
    done
  also have "\<dots> \<in> sigma_sets ?\<Omega> {Pi' I X |X. X \<in> (\<Pi> j\<in>I. sets (M j))}"
    using A
    by (intro sigma_sets.Basic )
       (auto intro: exI[where x="\<lambda>j. if j = i then B else space (M j)"])
  finally show "A \<in> sigma_sets ?\<Omega> {Pi' I X |X. X \<in> (\<Pi> j\<in>I. sets (M j))}" .
qed

text \<open>adapted from @{thm PiE_cong}\<close>

lemma Pi'_cong:
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i = g i"
  shows "Pi' I f = Pi' I g"
using assms by (auto simp: Pi'_def)

text \<open>adapted from @{thm Pi_UN}\<close>

lemma Pi'_UN:
  fixes A :: "nat \<Rightarrow> 'i \<Rightarrow> 'a set"
  assumes "finite I"
  assumes mono: "\<And>i n m. i \<in> I \<Longrightarrow> n \<le> m \<Longrightarrow> A n i \<subseteq> A m i"
  shows "(\<Union>n. Pi' I (A n)) = Pi' I (\<lambda>i. \<Union>n. A n i)"
proof (intro set_eqI iffI)
  fix f assume "f \<in> Pi' I (\<lambda>i. \<Union>n. A n i)"
  then have "\<forall>i\<in>I. \<exists>n. f i \<in> A n i" "domain f = I" by (auto simp: \<open>finite I\<close> Pi'_def)
  from bchoice[OF this(1)] obtain n where n: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> (A (n i) i)" by auto
  obtain k where k: "\<And>i. i \<in> I \<Longrightarrow> n i \<le> k"
    using \<open>finite I\<close> finite_nat_set_iff_bounded_le[of "n`I"] by auto
  have "f \<in> Pi' I (\<lambda>i. A k i)"
  proof
    fix i assume "i \<in> I"
    from mono[OF this, of "n i" k] k[OF this] n[OF this] \<open>domain f = I\<close> \<open>i \<in> I\<close>
    show "f i \<in> A k i " by (auto simp: \<open>finite I\<close>)
  qed (simp add: \<open>domain f = I\<close> \<open>finite I\<close>)
  then show "f \<in> (\<Union>n. Pi' I (A n))" by auto
qed (auto simp: Pi'_def \<open>finite I\<close>)

text \<open>adapted from @{thm sets_PiM_sigma}\<close>

lemma sigma_fprod_algebra_sigma_eq:
  fixes E :: "'i \<Rightarrow> 'a set set" and S :: "'i \<Rightarrow> nat \<Rightarrow> 'a set"
  assumes [simp]: "finite I" "I \<noteq> {}"
    and S_union: "\<And>i. i \<in> I \<Longrightarrow> (\<Union>j. S i j) = space (M i)"
    and S_in_E: "\<And>i. i \<in> I \<Longrightarrow> range (S i) \<subseteq> E i"
  assumes E_closed: "\<And>i. i \<in> I \<Longrightarrow> E i \<subseteq> Pow (space (M i))"
    and E_generates: "\<And>i. i \<in> I \<Longrightarrow> sets (M i) = sigma_sets (space (M i)) (E i)"
  defines "P == { Pi' I F | F. \<forall>i\<in>I. F i \<in> E i }"
  shows "sets (PiF {I} M) = sigma_sets (space (PiF {I} M)) P"
proof
  let ?P = "sigma (space (Pi\<^sub>F {I} M)) P"
  from \<open>finite I\<close>[THEN ex_bij_betw_finite_nat] obtain T where "bij_betw T I {0..<card I}" ..
  then have T: "\<And>i. i \<in> I \<Longrightarrow> T i < card I" "\<And>i. i\<in>I \<Longrightarrow> the_inv_into I T (T i) = i"
    by (auto simp add: bij_betw_def set_eq_iff image_iff the_inv_into_f_f simp del: \<open>finite I\<close>)
  have P_closed: "P \<subseteq> Pow (space (Pi\<^sub>F {I} M))"
    using E_closed by (auto simp: space_PiF P_def Pi'_iff subset_eq)
  then have space_P: "space ?P = (\<Pi>' i\<in>I. space (M i))"
    by (simp add: space_PiF)
  have "sets (PiF {I} M) =
      sigma_sets (space ?P) {{f \<in> \<Pi>' i\<in>I. space (M i). f i \<in> A} |i A. i \<in> I \<and> A \<in> sets (M i)}"
    using sets_PiF_single[of I M] by (simp add: space_P)
  also have "\<dots> \<subseteq> sets (sigma (space (PiF {I} M)) P)"
  proof (safe intro!: sets.sigma_sets_subset)
    fix i A assume "i \<in> I" and A: "A \<in> sets (M i)"
    have "(\<lambda>x. (x)\<^sub>F i) \<in> measurable ?P (sigma (space (M i)) (E i))"
    proof (subst measurable_iff_measure_of)
      show "E i \<subseteq> Pow (space (M i))" using \<open>i \<in> I\<close> by fact
      from space_P \<open>i \<in> I\<close> show "(\<lambda>x. (x)\<^sub>F i) \<in> space ?P \<rightarrow> space (M i)"
        by auto
      show "\<forall>A\<in>E i. (\<lambda>x. (x)\<^sub>F i) -` A \<inter> space ?P \<in> sets ?P"
      proof
        fix A assume A: "A \<in> E i"
        from T have *: "\<exists>xs. length xs = card I
          \<and> (\<forall>j\<in>I. (g)\<^sub>F j \<in> (if i = j then A else S j (xs ! T j)))"
          if "domain g = I" and "\<forall>j\<in>I. (g)\<^sub>F j \<in> (if i = j then A else S j (f j))" for g f
          using that by (auto intro!: exI [of _ "map (\<lambda>n. f (the_inv_into I T n)) [0..<card I]"])
        from A have "(\<lambda>x. (x)\<^sub>F i) -` A \<inter> space ?P = (\<Pi>' j\<in>I. if i = j then A else space (M j))"
          using E_closed \<open>i \<in> I\<close> by (auto simp: space_P Pi_iff subset_eq split: if_split_asm)
        also have "\<dots> = (\<Pi>' j\<in>I. \<Union>n. if i = j then A else S j n)"
          by (intro Pi'_cong) (simp_all add: S_union)
        also have "\<dots> = {g. domain g = I \<and> (\<exists>f. \<forall>j\<in>I. (g)\<^sub>F j \<in> (if i = j then A else S j (f j)))}"
          by (rule set_eqI) (simp del: if_image_distrib add: Pi'_iff bchoice_iff)
        also have "\<dots> = (\<Union>xs\<in>{xs. length xs = card I}. \<Pi>' j\<in>I. if i = j then A else S j (xs ! T j))"
          using * by (auto simp add: Pi'_iff split del: if_split)
        also have "\<dots> \<in> sets ?P"
        proof (safe intro!: sets.countable_UN)
          fix xs show "(\<Pi>' j\<in>I. if i = j then A else S j (xs ! T j)) \<in> sets ?P"
            using A S_in_E
            by (simp add: P_closed)
               (auto simp: P_def subset_eq intro!: exI[of _ "\<lambda>j. if i = j then A else S j (xs ! T j)"])
        qed
        finally show "(\<lambda>x. (x)\<^sub>F i) -` A \<inter> space ?P \<in> sets ?P"
          using P_closed by simp
      qed
    qed
    from measurable_sets[OF this, of A] A \<open>i \<in> I\<close> E_closed
    have "(\<lambda>x. (x)\<^sub>F i) -` A \<inter> space ?P \<in> sets ?P"
      by (simp add: E_generates)
    also have "(\<lambda>x. (x)\<^sub>F i) -` A \<inter> space ?P = {f \<in> \<Pi>' i\<in>I. space (M i). f i \<in> A}"
      using P_closed by (auto simp: space_PiF)
    finally show "\<dots> \<in> sets ?P" .
  qed
  finally show "sets (PiF {I} M) \<subseteq> sigma_sets (space (PiF {I} M)) P"
    by (simp add: P_closed)
  show "sigma_sets (space (PiF {I} M)) P \<subseteq> sets (PiF {I} M)"
    using \<open>finite I\<close> \<open>I \<noteq> {}\<close>
    by (auto intro!: sets.sigma_sets_subset product_in_sets_PiFI simp: E_generates P_def)
qed

lemma product_open_generates_sets_PiF_single:
  assumes "I \<noteq> {}"
  assumes [simp]: "finite I"
  shows "sets (PiF {I} (\<lambda>_. borel::'b::second_countable_topology measure)) =
    sigma_sets (space (PiF {I} (\<lambda>_. borel))) {Pi' I F |F. (\<forall>i\<in>I. F i \<in> Collect open)}"
proof -
  from open_countable_basisE[OF open_UNIV] obtain S::"'b set set"
    where S: "S \<subseteq> (SOME B. countable B \<and> topological_basis B)" "UNIV = \<Union> S"
    by auto
  show ?thesis
  proof (rule sigma_fprod_algebra_sigma_eq)
    show "finite I" by simp
    show "I \<noteq> {}" by fact
    define S' where "S' = from_nat_into S"
    show "(\<Union>j. S' j) = space borel"
      using S
      apply (auto simp add: from_nat_into countable_basis_proj S'_def basis_proj_def)
      apply (metis (lifting, mono_tags) UNIV_I UnionE basis_proj_def countable_basis_proj countable_subset from_nat_into_surj)
      done
    show "range S' \<subseteq> Collect open"
      using S
      apply (auto simp add: from_nat_into countable_basis_proj S'_def)
      apply (metis UNIV_not_empty Union_empty from_nat_into subsetD topological_basis_open[OF basis_proj] basis_proj_def)
      done
    show "Collect open \<subseteq> Pow (space borel)" by simp
    show "sets borel = sigma_sets (space borel) (Collect open)"
      by (simp add: borel_def)
  qed
qed

lemma finmap_UNIV[simp]: "(\<Union>J\<in>Collect finite. \<Pi>' j\<in>J. UNIV) = UNIV" by auto

lemma borel_eq_PiF_borel:
  shows "(borel :: ('i::countable \<Rightarrow>\<^sub>F 'a::polish_space) measure) =
    PiF (Collect finite) (\<lambda>_. borel :: 'a measure)"
  unfolding borel_def PiF_def
proof (rule measure_eqI, clarsimp, rule sigma_sets_eqI)
  fix a::"('i \<Rightarrow>\<^sub>F 'a) set" assume "a \<in> Collect open" hence "open a" by simp
  then obtain B' where B': "B'\<subseteq>basis_finmap" "a = \<Union>B'"
    using finmap_topological_basis by (force simp add: topological_basis_def)
  have "a \<in> sigma UNIV {Pi' J X |X J. finite J \<and> X \<in> J \<rightarrow> sigma_sets UNIV (Collect open)}"
    unfolding \<open>a = \<Union>B'\<close>
  proof (rule sets.countable_Union)
    from B' countable_basis_finmap show "countable B'" by (metis countable_subset)
  next
    show "B' \<subseteq> sets (sigma UNIV
      {Pi' J X |X J. finite J \<and> X \<in> J \<rightarrow> sigma_sets UNIV (Collect open)})" (is "_ \<subseteq> sets ?s")
    proof
      fix x assume "x \<in> B'" with B' have "x \<in> basis_finmap" by auto
      then obtain J X where "x = Pi' J X" "finite J" "X \<in> J \<rightarrow> sigma_sets UNIV (Collect open)"
        by (auto simp: basis_finmap_def topological_basis_open[OF basis_proj])
      thus "x \<in> sets ?s" by auto
    qed
  qed
  thus "a \<in> sigma_sets UNIV {Pi' J X |X J. finite J \<and> X \<in> J \<rightarrow> sigma_sets UNIV (Collect open)}"
    by simp
next
  fix b::"('i \<Rightarrow>\<^sub>F 'a) set"
  assume "b \<in> {Pi' J X |X J. finite J \<and> X \<in> J \<rightarrow> sigma_sets UNIV (Collect open)}"
  hence b': "b \<in> sets (Pi\<^sub>F (Collect finite) (\<lambda>_. borel))" by (auto simp: sets_PiF borel_def)
  let ?b = "\<lambda>J. b \<inter> {x. domain x = J}"
  have "b = \<Union>((\<lambda>J. ?b J) ` Collect finite)" by auto
  also have "\<dots> \<in> sets borel"
  proof (rule sets.countable_Union, safe)
    fix J::"'i set" assume "finite J"
    { assume ef: "J = {}"
      have "?b J \<in> sets borel"
      proof cases
        assume "?b J \<noteq> {}"
        then obtain f where "f \<in> b" "domain f = {}" using ef by auto
        hence "?b J = {f}" using \<open>J = {}\<close>
          by (auto simp: finmap_eq_iff)
        also have "{f} \<in> sets borel" by simp
        finally show ?thesis .
      qed simp
    } moreover {
      assume "J \<noteq> ({}::'i set)"
      have "(?b J) = b \<inter> {m. domain m \<in> {J}}" by auto
      also have "\<dots> \<in> sets (PiF {J} (\<lambda>_. borel))"
        using b' by (rule restrict_sets_measurable) (auto simp: \<open>finite J\<close>)
      also have "\<dots> = sigma_sets (space (PiF {J} (\<lambda>_. borel)))
        {Pi' (J) F |F. (\<forall>j\<in>J. F j \<in> Collect open)}"
        (is "_ = sigma_sets _ ?P")
       by (rule product_open_generates_sets_PiF_single[OF \<open>J \<noteq> {}\<close> \<open>finite J\<close>])
      also have "\<dots> \<subseteq> sigma_sets UNIV (Collect open)"
        by (intro sigma_sets_mono'') (auto intro!: open_Pi'I simp: space_PiF)
      finally have "(?b J) \<in> sets borel" by (simp add: borel_def)
    } ultimately show "(?b J) \<in> sets borel" by blast
  qed (simp add: countable_Collect_finite)
  finally show "b \<in> sigma_sets UNIV (Collect open)" by (simp add: borel_def)
qed (simp add: emeasure_sigma borel_def PiF_def)

subsection \<open>Isomorphism between Functions and Finite Maps\<close>

lemma measurable_finmap_compose:
  shows "(\<lambda>m. compose J m f) \<in> measurable (PiM (f ` J) (\<lambda>_. M)) (PiM J (\<lambda>_. M))"
  unfolding compose_def by measurable

lemma measurable_compose_inv:
  assumes inj: "\<And>j. j \<in> J \<Longrightarrow> f' (f j) = j"
  shows "(\<lambda>m. compose (f ` J) m f') \<in> measurable (PiM J (\<lambda>_. M)) (PiM (f ` J) (\<lambda>_. M))"
  unfolding compose_def by (rule measurable_restrict) (auto simp: inj)

locale function_to_finmap =
  fixes J::"'a set" and f :: "'a \<Rightarrow> 'b::countable" and f'
  assumes [simp]: "finite J"
  assumes inv: "i \<in> J \<Longrightarrow> f' (f i) = i"
begin

text \<open>to measure finmaps\<close>

definition "fm = (finmap_of (f ` J)) o (\<lambda>g. compose (f ` J) g f')"

lemma domain_fm[simp]: "domain (fm x) = f ` J"
  unfolding fm_def by simp

lemma fm_restrict[simp]: "fm (restrict y J) = fm y"
  unfolding fm_def by (auto simp: compose_def inv intro: restrict_ext)

lemma fm_product:
  assumes "\<And>i. space (M i) = UNIV"
  shows "fm -` Pi' (f ` J) S \<inter> space (Pi\<^sub>M J M) = (\<Pi>\<^sub>E j \<in> J. S (f j))"
  using assms
  by (auto simp: inv fm_def compose_def space_PiM Pi'_def)

lemma fm_measurable:
  assumes "f ` J \<in> N"
  shows "fm \<in> measurable (Pi\<^sub>M J (\<lambda>_. M)) (Pi\<^sub>F N (\<lambda>_. M))"
  unfolding fm_def
proof (rule measurable_comp, rule measurable_compose_inv)
  show "finmap_of (f ` J) \<in> measurable (Pi\<^sub>M (f ` J) (\<lambda>_. M)) (PiF N (\<lambda>_. M)) "
    using assms by (intro measurable_finmap_of measurable_component_singleton) auto
qed (simp_all add: inv)

lemma proj_fm:
  assumes "x \<in> J"
  shows "fm m (f x) = m x"
  using assms by (auto simp: fm_def compose_def o_def inv)

lemma inj_on_compose_f': "inj_on (\<lambda>g. compose (f ` J) g f') (extensional J)"
proof (rule inj_on_inverseI)
  fix x::"'a \<Rightarrow> 'c" assume "x \<in> extensional J"
  thus "(\<lambda>x. compose J x f) (compose (f ` J) x f') = x"
    by (auto simp: compose_def inv extensional_def)
qed

lemma inj_on_fm:
  assumes "\<And>i. space (M i) = UNIV"
  shows "inj_on fm (space (Pi\<^sub>M J M))"
  using assms
  apply (auto simp: fm_def space_PiM PiE_def)
  apply (rule comp_inj_on)
  apply (rule inj_on_compose_f')
  apply (rule finmap_of_inj_on_extensional_finite)
  apply simp
  apply (auto)
  done

text \<open>to measure functions\<close>

definition "mf = (\<lambda>g. compose J g f) o proj"

lemma mf_fm:
  assumes "x \<in> space (Pi\<^sub>M J (\<lambda>_. M))"
  shows "mf (fm x) = x"
proof -
  have "mf (fm x) \<in> extensional J"
    by (auto simp: mf_def extensional_def compose_def)
  moreover
  have "x \<in> extensional J" using assms sets.sets_into_space
    by (force simp: space_PiM PiE_def)
  moreover
  { fix i assume "i \<in> J"
    hence "mf (fm x) i = x i"
      by (auto simp: inv mf_def compose_def fm_def)
  }
  ultimately
  show ?thesis by (rule extensionalityI)
qed

lemma mf_measurable:
  assumes "space M = UNIV"
  shows "mf \<in> measurable (PiF {f ` J} (\<lambda>_. M)) (PiM J (\<lambda>_. M))"
  unfolding mf_def
proof (rule measurable_comp, rule measurable_proj_PiM)
  show "(\<lambda>g. compose J g f) \<in> measurable (Pi\<^sub>M (f ` J) (\<lambda>x. M)) (Pi\<^sub>M J (\<lambda>_. M))"
    by (rule measurable_finmap_compose)
qed (auto simp add: space_PiM extensional_def assms)

lemma fm_image_measurable:
  assumes "space M = UNIV"
  assumes "X \<in> sets (Pi\<^sub>M J (\<lambda>_. M))"
  shows "fm ` X \<in> sets (PiF {f ` J} (\<lambda>_. M))"
proof -
  have "fm ` X = (mf) -` X \<inter> space (PiF {f ` J} (\<lambda>_. M))"
  proof safe
    fix x assume "x \<in> X"
    with mf_fm[of x] sets.sets_into_space[OF assms(2)] show "fm x \<in> mf -` X" by auto
    show "fm x \<in> space (PiF {f ` J} (\<lambda>_. M))" by (simp add: space_PiF assms)
  next
    fix y x
    assume x: "mf y \<in> X"
    assume y: "y \<in> space (PiF {f ` J} (\<lambda>_. M))"
    thus "y \<in> fm ` X"
      by (intro image_eqI[OF _ x], unfold finmap_eq_iff)
         (auto simp: space_PiF fm_def mf_def compose_def inv Pi'_def)
  qed
  also have "\<dots> \<in> sets (PiF {f ` J} (\<lambda>_. M))"
    using assms
    by (intro measurable_sets[OF mf_measurable]) auto
  finally show ?thesis .
qed

lemma fm_image_measurable_finite:
  assumes "space M = UNIV"
  assumes "X \<in> sets (Pi\<^sub>M J (\<lambda>_. M::'c measure))"
  shows "fm ` X \<in> sets (PiF (Collect finite) (\<lambda>_. M::'c measure))"
  using fm_image_measurable[OF assms]
  by (rule subspace_set_in_sets) (auto simp: finite_subset)

text \<open>measure on finmaps\<close>

definition "mapmeasure M N = distr M (PiF (Collect finite) N) (fm)"

lemma sets_mapmeasure[simp]: "sets (mapmeasure M N) = sets (PiF (Collect finite) N)"
  unfolding mapmeasure_def by simp

lemma space_mapmeasure[simp]: "space (mapmeasure M N) = space (PiF (Collect finite) N)"
  unfolding mapmeasure_def by simp

lemma mapmeasure_PiF:
  assumes s1: "space M = space (Pi\<^sub>M J (\<lambda>_. N))"
  assumes s2: "sets M = sets (Pi\<^sub>M J (\<lambda>_. N))"
  assumes "space N = UNIV"
  assumes "X \<in> sets (PiF (Collect finite) (\<lambda>_. N))"
  shows "emeasure (mapmeasure M (\<lambda>_. N)) X = emeasure M ((fm -` X \<inter> extensional J))"
  using assms
  by (auto simp: measurable_cong_sets[OF s2 refl] mapmeasure_def emeasure_distr
    fm_measurable space_PiM PiE_def)

lemma mapmeasure_PiM:
  fixes N::"'c measure"
  assumes s1: "space M = space (Pi\<^sub>M J (\<lambda>_. N))"
  assumes s2: "sets M = (Pi\<^sub>M J (\<lambda>_. N))"
  assumes N: "space N = UNIV"
  assumes X: "X \<in> sets M"
  shows "emeasure M X = emeasure (mapmeasure M (\<lambda>_. N)) (fm ` X)"
  unfolding mapmeasure_def
proof (subst emeasure_distr, subst measurable_cong_sets[OF s2 refl], rule fm_measurable)
  have "X \<subseteq> space (Pi\<^sub>M J (\<lambda>_. N))" using assms by (simp add: sets.sets_into_space)
  from assms inj_on_fm[of "\<lambda>_. N"] subsetD[OF this] have "fm -` fm ` X \<inter> space (Pi\<^sub>M J (\<lambda>_. N)) = X"
    by (auto simp: vimage_image_eq inj_on_def)
  thus "emeasure M X = emeasure M (fm -` fm ` X \<inter> space M)" using s1
    by simp
  show "fm ` X \<in> sets (PiF (Collect finite) (\<lambda>_. N))"
    by (rule fm_image_measurable_finite[OF N X[simplified s2]])
qed simp

end

end
