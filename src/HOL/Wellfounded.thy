(*  Title:      HOL/Wellfounded.thy
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Konrad Slind
    Author:     Alexander Krauss
    Author:     Andrei Popescu, TU Muenchen
*)

section \<open>Well-founded Recursion\<close>

theory Wellfounded
  imports Transitive_Closure
begin

subsection \<open>Basic Definitions\<close>

definition wf :: "('a \<times> 'a) set \<Rightarrow> bool"
  where "wf r \<longleftrightarrow> (\<forall>P. (\<forall>x. (\<forall>y. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x. P x))"

definition wfP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "wfP r \<longleftrightarrow> wf {(x, y). r x y}"

lemma wfP_wf_eq [pred_set_conv]: "wfP (\<lambda>x y. (x, y) \<in> r) = wf r"
  by (simp add: wfP_def)

lemma wfUNIVI: "(\<And>P x. (\<forall>x. (\<forall>y. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x) \<Longrightarrow> P x) \<Longrightarrow> wf r"
  unfolding wf_def by blast

lemmas wfPUNIVI = wfUNIVI [to_pred]

text \<open>Restriction to domain \<open>A\<close> and range \<open>B\<close>.
  If \<open>r\<close> is well-founded over their intersection, then \<open>wf r\<close>.\<close>
lemma wfI:
  assumes "r \<subseteq> A \<times> B"
    and "\<And>x P. \<lbrakk>\<forall>x. (\<forall>y. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x;  x \<in> A; x \<in> B\<rbrakk> \<Longrightarrow> P x"
  shows "wf r"
  using assms unfolding wf_def by blast

lemma wf_induct:
  assumes "wf r"
    and "\<And>x. \<forall>y. (y, x) \<in> r \<longrightarrow> P y \<Longrightarrow> P x"
  shows "P a"
  using assms unfolding wf_def by blast

lemmas wfP_induct = wf_induct [to_pred]

lemmas wf_induct_rule = wf_induct [rule_format, consumes 1, case_names less, induct set: wf]

lemmas wfP_induct_rule = wf_induct_rule [to_pred, induct set: wfP]

lemma wf_not_sym: "wf r \<Longrightarrow> (a, x) \<in> r \<Longrightarrow> (x, a) \<notin> r"
  by (induct a arbitrary: x set: wf) blast

lemma wf_asym:
  assumes "wf r" "(a, x) \<in> r"
  obtains "(x, a) \<notin> r"
  by (drule wf_not_sym[OF assms])

lemma wf_not_refl [simp]: "wf r \<Longrightarrow> (a, a) \<notin> r"
  by (blast elim: wf_asym)

lemma wf_irrefl:
  assumes "wf r"
  obtains "(a, a) \<notin> r"
  by (drule wf_not_refl[OF assms])

lemma wf_wellorderI:
  assumes wf: "wf {(x::'a::ord, y). x < y}"
    and lin: "OFCLASS('a::ord, linorder_class)"
  shows "OFCLASS('a::ord, wellorder_class)"
  using lin
  apply (rule wellorder_class.intro)
  apply (rule class.wellorder_axioms.intro)
  apply (rule wf_induct_rule [OF wf])
  apply simp
  done

lemma (in wellorder) wf: "wf {(x, y). x < y}"
  unfolding wf_def by (blast intro: less_induct)


subsection \<open>Basic Results\<close>

text \<open>Point-free characterization of well-foundedness\<close>

lemma wfE_pf:
  assumes wf: "wf R"
    and a: "A \<subseteq> R `` A"
  shows "A = {}"
proof -
  from wf have "x \<notin> A" for x
  proof induct
    fix x assume "\<And>y. (y, x) \<in> R \<Longrightarrow> y \<notin> A"
    then have "x \<notin> R `` A" by blast
    with a show "x \<notin> A" by blast
  qed
  then show ?thesis by auto
qed

lemma wfI_pf:
  assumes a: "\<And>A. A \<subseteq> R `` A \<Longrightarrow> A = {}"
  shows "wf R"
proof (rule wfUNIVI)
  fix P :: "'a \<Rightarrow> bool" and x
  let ?A = "{x. \<not> P x}"
  assume "\<forall>x. (\<forall>y. (y, x) \<in> R \<longrightarrow> P y) \<longrightarrow> P x"
  then have "?A \<subseteq> R `` ?A" by blast
  with a show "P x" by blast
qed


subsubsection \<open>Minimal-element characterization of well-foundedness\<close>

lemma wfE_min:
  assumes wf: "wf R" and Q: "x \<in> Q"
  obtains z where "z \<in> Q" "\<And>y. (y, z) \<in> R \<Longrightarrow> y \<notin> Q"
  using Q wfE_pf[OF wf, of Q] by blast

lemma wfE_min':
  "wf R \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> (\<And>z. z \<in> Q \<Longrightarrow> (\<And>y. (y, z) \<in> R \<Longrightarrow> y \<notin> Q) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  using wfE_min[of R _ Q] by blast

lemma wfI_min:
  assumes a: "\<And>x Q. x \<in> Q \<Longrightarrow> \<exists>z\<in>Q. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> Q"
  shows "wf R"
proof (rule wfI_pf)
  fix A
  assume b: "A \<subseteq> R `` A"
  have False if "x \<in> A" for x
    using a[OF that] b by blast
  then show "A = {}" by blast
qed

lemma wf_eq_minimal: "wf r \<longleftrightarrow> (\<forall>Q x. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (y, z) \<in> r \<longrightarrow> y \<notin> Q))"
  apply auto
   apply (erule wfE_min)
    apply assumption
   apply blast
  apply (rule wfI_min)
  apply auto
  done

lemmas wfP_eq_minimal = wf_eq_minimal [to_pred]


subsubsection \<open>Well-foundedness of transitive closure\<close>

lemma wf_trancl:
  assumes "wf r"
  shows "wf (r\<^sup>+)"
proof -
  have "P x" if induct_step: "\<And>x. (\<And>y. (y, x) \<in> r\<^sup>+ \<Longrightarrow> P y) \<Longrightarrow> P x" for P x
  proof (rule induct_step)
    show "P y" if "(y, x) \<in> r\<^sup>+" for y
      using \<open>wf r\<close> and that
    proof (induct x arbitrary: y)
      case (less x)
      note hyp = \<open>\<And>x' y'. (x', x) \<in> r \<Longrightarrow> (y', x') \<in> r\<^sup>+ \<Longrightarrow> P y'\<close>
      from \<open>(y, x) \<in> r\<^sup>+\<close> show "P y"
      proof cases
        case base
        show "P y"
        proof (rule induct_step)
          fix y'
          assume "(y', y) \<in> r\<^sup>+"
          with \<open>(y, x) \<in> r\<close> show "P y'"
            by (rule hyp [of y y'])
        qed
      next
        case step
        then obtain x' where "(x', x) \<in> r" and "(y, x') \<in> r\<^sup>+"
          by simp
        then show "P y" by (rule hyp [of x' y])
      qed
    qed
  qed
  then show ?thesis unfolding wf_def by blast
qed

lemmas wfP_trancl = wf_trancl [to_pred]

lemma wf_converse_trancl: "wf (r\<inverse>) \<Longrightarrow> wf ((r\<^sup>+)\<inverse>)"
  apply (subst trancl_converse [symmetric])
  apply (erule wf_trancl)
  done

text \<open>Well-foundedness of subsets\<close>

lemma wf_subset: "wf r \<Longrightarrow> p \<subseteq> r \<Longrightarrow> wf p"
  by (simp add: wf_eq_minimal) fast

lemmas wfP_subset = wf_subset [to_pred]

text \<open>Well-foundedness of the empty relation\<close>

lemma wf_empty [iff]: "wf {}"
  by (simp add: wf_def)

lemma wfP_empty [iff]: "wfP (\<lambda>x y. False)"
proof -
  have "wfP bot"
    by (fact wf_empty[to_pred bot_empty_eq2])
  then show ?thesis
    by (simp add: bot_fun_def)
qed

lemma wf_Int1: "wf r \<Longrightarrow> wf (r \<inter> r')"
  by (erule wf_subset) (rule Int_lower1)

lemma wf_Int2: "wf r \<Longrightarrow> wf (r' \<inter> r)"
  by (erule wf_subset) (rule Int_lower2)

text \<open>Exponentiation.\<close>
lemma wf_exp:
  assumes "wf (R ^^ n)"
  shows "wf R"
proof (rule wfI_pf)
  fix A assume "A \<subseteq> R `` A"
  then have "A \<subseteq> (R ^^ n) `` A"
    by (induct n) force+
  with \<open>wf (R ^^ n)\<close> show "A = {}"
    by (rule wfE_pf)
qed

text \<open>Well-foundedness of \<open>insert\<close>.\<close>
lemma wf_insert [iff]: "wf (insert (y, x) r) \<longleftrightarrow> wf r \<and> (x, y) \<notin> r\<^sup>*"
  apply (rule iffI)
   apply (blast elim: wf_trancl [THEN wf_irrefl]
      intro: rtrancl_into_trancl1 wf_subset rtrancl_mono [THEN [2] rev_subsetD])
  apply (simp add: wf_eq_minimal)
  apply safe
  apply (rule allE)
   apply assumption
  apply (erule impE)
   apply blast
  apply (erule bexE)
  apply (rename_tac a, case_tac "a = x")
   prefer 2
   apply blast
  apply (case_tac "y \<in> Q")
   prefer 2
   apply blast
  apply (rule_tac x = "{z. z \<in> Q \<and> (z,y) \<in> r\<^sup>*}" in allE)
   apply assumption
  apply (erule_tac V = "\<forall>Q. (\<exists>x. x \<in> Q) \<longrightarrow> P Q" for P in thin_rl)
  (*essential for speed*)
  (*blast with new substOccur fails*)
  apply (fast intro: converse_rtrancl_into_rtrancl)
  done


subsubsection \<open>Well-foundedness of image\<close>

lemma wf_map_prod_image_Dom_Ran:
  fixes r:: "('a \<times> 'a) set"
    and f:: "'a \<Rightarrow> 'b"
  assumes wf_r: "wf r"
    and inj: "\<And> a a'. a \<in> Domain r \<Longrightarrow> a' \<in> Range r \<Longrightarrow> f a = f a' \<Longrightarrow> a = a'"
  shows "wf (map_prod f f ` r)"
proof (unfold wf_eq_minimal, clarify)
  fix B :: "'b set" and b::"'b"
  assume "b \<in> B"
  define A where "A = f -` B \<inter> Domain r"
  show "\<exists>z\<in>B. \<forall>y. (y, z) \<in> map_prod f f ` r \<longrightarrow> y \<notin> B"
  proof (cases "A = {}")
    case False
    then obtain a0 where "a0 \<in> A" and "\<forall>a. (a, a0) \<in> r \<longrightarrow> a \<notin> A"
      using wfE_min[OF wf_r] by auto
    thus ?thesis 
      using inj unfolding A_def
      by (intro bexI[of _ "f a0"]) auto
  qed (insert \<open>b \<in> B\<close>, unfold A_def, auto) 
qed

lemma wf_map_prod_image: "wf r \<Longrightarrow> inj f \<Longrightarrow> wf (map_prod f f ` r)"
by(rule wf_map_prod_image_Dom_Ran) (auto dest: inj_onD)


subsection \<open>Well-Foundedness Results for Unions\<close>

lemma wf_union_compatible:
  assumes "wf R" "wf S"
  assumes "R O S \<subseteq> R"
  shows "wf (R \<union> S)"
proof (rule wfI_min)
  fix x :: 'a and Q
  let ?Q' = "{x \<in> Q. \<forall>y. (y, x) \<in> R \<longrightarrow> y \<notin> Q}"
  assume "x \<in> Q"
  obtain a where "a \<in> ?Q'"
    by (rule wfE_min [OF \<open>wf R\<close> \<open>x \<in> Q\<close>]) blast
  with \<open>wf S\<close> obtain z where "z \<in> ?Q'" and zmin: "\<And>y. (y, z) \<in> S \<Longrightarrow> y \<notin> ?Q'"
    by (erule wfE_min)
  have "y \<notin> Q" if "(y, z) \<in> S" for y
  proof
    from that have "y \<notin> ?Q'" by (rule zmin)
    assume "y \<in> Q"
    with \<open>y \<notin> ?Q'\<close> obtain w where "(w, y) \<in> R" and "w \<in> Q" by auto
    from \<open>(w, y) \<in> R\<close> \<open>(y, z) \<in> S\<close> have "(w, z) \<in> R O S" by (rule relcompI)
    with \<open>R O S \<subseteq> R\<close> have "(w, z) \<in> R" ..
    with \<open>z \<in> ?Q'\<close> have "w \<notin> Q" by blast
    with \<open>w \<in> Q\<close> show False by contradiction
  qed
  with \<open>z \<in> ?Q'\<close> show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> R \<union> S \<longrightarrow> y \<notin> Q" by blast
qed


text \<open>Well-foundedness of indexed union with disjoint domains and ranges.\<close>

lemma wf_UN:
  assumes "\<forall>i\<in>I. wf (r i)"
    and "\<forall>i\<in>I. \<forall>j\<in>I. r i \<noteq> r j \<longrightarrow> Domain (r i) \<inter> Range (r j) = {}"
  shows "wf (\<Union>i\<in>I. r i)"
  using assms
  apply (simp only: wf_eq_minimal)
  apply clarify
  apply (rename_tac A a, case_tac "\<exists>i\<in>I. \<exists>a\<in>A. \<exists>b\<in>A. (b, a) \<in> r i")
   prefer 2
   apply force
  apply clarify
  apply (drule bspec, assumption)
  apply (erule_tac x="{a. a \<in> A \<and> (\<exists>b\<in>A. (b, a) \<in> r i) }" in allE)
  apply (blast elim!: allE)
  done

lemma wfP_SUP:
  "\<forall>i. wfP (r i) \<Longrightarrow> \<forall>i j. r i \<noteq> r j \<longrightarrow> inf (Domainp (r i)) (Rangep (r j)) = bot \<Longrightarrow>
    wfP (SUPREMUM UNIV r)"
  by (rule wf_UN[to_pred]) simp_all

lemma wf_Union:
  assumes "\<forall>r\<in>R. wf r"
    and "\<forall>r\<in>R. \<forall>s\<in>R. r \<noteq> s \<longrightarrow> Domain r \<inter> Range s = {}"
  shows "wf (\<Union>R)"
  using assms wf_UN[of R "\<lambda>i. i"] by simp

text \<open>
  Intuition: We find an \<open>R \<union> S\<close>-min element of a nonempty subset \<open>A\<close> by case distinction.
  \<^enum> There is a step \<open>a \<midarrow>R\<rightarrow> b\<close> with \<open>a, b \<in> A\<close>.
    Pick an \<open>R\<close>-min element \<open>z\<close> of the (nonempty) set \<open>{a\<in>A | \<exists>b\<in>A. a \<midarrow>R\<rightarrow> b}\<close>.
    By definition, there is \<open>z' \<in> A\<close> s.t. \<open>z \<midarrow>R\<rightarrow> z'\<close>. Because \<open>z\<close> is \<open>R\<close>-min in the
    subset, \<open>z'\<close> must be \<open>R\<close>-min in \<open>A\<close>. Because \<open>z'\<close> has an \<open>R\<close>-predecessor, it cannot
    have an \<open>S\<close>-successor and is thus \<open>S\<close>-min in \<open>A\<close> as well.
  \<^enum> There is no such step.
    Pick an \<open>S\<close>-min element of \<open>A\<close>. In this case it must be an \<open>R\<close>-min
    element of \<open>A\<close> as well.
\<close>
lemma wf_Un: "wf r \<Longrightarrow> wf s \<Longrightarrow> Domain r \<inter> Range s = {} \<Longrightarrow> wf (r \<union> s)"
  using wf_union_compatible[of s r]
  by (auto simp: Un_ac)

lemma wf_union_merge: "wf (R \<union> S) = wf (R O R \<union> S O R \<union> S)"
  (is "wf ?A = wf ?B")
proof
  assume "wf ?A"
  with wf_trancl have wfT: "wf (?A\<^sup>+)" .
  moreover have "?B \<subseteq> ?A\<^sup>+"
    by (subst trancl_unfold, subst trancl_unfold) blast
  ultimately show "wf ?B" by (rule wf_subset)
next
  assume "wf ?B"
  show "wf ?A"
  proof (rule wfI_min)
    fix Q :: "'a set" and x
    assume "x \<in> Q"
    with \<open>wf ?B\<close> obtain z where "z \<in> Q" and "\<And>y. (y, z) \<in> ?B \<Longrightarrow> y \<notin> Q"
      by (erule wfE_min)
    then have 1: "\<And>y. (y, z) \<in> R O R \<Longrightarrow> y \<notin> Q"
      and 2: "\<And>y. (y, z) \<in> S O R \<Longrightarrow> y \<notin> Q"
      and 3: "\<And>y. (y, z) \<in> S \<Longrightarrow> y \<notin> Q"
      by auto
    show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> ?A \<longrightarrow> y \<notin> Q"
    proof (cases "\<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> Q")
      case True
      with \<open>z \<in> Q\<close> 3 show ?thesis by blast
    next
      case False
      then obtain z' where "z'\<in>Q" "(z', z) \<in> R" by blast
      have "\<forall>y. (y, z') \<in> ?A \<longrightarrow> y \<notin> Q"
      proof (intro allI impI)
        fix y assume "(y, z') \<in> ?A"
        then show "y \<notin> Q"
        proof
          assume "(y, z') \<in> R"
          then have "(y, z) \<in> R O R" using \<open>(z', z) \<in> R\<close> ..
          with 1 show "y \<notin> Q" .
        next
          assume "(y, z') \<in> S"
          then have "(y, z) \<in> S O R" using  \<open>(z', z) \<in> R\<close> ..
          with 2 show "y \<notin> Q" .
        qed
      qed
      with \<open>z' \<in> Q\<close> show ?thesis ..
    qed
  qed
qed

lemma wf_comp_self: "wf R \<longleftrightarrow> wf (R O R)"  \<comment> \<open>special case\<close>
  by (rule wf_union_merge [where S = "{}", simplified])


subsection \<open>Well-Foundedness of Composition\<close>

text \<open>Bachmair and Dershowitz 1986, Lemma 2. [Provided by Tjark Weber]\<close>

lemma qc_wf_relto_iff:
  assumes "R O S \<subseteq> (R \<union> S)\<^sup>* O R" \<comment> \<open>R quasi-commutes over S\<close>
  shows "wf (S\<^sup>* O R O S\<^sup>*) \<longleftrightarrow> wf R"
    (is "wf ?S \<longleftrightarrow> _")
proof
  show "wf R" if "wf ?S"
  proof -
    have "R \<subseteq> ?S" by auto
    with wf_subset [of ?S] that show "wf R"
      by auto
  qed
next
  show "wf ?S" if "wf R"
  proof (rule wfI_pf)
    fix A
    assume A: "A \<subseteq> ?S `` A"
    let ?X = "(R \<union> S)\<^sup>* `` A"
    have *: "R O (R \<union> S)\<^sup>* \<subseteq> (R \<union> S)\<^sup>* O R"
    proof -
      have "(x, z) \<in> (R \<union> S)\<^sup>* O R" if "(y, z) \<in> (R \<union> S)\<^sup>*" and "(x, y) \<in> R" for x y z
        using that
      proof (induct y z)
        case rtrancl_refl
        then show ?case by auto
      next
        case (rtrancl_into_rtrancl a b c)
        then have "(x, c) \<in> ((R \<union> S)\<^sup>* O (R \<union> S)\<^sup>*) O R"
          using assms by blast
        then show ?case by simp
      qed
      then show ?thesis by auto
    qed
    then have "R O S\<^sup>* \<subseteq> (R \<union> S)\<^sup>* O R"
      using rtrancl_Un_subset by blast
    then have "?S \<subseteq> (R \<union> S)\<^sup>* O (R \<union> S)\<^sup>* O R"
      by (simp add: relcomp_mono rtrancl_mono)
    also have "\<dots> = (R \<union> S)\<^sup>* O R"
      by (simp add: O_assoc[symmetric])
    finally have "?S O (R \<union> S)\<^sup>* \<subseteq> (R \<union> S)\<^sup>* O R O (R \<union> S)\<^sup>*"
      by (simp add: O_assoc[symmetric] relcomp_mono)
    also have "\<dots> \<subseteq> (R \<union> S)\<^sup>* O (R \<union> S)\<^sup>* O R"
      using * by (simp add: relcomp_mono)
    finally have "?S O (R \<union> S)\<^sup>* \<subseteq> (R \<union> S)\<^sup>* O R"
      by (simp add: O_assoc[symmetric])
    then have "(?S O (R \<union> S)\<^sup>*) `` A \<subseteq> ((R \<union> S)\<^sup>* O R) `` A"
      by (simp add: Image_mono)
    moreover have "?X \<subseteq> (?S O (R \<union> S)\<^sup>*) `` A"
      using A by (auto simp: relcomp_Image)
    ultimately have "?X \<subseteq> R `` ?X"
      by (auto simp: relcomp_Image)
    then have "?X = {}"
      using \<open>wf R\<close> by (simp add: wfE_pf)
    moreover have "A \<subseteq> ?X" by auto
    ultimately show "A = {}" by simp
  qed
qed

corollary wf_relcomp_compatible:
  assumes "wf R" and "R O S \<subseteq> S O R"
  shows "wf (S O R)"
proof -
  have "R O S \<subseteq> (R \<union> S)\<^sup>* O R"
    using assms by blast
  then have "wf (S\<^sup>* O R O S\<^sup>*)"
    by (simp add: assms qc_wf_relto_iff)
  then show ?thesis
    by (rule Wellfounded.wf_subset) blast
qed


subsection \<open>Acyclic relations\<close>

lemma wf_acyclic: "wf r \<Longrightarrow> acyclic r"
  by (simp add: acyclic_def) (blast elim: wf_trancl [THEN wf_irrefl])

lemmas wfP_acyclicP = wf_acyclic [to_pred]


subsubsection \<open>Wellfoundedness of finite acyclic relations\<close>

lemma finite_acyclic_wf [rule_format]: "finite r \<Longrightarrow> acyclic r \<longrightarrow> wf r"
  apply (erule finite_induct)
   apply blast
  apply (simp add: split_tupled_all)
  done

lemma finite_acyclic_wf_converse: "finite r \<Longrightarrow> acyclic r \<Longrightarrow> wf (r\<inverse>)"
  apply (erule finite_converse [THEN iffD2, THEN finite_acyclic_wf])
  apply (erule acyclic_converse [THEN iffD2])
  done

text \<open>
  Observe that the converse of an irreflexive, transitive,
  and finite relation is again well-founded. Thus, we may
  employ it for well-founded induction.
\<close>
lemma wf_converse:
  assumes "irrefl r" and "trans r" and "finite r"
  shows "wf (r\<inverse>)"
proof -
  have "acyclic r"
    using \<open>irrefl r\<close> and \<open>trans r\<close>
    by (simp add: irrefl_def acyclic_irrefl)
  with \<open>finite r\<close> show ?thesis
    by (rule finite_acyclic_wf_converse)
qed

lemma wf_iff_acyclic_if_finite: "finite r \<Longrightarrow> wf r = acyclic r"
  by (blast intro: finite_acyclic_wf wf_acyclic)


subsection \<open>@{typ nat} is well-founded\<close>

lemma less_nat_rel: "(<) = (\<lambda>m n. n = Suc m)\<^sup>+\<^sup>+"
proof (rule ext, rule ext, rule iffI)
  fix n m :: nat
  show "(\<lambda>m n. n = Suc m)\<^sup>+\<^sup>+ m n" if "m < n"
    using that
  proof (induct n)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then show ?case
      by (auto simp add: less_Suc_eq_le le_less intro: tranclp.trancl_into_trancl)
  qed
  show "m < n" if "(\<lambda>m n. n = Suc m)\<^sup>+\<^sup>+ m n"
    using that by (induct n) (simp_all add: less_Suc_eq_le reflexive le_less)
qed

definition pred_nat :: "(nat \<times> nat) set"
  where "pred_nat = {(m, n). n = Suc m}"

definition less_than :: "(nat \<times> nat) set"
  where "less_than = pred_nat\<^sup>+"

lemma less_eq: "(m, n) \<in> pred_nat\<^sup>+ \<longleftrightarrow> m < n"
  unfolding less_nat_rel pred_nat_def trancl_def by simp

lemma pred_nat_trancl_eq_le: "(m, n) \<in> pred_nat\<^sup>* \<longleftrightarrow> m \<le> n"
  unfolding less_eq rtrancl_eq_or_trancl by auto

lemma wf_pred_nat: "wf pred_nat"
  apply (unfold wf_def pred_nat_def)
  apply clarify
  apply (induct_tac x)
   apply blast+
  done

lemma wf_less_than [iff]: "wf less_than"
  by (simp add: less_than_def wf_pred_nat [THEN wf_trancl])

lemma trans_less_than [iff]: "trans less_than"
  by (simp add: less_than_def)

lemma less_than_iff [iff]: "((x,y) \<in> less_than) = (x<y)"
  by (simp add: less_than_def less_eq)

lemma wf_less: "wf {(x, y::nat). x < y}"
  by (rule Wellfounded.wellorder_class.wf)


subsection \<open>Accessible Part\<close>

text \<open>
  Inductive definition of the accessible part \<open>acc r\<close> of a
  relation; see also @{cite "paulin-tlca"}.
\<close>

inductive_set acc :: "('a \<times> 'a) set \<Rightarrow> 'a set" for r :: "('a \<times> 'a) set"
  where accI: "(\<And>y. (y, x) \<in> r \<Longrightarrow> y \<in> acc r) \<Longrightarrow> x \<in> acc r"

abbreviation termip :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  where "termip r \<equiv> accp (r\<inverse>\<inverse>)"

abbreviation termi :: "('a \<times> 'a) set \<Rightarrow> 'a set"
  where "termi r \<equiv> acc (r\<inverse>)"

lemmas accpI = accp.accI

lemma accp_eq_acc [code]: "accp r = (\<lambda>x. x \<in> Wellfounded.acc {(x, y). r x y})"
  by (simp add: acc_def)


text \<open>Induction rules\<close>

theorem accp_induct:
  assumes major: "accp r a"
  assumes hyp: "\<And>x. accp r x \<Longrightarrow> \<forall>y. r y x \<longrightarrow> P y \<Longrightarrow> P x"
  shows "P a"
  apply (rule major [THEN accp.induct])
  apply (rule hyp)
   apply (rule accp.accI)
   apply fast
  apply fast
  done

lemmas accp_induct_rule = accp_induct [rule_format, induct set: accp]

theorem accp_downward: "accp r b \<Longrightarrow> r a b \<Longrightarrow> accp r a"
  by (cases rule: accp.cases)

lemma not_accp_down:
  assumes na: "\<not> accp R x"
  obtains z where "R z x" and "\<not> accp R z"
proof -
  assume a: "\<And>z. R z x \<Longrightarrow> \<not> accp R z \<Longrightarrow> thesis"
  show thesis
  proof (cases "\<forall>z. R z x \<longrightarrow> accp R z")
    case True
    then have "\<And>z. R z x \<Longrightarrow> accp R z" by auto
    then have "accp R x" by (rule accp.accI)
    with na show thesis ..
  next
    case False then obtain z where "R z x" and "\<not> accp R z"
      by auto
    with a show thesis .
  qed
qed

lemma accp_downwards_aux: "r\<^sup>*\<^sup>* b a \<Longrightarrow> accp r a \<longrightarrow> accp r b"
  by (erule rtranclp_induct) (blast dest: accp_downward)+

theorem accp_downwards: "accp r a \<Longrightarrow> r\<^sup>*\<^sup>* b a \<Longrightarrow> accp r b"
  by (blast dest: accp_downwards_aux)

theorem accp_wfPI: "\<forall>x. accp r x \<Longrightarrow> wfP r"
  apply (rule wfPUNIVI)
  apply (rule_tac P = P in accp_induct)
   apply blast
  apply blast
  done

theorem accp_wfPD: "wfP r \<Longrightarrow> accp r x"
  apply (erule wfP_induct_rule)
  apply (rule accp.accI)
  apply blast
  done

theorem wfP_accp_iff: "wfP r = (\<forall>x. accp r x)"
  by (blast intro: accp_wfPI dest: accp_wfPD)


text \<open>Smaller relations have bigger accessible parts:\<close>

lemma accp_subset:
  assumes "R1 \<le> R2"
  shows "accp R2 \<le> accp R1"
proof (rule predicate1I)
  fix x
  assume "accp R2 x"
  then show "accp R1 x"
  proof (induct x)
    fix x
    assume "\<And>y. R2 y x \<Longrightarrow> accp R1 y"
    with assms show "accp R1 x"
      by (blast intro: accp.accI)
  qed
qed


text \<open>This is a generalized induction theorem that works on
  subsets of the accessible part.\<close>

lemma accp_subset_induct:
  assumes subset: "D \<le> accp R"
    and dcl: "\<And>x z. D x \<Longrightarrow> R z x \<Longrightarrow> D z"
    and "D x"
    and istep: "\<And>x. D x \<Longrightarrow> (\<And>z. R z x \<Longrightarrow> P z) \<Longrightarrow> P x"
  shows "P x"
proof -
  from subset and \<open>D x\<close>
  have "accp R x" ..
  then show "P x" using \<open>D x\<close>
  proof (induct x)
    fix x
    assume "D x" and "\<And>y. R y x \<Longrightarrow> D y \<Longrightarrow> P y"
    with dcl and istep show "P x" by blast
  qed
qed


text \<open>Set versions of the above theorems\<close>

lemmas acc_induct = accp_induct [to_set]
lemmas acc_induct_rule = acc_induct [rule_format, induct set: acc]
lemmas acc_downward = accp_downward [to_set]
lemmas not_acc_down = not_accp_down [to_set]
lemmas acc_downwards_aux = accp_downwards_aux [to_set]
lemmas acc_downwards = accp_downwards [to_set]
lemmas acc_wfI = accp_wfPI [to_set]
lemmas acc_wfD = accp_wfPD [to_set]
lemmas wf_acc_iff = wfP_accp_iff [to_set]
lemmas acc_subset = accp_subset [to_set]
lemmas acc_subset_induct = accp_subset_induct [to_set]


subsection \<open>Tools for building wellfounded relations\<close>

text \<open>Inverse Image\<close>

lemma wf_inv_image [simp,intro!]: "wf r \<Longrightarrow> wf (inv_image r f)"
  for f :: "'a \<Rightarrow> 'b"
  apply (simp add: inv_image_def wf_eq_minimal)
  apply clarify
  apply (subgoal_tac "\<exists>w::'b. w \<in> {w. \<exists>x::'a. x \<in> Q \<and> f x = w}")
   prefer 2
   apply (blast del: allE)
  apply (erule allE)
  apply (erule (1) notE impE)
  apply blast
  done

text \<open>Measure functions into @{typ nat}\<close>

definition measure :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set"
  where "measure = inv_image less_than"

lemma in_measure[simp, code_unfold]: "(x, y) \<in> measure f \<longleftrightarrow> f x < f y"
  by (simp add:measure_def)

lemma wf_measure [iff]: "wf (measure f)"
  unfolding measure_def by (rule wf_less_than [THEN wf_inv_image])

lemma wf_if_measure: "(\<And>x. P x \<Longrightarrow> f(g x) < f x) \<Longrightarrow> wf {(y,x). P x \<and> y = g x}"
  for f :: "'a \<Rightarrow> nat"
  apply (insert wf_measure[of f])
  apply (simp only: measure_def inv_image_def less_than_def less_eq)
  apply (erule wf_subset)
  apply auto
  done


subsubsection \<open>Lexicographic combinations\<close>

definition lex_prod :: "('a \<times>'a) set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> (('a \<times> 'b) \<times> ('a \<times> 'b)) set"
    (infixr "<*lex*>" 80)
  where "ra <*lex*> rb = {((a, b), (a', b')). (a, a') \<in> ra \<or> a = a' \<and> (b, b') \<in> rb}"

lemma wf_lex_prod [intro!]: "wf ra \<Longrightarrow> wf rb \<Longrightarrow> wf (ra <*lex*> rb)"
  apply (unfold wf_def lex_prod_def)
  apply (rule allI)
  apply (rule impI)
  apply (simp only: split_paired_All)
  apply (drule spec)
  apply (erule mp)
  apply (rule allI)
  apply (rule impI)
  apply (drule spec)
  apply (erule mp)
  apply blast
  done

lemma in_lex_prod[simp]: "((a, b), (a', b')) \<in> r <*lex*> s \<longleftrightarrow> (a, a') \<in> r \<or> a = a' \<and> (b, b') \<in> s"
  by (auto simp:lex_prod_def)

text \<open>\<open><*lex*>\<close> preserves transitivity\<close>
lemma trans_lex_prod [intro!]: "trans R1 \<Longrightarrow> trans R2 \<Longrightarrow> trans (R1 <*lex*> R2)"
  unfolding trans_def lex_prod_def by blast


text \<open>lexicographic combinations with measure functions\<close>

definition mlex_prod :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" (infixr "<*mlex*>" 80)
  where "f <*mlex*> R = inv_image (less_than <*lex*> R) (\<lambda>x. (f x, x))"

lemma
  wf_mlex: "wf R \<Longrightarrow> wf (f <*mlex*> R)" and
  mlex_less: "f x < f y \<Longrightarrow> (x, y) \<in> f <*mlex*> R" and
  mlex_leq: "f x \<le> f y \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> (x, y) \<in> f <*mlex*> R" and
  mlex_iff: "(x, y) \<in> f <*mlex*> R \<longleftrightarrow> f x < f y \<or> f x = f y \<and> (x, y) \<in> R"
  by (auto simp: mlex_prod_def)

text \<open>Proper subset relation on finite sets.\<close>
definition finite_psubset :: "('a set \<times> 'a set) set"
  where "finite_psubset = {(A, B). A \<subset> B \<and> finite B}"

lemma wf_finite_psubset[simp]: "wf finite_psubset"
  apply (unfold finite_psubset_def)
  apply (rule wf_measure [THEN wf_subset])
  apply (simp add: measure_def inv_image_def less_than_def less_eq)
  apply (fast elim!: psubset_card_mono)
  done

lemma trans_finite_psubset: "trans finite_psubset"
  by (auto simp: finite_psubset_def less_le trans_def)

lemma in_finite_psubset[simp]: "(A, B) \<in> finite_psubset \<longleftrightarrow> A \<subset> B \<and> finite B"
  unfolding finite_psubset_def by auto

text \<open>max- and min-extension of order to finite sets\<close>

inductive_set max_ext :: "('a \<times> 'a) set \<Rightarrow> ('a set \<times> 'a set) set"
  for R :: "('a \<times> 'a) set"
  where max_extI[intro]:
    "finite X \<Longrightarrow> finite Y \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> \<exists>y\<in>Y. (x, y) \<in> R) \<Longrightarrow> (X, Y) \<in> max_ext R"

lemma max_ext_wf:
  assumes wf: "wf r"
  shows "wf (max_ext r)"
proof (rule acc_wfI, intro allI)
  show "M \<in> acc (max_ext r)" (is "_ \<in> ?W") for M
  proof (induct M rule: infinite_finite_induct)
    case empty
    show ?case
      by (rule accI) (auto elim: max_ext.cases)
  next
    case (insert a M)
    from wf \<open>M \<in> ?W\<close> \<open>finite M\<close> show "insert a M \<in> ?W"
    proof (induct arbitrary: M)
      fix M a
      assume "M \<in> ?W"
      assume [intro]: "finite M"
      assume hyp: "\<And>b M. (b, a) \<in> r \<Longrightarrow> M \<in> ?W \<Longrightarrow> finite M \<Longrightarrow> insert b M \<in> ?W"
      have add_less: "M \<in> ?W \<Longrightarrow> (\<And>y. y \<in> N \<Longrightarrow> (y, a) \<in> r) \<Longrightarrow> N \<union> M \<in> ?W"
        if "finite N" "finite M" for N M :: "'a set"
        using that by (induct N arbitrary: M) (auto simp: hyp)
      show "insert a M \<in> ?W"
      proof (rule accI)
        fix N
        assume Nless: "(N, insert a M) \<in> max_ext r"
        then have *: "\<And>x. x \<in> N \<Longrightarrow> (x, a) \<in> r \<or> (\<exists>y \<in> M. (x, y) \<in> r)"
          by (auto elim!: max_ext.cases)

        let ?N1 = "{n \<in> N. (n, a) \<in> r}"
        let ?N2 = "{n \<in> N. (n, a) \<notin> r}"
        have N: "?N1 \<union> ?N2 = N" by (rule set_eqI) auto
        from Nless have "finite N" by (auto elim: max_ext.cases)
        then have finites: "finite ?N1" "finite ?N2" by auto

        have "?N2 \<in> ?W"
        proof (cases "M = {}")
          case [simp]: True
          have Mw: "{} \<in> ?W" by (rule accI) (auto elim: max_ext.cases)
          from * have "?N2 = {}" by auto
          with Mw show "?N2 \<in> ?W" by (simp only:)
        next
          case False
          from * finites have N2: "(?N2, M) \<in> max_ext r"
            by (rule_tac max_extI[OF _ _ \<open>M \<noteq> {}\<close>]) auto
          with \<open>M \<in> ?W\<close> show "?N2 \<in> ?W" by (rule acc_downward)
        qed
        with finites have "?N1 \<union> ?N2 \<in> ?W"
          by (rule add_less) simp
        then show "N \<in> ?W" by (simp only: N)
      qed
    qed
  next
    case infinite
    show ?case
      by (rule accI) (auto elim: max_ext.cases simp: infinite)
  qed
qed

lemma max_ext_additive: "(A, B) \<in> max_ext R \<Longrightarrow> (C, D) \<in> max_ext R \<Longrightarrow> (A \<union> C, B \<union> D) \<in> max_ext R"
  by (force elim!: max_ext.cases)

definition min_ext :: "('a \<times> 'a) set \<Rightarrow> ('a set \<times> 'a set) set"
  where "min_ext r = {(X, Y) | X Y. X \<noteq> {} \<and> (\<forall>y \<in> Y. (\<exists>x \<in> X. (x, y) \<in> r))}"

lemma min_ext_wf:
  assumes "wf r"
  shows "wf (min_ext r)"
proof (rule wfI_min)
  show "\<exists>m \<in> Q. (\<forall>n. (n, m) \<in> min_ext r \<longrightarrow> n \<notin> Q)" if nonempty: "x \<in> Q"
    for Q :: "'a set set" and x
  proof (cases "Q = {{}}")
    case True
    then show ?thesis by (simp add: min_ext_def)
  next
    case False
    with nonempty obtain e x where "x \<in> Q" "e \<in> x" by force
    then have eU: "e \<in> \<Union>Q" by auto
    with \<open>wf r\<close>
    obtain z where z: "z \<in> \<Union>Q" "\<And>y. (y, z) \<in> r \<Longrightarrow> y \<notin> \<Union>Q"
      by (erule wfE_min)
    from z obtain m where "m \<in> Q" "z \<in> m" by auto
    from \<open>m \<in> Q\<close> show ?thesis
    proof (intro rev_bexI allI impI)
      fix n
      assume smaller: "(n, m) \<in> min_ext r"
      with \<open>z \<in> m\<close> obtain y where "y \<in> n" "(y, z) \<in> r"
        by (auto simp: min_ext_def)
      with z(2) show "n \<notin> Q" by auto
    qed
  qed
qed


subsubsection \<open>Bounded increase must terminate\<close>

lemma wf_bounded_measure:
  fixes ub :: "'a \<Rightarrow> nat"
    and f :: "'a \<Rightarrow> nat"
  assumes "\<And>a b. (b, a) \<in> r \<Longrightarrow> ub b \<le> ub a \<and> ub a \<ge> f b \<and> f b > f a"
  shows "wf r"
  by (rule wf_subset[OF wf_measure[of "\<lambda>a. ub a - f a"]]) (auto dest: assms)

lemma wf_bounded_set:
  fixes ub :: "'a \<Rightarrow> 'b set"
    and f :: "'a \<Rightarrow> 'b set"
  assumes "\<And>a b. (b,a) \<in> r \<Longrightarrow> finite (ub a) \<and> ub b \<subseteq> ub a \<and> ub a \<supseteq> f b \<and> f b \<supset> f a"
  shows "wf r"
  apply (rule wf_bounded_measure[of r "\<lambda>a. card (ub a)" "\<lambda>a. card (f a)"])
  apply (drule assms)
  apply (blast intro: card_mono finite_subset psubset_card_mono dest: psubset_eq[THEN iffD2])
  done

lemma finite_subset_wf:
  assumes "finite A"
  shows "wf {(X, Y). X \<subset> Y \<and> Y \<subseteq> A}"
  by (rule wf_subset[OF wf_finite_psubset[unfolded finite_psubset_def]])
    (auto intro: finite_subset[OF _ assms])

hide_const (open) acc accp

end
