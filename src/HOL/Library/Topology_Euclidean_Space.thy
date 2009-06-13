(* Title:      Topology
   Author:     Amine Chaieb, University of Cambridge
   Author:     Robert Himmelmann, TU Muenchen
*)

header {* Elementary topology in Euclidean space. *}

theory Topology_Euclidean_Space
imports SEQ Euclidean_Space Product_Vector
begin

declare fstcart_pastecart[simp] sndcart_pastecart[simp]

subsection{* General notion of a topology *}

definition "istopology L \<longleftrightarrow> {} \<in> L \<and> (\<forall>S \<in>L. \<forall>T \<in>L. S \<inter> T \<in> L) \<and> (\<forall>K. K \<subseteq>L \<longrightarrow> \<Union> K \<in> L)"
typedef (open) 'a topology = "{L::('a set) set. istopology L}"
  morphisms "openin" "topology"
  unfolding istopology_def by blast

lemma istopology_open_in[intro]: "istopology(openin U)"
  using openin[of U] by blast

lemma topology_inverse': "istopology U \<Longrightarrow> openin (topology U) = U"
  using topology_inverse[unfolded mem_def Collect_def] .

lemma topology_inverse_iff: "istopology U \<longleftrightarrow> openin (topology U) = U"
  using topology_inverse[of U] istopology_open_in[of "topology U"] by auto

lemma topology_eq: "T1 = T2 \<longleftrightarrow> (\<forall>S. openin T1 S \<longleftrightarrow> openin T2 S)"
proof-
  {assume "T1=T2" hence "\<forall>S. openin T1 S \<longleftrightarrow> openin T2 S" by simp}
  moreover
  {assume H: "\<forall>S. openin T1 S \<longleftrightarrow> openin T2 S"
    hence "openin T1 = openin T2" by (metis mem_def set_ext)
    hence "topology (openin T1) = topology (openin T2)" by simp
    hence "T1 = T2" unfolding openin_inverse .}
  ultimately show ?thesis by blast
qed

text{* Infer the "universe" from union of all sets in the topology. *}

definition "topspace T =  \<Union>{S. openin T S}"

subsection{* Main properties of open sets *}

lemma openin_clauses:
  fixes U :: "'a topology"
  shows "openin U {}"
  "\<And>S T. openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S\<inter>T)"
  "\<And>K. (\<forall>S \<in> K. openin U S) \<Longrightarrow> openin U (\<Union>K)"
  using openin[of U] unfolding istopology_def Collect_def mem_def
  by (metis mem_def subset_eq)+

lemma openin_subset[intro]: "openin U S \<Longrightarrow> S \<subseteq> topspace U"
  unfolding topspace_def by blast
lemma openin_empty[simp]: "openin U {}" by (simp add: openin_clauses)

lemma openin_Int[intro]: "openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S \<inter> T)"
  by (simp add: openin_clauses)

lemma openin_Union[intro]: "(\<forall>S \<in>K. openin U S) \<Longrightarrow> openin U (\<Union> K)" by (simp add: openin_clauses)

lemma openin_Un[intro]: "openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S \<union> T)"
  using openin_Union[of "{S,T}" U] by auto

lemma openin_topspace[intro, simp]: "openin U (topspace U)" by (simp add: openin_Union topspace_def)

lemma openin_subopen: "openin U S \<longleftrightarrow> (\<forall>x \<in> S. \<exists>T. openin U T \<and> x \<in> T \<and> T \<subseteq> S)" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume ?lhs then have ?rhs by auto }
  moreover
  {assume H: ?rhs
    then obtain t where t: "\<forall>x\<in>S. openin U (t x) \<and> x \<in> t x \<and> t x \<subseteq> S"
      unfolding Ball_def ex_simps(6)[symmetric] choice_iff by blast
    from t have th0: "\<forall>x\<in> t`S. openin U x" by auto
    have "\<Union> t`S = S" using t by auto
    with openin_Union[OF th0] have "openin U S" by simp }
  ultimately show ?thesis by blast
qed

subsection{* Closed sets *}

definition "closedin U S \<longleftrightarrow> S \<subseteq> topspace U \<and> openin U (topspace U - S)"

lemma closedin_subset: "closedin U S \<Longrightarrow> S \<subseteq> topspace U" by (metis closedin_def)
lemma closedin_empty[simp]: "closedin U {}" by (simp add: closedin_def)
lemma closedin_topspace[intro,simp]:
  "closedin U (topspace U)" by (simp add: closedin_def)
lemma closedin_Un[intro]: "closedin U S \<Longrightarrow> closedin U T \<Longrightarrow> closedin U (S \<union> T)"
  by (auto simp add: Diff_Un closedin_def)

lemma Diff_Inter[intro]: "A - \<Inter>S = \<Union> {A - s|s. s\<in>S}" by auto
lemma closedin_Inter[intro]: assumes Ke: "K \<noteq> {}" and Kc: "\<forall>S \<in>K. closedin U S"
  shows "closedin U (\<Inter> K)"  using Ke Kc unfolding closedin_def Diff_Inter by auto

lemma closedin_Int[intro]: "closedin U S \<Longrightarrow> closedin U T \<Longrightarrow> closedin U (S \<inter> T)"
  using closedin_Inter[of "{S,T}" U] by auto

lemma Diff_Diff_Int: "A - (A - B) = A \<inter> B" by blast
lemma openin_closedin_eq: "openin U S \<longleftrightarrow> S \<subseteq> topspace U \<and> closedin U (topspace U - S)"
  apply (auto simp add: closedin_def)
  apply (metis openin_subset subset_eq)
  apply (auto simp add: Diff_Diff_Int)
  apply (subgoal_tac "topspace U \<inter> S = S")
  by auto

lemma openin_closedin:  "S \<subseteq> topspace U \<Longrightarrow> (openin U S \<longleftrightarrow> closedin U (topspace U - S))"
  by (simp add: openin_closedin_eq)

lemma openin_diff[intro]: assumes oS: "openin U S" and cT: "closedin U T" shows "openin U (S - T)"
proof-
  have "S - T = S \<inter> (topspace U - T)" using openin_subset[of U S]  oS cT
    by (auto simp add: topspace_def openin_subset)
  then show ?thesis using oS cT by (auto simp add: closedin_def)
qed

lemma closedin_diff[intro]: assumes oS: "closedin U S" and cT: "openin U T" shows "closedin U (S - T)"
proof-
  have "S - T = S \<inter> (topspace U - T)" using closedin_subset[of U S]  oS cT
    by (auto simp add: topspace_def )
  then show ?thesis using oS cT by (auto simp add: openin_closedin_eq)
qed

subsection{* Subspace topology. *}

definition "subtopology U V = topology {S \<inter> V |S. openin U S}"

lemma istopology_subtopology: "istopology {S \<inter> V |S. openin U S}" (is "istopology ?L")
proof-
  have "{} \<in> ?L" by blast
  {fix A B assume A: "A \<in> ?L" and B: "B \<in> ?L"
    from A B obtain Sa and Sb where Sa: "openin U Sa" "A = Sa \<inter> V" and Sb: "openin U Sb" "B = Sb \<inter> V" by blast
    have "A\<inter>B = (Sa \<inter> Sb) \<inter> V" "openin U (Sa \<inter> Sb)"  using Sa Sb by blast+
    then have "A \<inter> B \<in> ?L" by blast}
  moreover
  {fix K assume K: "K \<subseteq> ?L"
    have th0: "?L = (\<lambda>S. S \<inter> V) ` openin U "
      apply (rule set_ext)
      apply (simp add: Ball_def image_iff)
      by (metis mem_def)
    from K[unfolded th0 subset_image_iff]
    obtain Sk where Sk: "Sk \<subseteq> openin U" "K = (\<lambda>S. S \<inter> V) ` Sk" by blast
    have "\<Union>K = (\<Union>Sk) \<inter> V" using Sk by auto
    moreover have "openin U (\<Union> Sk)" using Sk by (auto simp add: subset_eq mem_def)
    ultimately have "\<Union>K \<in> ?L" by blast}
  ultimately show ?thesis unfolding istopology_def by blast
qed

lemma openin_subtopology:
  "openin (subtopology U V) S \<longleftrightarrow> (\<exists> T. (openin U T) \<and> (S = T \<inter> V))"
  unfolding subtopology_def topology_inverse'[OF istopology_subtopology]
  by (auto simp add: Collect_def)

lemma topspace_subtopology: "topspace(subtopology U V) = topspace U \<inter> V"
  by (auto simp add: topspace_def openin_subtopology)

lemma closedin_subtopology:
  "closedin (subtopology U V) S \<longleftrightarrow> (\<exists>T. closedin U T \<and> S = T \<inter> V)"
  unfolding closedin_def topspace_subtopology
  apply (simp add: openin_subtopology)
  apply (rule iffI)
  apply clarify
  apply (rule_tac x="topspace U - T" in exI)
  by auto

lemma openin_subtopology_refl: "openin (subtopology U V) V \<longleftrightarrow> V \<subseteq> topspace U"
  unfolding openin_subtopology
  apply (rule iffI, clarify)
  apply (frule openin_subset[of U])  apply blast
  apply (rule exI[where x="topspace U"])
  by auto

lemma subtopology_superset: assumes UV: "topspace U \<subseteq> V"
  shows "subtopology U V = U"
proof-
  {fix S
    {fix T assume T: "openin U T" "S = T \<inter> V"
      from T openin_subset[OF T(1)] UV have eq: "S = T" by blast
      have "openin U S" unfolding eq using T by blast}
    moreover
    {assume S: "openin U S"
      hence "\<exists>T. openin U T \<and> S = T \<inter> V"
	using openin_subset[OF S] UV by auto}
    ultimately have "(\<exists>T. openin U T \<and> S = T \<inter> V) \<longleftrightarrow> openin U S" by blast}
  then show ?thesis unfolding topology_eq openin_subtopology by blast
qed


lemma subtopology_topspace[simp]: "subtopology U (topspace U) = U"
  by (simp add: subtopology_superset)

lemma subtopology_UNIV[simp]: "subtopology U UNIV = U"
  by (simp add: subtopology_superset)

subsection{* The universal Euclidean versions are what we use most of the time *}

definition
  euclidean :: "'a::topological_space topology" where
  "euclidean = topology open"

lemma open_openin: "open S \<longleftrightarrow> openin euclidean S"
  unfolding euclidean_def
  apply (rule cong[where x=S and y=S])
  apply (rule topology_inverse[symmetric])
  apply (auto simp add: istopology_def)
  by (auto simp add: mem_def subset_eq)

lemma topspace_euclidean: "topspace euclidean = UNIV"
  apply (simp add: topspace_def)
  apply (rule set_ext)
  by (auto simp add: open_openin[symmetric])

lemma topspace_euclidean_subtopology[simp]: "topspace (subtopology euclidean S) = S"
  by (simp add: topspace_euclidean topspace_subtopology)

lemma closed_closedin: "closed S \<longleftrightarrow> closedin euclidean S"
  by (simp add: closed_def closedin_def topspace_euclidean open_openin Compl_eq_Diff_UNIV)

lemma open_subopen: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> S)"
  by (simp add: open_openin openin_subopen[symmetric])

subsection{* Open and closed balls. *}

definition
  ball :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set" where
  "ball x e = {y. dist x y < e}"

definition
  cball :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set" where
  "cball x e = {y. dist x y \<le> e}"

lemma mem_ball[simp]: "y \<in> ball x e \<longleftrightarrow> dist x y < e" by (simp add: ball_def)
lemma mem_cball[simp]: "y \<in> cball x e \<longleftrightarrow> dist x y \<le> e" by (simp add: cball_def)

lemma mem_ball_0 [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "x \<in> ball 0 e \<longleftrightarrow> norm x < e"
  by (simp add: dist_norm)

lemma mem_cball_0 [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "x \<in> cball 0 e \<longleftrightarrow> norm x \<le> e"
  by (simp add: dist_norm)

lemma centre_in_cball[simp]: "x \<in> cball x e \<longleftrightarrow> 0\<le> e"  by simp
lemma ball_subset_cball[simp,intro]: "ball x e \<subseteq> cball x e" by (simp add: subset_eq)
lemma subset_ball[intro]: "d <= e ==> ball x d \<subseteq> ball x e" by (simp add: subset_eq)
lemma subset_cball[intro]: "d <= e ==> cball x d \<subseteq> cball x e" by (simp add: subset_eq)
lemma ball_max_Un: "ball a (max r s) = ball a r \<union> ball a s"
  by (simp add: expand_set_eq) arith

lemma ball_min_Int: "ball a (min r s) = ball a r \<inter> ball a s"
  by (simp add: expand_set_eq)

subsection{* Topological properties of open balls *}

lemma diff_less_iff: "(a::real) - b > 0 \<longleftrightarrow> a > b"
  "(a::real) - b < 0 \<longleftrightarrow> a < b"
  "a - b < c \<longleftrightarrow> a < c +b" "a - b > c \<longleftrightarrow> a > c +b" by arith+
lemma diff_le_iff: "(a::real) - b \<ge> 0 \<longleftrightarrow> a \<ge> b" "(a::real) - b \<le> 0 \<longleftrightarrow> a \<le> b"
  "a - b \<le> c \<longleftrightarrow> a \<le> c +b" "a - b \<ge> c \<longleftrightarrow> a \<ge> c +b"  by arith+

lemma open_ball[intro, simp]: "open (ball x e)"
  unfolding open_dist ball_def Collect_def Ball_def mem_def
  unfolding dist_commute
  apply clarify
  apply (rule_tac x="e - dist xa x" in exI)
  using dist_triangle_alt[where z=x]
  apply (clarsimp simp add: diff_less_iff)
  apply atomize
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="xa" in allE)
  by arith

lemma centre_in_ball[simp]: "x \<in> ball x e \<longleftrightarrow> e > 0" by (metis mem_ball dist_self)
lemma open_contains_ball: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. ball x e \<subseteq> S)"
  unfolding open_dist subset_eq mem_ball Ball_def dist_commute ..

lemma open_contains_ball_eq: "open S \<Longrightarrow> \<forall>x. x\<in>S \<longleftrightarrow> (\<exists>e>0. ball x e \<subseteq> S)"
  by (metis open_contains_ball subset_eq centre_in_ball)

lemma ball_eq_empty[simp]: "ball x e = {} \<longleftrightarrow> e \<le> 0"
  unfolding mem_ball expand_set_eq
  apply (simp add: not_less)
  by (metis zero_le_dist order_trans dist_self)

lemma ball_empty[intro]: "e \<le> 0 ==> ball x e = {}" by simp

subsection{* Basic "localization" results are handy for connectedness. *}

lemma openin_open: "openin (subtopology euclidean U) S \<longleftrightarrow> (\<exists>T. open T \<and> (S = U \<inter> T))"
  by (auto simp add: openin_subtopology open_openin[symmetric])

lemma openin_open_Int[intro]: "open S \<Longrightarrow> openin (subtopology euclidean U) (U \<inter> S)"
  by (auto simp add: openin_open)

lemma open_openin_trans[trans]:
 "open S \<Longrightarrow> open T \<Longrightarrow> T \<subseteq> S \<Longrightarrow> openin (subtopology euclidean S) T"
  by (metis Int_absorb1  openin_open_Int)

lemma open_subset:  "S \<subseteq> T \<Longrightarrow> open S \<Longrightarrow> openin (subtopology euclidean T) S"
  by (auto simp add: openin_open)

lemma closedin_closed: "closedin (subtopology euclidean U) S \<longleftrightarrow> (\<exists>T. closed T \<and> S = U \<inter> T)"
  by (simp add: closedin_subtopology closed_closedin Int_ac)

lemma closedin_closed_Int: "closed S ==> closedin (subtopology euclidean U) (U \<inter> S)"
  by (metis closedin_closed)

lemma closed_closedin_trans: "closed S \<Longrightarrow> closed T \<Longrightarrow> T \<subseteq> S \<Longrightarrow> closedin (subtopology euclidean S) T"
  apply (subgoal_tac "S \<inter> T = T" )
  apply auto
  apply (frule closedin_closed_Int[of T S])
  by simp

lemma closed_subset: "S \<subseteq> T \<Longrightarrow> closed S \<Longrightarrow> closedin (subtopology euclidean T) S"
  by (auto simp add: closedin_closed)

lemma openin_euclidean_subtopology_iff:
  fixes S U :: "'a::metric_space set"
  shows "openin (subtopology euclidean U) S
  \<longleftrightarrow> S \<subseteq> U \<and> (\<forall>x\<in>S. \<exists>e>0. \<forall>x'\<in>U. dist x' x < e \<longrightarrow> x'\<in> S)" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume ?lhs hence ?rhs unfolding openin_subtopology open_openin[symmetric]
      by (simp add: open_dist) blast}
  moreover
  {assume SU: "S \<subseteq> U" and H: "\<And>x. x \<in> S \<Longrightarrow> \<exists>e>0. \<forall>x'\<in>U. dist x' x < e \<longrightarrow> x' \<in> S"
    from H obtain d where d: "\<And>x . x\<in> S \<Longrightarrow> d x > 0 \<and> (\<forall>x' \<in> U. dist x' x < d x \<longrightarrow> x' \<in> S)"
      by metis
    let ?T = "\<Union>{B. \<exists>x\<in>S. B = ball x (d x)}"
    have oT: "open ?T" by auto
    { fix x assume "x\<in>S"
      hence "x \<in> \<Union>{B. \<exists>x\<in>S. B = ball x (d x)}"
	apply simp apply(rule_tac x="ball x(d x)" in exI) apply auto
        by (rule d [THEN conjunct1])
      hence "x\<in> ?T \<inter> U" using SU and `x\<in>S` by auto  }
    moreover
    { fix y assume "y\<in>?T"
      then obtain B where "y\<in>B" "B\<in>{B. \<exists>x\<in>S. B = ball x (d x)}" by auto
      then obtain x where "x\<in>S" and x:"y \<in> ball x (d x)" by auto
      assume "y\<in>U"
      hence "y\<in>S" using d[OF `x\<in>S`] and x by(auto simp add: dist_commute) }
    ultimately have "S = ?T \<inter> U" by blast
    with oT have ?lhs unfolding openin_subtopology open_openin[symmetric] by blast}
  ultimately show ?thesis by blast
qed

text{* These "transitivity" results are handy too. *}

lemma openin_trans[trans]: "openin (subtopology euclidean T) S \<Longrightarrow> openin (subtopology euclidean U) T
  \<Longrightarrow> openin (subtopology euclidean U) S"
  unfolding open_openin openin_open by blast

lemma openin_open_trans: "openin (subtopology euclidean T) S \<Longrightarrow> open T \<Longrightarrow> open S"
  by (auto simp add: openin_open intro: openin_trans)

lemma closedin_trans[trans]:
 "closedin (subtopology euclidean T) S \<Longrightarrow>
           closedin (subtopology euclidean U) T
           ==> closedin (subtopology euclidean U) S"
  by (auto simp add: closedin_closed closed_closedin closed_Inter Int_assoc)

lemma closedin_closed_trans: "closedin (subtopology euclidean T) S \<Longrightarrow> closed T \<Longrightarrow> closed S"
  by (auto simp add: closedin_closed intro: closedin_trans)

subsection{* Connectedness *}

definition "connected S \<longleftrightarrow>
  ~(\<exists>e1 e2. open e1 \<and> open e2 \<and> S \<subseteq> (e1 \<union> e2) \<and> (e1 \<inter> e2 \<inter> S = {})
  \<and> ~(e1 \<inter> S = {}) \<and> ~(e2 \<inter> S = {}))"

lemma connected_local:
 "connected S \<longleftrightarrow> ~(\<exists>e1 e2.
                 openin (subtopology euclidean S) e1 \<and>
                 openin (subtopology euclidean S) e2 \<and>
                 S \<subseteq> e1 \<union> e2 \<and>
                 e1 \<inter> e2 = {} \<and>
                 ~(e1 = {}) \<and>
                 ~(e2 = {}))"
unfolding connected_def openin_open by (safe, blast+)

lemma exists_diff: "(\<exists>S. P(UNIV - S)) \<longleftrightarrow> (\<exists>S. P S)" (is "?lhs \<longleftrightarrow> ?rhs")
proof-

  {assume "?lhs" hence ?rhs by blast }
  moreover
  {fix S assume H: "P S"
    have "S = UNIV - (UNIV - S)" by auto
    with H have "P (UNIV - (UNIV - S))" by metis }
  ultimately show ?thesis by metis
qed

lemma connected_clopen: "connected S \<longleftrightarrow>
        (\<forall>T. openin (subtopology euclidean S) T \<and>
            closedin (subtopology euclidean S) T \<longrightarrow> T = {} \<or> T = S)" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  have " \<not> connected S \<longleftrightarrow> (\<exists>e1 e2. open e1 \<and> open (UNIV - e2) \<and> S \<subseteq> e1 \<union> (UNIV - e2) \<and> e1 \<inter> (UNIV - e2) \<inter> S = {} \<and> e1 \<inter> S \<noteq> {} \<and> (UNIV - e2) \<inter> S \<noteq> {})"
    unfolding connected_def openin_open closedin_closed
    apply (subst exists_diff) by blast
  hence th0: "connected S \<longleftrightarrow> \<not> (\<exists>e2 e1. closed e2 \<and> open e1 \<and> S \<subseteq> e1 \<union> (UNIV - e2) \<and> e1 \<inter> (UNIV - e2) \<inter> S = {} \<and> e1 \<inter> S \<noteq> {} \<and> (UNIV - e2) \<inter> S \<noteq> {})"
    (is " _ \<longleftrightarrow> \<not> (\<exists>e2 e1. ?P e2 e1)") apply (simp add: closed_def Compl_eq_Diff_UNIV) by metis

  have th1: "?rhs \<longleftrightarrow> \<not> (\<exists>t' t. closed t'\<and>t = S\<inter>t' \<and> t\<noteq>{} \<and> t\<noteq>S \<and> (\<exists>t'. open t' \<and> t = S \<inter> t'))"
    (is "_ \<longleftrightarrow> \<not> (\<exists>t' t. ?Q t' t)")
    unfolding connected_def openin_open closedin_closed by auto
  {fix e2
    {fix e1 have "?P e2 e1 \<longleftrightarrow> (\<exists>t.  closed e2 \<and> t = S\<inter>e2 \<and> open e1 \<and> t = S\<inter>e1 \<and> t\<noteq>{} \<and> t\<noteq>S)"
	by auto}
    then have "(\<exists>e1. ?P e2 e1) \<longleftrightarrow> (\<exists>t. ?Q e2 t)" by metis}
  then have "\<forall>e2. (\<exists>e1. ?P e2 e1) \<longleftrightarrow> (\<exists>t. ?Q e2 t)" by blast
  then show ?thesis unfolding th0 th1 by simp
qed

lemma connected_empty[simp, intro]: "connected {}"
  by (simp add: connected_def)

subsection{* Hausdorff and other separation properties *}

class t0_space =
  assumes t0_space: "x \<noteq> y \<Longrightarrow> \<exists>U. open U \<and> \<not> (x \<in> U \<longleftrightarrow> y \<in> U)"

class t1_space =
  assumes t1_space: "x \<noteq> y \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<notin> U \<and> x \<notin> V \<and> y \<in> V"
begin

subclass t0_space
proof
qed (fast dest: t1_space)

end

text {* T2 spaces are also known as Hausdorff spaces. *}

class t2_space =
  assumes hausdorff: "x \<noteq> y \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
begin

subclass t1_space
proof
qed (fast dest: hausdorff)

end

instance metric_space \<subseteq> t2_space
proof
  fix x y :: "'a::metric_space"
  assume xy: "x \<noteq> y"
  let ?U = "ball x (dist x y / 2)"
  let ?V = "ball y (dist x y / 2)"
  have th0: "\<And>d x y z. (d x z :: real) <= d x y + d y z \<Longrightarrow> d y z = d z y
               ==> ~(d x y * 2 < d x z \<and> d z y * 2 < d x z)" by arith
  have "open ?U \<and> open ?V \<and> x \<in> ?U \<and> y \<in> ?V \<and> ?U \<inter> ?V = {}"
    using dist_pos_lt[OF xy] th0[of dist,OF dist_triangle dist_commute]
    by (auto simp add: expand_set_eq)
  then show "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by blast
qed

lemma separation_t2:
  fixes x y :: "'a::t2_space"
  shows "x \<noteq> y \<longleftrightarrow> (\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {})"
  using hausdorff[of x y] by blast

lemma separation_t1:
  fixes x y :: "'a::t1_space"
  shows "x \<noteq> y \<longleftrightarrow> (\<exists>U V. open U \<and> open V \<and> x \<in>U \<and> y\<notin> U \<and> x\<notin>V \<and> y\<in>V)"
  using t1_space[of x y] by blast

lemma separation_t0:
  fixes x y :: "'a::t0_space"
  shows "x \<noteq> y \<longleftrightarrow> (\<exists>U. open U \<and> ~(x\<in>U \<longleftrightarrow> y\<in>U))"
  using t0_space[of x y] by blast

subsection{* Limit points *}

definition
  islimpt:: "'a::topological_space \<Rightarrow> 'a set \<Rightarrow> bool"
    (infixr "islimpt" 60) where
  "x islimpt S \<longleftrightarrow> (\<forall>T. x\<in>T \<longrightarrow> open T \<longrightarrow> (\<exists>y\<in>S. y\<in>T \<and> y\<noteq>x))"

lemma islimptI:
  assumes "\<And>T. x \<in> T \<Longrightarrow> open T \<Longrightarrow> \<exists>y\<in>S. y \<in> T \<and> y \<noteq> x"
  shows "x islimpt S"
  using assms unfolding islimpt_def by auto

lemma islimptE:
  assumes "x islimpt S" and "x \<in> T" and "open T"
  obtains y where "y \<in> S" and "y \<in> T" and "y \<noteq> x"
  using assms unfolding islimpt_def by auto

lemma islimpt_subset: "x islimpt S \<Longrightarrow> S \<subseteq> T ==> x islimpt T" by (auto simp add: islimpt_def)

lemma islimpt_approachable:
  fixes x :: "'a::metric_space"
  shows "x islimpt S \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e)"
  unfolding islimpt_def
  apply auto
  apply(erule_tac x="ball x e" in allE)
  apply auto
  apply(rule_tac x=y in bexI)
  apply (auto simp add: dist_commute)
  apply (simp add: open_dist, drule (1) bspec)
  apply (clarify, drule spec, drule (1) mp, auto)
  done

lemma islimpt_approachable_le:
  fixes x :: "'a::metric_space"
  shows "x islimpt S \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in> S. x' \<noteq> x \<and> dist x' x <= e)"
  unfolding islimpt_approachable
  using approachable_lt_le[where f="\<lambda>x'. dist x' x" and P="\<lambda>x'. \<not> (x'\<in>S \<and> x'\<noteq>x)"]
  by metis (* FIXME: VERY slow! *)

class perfect_space =
  (* FIXME: perfect_space should inherit from topological_space *)
  assumes islimpt_UNIV [simp, intro]: "(x::'a::metric_space) islimpt UNIV"

lemma perfect_choose_dist:
  fixes x :: "'a::perfect_space"
  shows "0 < r \<Longrightarrow> \<exists>a. a \<noteq> x \<and> dist a x < r"
using islimpt_UNIV [of x]
by (simp add: islimpt_approachable)

instance real :: perfect_space
apply default
apply (rule islimpt_approachable [THEN iffD2])
apply (clarify, rule_tac x="x + e/2" in bexI)
apply (auto simp add: dist_norm)
done

instance "^" :: (perfect_space, finite) perfect_space
proof
  fix x :: "'a ^ 'b"
  {
    fix e :: real assume "0 < e"
    def a \<equiv> "x $ arbitrary"
    have "a islimpt UNIV" by (rule islimpt_UNIV)
    with `0 < e` obtain b where "b \<noteq> a" and "dist b a < e"
      unfolding islimpt_approachable by auto
    def y \<equiv> "Cart_lambda ((Cart_nth x)(arbitrary := b))"
    from `b \<noteq> a` have "y \<noteq> x"
      unfolding a_def y_def by (simp add: Cart_eq)
    from `dist b a < e` have "dist y x < e"
      unfolding dist_vector_def a_def y_def
      apply simp
      apply (rule le_less_trans [OF setL2_le_setsum [OF zero_le_dist]])
      apply (subst setsum_diff1' [where a=arbitrary], simp, simp, simp)
      done
    from `y \<noteq> x` and `dist y x < e`
    have "\<exists>y\<in>UNIV. y \<noteq> x \<and> dist y x < e" by auto
  }
  then show "x islimpt UNIV" unfolding islimpt_approachable by blast
qed

lemma closed_limpt: "closed S \<longleftrightarrow> (\<forall>x. x islimpt S \<longrightarrow> x \<in> S)"
  unfolding closed_def
  apply (subst open_subopen)
  apply (simp add: islimpt_def subset_eq Compl_eq_Diff_UNIV)
  by (metis DiffE DiffI UNIV_I insertCI insert_absorb mem_def)

lemma islimpt_EMPTY[simp]: "\<not> x islimpt {}"
  unfolding islimpt_def by auto

lemma closed_positive_orthant: "closed {x::real^'n::finite. \<forall>i. 0 \<le>x$i}"
proof-
  let ?U = "UNIV :: 'n set"
  let ?O = "{x::real^'n. \<forall>i. x$i\<ge>0}"
  {fix x:: "real^'n" and i::'n assume H: "\<forall>e>0. \<exists>x'\<in>?O. x' \<noteq> x \<and> dist x' x < e"
    and xi: "x$i < 0"
    from xi have th0: "-x$i > 0" by arith
    from H[rule_format, OF th0] obtain x' where x': "x' \<in>?O" "x' \<noteq> x" "dist x' x < -x $ i" by blast
      have th:" \<And>b a (x::real). abs x <= b \<Longrightarrow> b <= a ==> ~(a + x < 0)" by arith
      have th': "\<And>x (y::real). x < 0 \<Longrightarrow> 0 <= y ==> abs x <= abs (y - x)" by arith
      have th1: "\<bar>x$i\<bar> \<le> \<bar>(x' - x)$i\<bar>" using x'(1) xi
	apply (simp only: vector_component)
	by (rule th') auto
      have th2: "\<bar>dist x x'\<bar> \<ge> \<bar>(x' - x)$i\<bar>" using  component_le_norm[of "x'-x" i]
	apply (simp add: dist_norm) by norm
      from th[OF th1 th2] x'(3) have False by (simp add: dist_commute) }
  then show ?thesis unfolding closed_limpt islimpt_approachable
    unfolding not_le[symmetric] by blast
qed

lemma finite_set_avoid:
  fixes a :: "'a::metric_space"
  assumes fS: "finite S" shows  "\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<longrightarrow> d <= dist a x"
proof(induct rule: finite_induct[OF fS])
  case 1 thus ?case apply auto by ferrack
next
  case (2 x F)
  from 2 obtain d where d: "d >0" "\<forall>x\<in>F. x\<noteq>a \<longrightarrow> d \<le> dist a x" by blast
  {assume "x = a" hence ?case using d by auto  }
  moreover
  {assume xa: "x\<noteq>a"
    let ?d = "min d (dist a x)"
    have dp: "?d > 0" using xa d(1) using dist_nz by auto
    from d have d': "\<forall>x\<in>F. x\<noteq>a \<longrightarrow> ?d \<le> dist a x" by auto
    with dp xa have ?case by(auto intro!: exI[where x="?d"]) }
  ultimately show ?case by blast
qed

lemma islimpt_finite:
  fixes S :: "'a::metric_space set"
  assumes fS: "finite S" shows "\<not> a islimpt S"
  unfolding islimpt_approachable
  using finite_set_avoid[OF fS, of a] by (metis dist_commute  not_le)

lemma islimpt_Un: "x islimpt (S \<union> T) \<longleftrightarrow> x islimpt S \<or> x islimpt T"
  apply (rule iffI)
  defer
  apply (metis Un_upper1 Un_upper2 islimpt_subset)
  unfolding islimpt_def
  apply (rule ccontr, clarsimp, rename_tac A B)
  apply (drule_tac x="A \<inter> B" in spec)
  apply (auto simp add: open_Int)
  done

lemma discrete_imp_closed:
  fixes S :: "'a::metric_space set"
  assumes e: "0 < e" and d: "\<forall>x \<in> S. \<forall>y \<in> S. dist y x < e \<longrightarrow> y = x"
  shows "closed S"
proof-
  {fix x assume C: "\<forall>e>0. \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e"
    from e have e2: "e/2 > 0" by arith
    from C[rule_format, OF e2] obtain y where y: "y \<in> S" "y\<noteq>x" "dist y x < e/2" by blast
    let ?m = "min (e/2) (dist x y) "
    from e2 y(2) have mp: "?m > 0" by (simp add: dist_nz[THEN sym])
    from C[rule_format, OF mp] obtain z where z: "z \<in> S" "z\<noteq>x" "dist z x < ?m" by blast
    have th: "dist z y < e" using z y
      by (intro dist_triangle_lt [where z=x], simp)
    from d[rule_format, OF y(1) z(1) th] y z
    have False by (auto simp add: dist_commute)}
  then show ?thesis by (metis islimpt_approachable closed_limpt [where 'a='a])
qed

subsection{* Interior of a Set *}
definition "interior S = {x. \<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> S}"

lemma interior_eq: "interior S = S \<longleftrightarrow> open S"
  apply (simp add: expand_set_eq interior_def)
  apply (subst (2) open_subopen) by (safe, blast+)

lemma interior_open: "open S ==> (interior S = S)" by (metis interior_eq)

lemma interior_empty[simp]: "interior {} = {}" by (simp add: interior_def)

lemma open_interior[simp, intro]: "open(interior S)"
  apply (simp add: interior_def)
  apply (subst open_subopen) by blast

lemma interior_interior[simp]: "interior(interior S) = interior S" by (metis interior_eq open_interior)
lemma interior_subset: "interior S \<subseteq> S" by (auto simp add: interior_def)
lemma subset_interior: "S \<subseteq> T ==> (interior S) \<subseteq> (interior T)" by (auto simp add: interior_def)
lemma interior_maximal: "T \<subseteq> S \<Longrightarrow> open T ==> T \<subseteq> (interior S)" by (auto simp add: interior_def)
lemma interior_unique: "T \<subseteq> S \<Longrightarrow> open T  \<Longrightarrow> (\<forall>T'. T' \<subseteq> S \<and> open T' \<longrightarrow> T' \<subseteq> T) \<Longrightarrow> interior S = T"
  by (metis equalityI interior_maximal interior_subset open_interior)
lemma mem_interior: "x \<in> interior S \<longleftrightarrow> (\<exists>e. 0 < e \<and> ball x e \<subseteq> S)"
  apply (simp add: interior_def)
  by (metis open_contains_ball centre_in_ball open_ball subset_trans)

lemma open_subset_interior: "open S ==> S \<subseteq> interior T \<longleftrightarrow> S \<subseteq> T"
  by (metis interior_maximal interior_subset subset_trans)

lemma interior_inter[simp]: "interior(S \<inter> T) = interior S \<inter> interior T"
  apply (rule equalityI, simp)
  apply (metis Int_lower1 Int_lower2 subset_interior)
  by (metis Int_mono interior_subset open_Int open_interior open_subset_interior)

lemma interior_limit_point [intro]:
  fixes x :: "'a::perfect_space"
  assumes x: "x \<in> interior S" shows "x islimpt S"
proof-
  from x obtain e where e: "e>0" "\<forall>x'. dist x x' < e \<longrightarrow> x' \<in> S"
    unfolding mem_interior subset_eq Ball_def mem_ball by blast
  {
    fix d::real assume d: "d>0"
    let ?m = "min d e"
    have mde2: "0 < ?m" using e(1) d(1) by simp
    from perfect_choose_dist [OF mde2, of x]
    obtain y where "y \<noteq> x" and "dist y x < ?m" by blast
    then have "dist y x < e" "dist y x < d" by simp_all
    from `dist y x < e` e(2) have "y \<in> S" by (simp add: dist_commute)
    have "\<exists>x'\<in>S. x'\<noteq> x \<and> dist x' x < d"
      using `y \<in> S` `y \<noteq> x` `dist y x < d` by fast
  }
  then show ?thesis unfolding islimpt_approachable by blast
qed

lemma interior_closed_Un_empty_interior:
  assumes cS: "closed S" and iT: "interior T = {}"
  shows "interior(S \<union> T) = interior S"
proof
  show "interior S \<subseteq> interior (S\<union>T)"
    by (rule subset_interior, blast)
next
  show "interior (S \<union> T) \<subseteq> interior S"
  proof
    fix x assume "x \<in> interior (S \<union> T)"
    then obtain R where "open R" "x \<in> R" "R \<subseteq> S \<union> T"
      unfolding interior_def by fast
    show "x \<in> interior S"
    proof (rule ccontr)
      assume "x \<notin> interior S"
      with `x \<in> R` `open R` obtain y where "y \<in> R - S"
        unfolding interior_def expand_set_eq by fast
      from `open R` `closed S` have "open (R - S)" by (rule open_Diff)
      from `R \<subseteq> S \<union> T` have "R - S \<subseteq> T" by fast
      from `y \<in> R - S` `open (R - S)` `R - S \<subseteq> T` `interior T = {}`
      show "False" unfolding interior_def by fast
    qed
  qed
qed


subsection{* Closure of a Set *}

definition "closure S = S \<union> {x | x. x islimpt S}"

lemma closure_interior: "closure S = UNIV - interior (UNIV - S)"
proof-
  { fix x
    have "x\<in>UNIV - interior (UNIV - S) \<longleftrightarrow> x \<in> closure S"  (is "?lhs = ?rhs")
    proof
      let ?exT = "\<lambda> y. (\<exists>T. open T \<and> y \<in> T \<and> T \<subseteq> UNIV - S)"
      assume "?lhs"
      hence *:"\<not> ?exT x"
	unfolding interior_def
	by simp
      { assume "\<not> ?rhs"
	hence False using *
	  unfolding closure_def islimpt_def
	  by blast
      }
      thus "?rhs"
	by blast
    next
      assume "?rhs" thus "?lhs"
	unfolding closure_def interior_def islimpt_def
	by blast
    qed
  }
  thus ?thesis
    by blast
qed

lemma interior_closure: "interior S = UNIV - (closure (UNIV - S))"
proof-
  { fix x
    have "x \<in> interior S \<longleftrightarrow> x \<in> UNIV - (closure (UNIV - S))"
      unfolding interior_def closure_def islimpt_def
      by blast (* FIXME: VERY slow! *)
  }
  thus ?thesis
    by blast
qed

lemma closed_closure[simp, intro]: "closed (closure S)"
proof-
  have "closed (UNIV - interior (UNIV -S))" by blast
  thus ?thesis using closure_interior[of S] by simp
qed

lemma closure_hull: "closure S = closed hull S"
proof-
  have "S \<subseteq> closure S"
    unfolding closure_def
    by blast
  moreover
  have "closed (closure S)"
    using closed_closure[of S]
    by assumption
  moreover
  { fix t
    assume *:"S \<subseteq> t" "closed t"
    { fix x
      assume "x islimpt S"
      hence "x islimpt t" using *(1)
	using islimpt_subset[of x, of S, of t]
	by blast
    }
    with * have "closure S \<subseteq> t"
      unfolding closure_def
      using closed_limpt[of t]
      by auto
  }
  ultimately show ?thesis
    using hull_unique[of S, of "closure S", of closed]
    unfolding mem_def
    by simp
qed

lemma closure_eq: "closure S = S \<longleftrightarrow> closed S"
  unfolding closure_hull
  using hull_eq[of closed, unfolded mem_def, OF  closed_Inter, of S]
  by (metis mem_def subset_eq)

lemma closure_closed[simp]: "closed S \<Longrightarrow> closure S = S"
  using closure_eq[of S]
  by simp

lemma closure_closure[simp]: "closure (closure S) = closure S"
  unfolding closure_hull
  using hull_hull[of closed S]
  by assumption

lemma closure_subset: "S \<subseteq> closure S"
  unfolding closure_hull
  using hull_subset[of S closed]
  by assumption

lemma subset_closure: "S \<subseteq> T \<Longrightarrow> closure S \<subseteq> closure T"
  unfolding closure_hull
  using hull_mono[of S T closed]
  by assumption

lemma closure_minimal: "S \<subseteq> T \<Longrightarrow>  closed T \<Longrightarrow> closure S \<subseteq> T"
  using hull_minimal[of S T closed]
  unfolding closure_hull mem_def
  by simp

lemma closure_unique: "S \<subseteq> T \<and> closed T \<and> (\<forall> T'. S \<subseteq> T' \<and> closed T' \<longrightarrow> T \<subseteq> T') \<Longrightarrow> closure S = T"
  using hull_unique[of S T closed]
  unfolding closure_hull mem_def
  by simp

lemma closure_empty[simp]: "closure {} = {}"
  using closed_empty closure_closed[of "{}"]
  by simp

lemma closure_univ[simp]: "closure UNIV = UNIV"
  using closure_closed[of UNIV]
  by simp

lemma closure_eq_empty: "closure S = {} \<longleftrightarrow> S = {}"
  using closure_empty closure_subset[of S]
  by blast

lemma closure_subset_eq: "closure S \<subseteq> S \<longleftrightarrow> closed S"
  using closure_eq[of S] closure_subset[of S]
  by simp

lemma open_inter_closure_eq_empty:
  "open S \<Longrightarrow> (S \<inter> closure T) = {} \<longleftrightarrow> S \<inter> T = {}"
  using open_subset_interior[of S "UNIV - T"]
  using interior_subset[of "UNIV - T"]
  unfolding closure_interior
  by auto

lemma open_inter_closure_subset:
  "open S \<Longrightarrow> (S \<inter> (closure T)) \<subseteq> closure(S \<inter> T)"
proof
  fix x
  assume as: "open S" "x \<in> S \<inter> closure T"
  { assume *:"x islimpt T"
    have "x islimpt (S \<inter> T)"
    proof (rule islimptI)
      fix A
      assume "x \<in> A" "open A"
      with as have "x \<in> A \<inter> S" "open (A \<inter> S)"
        by (simp_all add: open_Int)
      with * obtain y where "y \<in> T" "y \<in> A \<inter> S" "y \<noteq> x"
        by (rule islimptE)
      hence "y \<in> S \<inter> T" "y \<in> A \<and> y \<noteq> x"
        by simp_all
      thus "\<exists>y\<in>(S \<inter> T). y \<in> A \<and> y \<noteq> x" ..
    qed
  }
  then show "x \<in> closure (S \<inter> T)" using as
    unfolding closure_def
    by blast
qed

lemma closure_complement: "closure(UNIV - S) = UNIV - interior(S)"
proof-
  have "S = UNIV - (UNIV - S)"
    by auto
  thus ?thesis
    unfolding closure_interior
    by auto
qed

lemma interior_complement: "interior(UNIV - S) = UNIV - closure(S)"
  unfolding closure_interior
  by blast

subsection{* Frontier (aka boundary) *}

definition "frontier S = closure S - interior S"

lemma frontier_closed: "closed(frontier S)"
  by (simp add: frontier_def closed_Diff)

lemma frontier_closures: "frontier S = (closure S) \<inter> (closure(UNIV - S))"
  by (auto simp add: frontier_def interior_closure)

lemma frontier_straddle:
  fixes a :: "'a::metric_space"
  shows "a \<in> frontier S \<longleftrightarrow> (\<forall>e>0. (\<exists>x\<in>S. dist a x < e) \<and> (\<exists>x. x \<notin> S \<and> dist a x < e))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  { fix e::real
    assume "e > 0"
    let ?rhse = "(\<exists>x\<in>S. dist a x < e) \<and> (\<exists>x. x \<notin> S \<and> dist a x < e)"
    { assume "a\<in>S"
      have "\<exists>x\<in>S. dist a x < e" using `e>0` `a\<in>S` by(rule_tac x=a in bexI) auto
      moreover have "\<exists>x. x \<notin> S \<and> dist a x < e" using `?lhs` `a\<in>S`
	unfolding frontier_closures closure_def islimpt_def using `e>0`
	by (auto, erule_tac x="ball a e" in allE, auto)
      ultimately have ?rhse by auto
    }
    moreover
    { assume "a\<notin>S"
      hence ?rhse using `?lhs`
	unfolding frontier_closures closure_def islimpt_def
	using open_ball[of a e] `e > 0`
	by (auto, erule_tac x = "ball a e" in allE, auto) (* FIXME: VERY slow! *)
    }
    ultimately have ?rhse by auto
  }
  thus ?rhs by auto
next
  assume ?rhs
  moreover
  { fix T assume "a\<notin>S" and
    as:"\<forall>e>0. (\<exists>x\<in>S. dist a x < e) \<and> (\<exists>x. x \<notin> S \<and> dist a x < e)" "a \<notin> S" "a \<in> T" "open T"
    from `open T` `a \<in> T` have "\<exists>e>0. ball a e \<subseteq> T" unfolding open_contains_ball[of T] by auto
    then obtain e where "e>0" "ball a e \<subseteq> T" by auto
    then obtain y where y:"y\<in>S" "dist a y < e"  using as(1) by auto
    have "\<exists>y\<in>S. y \<in> T \<and> y \<noteq> a"
      using `dist a y < e` `ball a e \<subseteq> T` unfolding ball_def using `y\<in>S` `a\<notin>S` by auto
  }
  hence "a \<in> closure S" unfolding closure_def islimpt_def using `?rhs` by auto
  moreover
  { fix T assume "a \<in> T"  "open T" "a\<in>S"
    then obtain e where "e>0" and balle: "ball a e \<subseteq> T" unfolding open_contains_ball using `?rhs` by auto
    obtain x where "x \<notin> S" "dist a x < e" using `?rhs` using `e>0` by auto
    hence "\<exists>y\<in>UNIV - S. y \<in> T \<and> y \<noteq> a" using balle `a\<in>S` unfolding ball_def by (rule_tac x=x in bexI)auto
  }
  hence "a islimpt (UNIV - S) \<or> a\<notin>S" unfolding islimpt_def by auto
  ultimately show ?lhs unfolding frontier_closures using closure_def[of "UNIV - S"] by auto
qed

lemma frontier_subset_closed: "closed S \<Longrightarrow> frontier S \<subseteq> S"
  by (metis frontier_def closure_closed Diff_subset)

lemma frontier_empty: "frontier {} = {}"
  by (simp add: frontier_def closure_empty)

lemma frontier_subset_eq: "frontier S \<subseteq> S \<longleftrightarrow> closed S"
proof-
  { assume "frontier S \<subseteq> S"
    hence "closure S \<subseteq> S" using interior_subset unfolding frontier_def by auto
    hence "closed S" using closure_subset_eq by auto
  }
  thus ?thesis using frontier_subset_closed[of S] by auto
qed

lemma frontier_complement: "frontier(UNIV - S) = frontier S"
  by (auto simp add: frontier_def closure_complement interior_complement)

lemma frontier_disjoint_eq: "frontier S \<inter> S = {} \<longleftrightarrow> open S"
  using frontier_complement frontier_subset_eq[of "UNIV - S"]
  unfolding open_closed Compl_eq_Diff_UNIV by auto

subsection{* Common nets and The "within" modifier for nets. *}

definition
  at_infinity :: "'a::real_normed_vector net" where
  "at_infinity = Abs_net (range (\<lambda>r. {x. r \<le> norm x}))"

definition
  indirection :: "'a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> 'a net" (infixr "indirection" 70) where
  "a indirection v = (at a) within {b. \<exists>c\<ge>0. b - a = scaleR c v}"

text{* Prove That They are all nets. *}

lemma Rep_net_at_infinity:
  "Rep_net at_infinity = range (\<lambda>r. {x. r \<le> norm x})"
unfolding at_infinity_def
apply (rule Abs_net_inverse')
apply (rule image_nonempty, simp)
apply (clarsimp, rename_tac r s)
apply (rule_tac x="max r s" in exI, auto)
done

lemma within_UNIV: "net within UNIV = net"
  by (simp add: Rep_net_inject [symmetric] Rep_net_within)

subsection{* Identify Trivial limits, where we can't approach arbitrarily closely. *}

definition
  trivial_limit :: "'a net \<Rightarrow> bool" where
  "trivial_limit net \<longleftrightarrow> {} \<in> Rep_net net"

lemma trivial_limit_within:
  shows "trivial_limit (at a within S) \<longleftrightarrow> \<not> a islimpt S"
proof
  assume "trivial_limit (at a within S)"
  thus "\<not> a islimpt S"
    unfolding trivial_limit_def
    unfolding Rep_net_within Rep_net_at
    unfolding islimpt_def
    apply (clarsimp simp add: expand_set_eq)
    apply (rename_tac T, rule_tac x=T in exI)
    apply (clarsimp, drule_tac x=y in spec, simp)
    done
next
  assume "\<not> a islimpt S"
  thus "trivial_limit (at a within S)"
    unfolding trivial_limit_def
    unfolding Rep_net_within Rep_net_at
    unfolding islimpt_def
    apply (clarsimp simp add: image_image)
    apply (rule_tac x=T in image_eqI)
    apply (auto simp add: expand_set_eq)
    done
qed

lemma trivial_limit_at_iff: "trivial_limit (at a) \<longleftrightarrow> \<not> a islimpt UNIV"
  using trivial_limit_within [of a UNIV]
  by (simp add: within_UNIV)

lemma trivial_limit_at:
  fixes a :: "'a::perfect_space"
  shows "\<not> trivial_limit (at a)"
  by (simp add: trivial_limit_at_iff)

lemma trivial_limit_at_infinity:
  "\<not> trivial_limit (at_infinity :: ('a::{real_normed_vector,zero_neq_one}) net)"
  (* FIXME: find a more appropriate type class *)
  unfolding trivial_limit_def Rep_net_at_infinity
  apply (clarsimp simp add: expand_set_eq)
  apply (drule_tac x="scaleR r (sgn 1)" in spec)
  apply (simp add: norm_sgn)
  done

lemma trivial_limit_sequentially: "\<not> trivial_limit sequentially"
  by (auto simp add: trivial_limit_def Rep_net_sequentially)

subsection{* Some property holds "sufficiently close" to the limit point. *}

lemma eventually_at: (* FIXME: this replaces Limits.eventually_at *)
  "eventually P (at a) \<longleftrightarrow> (\<exists>d>0. \<forall>x. 0 < dist x a \<and> dist x a < d \<longrightarrow> P x)"
unfolding eventually_at dist_nz by auto

lemma eventually_at_infinity:
  "eventually P at_infinity \<longleftrightarrow> (\<exists>b. \<forall>x. norm x >= b \<longrightarrow> P x)"
unfolding eventually_def Rep_net_at_infinity by auto

lemma eventually_within: "eventually P (at a within S) \<longleftrightarrow>
        (\<exists>d>0. \<forall>x\<in>S. 0 < dist x a \<and> dist x a < d \<longrightarrow> P x)"
unfolding eventually_within eventually_at dist_nz by auto

lemma eventually_within_le: "eventually P (at a within S) \<longleftrightarrow>
        (\<exists>d>0. \<forall>x\<in>S. 0 < dist x a \<and> dist x a <= d \<longrightarrow> P x)" (is "?lhs = ?rhs")
unfolding eventually_within
apply safe
apply (rule_tac x="d/2" in exI, simp)
apply (rule_tac x="d" in exI, simp)
done

lemma eventually_happens: "eventually P net ==> trivial_limit net \<or> (\<exists>x. P x)"
  unfolding eventually_def trivial_limit_def
  using Rep_net_nonempty [of net] by auto

lemma always_eventually: "(\<forall>x. P x) ==> eventually P net"
  unfolding eventually_def trivial_limit_def
  using Rep_net_nonempty [of net] by auto

lemma trivial_limit_eventually: "trivial_limit net \<Longrightarrow> eventually P net"
  unfolding trivial_limit_def eventually_def by auto

lemma eventually_False: "eventually (\<lambda>x. False) net \<longleftrightarrow> trivial_limit net"
  unfolding trivial_limit_def eventually_def by auto

lemma trivial_limit_eq: "trivial_limit net \<longleftrightarrow> (\<forall>P. eventually P net)"
  apply (safe elim!: trivial_limit_eventually)
  apply (simp add: eventually_False [symmetric])
  done

text{* Combining theorems for "eventually" *}

lemma eventually_conjI:
  "\<lbrakk>eventually (\<lambda>x. P x) net; eventually (\<lambda>x. Q x) net\<rbrakk>
    \<Longrightarrow> eventually (\<lambda>x. P x \<and> Q x) net"
by (rule eventually_conj)

lemma eventually_rev_mono:
  "eventually P net \<Longrightarrow> (\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow> eventually Q net"
using eventually_mono [of P Q] by fast

lemma eventually_and: " eventually (\<lambda>x. P x \<and> Q x) net \<longleftrightarrow> eventually P net \<and> eventually Q net"
  by (auto intro!: eventually_conjI elim: eventually_rev_mono)

lemma eventually_false: "eventually (\<lambda>x. False) net \<longleftrightarrow> trivial_limit net"
  by (auto simp add: eventually_False)

lemma not_eventually: "(\<forall>x. \<not> P x ) \<Longrightarrow> ~(trivial_limit net) ==> ~(eventually (\<lambda>x. P x) net)"
  by (simp add: eventually_False)

subsection{* Limits, defined as vacuously true when the limit is trivial. *}

  text{* Notation Lim to avoid collition with lim defined in analysis *}
definition
  Lim :: "'a net \<Rightarrow> ('a \<Rightarrow> 'b::metric_space) \<Rightarrow> 'b" where
  "Lim net f = (THE l. (f ---> l) net)"

lemma Lim:
 "(f ---> l) net \<longleftrightarrow>
        trivial_limit net \<or>
        (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) net)"
  unfolding tendsto_iff trivial_limit_eq by auto


text{* Show that they yield usual definitions in the various cases. *}

lemma Lim_within_le: "(f ---> l)(at a within S) \<longleftrightarrow>
           (\<forall>e>0. \<exists>d>0. \<forall>x\<in>S. 0 < dist x a  \<and> dist x a  <= d \<longrightarrow> dist (f x) l < e)"
  by (auto simp add: tendsto_iff eventually_within_le)

lemma Lim_within: "(f ---> l) (at a within S) \<longleftrightarrow>
        (\<forall>e >0. \<exists>d>0. \<forall>x \<in> S. 0 < dist x a  \<and> dist x a  < d  \<longrightarrow> dist (f x) l < e)"
  by (auto simp add: tendsto_iff eventually_within)

lemma Lim_at: "(f ---> l) (at a) \<longleftrightarrow>
        (\<forall>e >0. \<exists>d>0. \<forall>x. 0 < dist x a  \<and> dist x a  < d  \<longrightarrow> dist (f x) l < e)"
  by (auto simp add: tendsto_iff eventually_at)

lemma Lim_at_iff_LIM: "(f ---> l) (at a) \<longleftrightarrow> f -- a --> l"
  unfolding Lim_at LIM_def by (simp only: zero_less_dist_iff)

lemma Lim_at_infinity:
  "(f ---> l) at_infinity \<longleftrightarrow> (\<forall>e>0. \<exists>b. \<forall>x. norm x >= b \<longrightarrow> dist (f x) l < e)"
  by (auto simp add: tendsto_iff eventually_at_infinity)

lemma Lim_sequentially:
 "(S ---> l) sequentially \<longleftrightarrow>
          (\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (S n) l < e)"
  by (auto simp add: tendsto_iff eventually_sequentially)

lemma Lim_sequentially_iff_LIMSEQ: "(S ---> l) sequentially \<longleftrightarrow> S ----> l"
  unfolding Lim_sequentially LIMSEQ_def ..

lemma Lim_eventually: "eventually (\<lambda>x. f x = l) net \<Longrightarrow> (f ---> l) net"
  by (rule topological_tendstoI, auto elim: eventually_rev_mono)

text{* The expected monotonicity property. *}

lemma Lim_within_empty: "(f ---> l) (net within {})"
  unfolding tendsto_def Limits.eventually_within by simp

lemma Lim_within_subset: "(f ---> l) (net within S) \<Longrightarrow> T \<subseteq> S \<Longrightarrow> (f ---> l) (net within T)"
  unfolding tendsto_def Limits.eventually_within
  by (auto elim!: eventually_elim1)

lemma Lim_Un: assumes "(f ---> l) (net within S)" "(f ---> l) (net within T)"
  shows "(f ---> l) (net within (S \<union> T))"
  using assms unfolding tendsto_def Limits.eventually_within
  apply clarify
  apply (drule spec, drule (1) mp, drule (1) mp)
  apply (drule spec, drule (1) mp, drule (1) mp)
  apply (auto elim: eventually_elim2)
  done

lemma Lim_Un_univ:
 "(f ---> l) (net within S) \<Longrightarrow> (f ---> l) (net within T) \<Longrightarrow>  S \<union> T = UNIV
        ==> (f ---> l) net"
  by (metis Lim_Un within_UNIV)

text{* Interrelations between restricted and unrestricted limits. *}

lemma Lim_at_within: "(f ---> l) net ==> (f ---> l)(net within S)"
  (* FIXME: rename *)
  unfolding tendsto_def Limits.eventually_within
  apply (clarify, drule spec, drule (1) mp, drule (1) mp)
  by (auto elim!: eventually_elim1)

lemma Lim_within_open:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes"a \<in> S" "open S"
  shows "(f ---> l)(at a within S) \<longleftrightarrow> (f ---> l)(at a)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  { fix A assume "open A" "l \<in> A"
    with `?lhs` have "eventually (\<lambda>x. f x \<in> A) (at a within S)"
      by (rule topological_tendstoD)
    hence "eventually (\<lambda>x. x \<in> S \<longrightarrow> f x \<in> A) (at a)"
      unfolding Limits.eventually_within .
    then obtain T where "open T" "a \<in> T" "\<forall>x\<in>T. x \<noteq> a \<longrightarrow> x \<in> S \<longrightarrow> f x \<in> A"
      unfolding eventually_at_topological by fast
    hence "open (T \<inter> S)" "a \<in> T \<inter> S" "\<forall>x\<in>(T \<inter> S). x \<noteq> a \<longrightarrow> f x \<in> A"
      using assms by auto
    hence "\<exists>T. open T \<and> a \<in> T \<and> (\<forall>x\<in>T. x \<noteq> a \<longrightarrow> f x \<in> A)"
      by fast
    hence "eventually (\<lambda>x. f x \<in> A) (at a)"
      unfolding eventually_at_topological .
  }
  thus ?rhs by (rule topological_tendstoI)
next
  assume ?rhs
  thus ?lhs by (rule Lim_at_within)
qed

text{* Another limit point characterization. *}

lemma islimpt_sequential:
  fixes x :: "'a::metric_space" (* FIXME: generalize to topological_space *)
  shows "x islimpt S \<longleftrightarrow> (\<exists>f. (\<forall>n::nat. f n \<in> S -{x}) \<and> (f ---> x) sequentially)"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain f where f:"\<forall>y. y>0 \<longrightarrow> f y \<in> S \<and> f y \<noteq> x \<and> dist (f y) x < y"
    unfolding islimpt_approachable using choice[of "\<lambda>e y. e>0 \<longrightarrow> y\<in>S \<and> y\<noteq>x \<and> dist y x < e"] by auto
  { fix n::nat
    have "f (inverse (real n + 1)) \<in> S - {x}" using f by auto
  }
  moreover
  { fix e::real assume "e>0"
    hence "\<exists>N::nat. inverse (real (N + 1)) < e" using real_arch_inv[of e] apply (auto simp add: Suc_pred') apply(rule_tac x="n - 1" in exI) by auto
    then obtain N::nat where "inverse (real (N + 1)) < e" by auto
    hence "\<forall>n\<ge>N. inverse (real n + 1) < e" by (auto, metis Suc_le_mono le_SucE less_imp_inverse_less nat_le_real_less order_less_trans real_of_nat_Suc real_of_nat_Suc_gt_zero)
    moreover have "\<forall>n\<ge>N. dist (f (inverse (real n + 1))) x < (inverse (real n + 1))" using f `e>0` by auto
    ultimately have "\<exists>N::nat. \<forall>n\<ge>N. dist (f (inverse (real n + 1))) x < e" apply(rule_tac x=N in exI) apply auto apply(erule_tac x=n in allE)+ by auto
  }
  hence " ((\<lambda>n. f (inverse (real n + 1))) ---> x) sequentially"
    unfolding Lim_sequentially using f by auto
  ultimately show ?rhs apply (rule_tac x="(\<lambda>n::nat. f (inverse (real n + 1)))" in exI) by auto
next
  assume ?rhs
  then obtain f::"nat\<Rightarrow>'a"  where f:"(\<forall>n. f n \<in> S - {x})" "(\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (f n) x < e)" unfolding Lim_sequentially by auto
  { fix e::real assume "e>0"
    then obtain N where "dist (f N) x < e" using f(2) by auto
    moreover have "f N\<in>S" "f N \<noteq> x" using f(1) by auto
    ultimately have "\<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e" by auto
  }
  thus ?lhs unfolding islimpt_approachable by auto
qed

text{* Basic arithmetical combining theorems for limits. *}

lemma Lim_linear: fixes f :: "('a \<Rightarrow> real^'n::finite)" and h :: "(real^'n \<Rightarrow> real^'m::finite)"
  assumes "(f ---> l) net" "linear h"
  shows "((\<lambda>x. h (f x)) ---> h l) net"
using `linear h` `(f ---> l) net`
unfolding linear_conv_bounded_linear
by (rule bounded_linear.tendsto)

lemma Lim_ident_at: "((\<lambda>x. x) ---> a) (at a)"
  unfolding tendsto_def Limits.eventually_at_topological by fast

lemma Lim_const: "((\<lambda>x. a) ---> a) net"
  by (rule tendsto_const)

lemma Lim_cmul:
  fixes f :: "'a \<Rightarrow> real ^ 'n::finite"
  shows "(f ---> l) net ==> ((\<lambda>x. c *\<^sub>R f x) ---> c *\<^sub>R l) net"
  by (intro tendsto_intros)

lemma Lim_neg:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "(f ---> l) net ==> ((\<lambda>x. -(f x)) ---> -l) net"
  by (rule tendsto_minus)

lemma Lim_add: fixes f :: "'a \<Rightarrow> 'b::real_normed_vector" shows
 "(f ---> l) net \<Longrightarrow> (g ---> m) net \<Longrightarrow> ((\<lambda>x. f(x) + g(x)) ---> l + m) net"
  by (rule tendsto_add)

lemma Lim_sub:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "(f ---> l) net \<Longrightarrow> (g ---> m) net \<Longrightarrow> ((\<lambda>x. f(x) - g(x)) ---> l - m) net"
  by (rule tendsto_diff)

lemma Lim_null:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "(f ---> l) net \<longleftrightarrow> ((\<lambda>x. f(x) - l) ---> 0) net" by (simp add: Lim dist_norm)

lemma Lim_null_norm:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "(f ---> 0) net \<longleftrightarrow> ((\<lambda>x. norm(f x)) ---> 0) net"
  by (simp add: Lim dist_norm)

lemma Lim_null_comparison:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "eventually (\<lambda>x. norm (f x) \<le> g x) net" "(g ---> 0) net"
  shows "(f ---> 0) net"
proof(simp add: tendsto_iff, rule+)
  fix e::real assume "0<e"
  { fix x
    assume "norm (f x) \<le> g x" "dist (g x) 0 < e"
    hence "dist (f x) 0 < e" by (simp add: dist_norm)
  }
  thus "eventually (\<lambda>x. dist (f x) 0 < e) net"
    using eventually_and[of "\<lambda>x. norm(f x) <= g x" "\<lambda>x. dist (g x) 0 < e" net]
    using eventually_mono[of "(\<lambda>x. norm (f x) \<le> g x \<and> dist (g x) 0 < e)" "(\<lambda>x. dist (f x) 0 < e)" net]
    using assms `e>0` unfolding tendsto_iff by auto
qed

lemma Lim_component:
  fixes f :: "'a \<Rightarrow> 'b::metric_space ^ 'n::finite"
  shows "(f ---> l) net \<Longrightarrow> ((\<lambda>a. f a $i) ---> l$i) net"
  unfolding tendsto_iff
  apply (clarify)
  apply (drule spec, drule (1) mp)
  apply (erule eventually_elim1)
  apply (erule le_less_trans [OF dist_nth_le])
  done

lemma Lim_transform_bound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  fixes g :: "'a \<Rightarrow> 'c::real_normed_vector"
  assumes "eventually (\<lambda>n. norm(f n) <= norm(g n)) net"  "(g ---> 0) net"
  shows "(f ---> 0) net"
proof (rule tendstoI)
  fix e::real assume "e>0"
  { fix x
    assume "norm (f x) \<le> norm (g x)" "dist (g x) 0 < e"
    hence "dist (f x) 0 < e" by (simp add: dist_norm)}
  thus "eventually (\<lambda>x. dist (f x) 0 < e) net"
    using eventually_and[of "\<lambda>x. norm (f x) \<le> norm (g x)" "\<lambda>x. dist (g x) 0 < e" net]
    using eventually_mono[of "\<lambda>x. norm (f x) \<le> norm (g x) \<and> dist (g x) 0 < e" "\<lambda>x. dist (f x) 0 < e" net]
    using assms `e>0` unfolding tendsto_iff by blast
qed

text{* Deducing things about the limit from the elements. *}

lemma Lim_in_closed_set:
  assumes "closed S" "eventually (\<lambda>x. f(x) \<in> S) net" "\<not>(trivial_limit net)" "(f ---> l) net"
  shows "l \<in> S"
proof (rule ccontr)
  assume "l \<notin> S"
  with `closed S` have "open (- S)" "l \<in> - S"
    by (simp_all add: open_Compl)
  with assms(4) have "eventually (\<lambda>x. f x \<in> - S) net"
    by (rule topological_tendstoD)
  with assms(2) have "eventually (\<lambda>x. False) net"
    by (rule eventually_elim2) simp
  with assms(3) show "False"
    by (simp add: eventually_False)
qed

text{* Need to prove closed(cball(x,e)) before deducing this as a corollary. *}

lemma Lim_dist_ubound:
  assumes "\<not>(trivial_limit net)" "(f ---> l) net" "eventually (\<lambda>x. dist a (f x) <= e) net"
  shows "dist a l <= e"
proof (rule ccontr)
  assume "\<not> dist a l \<le> e"
  then have "0 < dist a l - e" by simp
  with assms(2) have "eventually (\<lambda>x. dist (f x) l < dist a l - e) net"
    by (rule tendstoD)
  with assms(3) have "eventually (\<lambda>x. dist a (f x) \<le> e \<and> dist (f x) l < dist a l - e) net"
    by (rule eventually_conjI)
  then obtain w where "dist a (f w) \<le> e" "dist (f w) l < dist a l - e"
    using assms(1) eventually_happens by auto
  hence "dist a (f w) + dist (f w) l < e + (dist a l - e)"
    by (rule add_le_less_mono)
  hence "dist a (f w) + dist (f w) l < dist a l"
    by simp
  also have "\<dots> \<le> dist a (f w) + dist (f w) l"
    by (rule dist_triangle)
  finally show False by simp
qed

lemma Lim_norm_ubound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "\<not>(trivial_limit net)" "(f ---> l) net" "eventually (\<lambda>x. norm(f x) <= e) net"
  shows "norm(l) <= e"
proof (rule ccontr)
  assume "\<not> norm l \<le> e"
  then have "0 < norm l - e" by simp
  with assms(2) have "eventually (\<lambda>x. dist (f x) l < norm l - e) net"
    by (rule tendstoD)
  with assms(3) have "eventually (\<lambda>x. norm (f x) \<le> e \<and> dist (f x) l < norm l - e) net"
    by (rule eventually_conjI)
  then obtain w where "norm (f w) \<le> e" "dist (f w) l < norm l - e"
    using assms(1) eventually_happens by auto
  hence "norm (f w - l) < norm l - e" "norm (f w) \<le> e" by (simp_all add: dist_norm)
  hence "norm (f w - l) + norm (f w) < norm l" by simp
  hence "norm (f w - l - f w) < norm l" by (rule le_less_trans [OF norm_triangle_ineq4])
  thus False using `\<not> norm l \<le> e` by simp
qed

lemma Lim_norm_lbound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "\<not> (trivial_limit net)"  "(f ---> l) net"  "eventually (\<lambda>x. e <= norm(f x)) net"
  shows "e \<le> norm l"
proof (rule ccontr)
  assume "\<not> e \<le> norm l"
  then have "0 < e - norm l" by simp
  with assms(2) have "eventually (\<lambda>x. dist (f x) l < e - norm l) net"
    by (rule tendstoD)
  with assms(3) have "eventually (\<lambda>x. e \<le> norm (f x) \<and> dist (f x) l < e - norm l) net"
    by (rule eventually_conjI)
  then obtain w where "e \<le> norm (f w)" "dist (f w) l < e - norm l"
    using assms(1) eventually_happens by auto
  hence "norm (f w - l) + norm l < e" "e \<le> norm (f w)" by (simp_all add: dist_norm)
  hence "norm (f w - l) + norm l < norm (f w)" by (rule less_le_trans)
  hence "norm (f w - l + l) < norm (f w)" by (rule le_less_trans [OF norm_triangle_ineq])
  thus False by simp
qed

text{* Uniqueness of the limit, when nontrivial. *}

lemma Lim_unique:
  fixes f :: "'a \<Rightarrow> 'b::metric_space"
  assumes "\<not> trivial_limit net"  "(f ---> l) net"  "(f ---> l') net"
  shows "l = l'"
proof (rule ccontr)
  let ?d = "dist l l' / 2"
  assume "l \<noteq> l'"
  then have "0 < ?d" by (simp add: dist_nz)
  have "eventually (\<lambda>x. dist (f x) l < ?d) net"
    using `(f ---> l) net` `0 < ?d` by (rule tendstoD)
  moreover
  have "eventually (\<lambda>x. dist (f x) l' < ?d) net"
    using `(f ---> l') net` `0 < ?d` by (rule tendstoD)
  ultimately
  have "eventually (\<lambda>x. False) net"
  proof (rule eventually_elim2)
    fix x
    assume *: "dist (f x) l < ?d" "dist (f x) l' < ?d"
    have "dist l l' \<le> dist (f x) l + dist (f x) l'"
      by (rule dist_triangle_alt)
    also from * have "\<dots> < ?d + ?d"
      by (rule add_strict_mono)
    also have "\<dots> = dist l l'" by simp
    finally show "False" by simp
  qed
  with `\<not> trivial_limit net` show "False"
    by (simp add: eventually_False)
qed

lemma tendsto_Lim:
  fixes f :: "'a \<Rightarrow> 'b::metric_space"
  shows "~(trivial_limit net) \<Longrightarrow> (f ---> l) net ==> Lim net f = l"
  unfolding Lim_def using Lim_unique[of net f] by auto

text{* Limit under bilinear function *}

lemma Lim_bilinear:
  fixes net :: "'a net" and h:: "real ^'m::finite \<Rightarrow> real ^'n::finite \<Rightarrow> real ^'p::finite"
  assumes "(f ---> l) net" and "(g ---> m) net" and "bilinear h"
  shows "((\<lambda>x. h (f x) (g x)) ---> (h l m)) net"
using `bilinear h` `(f ---> l) net` `(g ---> m) net`
unfolding bilinear_conv_bounded_bilinear
by (rule bounded_bilinear.tendsto)

text{* These are special for limits out of the same vector space. *}

lemma Lim_within_id: "(id ---> a) (at a within s)"
  unfolding tendsto_def Limits.eventually_within eventually_at_topological
  by auto

lemma Lim_at_id: "(id ---> a) (at a)"
apply (subst within_UNIV[symmetric]) by (simp add: Lim_within_id)

lemma Lim_at_zero:
  fixes a :: "'a::real_normed_vector"
  fixes l :: "'b::topological_space"
  shows "(f ---> l) (at a) \<longleftrightarrow> ((\<lambda>x. f(a + x)) ---> l) (at 0)" (is "?lhs = ?rhs")
proof
  assume "?lhs"
  { fix S assume "open S" "l \<in> S"
    with `?lhs` have "eventually (\<lambda>x. f x \<in> S) (at a)"
      by (rule topological_tendstoD)
    then obtain d where d: "d>0" "\<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<in> S"
      unfolding Limits.eventually_at by fast
    { fix x::"'a" assume "x \<noteq> 0 \<and> dist x 0 < d"
      hence "f (a + x) \<in> S" using d
      apply(erule_tac x="x+a" in allE)
      by(auto simp add: comm_monoid_add.mult_commute dist_norm dist_commute)
    }
    hence "\<exists>d>0. \<forall>x. x \<noteq> 0 \<and> dist x 0 < d \<longrightarrow> f (a + x) \<in> S"
      using d(1) by auto
    hence "eventually (\<lambda>x. f (a + x) \<in> S) (at 0)"
      unfolding Limits.eventually_at .
  }
  thus "?rhs" by (rule topological_tendstoI)
next
  assume "?rhs"
  { fix S assume "open S" "l \<in> S"
    with `?rhs` have "eventually (\<lambda>x. f (a + x) \<in> S) (at 0)"
      by (rule topological_tendstoD)
    then obtain d where d: "d>0" "\<forall>x. x \<noteq> 0 \<and> dist x 0 < d \<longrightarrow> f (a + x) \<in> S"
      unfolding Limits.eventually_at by fast
    { fix x::"'a" assume "x \<noteq> a \<and> dist x a < d"
      hence "f x \<in> S" using d apply(erule_tac x="x-a" in allE)
	by(auto simp add: comm_monoid_add.mult_commute dist_norm dist_commute)
    }
    hence "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<in> S" using d(1) by auto
    hence "eventually (\<lambda>x. f x \<in> S) (at a)" unfolding Limits.eventually_at .
  }
  thus "?lhs" by (rule topological_tendstoI)
qed

text{* It's also sometimes useful to extract the limit point from the net.  *}

definition
  netlimit :: "'a::metric_space net \<Rightarrow> 'a" where
  "netlimit net = (SOME a. \<forall>r>0. eventually (\<lambda>x. dist x a < r) net)"

lemma netlimit_within:
  assumes "\<not> trivial_limit (at a within S)"
  shows "netlimit (at a within S) = a"
using assms
apply (simp add: trivial_limit_within)
apply (simp add: netlimit_def eventually_within zero_less_dist_iff)
apply (rule some_equality, fast)
apply (rename_tac b)
apply (rule ccontr)
apply (drule_tac x="dist b a / 2" in spec, drule mp, simp add: dist_nz)
apply (clarify, rename_tac r)
apply (simp only: islimpt_approachable)
apply (drule_tac x="min r (dist b a / 2)" in spec, drule mp, simp add: dist_nz)
apply (clarify)
apply (drule_tac x=x' in bspec, simp)
apply (drule mp, simp)
apply (subgoal_tac "dist b a < dist b a / 2 + dist b a / 2", simp)
apply (rule le_less_trans [OF dist_triangle3])
apply (erule add_strict_mono)
apply simp
done

lemma netlimit_at:
  fixes a :: "'a::perfect_space"
  shows "netlimit (at a) = a"
  apply (subst within_UNIV[symmetric])
  using netlimit_within[of a UNIV]
  by (simp add: trivial_limit_at within_UNIV)

text{* Transformation of limit. *}

lemma Lim_transform:
  fixes f g :: "'a::type \<Rightarrow> 'b::real_normed_vector"
  assumes "((\<lambda>x. f x - g x) ---> 0) net" "(f ---> l) net"
  shows "(g ---> l) net"
proof-
  from assms have "((\<lambda>x. f x - g x - f x) ---> 0 - l) net" using Lim_sub[of "\<lambda>x. f x - g x" 0 net f l] by auto
  thus "?thesis" using Lim_neg [of "\<lambda> x. - g x" "-l" net] by auto
qed

lemma Lim_transform_eventually:
  "eventually (\<lambda>x. f x = g x) net \<Longrightarrow> (f ---> l) net ==> (g ---> l) net"
  apply (rule topological_tendstoI)
  apply (drule (2) topological_tendstoD)
  apply (erule (1) eventually_elim2, simp)
  done

lemma Lim_transform_within:
  fixes l :: "'b::metric_space" (* TODO: generalize *)
  assumes "0 < d" "(\<forall>x'\<in>S. 0 < dist x' x \<and> dist x' x < d \<longrightarrow> f x' = g x')"
          "(f ---> l) (at x within S)"
  shows   "(g ---> l) (at x within S)"
  using assms(1,3) unfolding Lim_within
  apply -
  apply (clarify, rename_tac e)
  apply (drule_tac x=e in spec, clarsimp, rename_tac r)
  apply (rule_tac x="min d r" in exI, clarsimp, rename_tac y)
  apply (drule_tac x=y in bspec, assumption, clarsimp)
  apply (simp add: assms(2))
  done

lemma Lim_transform_at:
  fixes l :: "'b::metric_space" (* TODO: generalize *)
  shows "0 < d \<Longrightarrow> (\<forall>x'. 0 < dist x' x \<and> dist x' x < d \<longrightarrow> f x' = g x') \<Longrightarrow>
  (f ---> l) (at x) ==> (g ---> l) (at x)"
  apply (subst within_UNIV[symmetric])
  using Lim_transform_within[of d UNIV x f g l]
  by (auto simp add: within_UNIV)

text{* Common case assuming being away from some crucial point like 0. *}

lemma Lim_transform_away_within:
  fixes a b :: "'a::metric_space"
  fixes l :: "'b::metric_space" (* TODO: generalize *)
  assumes "a\<noteq>b" "\<forall>x\<in> S. x \<noteq> a \<and> x \<noteq> b \<longrightarrow> f x = g x"
  and "(f ---> l) (at a within S)"
  shows "(g ---> l) (at a within S)"
proof-
  have "\<forall>x'\<in>S. 0 < dist x' a \<and> dist x' a < dist a b \<longrightarrow> f x' = g x'" using assms(2)
    apply auto apply(erule_tac x=x' in ballE) by (auto simp add: dist_commute)
  thus ?thesis using Lim_transform_within[of "dist a b" S a f g l] using assms(1,3) unfolding dist_nz by auto
qed

lemma Lim_transform_away_at:
  fixes a b :: "'a::metric_space"
  fixes l :: "'b::metric_space" (* TODO: generalize *)
  assumes ab: "a\<noteq>b" and fg: "\<forall>x. x \<noteq> a \<and> x \<noteq> b \<longrightarrow> f x = g x"
  and fl: "(f ---> l) (at a)"
  shows "(g ---> l) (at a)"
  using Lim_transform_away_within[OF ab, of UNIV f g l] fg fl
  by (auto simp add: within_UNIV)

text{* Alternatively, within an open set. *}

lemma Lim_transform_within_open:
  fixes a :: "'a::metric_space"
  fixes l :: "'b::metric_space" (* TODO: generalize *)
  assumes "open S"  "a \<in> S"  "\<forall>x\<in>S. x \<noteq> a \<longrightarrow> f x = g x"  "(f ---> l) (at a)"
  shows "(g ---> l) (at a)"
proof-
  from assms(1,2) obtain e::real where "e>0" and e:"ball a e \<subseteq> S" unfolding open_contains_ball by auto
  hence "\<forall>x'. 0 < dist x' a \<and> dist x' a < e \<longrightarrow> f x' = g x'" using assms(3)
    unfolding ball_def subset_eq apply auto apply(erule_tac x=x' in allE) apply(erule_tac x=x' in ballE) by(auto simp add: dist_commute)
  thus ?thesis using Lim_transform_at[of e a f g l] `e>0` assms(4) by auto
qed

text{* A congruence rule allowing us to transform limits assuming not at point. *}

(* FIXME: Only one congruence rule for tendsto can be used at a time! *)

lemma Lim_cong_within[cong add]:
  fixes a :: "'a::metric_space"
  fixes l :: "'b::metric_space" (* TODO: generalize *)
  shows "(\<And>x. x \<noteq> a \<Longrightarrow> f x = g x) ==> ((\<lambda>x. f x) ---> l) (at a within S) \<longleftrightarrow> ((g ---> l) (at a within S))"
  by (simp add: Lim_within dist_nz[symmetric])

lemma Lim_cong_at[cong add]:
  fixes a :: "'a::metric_space"
  fixes l :: "'b::metric_space" (* TODO: generalize *)
  shows "(\<And>x. x \<noteq> a ==> f x = g x) ==> (((\<lambda>x. f x) ---> l) (at a) \<longleftrightarrow> ((g ---> l) (at a)))"
  by (simp add: Lim_at dist_nz[symmetric])

text{* Useful lemmas on closure and set of possible sequential limits.*}

lemma closure_sequential:
  fixes l :: "'a::metric_space" (* TODO: generalize *)
  shows "l \<in> closure S \<longleftrightarrow> (\<exists>x. (\<forall>n. x n \<in> S) \<and> (x ---> l) sequentially)" (is "?lhs = ?rhs")
proof
  assume "?lhs" moreover
  { assume "l \<in> S"
    hence "?rhs" using Lim_const[of l sequentially] by auto
  } moreover
  { assume "l islimpt S"
    hence "?rhs" unfolding islimpt_sequential by auto
  } ultimately
  show "?rhs" unfolding closure_def by auto
next
  assume "?rhs"
  thus "?lhs" unfolding closure_def unfolding islimpt_sequential by auto
qed

lemma closed_sequential_limits:
  fixes S :: "'a::metric_space set"
  shows "closed S \<longleftrightarrow> (\<forall>x l. (\<forall>n. x n \<in> S) \<and> (x ---> l) sequentially \<longrightarrow> l \<in> S)"
  unfolding closed_limpt
  using closure_sequential [where 'a='a] closure_closed [where 'a='a] closed_limpt [where 'a='a] islimpt_sequential [where 'a='a] mem_delete [where 'a='a]
  by metis

lemma closure_approachable:
  fixes S :: "'a::metric_space set"
  shows "x \<in> closure S \<longleftrightarrow> (\<forall>e>0. \<exists>y\<in>S. dist y x < e)"
  apply (auto simp add: closure_def islimpt_approachable)
  by (metis dist_self)

lemma closed_approachable:
  fixes S :: "'a::metric_space set"
  shows "closed S ==> (\<forall>e>0. \<exists>y\<in>S. dist y x < e) \<longleftrightarrow> x \<in> S"
  by (metis closure_closed closure_approachable)

text{* Some other lemmas about sequences. *}

lemma seq_offset:
  fixes l :: "'a::metric_space" (* TODO: generalize *)
  shows "(f ---> l) sequentially ==> ((\<lambda>i. f( i + k)) ---> l) sequentially"
  apply (auto simp add: Lim_sequentially)
  by (metis trans_le_add1 )

lemma seq_offset_neg:
  "(f ---> l) sequentially ==> ((\<lambda>i. f(i - k)) ---> l) sequentially"
  apply (rule topological_tendstoI)
  apply (drule (2) topological_tendstoD)
  apply (simp only: eventually_sequentially)
  apply (subgoal_tac "\<And>N k (n::nat). N + k <= n ==> N <= n - k")
  apply metis
  by arith

lemma seq_offset_rev:
  "((\<lambda>i. f(i + k)) ---> l) sequentially ==> (f ---> l) sequentially"
  apply (rule topological_tendstoI)
  apply (drule (2) topological_tendstoD)
  apply (simp only: eventually_sequentially)
  apply (subgoal_tac "\<And>N k (n::nat). N + k <= n ==> N <= n - k \<and> (n - k) + k = n")
  by metis arith

lemma seq_harmonic: "((\<lambda>n. inverse (real n)) ---> 0) sequentially"
proof-
  { fix e::real assume "e>0"
    hence "\<exists>N::nat. \<forall>n::nat\<ge>N. inverse (real n) < e"
      using real_arch_inv[of e] apply auto apply(rule_tac x=n in exI)
      by (metis not_le le_imp_inverse_le not_less real_of_nat_gt_zero_cancel_iff real_of_nat_less_iff xt1(7))
  }
  thus ?thesis unfolding Lim_sequentially dist_norm by simp
qed

text{* More properties of closed balls. *}

lemma closed_cball: "closed (cball x e)"
unfolding cball_def closed_def
unfolding Collect_neg_eq [symmetric] not_le
apply (clarsimp simp add: open_dist, rename_tac y)
apply (rule_tac x="dist x y - e" in exI, clarsimp)
apply (rename_tac x')
apply (cut_tac x=x and y=x' and z=y in dist_triangle)
apply simp
done

lemma open_contains_cball: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0.  cball x e \<subseteq> S)"
proof-
  { fix x and e::real assume "x\<in>S" "e>0" "ball x e \<subseteq> S"
    hence "\<exists>d>0. cball x d \<subseteq> S" unfolding subset_eq by (rule_tac x="e/2" in exI, auto)
  } moreover
  { fix x and e::real assume "x\<in>S" "e>0" "cball x e \<subseteq> S"
    hence "\<exists>d>0. ball x d \<subseteq> S" unfolding subset_eq apply(rule_tac x="e/2" in exI) by auto
  } ultimately
  show ?thesis unfolding open_contains_ball by auto
qed

lemma open_contains_cball_eq: "open S ==> (\<forall>x. x \<in> S \<longleftrightarrow> (\<exists>e>0. cball x e \<subseteq> S))"
  by (metis open_contains_cball subset_eq order_less_imp_le centre_in_cball mem_def)

lemma mem_interior_cball: "x \<in> interior S \<longleftrightarrow> (\<exists>e>0. cball x e \<subseteq> S)"
  apply (simp add: interior_def, safe)
  apply (force simp add: open_contains_cball)
  apply (rule_tac x="ball x e" in exI)
  apply (simp add: open_ball centre_in_ball subset_trans [OF ball_subset_cball])
  done

lemma islimpt_ball:
  fixes x y :: "'a::{real_normed_vector,perfect_space}"
  shows "y islimpt ball x e \<longleftrightarrow> 0 < e \<and> y \<in> cball x e" (is "?lhs = ?rhs")
proof
  assume "?lhs"
  { assume "e \<le> 0"
    hence *:"ball x e = {}" using ball_eq_empty[of x e] by auto
    have False using `?lhs` unfolding * using islimpt_EMPTY[of y] by auto
  }
  hence "e > 0" by (metis not_less)
  moreover
  have "y \<in> cball x e" using closed_cball[of x e] islimpt_subset[of y "ball x e" "cball x e"] ball_subset_cball[of x e] `?lhs` unfolding closed_limpt by auto
  ultimately show "?rhs" by auto
next
  assume "?rhs" hence "e>0"  by auto
  { fix d::real assume "d>0"
    have "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
    proof(cases "d \<le> dist x y")
      case True thus "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
      proof(cases "x=y")
	case True hence False using `d \<le> dist x y` `d>0` by auto
	thus "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d" by auto
      next
	case False

	have "dist x (y - (d / (2 * dist y x)) *\<^sub>R (y - x))
	      = norm (x - y + (d / (2 * norm (y - x))) *\<^sub>R (y - x))"
	  unfolding mem_cball mem_ball dist_norm diff_diff_eq2 diff_add_eq[THEN sym] by auto
	also have "\<dots> = \<bar>- 1 + d / (2 * norm (x - y))\<bar> * norm (x - y)"
	  using scaleR_left_distrib[of "- 1" "d / (2 * norm (y - x))", THEN sym, of "y - x"]
	  unfolding scaleR_minus_left scaleR_one
	  by (auto simp add: norm_minus_commute)
	also have "\<dots> = \<bar>- norm (x - y) + d / 2\<bar>"
	  unfolding abs_mult_pos[of "norm (x - y)", OF norm_ge_zero[of "x - y"]]
	  unfolding real_add_mult_distrib using `x\<noteq>y`[unfolded dist_nz, unfolded dist_norm] by auto
	also have "\<dots> \<le> e - d/2" using `d \<le> dist x y` and `d>0` and `?rhs` by(auto simp add: dist_norm)
	finally have "y - (d / (2 * dist y x)) *\<^sub>R (y - x) \<in> ball x e" using `d>0` by auto

	moreover

	have "(d / (2*dist y x)) *\<^sub>R (y - x) \<noteq> 0"
	  using `x\<noteq>y`[unfolded dist_nz] `d>0` unfolding scaleR_eq_0_iff by (auto simp add: dist_commute)
	moreover
	have "dist (y - (d / (2 * dist y x)) *\<^sub>R (y - x)) y < d" unfolding dist_norm apply simp unfolding norm_minus_cancel
	  using `d>0` `x\<noteq>y`[unfolded dist_nz] dist_commute[of x y]
	  unfolding dist_norm by auto
	ultimately show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d" by (rule_tac  x="y - (d / (2*dist y x)) *\<^sub>R (y - x)" in bexI) auto
      qed
    next
      case False hence "d > dist x y" by auto
      show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
      proof(cases "x=y")
	case True
	obtain z where **: "z \<noteq> y" "dist z y < min e d"
          using perfect_choose_dist[of "min e d" y]
	  using `d > 0` `e>0` by auto
	show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
          unfolding `x = y`
          using `z \<noteq> y` **
          by (rule_tac x=z in bexI, auto simp add: dist_commute)
      next
	case False thus "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
	  using `d>0` `d > dist x y` `?rhs` by(rule_tac x=x in bexI, auto)
      qed
    qed  }
  thus "?lhs" unfolding mem_cball islimpt_approachable mem_ball by auto
qed

lemma closure_ball_lemma:
  fixes x y :: "'a::real_normed_vector"
  assumes "x \<noteq> y" shows "y islimpt ball x (dist x y)"
proof (rule islimptI)
  fix T assume "y \<in> T" "open T"
  then obtain r where "0 < r" "\<forall>z. dist z y < r \<longrightarrow> z \<in> T"
    unfolding open_dist by fast
  (* choose point between x and y, within distance r of y. *)
  def k \<equiv> "min 1 (r / (2 * dist x y))"
  def z \<equiv> "y + scaleR k (x - y)"
  have z_def2: "z = x + scaleR (1 - k) (y - x)"
    unfolding z_def by (simp add: algebra_simps)
  have "dist z y < r"
    unfolding z_def k_def using `0 < r`
    by (simp add: dist_norm min_def)
  hence "z \<in> T" using `\<forall>z. dist z y < r \<longrightarrow> z \<in> T` by simp
  have "dist x z < dist x y"
    unfolding z_def2 dist_norm
    apply (simp add: norm_minus_commute)
    apply (simp only: dist_norm [symmetric])
    apply (subgoal_tac "\<bar>1 - k\<bar> * dist x y < 1 * dist x y", simp)
    apply (rule mult_strict_right_mono)
    apply (simp add: k_def divide_pos_pos zero_less_dist_iff `0 < r` `x \<noteq> y`)
    apply (simp add: zero_less_dist_iff `x \<noteq> y`)
    done
  hence "z \<in> ball x (dist x y)" by simp
  have "z \<noteq> y"
    unfolding z_def k_def using `x \<noteq> y` `0 < r`
    by (simp add: min_def)
  show "\<exists>z\<in>ball x (dist x y). z \<in> T \<and> z \<noteq> y"
    using `z \<in> ball x (dist x y)` `z \<in> T` `z \<noteq> y`
    by fast
qed

lemma closure_ball:
  fixes x :: "'a::real_normed_vector"
  shows "0 < e \<Longrightarrow> closure (ball x e) = cball x e"
apply (rule equalityI)
apply (rule closure_minimal)
apply (rule ball_subset_cball)
apply (rule closed_cball)
apply (rule subsetI, rename_tac y)
apply (simp add: le_less [where 'a=real])
apply (erule disjE)
apply (rule subsetD [OF closure_subset], simp)
apply (simp add: closure_def)
apply clarify
apply (rule closure_ball_lemma)
apply (simp add: zero_less_dist_iff)
done

(* In a trivial vector space, this fails for e = 0. *)
lemma interior_cball:
  fixes x :: "'a::{real_normed_vector, perfect_space}"
  shows "interior (cball x e) = ball x e"
proof(cases "e\<ge>0")
  case False note cs = this
  from cs have "ball x e = {}" using ball_empty[of e x] by auto moreover
  { fix y assume "y \<in> cball x e"
    hence False unfolding mem_cball using dist_nz[of x y] cs by auto  }
  hence "cball x e = {}" by auto
  hence "interior (cball x e) = {}" using interior_empty by auto
  ultimately show ?thesis by blast
next
  case True note cs = this
  have "ball x e \<subseteq> cball x e" using ball_subset_cball by auto moreover
  { fix S y assume as: "S \<subseteq> cball x e" "open S" "y\<in>S"
    then obtain d where "d>0" and d:"\<forall>x'. dist x' y < d \<longrightarrow> x' \<in> S" unfolding open_dist by blast

    then obtain xa where xa_y: "xa \<noteq> y" and xa: "dist xa y < d"
      using perfect_choose_dist [of d] by auto
    have "xa\<in>S" using d[THEN spec[where x=xa]] using xa by(auto simp add: dist_commute)
    hence xa_cball:"xa \<in> cball x e" using as(1) by auto

    hence "y \<in> ball x e" proof(cases "x = y")
      case True
      hence "e>0" using xa_y[unfolded dist_nz] xa_cball[unfolded mem_cball] by (auto simp add: dist_commute)
      thus "y \<in> ball x e" using `x = y ` by simp
    next
      case False
      have "dist (y + (d / 2 / dist y x) *\<^sub>R (y - x)) y < d" unfolding dist_norm
	using `d>0` norm_ge_zero[of "y - x"] `x \<noteq> y` by auto
      hence *:"y + (d / 2 / dist y x) *\<^sub>R (y - x) \<in> cball x e" using d as(1)[unfolded subset_eq] by blast
      have "y - x \<noteq> 0" using `x \<noteq> y` by auto
      hence **:"d / (2 * norm (y - x)) > 0" unfolding zero_less_norm_iff[THEN sym]
	using `d>0` divide_pos_pos[of d "2*norm (y - x)"] by auto

      have "dist (y + (d / 2 / dist y x) *\<^sub>R (y - x)) x = norm (y + (d / (2 * norm (y - x))) *\<^sub>R y - (d / (2 * norm (y - x))) *\<^sub>R x - x)"
        by (auto simp add: dist_norm algebra_simps)
      also have "\<dots> = norm ((1 + d / (2 * norm (y - x))) *\<^sub>R (y - x))"
        by (auto simp add: algebra_simps)
      also have "\<dots> = \<bar>1 + d / (2 * norm (y - x))\<bar> * norm (y - x)"
        using ** by auto
      also have "\<dots> = (dist y x) + d/2"using ** by (auto simp add: left_distrib dist_norm)
      finally have "e \<ge> dist x y +d/2" using *[unfolded mem_cball] by (auto simp add: dist_commute)
      thus "y \<in> ball x e" unfolding mem_ball using `d>0` by auto
    qed  }
  hence "\<forall>S \<subseteq> cball x e. open S \<longrightarrow> S \<subseteq> ball x e" by auto
  ultimately show ?thesis using interior_unique[of "ball x e" "cball x e"] using open_ball[of x e] by auto
qed

lemma frontier_ball:
  fixes a :: "'a::real_normed_vector"
  shows "0 < e ==> frontier(ball a e) = {x. dist a x = e}"
  apply (simp add: frontier_def closure_ball interior_open open_ball order_less_imp_le)
  apply (simp add: expand_set_eq)
  by arith

lemma frontier_cball:
  fixes a :: "'a::{real_normed_vector, perfect_space}"
  shows "frontier(cball a e) = {x. dist a x = e}"
  apply (simp add: frontier_def interior_cball closed_cball closure_closed order_less_imp_le)
  apply (simp add: expand_set_eq)
  by arith

lemma cball_eq_empty: "(cball x e = {}) \<longleftrightarrow> e < 0"
  apply (simp add: expand_set_eq not_le)
  by (metis zero_le_dist dist_self order_less_le_trans)
lemma cball_empty: "e < 0 ==> cball x e = {}" by (simp add: cball_eq_empty)

lemma cball_eq_sing:
  fixes x :: "'a::perfect_space"
  shows "(cball x e = {x}) \<longleftrightarrow> e = 0"
proof (rule linorder_cases)
  assume e: "0 < e"
  obtain a where "a \<noteq> x" "dist a x < e"
    using perfect_choose_dist [OF e] by auto
  hence "a \<noteq> x" "dist x a \<le> e" by (auto simp add: dist_commute)
  with e show ?thesis by (auto simp add: expand_set_eq)
qed auto

lemma cball_sing:
  fixes x :: "'a::metric_space"
  shows "e = 0 ==> cball x e = {x}"
  by (auto simp add: expand_set_eq)

text{* For points in the interior, localization of limits makes no difference.   *}

lemma eventually_within_interior:
  assumes "x \<in> interior S"
  shows "eventually P (at x within S) \<longleftrightarrow> eventually P (at x)" (is "?lhs = ?rhs")
proof-
  from assms obtain T where T: "open T" "x \<in> T" "T \<subseteq> S"
    unfolding interior_def by fast
  { assume "?lhs"
    then obtain A where "open A" "x \<in> A" "\<forall>y\<in>A. y \<noteq> x \<longrightarrow> y \<in> S \<longrightarrow> P y"
      unfolding Limits.eventually_within Limits.eventually_at_topological
      by auto
    with T have "open (A \<inter> T)" "x \<in> A \<inter> T" "\<forall>y\<in>(A \<inter> T). y \<noteq> x \<longrightarrow> P y"
      by auto
    then have "?rhs"
      unfolding Limits.eventually_at_topological by auto
  } moreover
  { assume "?rhs" hence "?lhs"
      unfolding Limits.eventually_within
      by (auto elim: eventually_elim1)
  } ultimately
  show "?thesis" ..
qed

lemma lim_within_interior:
  "x \<in> interior S \<Longrightarrow> (f ---> l) (at x within S) \<longleftrightarrow> (f ---> l) (at x)"
  unfolding tendsto_def by (simp add: eventually_within_interior)

lemma netlimit_within_interior:
  fixes x :: "'a::{perfect_space, real_normed_vector}"
    (* FIXME: generalize to perfect_space *)
  assumes "x \<in> interior S"
  shows "netlimit(at x within S) = x" (is "?lhs = ?rhs")
proof-
  from assms obtain e::real where e:"e>0" "ball x e \<subseteq> S" using open_interior[of S] unfolding open_contains_ball using interior_subset[of S] by auto
  hence "\<not> trivial_limit (at x within S)" using islimpt_subset[of x "ball x e" S] unfolding trivial_limit_within islimpt_ball centre_in_cball by auto
  thus ?thesis using netlimit_within by auto
qed

subsection{* Boundedness. *}

  (* FIXME: This has to be unified with BSEQ!! *)
definition
  bounded :: "'a::metric_space set \<Rightarrow> bool" where
  "bounded S \<longleftrightarrow> (\<exists>x e. \<forall>y\<in>S. dist x y \<le> e)"

lemma bounded_any_center: "bounded S \<longleftrightarrow> (\<exists>e. \<forall>y\<in>S. dist a y \<le> e)"
unfolding bounded_def
apply safe
apply (rule_tac x="dist a x + e" in exI, clarify)
apply (drule (1) bspec)
apply (erule order_trans [OF dist_triangle add_left_mono])
apply auto
done

lemma bounded_iff: "bounded S \<longleftrightarrow> (\<exists>a. \<forall>x\<in>S. norm x \<le> a)"
unfolding bounded_any_center [where a=0]
by (simp add: dist_norm)

lemma bounded_empty[simp]: "bounded {}" by (simp add: bounded_def)
lemma bounded_subset: "bounded T \<Longrightarrow> S \<subseteq> T ==> bounded S"
  by (metis bounded_def subset_eq)

lemma bounded_interior[intro]: "bounded S ==> bounded(interior S)"
  by (metis bounded_subset interior_subset)

lemma bounded_closure[intro]: assumes "bounded S" shows "bounded(closure S)"
proof-
  from assms obtain x and a where a: "\<forall>y\<in>S. dist x y \<le> a" unfolding bounded_def by auto
  { fix y assume "y \<in> closure S"
    then obtain f where f: "\<forall>n. f n \<in> S"  "(f ---> y) sequentially"
      unfolding closure_sequential by auto
    have "\<forall>n. f n \<in> S \<longrightarrow> dist x (f n) \<le> a" using a by simp
    hence "eventually (\<lambda>n. dist x (f n) \<le> a) sequentially"
      by (rule eventually_mono, simp add: f(1))
    have "dist x y \<le> a"
      apply (rule Lim_dist_ubound [of sequentially f])
      apply (rule trivial_limit_sequentially)
      apply (rule f(2))
      apply fact
      done
  }
  thus ?thesis unfolding bounded_def by auto
qed

lemma bounded_cball[simp,intro]: "bounded (cball x e)"
  apply (simp add: bounded_def)
  apply (rule_tac x=x in exI)
  apply (rule_tac x=e in exI)
  apply auto
  done

lemma bounded_ball[simp,intro]: "bounded(ball x e)"
  by (metis ball_subset_cball bounded_cball bounded_subset)

lemma finite_imp_bounded[intro]: assumes "finite S" shows "bounded S"
proof-
  { fix a F assume as:"bounded F"
    then obtain x e where "\<forall>y\<in>F. dist x y \<le> e" unfolding bounded_def by auto
    hence "\<forall>y\<in>(insert a F). dist x y \<le> max e (dist x a)" by auto
    hence "bounded (insert a F)" unfolding bounded_def by (intro exI)
  }
  thus ?thesis using finite_induct[of S bounded]  using bounded_empty assms by auto
qed

lemma bounded_Un[simp]: "bounded (S \<union> T) \<longleftrightarrow> bounded S \<and> bounded T"
  apply (auto simp add: bounded_def)
  apply (rename_tac x y r s)
  apply (rule_tac x=x in exI)
  apply (rule_tac x="max r (dist x y + s)" in exI)
  apply (rule ballI, rename_tac z, safe)
  apply (drule (1) bspec, simp)
  apply (drule (1) bspec)
  apply (rule min_max.le_supI2)
  apply (erule order_trans [OF dist_triangle add_left_mono])
  done

lemma bounded_Union[intro]: "finite F \<Longrightarrow> (\<forall>S\<in>F. bounded S) \<Longrightarrow> bounded(\<Union>F)"
  by (induct rule: finite_induct[of F], auto)

lemma bounded_pos: "bounded S \<longleftrightarrow> (\<exists>b>0. \<forall>x\<in> S. norm x <= b)"
  apply (simp add: bounded_iff)
  apply (subgoal_tac "\<And>x (y::real). 0 < 1 + abs y \<and> (x <= y \<longrightarrow> x <= 1 + abs y)")
  by metis arith

lemma bounded_Int[intro]: "bounded S \<or> bounded T \<Longrightarrow> bounded (S \<inter> T)"
  by (metis Int_lower1 Int_lower2 bounded_subset)

lemma bounded_diff[intro]: "bounded S ==> bounded (S - T)"
apply (metis Diff_subset bounded_subset)
done

lemma bounded_insert[intro]:"bounded(insert x S) \<longleftrightarrow> bounded S"
  by (metis Diff_cancel Un_empty_right Un_insert_right bounded_Un bounded_subset finite.emptyI finite_imp_bounded infinite_remove subset_insertI)

lemma not_bounded_UNIV[simp, intro]:
  "\<not> bounded (UNIV :: 'a::{real_normed_vector, perfect_space} set)"
proof(auto simp add: bounded_pos not_le)
  obtain x :: 'a where "x \<noteq> 0"
    using perfect_choose_dist [OF zero_less_one] by fast
  fix b::real  assume b: "b >0"
  have b1: "b +1 \<ge> 0" using b by simp
  with `x \<noteq> 0` have "b < norm (scaleR (b + 1) (sgn x))"
    by (simp add: norm_sgn)
  then show "\<exists>x::'a. b < norm x" ..
qed

lemma bounded_linear_image:
  fixes f :: "real^'m::finite \<Rightarrow> real^'n::finite"
  assumes "bounded S" "linear f"
  shows "bounded(f ` S)"
proof-
  from assms(1) obtain b where b:"b>0" "\<forall>x\<in>S. norm x \<le> b" unfolding bounded_pos by auto
  from assms(2) obtain B where B:"B>0" "\<forall>x. norm (f x) \<le> B * norm x"  using linear_bounded_pos by auto
  { fix x assume "x\<in>S"
    hence "norm x \<le> b" using b by auto
    hence "norm (f x) \<le> B * b" using B(2) apply(erule_tac x=x in allE)
      by (metis B(1) B(2) real_le_trans real_mult_le_cancel_iff2)
  }
  thus ?thesis unfolding bounded_pos apply(rule_tac x="b*B" in exI)
    using b B real_mult_order[of b B] by (auto simp add: real_mult_commute)
qed

lemma bounded_scaling:
  fixes S :: "(real ^ 'n::finite) set"
  shows "bounded S \<Longrightarrow> bounded ((\<lambda>x. c *\<^sub>R x) ` S)"
  apply (rule bounded_linear_image, assumption)
  apply (simp only: linear_conv_bounded_linear)
  apply (rule scaleR.bounded_linear_right)
  done

lemma bounded_translation:
  fixes S :: "'a::real_normed_vector set"
  assumes "bounded S" shows "bounded ((\<lambda>x. a + x) ` S)"
proof-
  from assms obtain b where b:"b>0" "\<forall>x\<in>S. norm x \<le> b" unfolding bounded_pos by auto
  { fix x assume "x\<in>S"
    hence "norm (a + x) \<le> b + norm a" using norm_triangle_ineq[of a x] b by auto
  }
  thus ?thesis unfolding bounded_pos using norm_ge_zero[of a] b(1) using add_strict_increasing[of b 0 "norm a"]
    by (auto intro!: add exI[of _ "b + norm a"])
qed


text{* Some theorems on sups and infs using the notion "bounded". *}

lemma bounded_real:
  fixes S :: "real set"
  shows "bounded S \<longleftrightarrow>  (\<exists>a. \<forall>x\<in>S. abs x <= a)"
  by (simp add: bounded_iff)

lemma bounded_has_rsup: assumes "bounded S" "S \<noteq> {}"
  shows "\<forall>x\<in>S. x <= rsup S" and "\<forall>b. (\<forall>x\<in>S. x <= b) \<longrightarrow> rsup S <= b"
proof
  fix x assume "x\<in>S"
  from assms(1) obtain a where a:"\<forall>x\<in>S. \<bar>x\<bar> \<le> a" unfolding bounded_real by auto
  hence *:"S *<= a" using setleI[of S a] by (metis abs_le_interval_iff mem_def)
  thus "x \<le> rsup S" using rsup[OF `S\<noteq>{}`] using assms(1)[unfolded bounded_real] using isLubD2[of UNIV S "rsup S" x] using `x\<in>S` by auto
next
  show "\<forall>b. (\<forall>x\<in>S. x \<le> b) \<longrightarrow> rsup S \<le> b" using assms
  using rsup[of S, unfolded isLub_def isUb_def leastP_def setle_def setge_def]
  apply (auto simp add: bounded_real)
  by (auto simp add: isLub_def isUb_def leastP_def setle_def setge_def)
qed

lemma rsup_insert: assumes "bounded S"
  shows "rsup(insert x S) = (if S = {} then x else max x (rsup S))"
proof(cases "S={}")
  case True thus ?thesis using rsup_finite_in[of "{x}"] by auto
next
  let ?S = "insert x S"
  case False
  hence *:"\<forall>x\<in>S. x \<le> rsup S" using bounded_has_rsup(1)[of S] using assms by auto
  hence "insert x S *<= max x (rsup S)" unfolding setle_def by auto
  hence "isLub UNIV ?S (rsup ?S)" using rsup[of ?S] by auto
  moreover
  have **:"isUb UNIV ?S (max x (rsup S))" unfolding isUb_def setle_def using * by auto
  { fix y assume as:"isUb UNIV (insert x S) y"
    hence "max x (rsup S) \<le> y" unfolding isUb_def using rsup_le[OF `S\<noteq>{}`]
      unfolding setle_def by auto  }
  hence "max x (rsup S) <=* isUb UNIV (insert x S)" unfolding setge_def Ball_def mem_def by auto
  hence "isLub UNIV ?S (max x (rsup S))" using ** isLubI2[of UNIV ?S "max x (rsup S)"] unfolding Collect_def by auto
  ultimately show ?thesis using real_isLub_unique[of UNIV ?S] using `S\<noteq>{}` by auto
qed

lemma sup_insert_finite: "finite S \<Longrightarrow> rsup(insert x S) = (if S = {} then x else max x (rsup S))"
  apply (rule rsup_insert)
  apply (rule finite_imp_bounded)
  by simp

lemma bounded_has_rinf:
  assumes "bounded S"  "S \<noteq> {}"
  shows "\<forall>x\<in>S. x >= rinf S" and "\<forall>b. (\<forall>x\<in>S. x >= b) \<longrightarrow> rinf S >= b"
proof
  fix x assume "x\<in>S"
  from assms(1) obtain a where a:"\<forall>x\<in>S. \<bar>x\<bar> \<le> a" unfolding bounded_real by auto
  hence *:"- a <=* S" using setgeI[of S "-a"] unfolding abs_le_interval_iff by auto
  thus "x \<ge> rinf S" using rinf[OF `S\<noteq>{}`] using isGlbD2[of UNIV S "rinf S" x] using `x\<in>S` by auto
next
  show "\<forall>b. (\<forall>x\<in>S. x >= b) \<longrightarrow> rinf S \<ge> b" using assms
  using rinf[of S, unfolded isGlb_def isLb_def greatestP_def setle_def setge_def]
  apply (auto simp add: bounded_real)
  by (auto simp add: isGlb_def isLb_def greatestP_def setle_def setge_def)
qed

(* TODO: Move this to RComplete.thy -- would need to include Glb into RComplete *)
lemma real_isGlb_unique: "[| isGlb R S x; isGlb R S y |] ==> x = (y::real)"
  apply (frule isGlb_isLb)
  apply (frule_tac x = y in isGlb_isLb)
  apply (blast intro!: order_antisym dest!: isGlb_le_isLb)
  done

lemma rinf_insert: assumes "bounded S"
  shows "rinf(insert x S) = (if S = {} then x else min x (rinf S))" (is "?lhs = ?rhs")
proof(cases "S={}")
  case True thus ?thesis using rinf_finite_in[of "{x}"] by auto
next
  let ?S = "insert x S"
  case False
  hence *:"\<forall>x\<in>S. x \<ge> rinf S" using bounded_has_rinf(1)[of S] using assms by auto
  hence "min x (rinf S) <=* insert x S" unfolding setge_def by auto
  hence "isGlb UNIV ?S (rinf ?S)" using rinf[of ?S] by auto
  moreover
  have **:"isLb UNIV ?S (min x (rinf S))" unfolding isLb_def setge_def using * by auto
  { fix y assume as:"isLb UNIV (insert x S) y"
    hence "min x (rinf S) \<ge> y" unfolding isLb_def using rinf_ge[OF `S\<noteq>{}`]
      unfolding setge_def by auto  }
  hence "isLb UNIV (insert x S) *<= min x (rinf S)" unfolding setle_def Ball_def mem_def by auto
  hence "isGlb UNIV ?S (min x (rinf S))" using ** isGlbI2[of UNIV ?S "min x (rinf S)"] unfolding Collect_def by auto
  ultimately show ?thesis using real_isGlb_unique[of UNIV ?S] using `S\<noteq>{}` by auto
qed

lemma inf_insert_finite: "finite S ==> rinf(insert x S) = (if S = {} then x else min x (rinf S))"
  by (rule rinf_insert, rule finite_imp_bounded, simp)

subsection{* Compactness (the definition is the one based on convegent subsequences). *}

definition
  compact :: "'a::metric_space set \<Rightarrow> bool" where (* TODO: generalize *)
  "compact S \<longleftrightarrow>
   (\<forall>f. (\<forall>n. f n \<in> S) \<longrightarrow>
       (\<exists>l\<in>S. \<exists>r. subseq r \<and> ((f o r) ---> l) sequentially))"

text {*
  A metric space (or topological vector space) is said to have the
  Heine-Borel property if every closed and bounded subset is compact.
*}

class heine_borel =
  assumes bounded_imp_convergent_subsequence:
    "bounded s \<Longrightarrow> \<forall>n. f n \<in> s
      \<Longrightarrow> \<exists>l r. subseq r \<and> ((f \<circ> r) ---> l) sequentially"

lemma bounded_closed_imp_compact:
  fixes s::"'a::heine_borel set"
  assumes "bounded s" and "closed s" shows "compact s"
proof (unfold compact_def, clarify)
  fix f :: "nat \<Rightarrow> 'a" assume f: "\<forall>n. f n \<in> s"
  obtain l r where r: "subseq r" and l: "((f \<circ> r) ---> l) sequentially"
    using bounded_imp_convergent_subsequence [OF `bounded s` `\<forall>n. f n \<in> s`] by auto
  from f have fr: "\<forall>n. (f \<circ> r) n \<in> s" by simp
  have "l \<in> s" using `closed s` fr l
    unfolding closed_sequential_limits by blast
  show "\<exists>l\<in>s. \<exists>r. subseq r \<and> ((f \<circ> r) ---> l) sequentially"
    using `l \<in> s` r l by blast
qed

lemma subseq_bigger: assumes "subseq r" shows "n \<le> r n"
proof(induct n)
  show "0 \<le> r 0" by auto
next
  fix n assume "n \<le> r n"
  moreover have "r n < r (Suc n)"
    using assms [unfolded subseq_def] by auto
  ultimately show "Suc n \<le> r (Suc n)" by auto
qed

lemma eventually_subseq:
  assumes r: "subseq r"
  shows "eventually P sequentially \<Longrightarrow> eventually (\<lambda>n. P (r n)) sequentially"
unfolding eventually_sequentially
by (metis subseq_bigger [OF r] le_trans)

lemma lim_subseq:
  "subseq r \<Longrightarrow> (s ---> l) sequentially \<Longrightarrow> ((s o r) ---> l) sequentially"
unfolding tendsto_def eventually_sequentially o_def
by (metis subseq_bigger le_trans)

lemma num_Axiom: "EX! g. g 0 = e \<and> (\<forall>n. g (Suc n) = f n (g n))"
  unfolding Ex1_def
  apply (rule_tac x="nat_rec e f" in exI)
  apply (rule conjI)+
apply (rule def_nat_rec_0, simp)
apply (rule allI, rule def_nat_rec_Suc, simp)
apply (rule allI, rule impI, rule ext)
apply (erule conjE)
apply (induct_tac x)
apply (simp add: nat_rec_0)
apply (erule_tac x="n" in allE)
apply (simp)
done

lemma convergent_bounded_increasing: fixes s ::"nat\<Rightarrow>real"
  assumes "incseq s" and "\<forall>n. abs(s n) \<le> b"
  shows "\<exists> l. \<forall>e::real>0. \<exists> N. \<forall>n \<ge> N.  abs(s n - l) < e"
proof-
  have "isUb UNIV (range s) b" using assms(2) and abs_le_D1 unfolding isUb_def and setle_def by auto
  then obtain t where t:"isLub UNIV (range s) t" using reals_complete[of "range s" ] by auto
  { fix e::real assume "e>0" and as:"\<forall>N. \<exists>n\<ge>N. \<not> \<bar>s n - t\<bar> < e"
    { fix n::nat
      obtain N where "N\<ge>n" and n:"\<bar>s N - t\<bar> \<ge> e" using as[THEN spec[where x=n]] by auto
      have "t \<ge> s N" using isLub_isUb[OF t, unfolded isUb_def setle_def] by auto
      with n have "s N \<le> t - e" using `e>0` by auto
      hence "s n \<le> t - e" using assms(1)[unfolded incseq_def, THEN spec[where x=n], THEN spec[where x=N]] using `n\<le>N` by auto  }
    hence "isUb UNIV (range s) (t - e)" unfolding isUb_def and setle_def by auto
    hence False using isLub_le_isUb[OF t, of "t - e"] and `e>0` by auto  }
  thus ?thesis by blast
qed

lemma convergent_bounded_monotone: fixes s::"nat \<Rightarrow> real"
  assumes "\<forall>n. abs(s n) \<le> b" and "monoseq s"
  shows "\<exists>l. \<forall>e::real>0. \<exists>N. \<forall>n\<ge>N. abs(s n - l) < e"
  using convergent_bounded_increasing[of s b] assms using convergent_bounded_increasing[of "\<lambda>n. - s n" b]
  unfolding monoseq_def incseq_def
  apply auto unfolding minus_add_distrib[THEN sym, unfolded diff_minus[THEN sym]]
  unfolding abs_minus_cancel by(rule_tac x="-l" in exI)auto

lemma compact_real_lemma:
  assumes "\<forall>n::nat. abs(s n) \<le> b"
  shows "\<exists>(l::real) r. subseq r \<and> ((s \<circ> r) ---> l) sequentially"
proof-
  obtain r where r:"subseq r" "monoseq (\<lambda>n. s (r n))"
    using seq_monosub[of s] by auto
  thus ?thesis using convergent_bounded_monotone[of "\<lambda>n. s (r n)" b] and assms
    unfolding tendsto_iff dist_norm eventually_sequentially by auto
qed

instance real :: heine_borel
proof
  fix s :: "real set" and f :: "nat \<Rightarrow> real"
  assume s: "bounded s" and f: "\<forall>n. f n \<in> s"
  then obtain b where b: "\<forall>n. abs (f n) \<le> b"
    unfolding bounded_iff by auto
  obtain l :: real and r :: "nat \<Rightarrow> nat" where
    r: "subseq r" and l: "((f \<circ> r) ---> l) sequentially"
    using compact_real_lemma [OF b] by auto
  thus "\<exists>l r. subseq r \<and> ((f \<circ> r) ---> l) sequentially"
    by auto
qed

lemma bounded_component: "bounded s \<Longrightarrow> bounded ((\<lambda>x. x $ i) ` s)"
unfolding bounded_def
apply clarify
apply (rule_tac x="x $ i" in exI)
apply (rule_tac x="e" in exI)
apply clarify
apply (rule order_trans [OF dist_nth_le], simp)
done

lemma compact_lemma:
  fixes f :: "nat \<Rightarrow> 'a::heine_borel ^ 'n::finite"
  assumes "bounded s" and "\<forall>n. f n \<in> s"
  shows "\<forall>d.
        \<exists>l r. subseq r \<and>
        (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) $ i) (l $ i) < e) sequentially)"
proof
  fix d::"'n set" have "finite d" by simp
  thus "\<exists>l::'a ^ 'n. \<exists>r. subseq r \<and>
      (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) $ i) (l $ i) < e) sequentially)"
  proof(induct d) case empty thus ?case unfolding subseq_def by auto
  next case (insert k d)
    have s': "bounded ((\<lambda>x. x $ k) ` s)" using `bounded s` by (rule bounded_component)
    obtain l1::"'a^'n" and r1 where r1:"subseq r1" and lr1:"\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 n) $ i) (l1 $ i) < e) sequentially"
      using insert(3) by auto
    have f': "\<forall>n. f (r1 n) $ k \<in> (\<lambda>x. x $ k) ` s" using `\<forall>n. f n \<in> s` by simp
    obtain l2 r2 where r2:"subseq r2" and lr2:"((\<lambda>i. f (r1 (r2 i)) $ k) ---> l2) sequentially"
      using bounded_imp_convergent_subsequence[OF s' f'] unfolding o_def by auto
    def r \<equiv> "r1 \<circ> r2" have r:"subseq r"
      using r1 and r2 unfolding r_def o_def subseq_def by auto
    moreover
    def l \<equiv> "(\<chi> i. if i = k then l2 else l1$i)::'a^'n"
    { fix e::real assume "e>0"
      from lr1 `e>0` have N1:"eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 n) $ i) (l1 $ i) < e) sequentially" by blast
      from lr2 `e>0` have N2:"eventually (\<lambda>n. dist (f (r1 (r2 n)) $ k) l2 < e) sequentially" by (rule tendstoD)
      from r2 N1 have N1': "eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 (r2 n)) $ i) (l1 $ i) < e) sequentially"
        by (rule eventually_subseq)
      have "eventually (\<lambda>n. \<forall>i\<in>(insert k d). dist (f (r n) $ i) (l $ i) < e) sequentially"
        using N1' N2 by (rule eventually_elim2, simp add: l_def r_def)
    }
    ultimately show ?case by auto
  qed
qed

instance "^" :: (heine_borel, finite) heine_borel
proof
  fix s :: "('a ^ 'b) set" and f :: "nat \<Rightarrow> 'a ^ 'b"
  assume s: "bounded s" and f: "\<forall>n. f n \<in> s"
  then obtain l r where r: "subseq r"
    and l: "\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>UNIV. dist (f (r n) $ i) (l $ i) < e) sequentially"
    using compact_lemma [OF s f] by blast
  let ?d = "UNIV::'b set"
  { fix e::real assume "e>0"
    hence "0 < e / (real_of_nat (card ?d))"
      using zero_less_card_finite using divide_pos_pos[of e, of "real_of_nat (card ?d)"] by auto
    with l have "eventually (\<lambda>n. \<forall>i. dist (f (r n) $ i) (l $ i) < e / (real_of_nat (card ?d))) sequentially"
      by simp
    moreover
    { fix n assume n: "\<forall>i. dist (f (r n) $ i) (l $ i) < e / (real_of_nat (card ?d))"
      have "dist (f (r n)) l \<le> (\<Sum>i\<in>?d. dist (f (r n) $ i) (l $ i))"
        unfolding dist_vector_def using zero_le_dist by (rule setL2_le_setsum)
      also have "\<dots> < (\<Sum>i\<in>?d. e / (real_of_nat (card ?d)))"
        by (rule setsum_strict_mono) (simp_all add: n)
      finally have "dist (f (r n)) l < e" by simp
    }
    ultimately have "eventually (\<lambda>n. dist (f (r n)) l < e) sequentially"
      by (rule eventually_elim1)
  }
  hence *:"((f \<circ> r) ---> l) sequentially" unfolding o_def tendsto_iff by simp
  with r show "\<exists>l r. subseq r \<and> ((f \<circ> r) ---> l) sequentially" by auto
qed

lemma bounded_fst: "bounded s \<Longrightarrow> bounded (fst ` s)"
unfolding bounded_def
apply clarify
apply (rule_tac x="a" in exI)
apply (rule_tac x="e" in exI)
apply clarsimp
apply (drule (1) bspec)
apply (simp add: dist_Pair_Pair)
apply (erule order_trans [OF real_sqrt_sum_squares_ge1])
done

lemma bounded_snd: "bounded s \<Longrightarrow> bounded (snd ` s)"
unfolding bounded_def
apply clarify
apply (rule_tac x="b" in exI)
apply (rule_tac x="e" in exI)
apply clarsimp
apply (drule (1) bspec)
apply (simp add: dist_Pair_Pair)
apply (erule order_trans [OF real_sqrt_sum_squares_ge2])
done

instance "*" :: (heine_borel, heine_borel) heine_borel
proof
  fix s :: "('a * 'b) set" and f :: "nat \<Rightarrow> 'a * 'b"
  assume s: "bounded s" and f: "\<forall>n. f n \<in> s"
  from s have s1: "bounded (fst ` s)" by (rule bounded_fst)
  from f have f1: "\<forall>n. fst (f n) \<in> fst ` s" by simp
  obtain l1 r1 where r1: "subseq r1"
    and l1: "((\<lambda>n. fst (f (r1 n))) ---> l1) sequentially"
    using bounded_imp_convergent_subsequence [OF s1 f1]
    unfolding o_def by fast
  from s have s2: "bounded (snd ` s)" by (rule bounded_snd)
  from f have f2: "\<forall>n. snd (f (r1 n)) \<in> snd ` s" by simp
  obtain l2 r2 where r2: "subseq r2"
    and l2: "((\<lambda>n. snd (f (r1 (r2 n)))) ---> l2) sequentially"
    using bounded_imp_convergent_subsequence [OF s2 f2]
    unfolding o_def by fast
  have l1': "((\<lambda>n. fst (f (r1 (r2 n)))) ---> l1) sequentially"
    using lim_subseq [OF r2 l1] unfolding o_def .
  have l: "((f \<circ> (r1 \<circ> r2)) ---> (l1, l2)) sequentially"
    using tendsto_Pair [OF l1' l2] unfolding o_def by simp
  have r: "subseq (r1 \<circ> r2)"
    using r1 r2 unfolding subseq_def by simp
  show "\<exists>l r. subseq r \<and> ((f \<circ> r) ---> l) sequentially"
    using l r by fast
qed

subsection{* Completeness. *}

lemma cauchy_def:
  "Cauchy s \<longleftrightarrow> (\<forall>e>0. \<exists>N. \<forall>m n. m \<ge> N \<and> n \<ge> N --> dist(s m)(s n) < e)"
unfolding Cauchy_def by blast

definition
  complete :: "'a::metric_space set \<Rightarrow> bool" where
  "complete s \<longleftrightarrow> (\<forall>f. (\<forall>n. f n \<in> s) \<and> Cauchy f
                      --> (\<exists>l \<in> s. (f ---> l) sequentially))"

lemma cauchy: "Cauchy s \<longleftrightarrow> (\<forall>e>0.\<exists> N::nat. \<forall>n\<ge>N. dist(s n)(s N) < e)" (is "?lhs = ?rhs")
proof-
  { assume ?rhs
    { fix e::real
      assume "e>0"
      with `?rhs` obtain N where N:"\<forall>n\<ge>N. dist (s n) (s N) < e/2"
	by (erule_tac x="e/2" in allE) auto
      { fix n m
	assume nm:"N \<le> m \<and> N \<le> n"
	hence "dist (s m) (s n) < e" using N
	  using dist_triangle_half_l[of "s m" "s N" "e" "s n"]
	  by blast
      }
      hence "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (s m) (s n) < e"
	by blast
    }
    hence ?lhs
      unfolding cauchy_def
      by blast
  }
  thus ?thesis
    unfolding cauchy_def
    using dist_triangle_half_l
    by blast
qed

lemma convergent_imp_cauchy:
 "(s ---> l) sequentially ==> Cauchy s"
proof(simp only: cauchy_def, rule, rule)
  fix e::real assume "e>0" "(s ---> l) sequentially"
  then obtain N::nat where N:"\<forall>n\<ge>N. dist (s n) l < e/2" unfolding Lim_sequentially by(erule_tac x="e/2" in allE) auto
  thus "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (s m) (s n) < e"  using dist_triangle_half_l[of _ l e _] by (rule_tac x=N in exI) auto
qed

lemma cauchy_imp_bounded: assumes "Cauchy s" shows "bounded {y. (\<exists>n::nat. y = s n)}"
proof-
  from assms obtain N::nat where "\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (s m) (s n) < 1" unfolding cauchy_def apply(erule_tac x= 1 in allE) by auto
  hence N:"\<forall>n. N \<le> n \<longrightarrow> dist (s N) (s n) < 1" by auto
  moreover
  have "bounded (s ` {0..N})" using finite_imp_bounded[of "s ` {1..N}"] by auto
  then obtain a where a:"\<forall>x\<in>s ` {0..N}. dist (s N) x \<le> a"
    unfolding bounded_any_center [where a="s N"] by auto
  ultimately show "?thesis"
    unfolding bounded_any_center [where a="s N"]
    apply(rule_tac x="max a 1" in exI) apply auto
    apply(erule_tac x=n in allE) apply(erule_tac x=n in ballE) by auto
qed

lemma compact_imp_complete: assumes "compact s" shows "complete s"
proof-
  { fix f assume as: "(\<forall>n::nat. f n \<in> s)" "Cauchy f"
    from as(1) obtain l r where lr: "l\<in>s" "subseq r" "((f \<circ> r) ---> l) sequentially" using assms unfolding compact_def by blast

    note lr' = subseq_bigger [OF lr(2)]

    { fix e::real assume "e>0"
      from as(2) obtain N where N:"\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (f m) (f n) < e/2" unfolding cauchy_def using `e>0` apply (erule_tac x="e/2" in allE) by auto
      from lr(3)[unfolded Lim_sequentially, THEN spec[where x="e/2"]] obtain M where M:"\<forall>n\<ge>M. dist ((f \<circ> r) n) l < e/2" using `e>0` by auto
      { fix n::nat assume n:"n \<ge> max N M"
	have "dist ((f \<circ> r) n) l < e/2" using n M by auto
	moreover have "r n \<ge> N" using lr'[of n] n by auto
	hence "dist (f n) ((f \<circ> r) n) < e / 2" using N using n by auto
	ultimately have "dist (f n) l < e" using dist_triangle_half_r[of "f (r n)" "f n" e l] by (auto simp add: dist_commute)  }
      hence "\<exists>N. \<forall>n\<ge>N. dist (f n) l < e" by blast  }
    hence "\<exists>l\<in>s. (f ---> l) sequentially" using `l\<in>s` unfolding Lim_sequentially by auto  }
  thus ?thesis unfolding complete_def by auto
qed

instance heine_borel < complete_space
proof
  fix f :: "nat \<Rightarrow> 'a" assume "Cauchy f"
  hence "bounded (range f)" unfolding image_def
    using cauchy_imp_bounded [of f] by auto
  hence "compact (closure (range f))"
    using bounded_closed_imp_compact [of "closure (range f)"] by auto
  hence "complete (closure (range f))"
    using compact_imp_complete by auto
  moreover have "\<forall>n. f n \<in> closure (range f)"
    using closure_subset [of "range f"] by auto
  ultimately have "\<exists>l\<in>closure (range f). (f ---> l) sequentially"
    using `Cauchy f` unfolding complete_def by auto
  then show "convergent f"
    unfolding convergent_def LIMSEQ_conv_tendsto [symmetric] by auto
qed

lemma complete_univ: "complete (UNIV :: 'a::complete_space set)"
proof(simp add: complete_def, rule, rule)
  fix f :: "nat \<Rightarrow> 'a" assume "Cauchy f"
  hence "convergent f" by (rule Cauchy_convergent)
  hence "\<exists>l. f ----> l" unfolding convergent_def .  
  thus "\<exists>l. (f ---> l) sequentially" unfolding LIMSEQ_conv_tendsto .
qed

lemma complete_imp_closed: assumes "complete s" shows "closed s"
proof -
  { fix x assume "x islimpt s"
    then obtain f where f: "\<forall>n. f n \<in> s - {x}" "(f ---> x) sequentially"
      unfolding islimpt_sequential by auto
    then obtain l where l: "l\<in>s" "(f ---> l) sequentially"
      using `complete s`[unfolded complete_def] using convergent_imp_cauchy[of f x] by auto
    hence "x \<in> s"  using Lim_unique[of sequentially f l x] trivial_limit_sequentially f(2) by auto
  }
  thus "closed s" unfolding closed_limpt by auto
qed

lemma complete_eq_closed:
  fixes s :: "'a::complete_space set"
  shows "complete s \<longleftrightarrow> closed s" (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs by (rule complete_imp_closed)
next
  assume ?rhs
  { fix f assume as:"\<forall>n::nat. f n \<in> s" "Cauchy f"
    then obtain l where "(f ---> l) sequentially" using complete_univ[unfolded complete_def, THEN spec[where x=f]] by auto
    hence "\<exists>l\<in>s. (f ---> l) sequentially" using `?rhs`[unfolded closed_sequential_limits, THEN spec[where x=f], THEN spec[where x=l]] using as(1) by auto  }
  thus ?lhs unfolding complete_def by auto
qed

lemma convergent_eq_cauchy:
  fixes s :: "nat \<Rightarrow> 'a::complete_space"
  shows "(\<exists>l. (s ---> l) sequentially) \<longleftrightarrow> Cauchy s" (is "?lhs = ?rhs")
proof
  assume ?lhs then obtain l where "(s ---> l) sequentially" by auto
  thus ?rhs using convergent_imp_cauchy by auto
next
  assume ?rhs thus ?lhs using complete_univ[unfolded complete_def, THEN spec[where x=s]] by auto
qed

lemma convergent_imp_bounded:
  fixes s :: "nat \<Rightarrow> 'a::metric_space"
  shows "(s ---> l) sequentially ==> bounded (s ` (UNIV::(nat set)))"
  using convergent_imp_cauchy[of s]
  using cauchy_imp_bounded[of s]
  unfolding image_def
  by auto

subsection{* Total boundedness. *}

fun helper_1::"('a::metric_space set) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> 'a" where
  "helper_1 s e n = (SOME y::'a. y \<in> s \<and> (\<forall>m<n. \<not> (dist (helper_1 s e m) y < e)))"
declare helper_1.simps[simp del]

lemma compact_imp_totally_bounded:
  assumes "compact s"
  shows "\<forall>e>0. \<exists>k. finite k \<and> k \<subseteq> s \<and> s \<subseteq> (\<Union>((\<lambda>x. ball x e) ` k))"
proof(rule, rule, rule ccontr)
  fix e::real assume "e>0" and assm:"\<not> (\<exists>k. finite k \<and> k \<subseteq> s \<and> s \<subseteq> \<Union>(\<lambda>x. ball x e) ` k)"
  def x \<equiv> "helper_1 s e"
  { fix n
    have "x n \<in> s \<and> (\<forall>m<n. \<not> dist (x m) (x n) < e)"
    proof(induct_tac rule:nat_less_induct)
      fix n  def Q \<equiv> "(\<lambda>y. y \<in> s \<and> (\<forall>m<n. \<not> dist (x m) y < e))"
      assume as:"\<forall>m<n. x m \<in> s \<and> (\<forall>ma<m. \<not> dist (x ma) (x m) < e)"
      have "\<not> s \<subseteq> (\<Union>x\<in>x ` {0..<n}. ball x e)" using assm apply simp apply(erule_tac x="x ` {0 ..< n}" in allE) using as by auto
      then obtain z where z:"z\<in>s" "z \<notin> (\<Union>x\<in>x ` {0..<n}. ball x e)" unfolding subset_eq by auto
      have "Q (x n)" unfolding x_def and helper_1.simps[of s e n]
	apply(rule someI2[where a=z]) unfolding x_def[symmetric] and Q_def using z by auto
      thus "x n \<in> s \<and> (\<forall>m<n. \<not> dist (x m) (x n) < e)" unfolding Q_def by auto
    qed }
  hence "\<forall>n::nat. x n \<in> s" and x:"\<forall>n. \<forall>m < n. \<not> (dist (x m) (x n) < e)" by blast+
  then obtain l r where "l\<in>s" and r:"subseq r" and "((x \<circ> r) ---> l) sequentially" using assms(1)[unfolded compact_def, THEN spec[where x=x]] by auto
  from this(3) have "Cauchy (x \<circ> r)" using convergent_imp_cauchy by auto
  then obtain N::nat where N:"\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist ((x \<circ> r) m) ((x \<circ> r) n) < e" unfolding cauchy_def using `e>0` by auto
  show False
    using N[THEN spec[where x=N], THEN spec[where x="N+1"]]
    using r[unfolded subseq_def, THEN spec[where x=N], THEN spec[where x="N+1"]]
    using x[THEN spec[where x="r (N+1)"], THEN spec[where x="r (N)"]] by auto
qed

subsection{* Heine-Borel theorem (following Burkill \& Burkill vol. 2) *}

lemma heine_borel_lemma: fixes s::"'a::metric_space set"
  assumes "compact s"  "s \<subseteq> (\<Union> t)"  "\<forall>b \<in> t. open b"
  shows "\<exists>e>0. \<forall>x \<in> s. \<exists>b \<in> t. ball x e \<subseteq> b"
proof(rule ccontr)
  assume "\<not> (\<exists>e>0. \<forall>x\<in>s. \<exists>b\<in>t. ball x e \<subseteq> b)"
  hence cont:"\<forall>e>0. \<exists>x\<in>s. \<forall>xa\<in>t. \<not> (ball x e \<subseteq> xa)" by auto
  { fix n::nat
    have "1 / real (n + 1) > 0" by auto
    hence "\<exists>x. x\<in>s \<and> (\<forall>xa\<in>t. \<not> (ball x (inverse (real (n+1))) \<subseteq> xa))" using cont unfolding Bex_def by auto }
  hence "\<forall>n::nat. \<exists>x. x \<in> s \<and> (\<forall>xa\<in>t. \<not> ball x (inverse (real (n + 1))) \<subseteq> xa)" by auto
  then obtain f where f:"\<forall>n::nat. f n \<in> s \<and> (\<forall>xa\<in>t. \<not> ball (f n) (inverse (real (n + 1))) \<subseteq> xa)"
    using choice[of "\<lambda>n::nat. \<lambda>x. x\<in>s \<and> (\<forall>xa\<in>t. \<not> ball x (inverse (real (n + 1))) \<subseteq> xa)"] by auto

  then obtain l r where l:"l\<in>s" and r:"subseq r" and lr:"((f \<circ> r) ---> l) sequentially"
    using assms(1)[unfolded compact_def, THEN spec[where x=f]] by auto

  obtain b where "l\<in>b" "b\<in>t" using assms(2) and l by auto
  then obtain e where "e>0" and e:"\<forall>z. dist z l < e \<longrightarrow> z\<in>b"
    using assms(3)[THEN bspec[where x=b]] unfolding open_dist by auto

  then obtain N1 where N1:"\<forall>n\<ge>N1. dist ((f \<circ> r) n) l < e / 2"
    using lr[unfolded Lim_sequentially, THEN spec[where x="e/2"]] by auto

  obtain N2::nat where N2:"N2>0" "inverse (real N2) < e /2" using real_arch_inv[of "e/2"] and `e>0` by auto
  have N2':"inverse (real (r (N1 + N2) +1 )) < e/2"
    apply(rule order_less_trans) apply(rule less_imp_inverse_less) using N2
    using subseq_bigger[OF r, of "N1 + N2"] by auto

  def x \<equiv> "(f (r (N1 + N2)))"
  have x:"\<not> ball x (inverse (real (r (N1 + N2) + 1))) \<subseteq> b" unfolding x_def
    using f[THEN spec[where x="r (N1 + N2)"]] using `b\<in>t` by auto
  have "\<exists>y\<in>ball x (inverse (real (r (N1 + N2) + 1))). y\<notin>b" apply(rule ccontr) using x by auto
  then obtain y where y:"y \<in> ball x (inverse (real (r (N1 + N2) + 1)))" "y \<notin> b" by auto

  have "dist x l < e/2" using N1 unfolding x_def o_def by auto
  hence "dist y l < e" using y N2' using dist_triangle[of y l x]by (auto simp add:dist_commute)

  thus False using e and `y\<notin>b` by auto
qed

lemma compact_imp_heine_borel: "compact s ==> (\<forall>f. (\<forall>t \<in> f. open t) \<and> s \<subseteq> (\<Union> f)
               \<longrightarrow> (\<exists>f'. f' \<subseteq> f \<and> finite f' \<and> s \<subseteq> (\<Union> f')))"
proof clarify
  fix f assume "compact s" " \<forall>t\<in>f. open t" "s \<subseteq> \<Union>f"
  then obtain e::real where "e>0" and "\<forall>x\<in>s. \<exists>b\<in>f. ball x e \<subseteq> b" using heine_borel_lemma[of s f] by auto
  hence "\<forall>x\<in>s. \<exists>b. b\<in>f \<and> ball x e \<subseteq> b" by auto
  hence "\<exists>bb. \<forall>x\<in>s. bb x \<in>f \<and> ball x e \<subseteq> bb x" using bchoice[of s "\<lambda>x b. b\<in>f \<and> ball x e \<subseteq> b"] by auto
  then obtain  bb where bb:"\<forall>x\<in>s. (bb x) \<in> f \<and> ball x e \<subseteq> (bb x)" by blast

  from `compact s` have  "\<exists> k. finite k \<and> k \<subseteq> s \<and> s \<subseteq> \<Union>(\<lambda>x. ball x e) ` k" using compact_imp_totally_bounded[of s] `e>0` by auto
  then obtain k where k:"finite k" "k \<subseteq> s" "s \<subseteq> \<Union>(\<lambda>x. ball x e) ` k" by auto

  have "finite (bb ` k)" using k(1) by auto
  moreover
  { fix x assume "x\<in>s"
    hence "x\<in>\<Union>(\<lambda>x. ball x e) ` k" using k(3)  unfolding subset_eq by auto
    hence "\<exists>X\<in>bb ` k. x \<in> X" using bb k(2) by blast
    hence "x \<in> \<Union>(bb ` k)" using  Union_iff[of x "bb ` k"] by auto
  }
  ultimately show "\<exists>f'\<subseteq>f. finite f' \<and> s \<subseteq> \<Union>f'" using bb k(2) by (rule_tac x="bb ` k" in exI) auto
qed

subsection{* Bolzano-Weierstrass property. *}

lemma heine_borel_imp_bolzano_weierstrass:
  assumes "\<forall>f. (\<forall>t \<in> f. open t) \<and> s \<subseteq> (\<Union> f) --> (\<exists>f'. f' \<subseteq> f \<and> finite f' \<and> s \<subseteq> (\<Union> f'))"
          "infinite t"  "t \<subseteq> s"
  shows "\<exists>x \<in> s. x islimpt t"
proof(rule ccontr)
  assume "\<not> (\<exists>x \<in> s. x islimpt t)"
  then obtain f where f:"\<forall>x\<in>s. x \<in> f x \<and> open (f x) \<and> (\<forall>y\<in>t. y \<in> f x \<longrightarrow> y = x)" unfolding islimpt_def
    using bchoice[of s "\<lambda> x T. x \<in> T \<and> open T \<and> (\<forall>y\<in>t. y \<in> T \<longrightarrow> y = x)"] by auto
  obtain g where g:"g\<subseteq>{t. \<exists>x. x \<in> s \<and> t = f x}" "finite g" "s \<subseteq> \<Union>g"
    using assms(1)[THEN spec[where x="{t. \<exists>x. x\<in>s \<and> t = f x}"]] using f by auto
  from g(1,3) have g':"\<forall>x\<in>g. \<exists>xa \<in> s. x = f xa" by auto
  { fix x y assume "x\<in>t" "y\<in>t" "f x = f y"
    hence "x \<in> f x"  "y \<in> f x \<longrightarrow> y = x" using f[THEN bspec[where x=x]] and `t\<subseteq>s` by auto
    hence "x = y" using `f x = f y` and f[THEN bspec[where x=y]] and `y\<in>t` and `t\<subseteq>s` by auto  }
  hence "infinite (f ` t)" using assms(2) using finite_imageD[unfolded inj_on_def, of f t] by auto
  moreover
  { fix x assume "x\<in>t" "f x \<notin> g"
    from g(3) assms(3) `x\<in>t` obtain h where "h\<in>g" and "x\<in>h" by auto
    then obtain y where "y\<in>s" "h = f y" using g'[THEN bspec[where x=h]] by auto
    hence "y = x" using f[THEN bspec[where x=y]] and `x\<in>t` and `x\<in>h`[unfolded `h = f y`] by auto
    hence False using `f x \<notin> g` `h\<in>g` unfolding `h = f y` by auto  }
  hence "f ` t \<subseteq> g" by auto
  ultimately show False using g(2) using finite_subset by auto
qed

subsection{* Complete the chain of compactness variants. *}

primrec helper_2::"(real \<Rightarrow> 'a::metric_space) \<Rightarrow> nat \<Rightarrow> 'a" where
  "helper_2 beyond 0 = beyond 0" |
  "helper_2 beyond (Suc n) = beyond (dist arbitrary (helper_2 beyond n) + 1 )"

lemma bolzano_weierstrass_imp_bounded: fixes s::"'a::metric_space set"
  assumes "\<forall>t. infinite t \<and> t \<subseteq> s --> (\<exists>x \<in> s. x islimpt t)"
  shows "bounded s"
proof(rule ccontr)
  assume "\<not> bounded s"
  then obtain beyond where "\<forall>a. beyond a \<in>s \<and> \<not> dist arbitrary (beyond a) \<le> a"
    unfolding bounded_any_center [where a=arbitrary]
    apply simp using choice[of "\<lambda>a x. x\<in>s \<and> \<not> dist arbitrary x \<le> a"] by auto
  hence beyond:"\<And>a. beyond a \<in>s" "\<And>a. dist arbitrary (beyond a) > a"
    unfolding linorder_not_le by auto
  def x \<equiv> "helper_2 beyond"

  { fix m n ::nat assume "m<n"
    hence "dist arbitrary (x m) + 1 < dist arbitrary (x n)"
    proof(induct n)
      case 0 thus ?case by auto
    next
      case (Suc n)
      have *:"dist arbitrary (x n) + 1 < dist arbitrary (x (Suc n))"
        unfolding x_def and helper_2.simps
	using beyond(2)[of "dist arbitrary (helper_2 beyond n) + 1"] by auto
      thus ?case proof(cases "m < n")
	case True thus ?thesis using Suc and * by auto
      next
	case False hence "m = n" using Suc(2) by auto
	thus ?thesis using * by auto
      qed
    qed  } note * = this
  { fix m n ::nat assume "m\<noteq>n"
    have "1 < dist (x m) (x n)"
    proof(cases "m<n")
      case True
      hence "1 < dist arbitrary (x n) - dist arbitrary (x m)" using *[of m n] by auto
      thus ?thesis using dist_triangle [of arbitrary "x n" "x m"] by arith
    next
      case False hence "n<m" using `m\<noteq>n` by auto
      hence "1 < dist arbitrary (x m) - dist arbitrary (x n)" using *[of n m] by auto
      thus ?thesis using dist_triangle2 [of arbitrary "x m" "x n"] by arith
    qed  } note ** = this
  { fix a b assume "x a = x b" "a \<noteq> b"
    hence False using **[of a b] by auto  }
  hence "inj x" unfolding inj_on_def by auto
  moreover
  { fix n::nat
    have "x n \<in> s"
    proof(cases "n = 0")
      case True thus ?thesis unfolding x_def using beyond by auto
    next
      case False then obtain z where "n = Suc z" using not0_implies_Suc by auto
      thus ?thesis unfolding x_def using beyond by auto
    qed  }
  ultimately have "infinite (range x) \<and> range x \<subseteq> s" unfolding x_def using range_inj_infinite[of "helper_2 beyond"] using beyond(1) by auto

  then obtain l where "l\<in>s" and l:"l islimpt range x" using assms[THEN spec[where x="range x"]] by auto
  then obtain y where "x y \<noteq> l" and y:"dist (x y) l < 1/2" unfolding islimpt_approachable apply(erule_tac x="1/2" in allE) by auto
  then obtain z where "x z \<noteq> l" and z:"dist (x z) l < dist (x y) l" using l[unfolded islimpt_approachable, THEN spec[where x="dist (x y) l"]]
    unfolding dist_nz by auto
  show False using y and z and dist_triangle_half_l[of "x y" l 1 "x z"] and **[of y z] by auto
qed

lemma sequence_infinite_lemma:
  fixes l :: "'a::metric_space" (* TODO: generalize *)
  assumes "\<forall>n::nat. (f n  \<noteq> l)"  "(f ---> l) sequentially"
  shows "infinite {y. (\<exists> n. y = f n)}"
proof(rule ccontr)
  let ?A = "(\<lambda>x. dist x l) ` {y. \<exists>n. y = f n}"
  assume "\<not> infinite {y. \<exists>n. y = f n}"
  hence **:"finite ?A" "?A \<noteq> {}" by auto
  obtain k where k:"dist (f k) l = Min ?A" using Min_in[OF **] by auto
  have "0 < Min ?A" using assms(1) unfolding dist_nz unfolding Min_gr_iff[OF **] by auto
  then obtain N where "dist (f N) l < Min ?A" using assms(2)[unfolded Lim_sequentially, THEN spec[where x="Min ?A"]] by auto
  moreover have "dist (f N) l \<in> ?A" by auto
  ultimately show False using Min_le[OF **(1), of "dist (f N) l"] by auto
qed

lemma sequence_unique_limpt:
  fixes l :: "'a::metric_space" (* TODO: generalize *)
  assumes "\<forall>n::nat. (f n \<noteq> l)"  "(f ---> l) sequentially"  "l' islimpt {y.  (\<exists>n. y = f n)}"
  shows "l' = l"
proof(rule ccontr)
  def e \<equiv> "dist l' l"
  assume "l' \<noteq> l" hence "e>0" unfolding dist_nz e_def by auto
  then obtain N::nat where N:"\<forall>n\<ge>N. dist (f n) l < e / 2"
    using assms(2)[unfolded Lim_sequentially, THEN spec[where x="e/2"]] by auto
  def d \<equiv> "Min (insert (e/2) ((\<lambda>n. if dist (f n) l' = 0 then e/2 else dist (f n) l') ` {0 .. N}))"
  have "d>0" using `e>0` unfolding d_def e_def using zero_le_dist[of _ l', unfolded order_le_less] by auto
  obtain k where k:"f k \<noteq> l'"  "dist (f k) l' < d" using `d>0` and assms(3)[unfolded islimpt_approachable, THEN spec[where x="d"]] by auto
  have "k\<ge>N" using k(1)[unfolded dist_nz] using k(2)[unfolded d_def]
    by force
  hence "dist l' l < e" using N[THEN spec[where x=k]] using k(2)[unfolded d_def] and dist_triangle_half_r[of "f k" l' e l] by auto
  thus False unfolding e_def by auto
qed

lemma bolzano_weierstrass_imp_closed:
  fixes s :: "'a::metric_space set" (* TODO: can this be generalized? *)
  assumes "\<forall>t. infinite t \<and> t \<subseteq> s --> (\<exists>x \<in> s. x islimpt t)"
  shows "closed s"
proof-
  { fix x l assume as: "\<forall>n::nat. x n \<in> s" "(x ---> l) sequentially"
    hence "l \<in> s"
    proof(cases "\<forall>n. x n \<noteq> l")
      case False thus "l\<in>s" using as(1) by auto
    next
      case True note cas = this
      with as(2) have "infinite {y. \<exists>n. y = x n}" using sequence_infinite_lemma[of x l] by auto
      then obtain l' where "l'\<in>s" "l' islimpt {y. \<exists>n. y = x n}" using assms[THEN spec[where x="{y. \<exists>n. y = x n}"]] as(1) by auto
      thus "l\<in>s" using sequence_unique_limpt[of x l l'] using as cas by auto
    qed  }
  thus ?thesis unfolding closed_sequential_limits by fast
qed

text{* Hence express everything as an equivalence.   *}

lemma compact_eq_heine_borel:
  fixes s :: "'a::heine_borel set"
  shows "compact s \<longleftrightarrow>
           (\<forall>f. (\<forall>t \<in> f. open t) \<and> s \<subseteq> (\<Union> f)
               --> (\<exists>f'. f' \<subseteq> f \<and> finite f' \<and> s \<subseteq> (\<Union> f')))" (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs using compact_imp_heine_borel[of s] by blast
next
  assume ?rhs
  hence "\<forall>t. infinite t \<and> t \<subseteq> s \<longrightarrow> (\<exists>x\<in>s. x islimpt t)"
    by (blast intro: heine_borel_imp_bolzano_weierstrass[of s])
  thus ?lhs using bolzano_weierstrass_imp_bounded[of s] bolzano_weierstrass_imp_closed[of s] bounded_closed_imp_compact[of s] by blast
qed

lemma compact_eq_bolzano_weierstrass:
  fixes s :: "'a::heine_borel set"
  shows "compact s \<longleftrightarrow> (\<forall>t. infinite t \<and> t \<subseteq> s --> (\<exists>x \<in> s. x islimpt t))" (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs unfolding compact_eq_heine_borel using heine_borel_imp_bolzano_weierstrass[of s] by auto
next
  assume ?rhs thus ?lhs using bolzano_weierstrass_imp_bounded bolzano_weierstrass_imp_closed bounded_closed_imp_compact by auto
qed

lemma compact_eq_bounded_closed:
  fixes s :: "'a::heine_borel set"
  shows "compact s \<longleftrightarrow> bounded s \<and> closed s"  (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs unfolding compact_eq_bolzano_weierstrass using bolzano_weierstrass_imp_bounded bolzano_weierstrass_imp_closed by auto
next
  assume ?rhs thus ?lhs using bounded_closed_imp_compact by auto
qed

lemma compact_imp_bounded:
  fixes s :: "'a::metric_space set"
  shows "compact s ==> bounded s"
proof -
  assume "compact s"
  hence "\<forall>f. (\<forall>t\<in>f. open t) \<and> s \<subseteq> \<Union>f \<longrightarrow> (\<exists>f'\<subseteq>f. finite f' \<and> s \<subseteq> \<Union>f')"
    by (rule compact_imp_heine_borel)
  hence "\<forall>t. infinite t \<and> t \<subseteq> s \<longrightarrow> (\<exists>x \<in> s. x islimpt t)"
    using heine_borel_imp_bolzano_weierstrass[of s] by auto
  thus "bounded s"
    by (rule bolzano_weierstrass_imp_bounded)
qed

lemma compact_imp_closed:
  fixes s :: "'a::metric_space set"
  shows "compact s ==> closed s"
proof -
  assume "compact s"
  hence "\<forall>f. (\<forall>t\<in>f. open t) \<and> s \<subseteq> \<Union>f \<longrightarrow> (\<exists>f'\<subseteq>f. finite f' \<and> s \<subseteq> \<Union>f')"
    by (rule compact_imp_heine_borel)
  hence "\<forall>t. infinite t \<and> t \<subseteq> s \<longrightarrow> (\<exists>x \<in> s. x islimpt t)"
    using heine_borel_imp_bolzano_weierstrass[of s] by auto
  thus "closed s"
    by (rule bolzano_weierstrass_imp_closed)
qed

text{* In particular, some common special cases. *}

lemma compact_empty[simp]:
 "compact {}"
  unfolding compact_def
  by simp

(* TODO: can any of the next 3 lemmas be generalized to metric spaces? *)

  (* FIXME : Rename *)
lemma compact_union[intro]:
  fixes s t :: "'a::heine_borel set"
  shows "compact s \<Longrightarrow> compact t ==> compact (s \<union> t)"
  unfolding compact_eq_bounded_closed
  using bounded_Un[of s t]
  using closed_Un[of s t]
  by simp

lemma compact_inter[intro]:
  fixes s t :: "'a::heine_borel set"
  shows "compact s \<Longrightarrow> compact t ==> compact (s \<inter> t)"
  unfolding compact_eq_bounded_closed
  using bounded_Int[of s t]
  using closed_Int[of s t]
  by simp

lemma compact_inter_closed[intro]:
  fixes s t :: "'a::heine_borel set"
  shows "compact s \<Longrightarrow> closed t ==> compact (s \<inter> t)"
  unfolding compact_eq_bounded_closed
  using closed_Int[of s t]
  using bounded_subset[of "s \<inter> t" s]
  by blast

lemma closed_inter_compact[intro]:
  fixes s t :: "'a::heine_borel set"
  shows "closed s \<Longrightarrow> compact t ==> compact (s \<inter> t)"
proof-
  assume "closed s" "compact t"
  moreover
  have "s \<inter> t = t \<inter> s" by auto ultimately
  show ?thesis
    using compact_inter_closed[of t s]
    by auto
qed

lemma closed_sing [simp]:
  fixes a :: "'a::metric_space"
  shows "closed {a}"
  apply (clarsimp simp add: closed_def open_dist)
  apply (rule ccontr)
  apply (drule_tac x="dist x a" in spec)
  apply (simp add: dist_nz dist_commute)
  done

lemma finite_imp_closed:
  fixes s :: "'a::metric_space set"
  shows "finite s ==> closed s"
proof (induct set: finite)
  case empty show "closed {}" by simp
next
  case (insert x F)
  hence "closed ({x} \<union> F)" by (simp only: closed_Un closed_sing)
  thus "closed (insert x F)" by simp
qed

lemma finite_imp_compact:
  fixes s :: "'a::heine_borel set"
  shows "finite s ==> compact s"
  unfolding compact_eq_bounded_closed
  using finite_imp_closed finite_imp_bounded
  by blast

lemma compact_sing [simp]: "compact {a}"
  unfolding compact_def o_def subseq_def
  by (auto simp add: tendsto_const)

lemma compact_cball[simp]:
  fixes x :: "'a::heine_borel"
  shows "compact(cball x e)"
  using compact_eq_bounded_closed bounded_cball closed_cball
  by blast

lemma compact_frontier_bounded[intro]:
  fixes s :: "'a::heine_borel set"
  shows "bounded s ==> compact(frontier s)"
  unfolding frontier_def
  using compact_eq_bounded_closed
  by blast

lemma compact_frontier[intro]:
  fixes s :: "'a::heine_borel set"
  shows "compact s ==> compact (frontier s)"
  using compact_eq_bounded_closed compact_frontier_bounded
  by blast

lemma frontier_subset_compact:
  fixes s :: "'a::heine_borel set"
  shows "compact s ==> frontier s \<subseteq> s"
  using frontier_subset_closed compact_eq_bounded_closed
  by blast

lemma open_delete:
  fixes s :: "'a::metric_space set"
  shows "open s ==> open(s - {x})"
  using open_Diff[of s "{x}"] closed_sing
  by blast

text{* Finite intersection property. I could make it an equivalence in fact. *}

lemma compact_imp_fip:
  fixes s :: "'a::heine_borel set"
  assumes "compact s"  "\<forall>t \<in> f. closed t"
        "\<forall>f'. finite f' \<and> f' \<subseteq> f --> (s \<inter> (\<Inter> f') \<noteq> {})"
  shows "s \<inter> (\<Inter> f) \<noteq> {}"
proof
  assume as:"s \<inter> (\<Inter> f) = {}"
  hence "s \<subseteq> \<Union>op - UNIV ` f" by auto
  moreover have "Ball (op - UNIV ` f) open" using open_Diff closed_Diff using assms(2) by auto
  ultimately obtain f' where f':"f' \<subseteq> op - UNIV ` f"  "finite f'"  "s \<subseteq> \<Union>f'" using assms(1)[unfolded compact_eq_heine_borel, THEN spec[where x="(\<lambda>t. UNIV - t) ` f"]] by auto
  hence "finite (op - UNIV ` f') \<and> op - UNIV ` f' \<subseteq> f" by(auto simp add: Diff_Diff_Int)
  hence "s \<inter> \<Inter>op - UNIV ` f' \<noteq> {}" using assms(3)[THEN spec[where x="op - UNIV ` f'"]] by auto
  thus False using f'(3) unfolding subset_eq and Union_iff by blast
qed

subsection{* Bounded closed nest property (proof does not use Heine-Borel).            *}

lemma bounded_closed_nest:
  assumes "\<forall>n. closed(s n)" "\<forall>n. (s n \<noteq> {})"
  "(\<forall>m n. m \<le> n --> s n \<subseteq> s m)"  "bounded(s 0)"
  shows "\<exists>a::'a::heine_borel. \<forall>n::nat. a \<in> s(n)"
proof-
  from assms(2) obtain x where x:"\<forall>n::nat. x n \<in> s n" using choice[of "\<lambda>n x. x\<in> s n"] by auto
  from assms(4,1) have *:"compact (s 0)" using bounded_closed_imp_compact[of "s 0"] by auto

  then obtain l r where lr:"l\<in>s 0" "subseq r" "((x \<circ> r) ---> l) sequentially"
    unfolding compact_def apply(erule_tac x=x in allE)  using x using assms(3) by blast

  { fix n::nat
    { fix e::real assume "e>0"
      with lr(3) obtain N where N:"\<forall>m\<ge>N. dist ((x \<circ> r) m) l < e" unfolding Lim_sequentially by auto
      hence "dist ((x \<circ> r) (max N n)) l < e" by auto
      moreover
      have "r (max N n) \<ge> n" using lr(2) using subseq_bigger[of r "max N n"] by auto
      hence "(x \<circ> r) (max N n) \<in> s n"
	using x apply(erule_tac x=n in allE)
	using x apply(erule_tac x="r (max N n)" in allE)
	using assms(3) apply(erule_tac x=n in allE)apply( erule_tac x="r (max N n)" in allE) by auto
      ultimately have "\<exists>y\<in>s n. dist y l < e" by auto
    }
    hence "l \<in> s n" using closed_approachable[of "s n" l] assms(1) by blast
  }
  thus ?thesis by auto
qed

text{* Decreasing case does not even need compactness, just completeness.        *}

lemma decreasing_closed_nest:
  assumes "\<forall>n. closed(s n)"
          "\<forall>n. (s n \<noteq> {})"
          "\<forall>m n. m \<le> n --> s n \<subseteq> s m"
          "\<forall>e>0. \<exists>n. \<forall>x \<in> (s n). \<forall> y \<in> (s n). dist x y < e"
  shows "\<exists>a::'a::heine_borel. \<forall>n::nat. a \<in> s n"
proof-
  have "\<forall>n. \<exists> x. x\<in>s n" using assms(2) by auto
  hence "\<exists>t. \<forall>n. t n \<in> s n" using choice[of "\<lambda> n x. x \<in> s n"] by auto
  then obtain t where t: "\<forall>n. t n \<in> s n" by auto
  { fix e::real assume "e>0"
    then obtain N where N:"\<forall>x\<in>s N. \<forall>y\<in>s N. dist x y < e" using assms(4) by auto
    { fix m n ::nat assume "N \<le> m \<and> N \<le> n"
      hence "t m \<in> s N" "t n \<in> s N" using assms(3) t unfolding  subset_eq t by blast+
      hence "dist (t m) (t n) < e" using N by auto
    }
    hence "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (t m) (t n) < e" by auto
  }
  hence  "Cauchy t" unfolding cauchy_def by auto
  then obtain l where l:"(t ---> l) sequentially" using complete_univ unfolding complete_def by auto
  { fix n::nat
    { fix e::real assume "e>0"
      then obtain N::nat where N:"\<forall>n\<ge>N. dist (t n) l < e" using l[unfolded Lim_sequentially] by auto
      have "t (max n N) \<in> s n" using assms(3) unfolding subset_eq apply(erule_tac x=n in allE) apply (erule_tac x="max n N" in allE) using t by auto
      hence "\<exists>y\<in>s n. dist y l < e" apply(rule_tac x="t (max n N)" in bexI) using N by auto
    }
    hence "l \<in> s n" using closed_approachable[of "s n" l] assms(1) by auto
  }
  then show ?thesis by auto
qed

text{* Strengthen it to the intersection actually being a singleton.             *}

lemma decreasing_closed_nest_sing:
  assumes "\<forall>n. closed(s n)"
          "\<forall>n. s n \<noteq> {}"
          "\<forall>m n. m \<le> n --> s n \<subseteq> s m"
          "\<forall>e>0. \<exists>n. \<forall>x \<in> (s n). \<forall> y\<in>(s n). dist x y < e"
  shows "\<exists>a::'a::heine_borel. \<Inter> {t. (\<exists>n::nat. t = s n)} = {a}"
proof-
  obtain a where a:"\<forall>n. a \<in> s n" using decreasing_closed_nest[of s] using assms by auto
  { fix b assume b:"b \<in> \<Inter>{t. \<exists>n. t = s n}"
    { fix e::real assume "e>0"
      hence "dist a b < e" using assms(4 )using b using a by blast
    }
    hence "dist a b = 0" by (metis dist_eq_0_iff dist_nz real_less_def)
  }
  with a have "\<Inter>{t. \<exists>n. t = s n} = {a}"  by auto
  thus ?thesis by auto
qed

text{* Cauchy-type criteria for uniform convergence. *}

lemma uniformly_convergent_eq_cauchy: fixes s::"nat \<Rightarrow> 'b \<Rightarrow> 'a::heine_borel" shows
 "(\<exists>l. \<forall>e>0. \<exists>N. \<forall>n x. N \<le> n \<and> P x --> dist(s n x)(l x) < e) \<longleftrightarrow>
  (\<forall>e>0. \<exists>N. \<forall>m n x. N \<le> m \<and> N \<le> n \<and> P x  --> dist (s m x) (s n x) < e)" (is "?lhs = ?rhs")
proof(rule)
  assume ?lhs
  then obtain l where l:"\<forall>e>0. \<exists>N. \<forall>n x. N \<le> n \<and> P x \<longrightarrow> dist (s n x) (l x) < e" by auto
  { fix e::real assume "e>0"
    then obtain N::nat where N:"\<forall>n x. N \<le> n \<and> P x \<longrightarrow> dist (s n x) (l x) < e / 2" using l[THEN spec[where x="e/2"]] by auto
    { fix n m::nat and x::"'b" assume "N \<le> m \<and> N \<le> n \<and> P x"
      hence "dist (s m x) (s n x) < e"
	using N[THEN spec[where x=m], THEN spec[where x=x]]
	using N[THEN spec[where x=n], THEN spec[where x=x]]
	using dist_triangle_half_l[of "s m x" "l x" e "s n x"] by auto  }
    hence "\<exists>N. \<forall>m n x. N \<le> m \<and> N \<le> n \<and> P x  --> dist (s m x) (s n x) < e"  by auto  }
  thus ?rhs by auto
next
  assume ?rhs
  hence "\<forall>x. P x \<longrightarrow> Cauchy (\<lambda>n. s n x)" unfolding cauchy_def apply auto by (erule_tac x=e in allE)auto
  then obtain l where l:"\<forall>x. P x \<longrightarrow> ((\<lambda>n. s n x) ---> l x) sequentially" unfolding convergent_eq_cauchy[THEN sym]
    using choice[of "\<lambda>x l. P x \<longrightarrow> ((\<lambda>n. s n x) ---> l) sequentially"] by auto
  { fix e::real assume "e>0"
    then obtain N where N:"\<forall>m n x. N \<le> m \<and> N \<le> n \<and> P x \<longrightarrow> dist (s m x) (s n x) < e/2"
      using `?rhs`[THEN spec[where x="e/2"]] by auto
    { fix x assume "P x"
      then obtain M where M:"\<forall>n\<ge>M. dist (s n x) (l x) < e/2"
	using l[THEN spec[where x=x], unfolded Lim_sequentially] using `e>0` by(auto elim!: allE[where x="e/2"])
      fix n::nat assume "n\<ge>N"
      hence "dist(s n x)(l x) < e"  using `P x`and N[THEN spec[where x=n], THEN spec[where x="N+M"], THEN spec[where x=x]]
	using M[THEN spec[where x="N+M"]] and dist_triangle_half_l[of "s n x" "s (N+M) x" e "l x"] by (auto simp add: dist_commute)  }
    hence "\<exists>N. \<forall>n x. N \<le> n \<and> P x \<longrightarrow> dist(s n x)(l x) < e" by auto }
  thus ?lhs by auto
qed

lemma uniformly_cauchy_imp_uniformly_convergent:
  fixes s :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::heine_borel"
  assumes "\<forall>e>0.\<exists>N. \<forall>m (n::nat) x. N \<le> m \<and> N \<le> n \<and> P x --> dist(s m x)(s n x) < e"
          "\<forall>x. P x --> (\<forall>e>0. \<exists>N. \<forall>n. N \<le> n --> dist(s n x)(l x) < e)"
  shows "\<forall>e>0. \<exists>N. \<forall>n x. N \<le> n \<and> P x --> dist(s n x)(l x) < e"
proof-
  obtain l' where l:"\<forall>e>0. \<exists>N. \<forall>n x. N \<le> n \<and> P x \<longrightarrow> dist (s n x) (l' x) < e"
    using assms(1) unfolding uniformly_convergent_eq_cauchy[THEN sym] by auto
  moreover
  { fix x assume "P x"
    hence "l x = l' x" using Lim_unique[OF trivial_limit_sequentially, of "\<lambda>n. s n x" "l x" "l' x"]
      using l and assms(2) unfolding Lim_sequentially by blast  }
  ultimately show ?thesis by auto
qed

subsection{* Define continuity over a net to take in restrictions of the set. *}

definition
  continuous :: "'a::metric_space net \<Rightarrow> ('a \<Rightarrow> 'b::metric_space) \<Rightarrow> bool" where
  "continuous net f \<longleftrightarrow> (f ---> f(netlimit net)) net"
  (* FIXME: generalize 'b to topological_space *)

lemma continuous_trivial_limit:
 "trivial_limit net ==> continuous net f"
  unfolding continuous_def tendsto_iff trivial_limit_eq by auto

lemma continuous_within: "continuous (at x within s) f \<longleftrightarrow> (f ---> f(x)) (at x within s)"
  unfolding continuous_def
  unfolding tendsto_iff
  using netlimit_within[of x s]
  by (cases "trivial_limit (at x within s)") (auto simp add: trivial_limit_eventually)

lemma continuous_at: "continuous (at x) f \<longleftrightarrow> (f ---> f(x)) (at x)"
  using continuous_within [of x UNIV f] by (simp add: within_UNIV)

lemma continuous_at_within:
  fixes x :: "'a::perfect_space"
  assumes "continuous (at x) f"  shows "continuous (at x within s) f"
  (* FIXME: generalize *)
proof(cases "x islimpt s")
  case True show ?thesis using assms unfolding continuous_def and netlimit_at
    using Lim_at_within[of f "f x" "at x" s]
    unfolding netlimit_within[unfolded trivial_limit_within not_not, OF True] by blast
next
  case False thus ?thesis unfolding continuous_def and netlimit_at
    unfolding Lim and trivial_limit_within by auto
qed

text{* Derive the epsilon-delta forms, which we often use as "definitions" *}

lemma continuous_within_eps_delta:
  "continuous (at x within s) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. \<forall>x'\<in> s.  dist x' x < d --> dist (f x') (f x) < e)"
  unfolding continuous_within and Lim_within
  apply auto unfolding dist_nz[THEN sym] apply(auto elim!:allE) apply(rule_tac x=d in exI) by auto

lemma continuous_at_eps_delta: "continuous (at x) f \<longleftrightarrow>  (\<forall>e>0. \<exists>d>0.
                           \<forall>x'. dist x' x < d --> dist(f x')(f x) < e)"
  using continuous_within_eps_delta[of x UNIV f]
  unfolding within_UNIV by blast

text{* Versions in terms of open balls. *}

lemma continuous_within_ball:
 "continuous (at x within s) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0.
                            f ` (ball x d \<inter> s) \<subseteq> ball (f x) e)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  { fix e::real assume "e>0"
    then obtain d where d: "d>0" "\<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (f x) < e"
      using `?lhs`[unfolded continuous_within Lim_within] by auto
    { fix y assume "y\<in>f ` (ball x d \<inter> s)"
      hence "y \<in> ball (f x) e" using d(2) unfolding dist_nz[THEN sym]
	apply (auto simp add: dist_commute mem_ball) apply(erule_tac x=xa in ballE) apply auto using `e>0` by auto
    }
    hence "\<exists>d>0. f ` (ball x d \<inter> s) \<subseteq> ball (f x) e" using `d>0` unfolding subset_eq ball_def by (auto simp add: dist_commute)  }
  thus ?rhs by auto
next
  assume ?rhs thus ?lhs unfolding continuous_within Lim_within ball_def subset_eq
    apply (auto simp add: dist_commute) apply(erule_tac x=e in allE) by auto
qed

lemma continuous_at_ball:
  "continuous (at x) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. f ` (ball x d) \<subseteq> ball (f x) e)" (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs unfolding continuous_at Lim_at subset_eq Ball_def Bex_def image_iff mem_ball
    apply auto apply(erule_tac x=e in allE) apply auto apply(rule_tac x=d in exI) apply auto apply(erule_tac x=xa in allE) apply (auto simp add: dist_commute dist_nz)
    unfolding dist_nz[THEN sym] by auto
next
  assume ?rhs thus ?lhs unfolding continuous_at Lim_at subset_eq Ball_def Bex_def image_iff mem_ball
    apply auto apply(erule_tac x=e in allE) apply auto apply(rule_tac x=d in exI) apply auto apply(erule_tac x="f xa" in allE) by (auto simp add: dist_commute dist_nz)
qed

text{* For setwise continuity, just start from the epsilon-delta definitions. *}

definition
  continuous_on :: "'a::metric_space set \<Rightarrow> ('a \<Rightarrow> 'b::metric_space) \<Rightarrow> bool" where
  "continuous_on s f \<longleftrightarrow> (\<forall>x \<in> s. \<forall>e>0. \<exists>d::real>0. \<forall>x' \<in> s. dist x' x < d --> dist (f x') (f x) < e)"


definition
  uniformly_continuous_on ::
    "'a::metric_space set \<Rightarrow> ('a \<Rightarrow> 'b::metric_space) \<Rightarrow> bool" where
  "uniformly_continuous_on s f \<longleftrightarrow>
        (\<forall>e>0. \<exists>d>0. \<forall>x\<in>s. \<forall> x'\<in>s. dist x' x < d
                           --> dist (f x') (f x) < e)"

text{* Some simple consequential lemmas. *}

lemma uniformly_continuous_imp_continuous:
 " uniformly_continuous_on s f ==> continuous_on s f"
  unfolding uniformly_continuous_on_def continuous_on_def by blast

lemma continuous_at_imp_continuous_within:
 "continuous (at x) f ==> continuous (at x within s) f"
  unfolding continuous_within continuous_at using Lim_at_within by auto

lemma continuous_at_imp_continuous_on: assumes "(\<forall>x \<in> s. continuous (at x) f)"
  shows "continuous_on s f"
proof(simp add: continuous_at continuous_on_def, rule, rule, rule)
  fix x and e::real assume "x\<in>s" "e>0"
  hence "eventually (\<lambda>xa. dist (f xa) (f x) < e) (at x)" using assms unfolding continuous_at tendsto_iff by auto
  then obtain d where d:"d>0" "\<forall>xa. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (f x) < e" unfolding eventually_at by auto
  { fix x' assume "\<not> 0 < dist x' x"
    hence "x=x'"
      using dist_nz[of x' x] by auto
    hence "dist (f x') (f x) < e" using `e>0` by auto
  }
  thus "\<exists>d>0. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e" using d by auto
qed

lemma continuous_on_eq_continuous_within:
 "continuous_on s f \<longleftrightarrow> (\<forall>x \<in> s. continuous (at x within s) f)" (is "?lhs = ?rhs")
proof
  assume ?rhs
  { fix x assume "x\<in>s"
    fix e::real assume "e>0"
    assume "\<exists>d>0. \<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (f x) < e"
    then obtain d where "d>0" and d:"\<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (f x) < e" by auto
    { fix x' assume as:"x'\<in>s" "dist x' x < d"
      hence "dist (f x') (f x) < e" using `e>0` d `x'\<in>s` dist_eq_0_iff[of x' x] zero_le_dist[of x' x] as(2) by (metis dist_eq_0_iff dist_nz) }
    hence "\<exists>d>0. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e" using `d>0` by auto
  }
  thus ?lhs using `?rhs` unfolding continuous_on_def continuous_within Lim_within by auto
next
  assume ?lhs
  thus ?rhs unfolding continuous_on_def continuous_within Lim_within by blast
qed

lemma continuous_on:
 "continuous_on s f \<longleftrightarrow> (\<forall>x \<in> s. (f ---> f(x)) (at x within s))"
  by (auto simp add: continuous_on_eq_continuous_within continuous_within)

lemma continuous_on_eq_continuous_at:
 "open s ==> (continuous_on s f \<longleftrightarrow> (\<forall>x \<in> s. continuous (at x) f))"
  by (auto simp add: continuous_on continuous_at Lim_within_open)

lemma continuous_within_subset:
 "continuous (at x within s) f \<Longrightarrow> t \<subseteq> s
             ==> continuous (at x within t) f"
  unfolding continuous_within by(metis Lim_within_subset)

lemma continuous_on_subset:
 "continuous_on s f \<Longrightarrow> t \<subseteq> s ==> continuous_on t f"
  unfolding continuous_on by (metis subset_eq Lim_within_subset)

lemma continuous_on_interior:
 "continuous_on s f \<Longrightarrow> x \<in> interior s ==> continuous (at x) f"
unfolding interior_def
apply simp
by (meson continuous_on_eq_continuous_at continuous_on_subset)

lemma continuous_on_eq:
 "(\<forall>x \<in> s. f x = g x) \<Longrightarrow> continuous_on s f
           ==> continuous_on s g"
  by (simp add: continuous_on_def)

text{* Characterization of various kinds of continuity in terms of sequences.  *}

lemma continuous_within_sequentially:
 "continuous (at a within s) f \<longleftrightarrow>
                (\<forall>x. (\<forall>n::nat. x n \<in> s) \<and> (x ---> a) sequentially
                     --> ((f o x) ---> f a) sequentially)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  { fix x::"nat \<Rightarrow> 'a" assume x:"\<forall>n. x n \<in> s" "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (x n) a < e"
    fix e::real assume "e>0"
    from `?lhs` obtain d where "d>0" and d:"\<forall>x\<in>s. 0 < dist x a \<and> dist x a < d \<longrightarrow> dist (f x) (f a) < e" unfolding continuous_within Lim_within using `e>0` by auto
    from x(2) `d>0` obtain N where N:"\<forall>n\<ge>N. dist (x n) a < d" by auto
    hence "\<exists>N. \<forall>n\<ge>N. dist ((f \<circ> x) n) (f a) < e"
      apply(rule_tac  x=N in exI) using N d  apply auto using x(1)
      apply(erule_tac x=n in allE) apply(erule_tac x=n in allE)
      apply(erule_tac x="x n" in ballE)  apply auto unfolding dist_nz[THEN sym] apply auto using `e>0` by auto
  }
  thus ?rhs unfolding continuous_within unfolding Lim_sequentially by simp
next
  assume ?rhs
  { fix e::real assume "e>0"
    assume "\<not> (\<exists>d>0. \<forall>x\<in>s. 0 < dist x a \<and> dist x a < d \<longrightarrow> dist (f x) (f a) < e)"
    hence "\<forall>d. \<exists>x. d>0 \<longrightarrow> x\<in>s \<and> (0 < dist x a \<and> dist x a < d \<and> \<not> dist (f x) (f a) < e)" by blast
    then obtain x where x:"\<forall>d>0. x d \<in> s \<and> (0 < dist (x d) a \<and> dist (x d) a < d \<and> \<not> dist (f (x d)) (f a) < e)"
      using choice[of "\<lambda>d x.0<d \<longrightarrow> x\<in>s \<and> (0 < dist x a \<and> dist x a < d \<and> \<not> dist (f x) (f a) < e)"] by auto
    { fix d::real assume "d>0"
      hence "\<exists>N::nat. inverse (real (N + 1)) < d" using real_arch_inv[of d] by (auto, rule_tac x="n - 1" in exI)auto
      then obtain N::nat where N:"inverse (real (N + 1)) < d" by auto
      { fix n::nat assume n:"n\<ge>N"
	hence "dist (x (inverse (real (n + 1)))) a < inverse (real (n + 1))" using x[THEN spec[where x="inverse (real (n + 1))"]] by auto
	moreover have "inverse (real (n + 1)) < d" using N n by (auto, metis Suc_le_mono le_SucE less_imp_inverse_less nat_le_real_less order_less_trans real_of_nat_Suc real_of_nat_Suc_gt_zero)
	ultimately have "dist (x (inverse (real (n + 1)))) a < d" by auto
      }
      hence "\<exists>N::nat. \<forall>n\<ge>N. dist (x (inverse (real (n + 1)))) a < d" by auto
    }
    hence "(\<forall>n::nat. x (inverse (real (n + 1))) \<in> s) \<and> (\<forall>e>0. \<exists>N::nat. \<forall>n\<ge>N. dist (x (inverse (real (n + 1)))) a < e)" using x by auto
    hence "\<forall>e>0. \<exists>N::nat. \<forall>n\<ge>N. dist (f (x (inverse (real (n + 1))))) (f a) < e"  using `?rhs`[THEN spec[where x="\<lambda>n::nat. x (inverse (real (n+1)))"], unfolded Lim_sequentially] by auto
    hence "False" apply(erule_tac x=e in allE) using `e>0` using x by auto
  }
  thus ?lhs  unfolding continuous_within unfolding Lim_within unfolding Lim_sequentially by blast
qed

lemma continuous_at_sequentially:
 "continuous (at a) f \<longleftrightarrow> (\<forall>x. (x ---> a) sequentially
                  --> ((f o x) ---> f a) sequentially)"
  using continuous_within_sequentially[of a UNIV f] unfolding within_UNIV by auto

lemma continuous_on_sequentially:
 "continuous_on s f \<longleftrightarrow>  (\<forall>x. \<forall>a \<in> s. (\<forall>n. x(n) \<in> s) \<and> (x ---> a) sequentially
                    --> ((f o x) ---> f(a)) sequentially)" (is "?lhs = ?rhs")
proof
  assume ?rhs thus ?lhs using continuous_within_sequentially[of _ s f] unfolding continuous_on_eq_continuous_within by auto
next
  assume ?lhs thus ?rhs unfolding continuous_on_eq_continuous_within using continuous_within_sequentially[of _ s f] by auto
qed

lemma uniformly_continuous_on_sequentially:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  shows "uniformly_continuous_on s f \<longleftrightarrow> (\<forall>x y. (\<forall>n. x n \<in> s) \<and> (\<forall>n. y n \<in> s) \<and>
                    ((\<lambda>n. x n - y n) ---> 0) sequentially
                    \<longrightarrow> ((\<lambda>n. f(x n) - f(y n)) ---> 0) sequentially)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  { fix x y assume x:"\<forall>n. x n \<in> s" and y:"\<forall>n. y n \<in> s" and xy:"((\<lambda>n. x n - y n) ---> 0) sequentially"
    { fix e::real assume "e>0"
      then obtain d where "d>0" and d:"\<forall>x\<in>s. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e"
	using `?lhs`[unfolded uniformly_continuous_on_def, THEN spec[where x=e]] by auto
      obtain N where N:"\<forall>n\<ge>N. norm (x n - y n - 0) < d" using xy[unfolded Lim_sequentially dist_norm] and `d>0` by auto
      { fix n assume "n\<ge>N"
	hence "norm (f (x n) - f (y n) - 0) < e"
	  using N[THEN spec[where x=n]] using d[THEN bspec[where x="x n"], THEN bspec[where x="y n"]] using x and y
	  unfolding dist_commute and dist_norm by simp  }
      hence "\<exists>N. \<forall>n\<ge>N. norm (f (x n) - f (y n) - 0) < e"  by auto  }
    hence "((\<lambda>n. f(x n) - f(y n)) ---> 0) sequentially" unfolding Lim_sequentially and dist_norm by auto  }
  thus ?rhs by auto
next
  assume ?rhs
  { assume "\<not> ?lhs"
    then obtain e where "e>0" "\<forall>d>0. \<exists>x\<in>s. \<exists>x'\<in>s. dist x' x < d \<and> \<not> dist (f x') (f x) < e" unfolding uniformly_continuous_on_def by auto
    then obtain fa where fa:"\<forall>x.  0 < x \<longrightarrow> fst (fa x) \<in> s \<and> snd (fa x) \<in> s \<and> dist (fst (fa x)) (snd (fa x)) < x \<and> \<not> dist (f (fst (fa x))) (f (snd (fa x))) < e"
      using choice[of "\<lambda>d x. d>0 \<longrightarrow> fst x \<in> s \<and> snd x \<in> s \<and> dist (snd x) (fst x) < d \<and> \<not> dist (f (snd x)) (f (fst x)) < e"] unfolding Bex_def
      by (auto simp add: dist_commute)
    def x \<equiv> "\<lambda>n::nat. fst (fa (inverse (real n + 1)))"
    def y \<equiv> "\<lambda>n::nat. snd (fa (inverse (real n + 1)))"
    have xyn:"\<forall>n. x n \<in> s \<and> y n \<in> s" and xy0:"\<forall>n. dist (x n) (y n) < inverse (real n + 1)" and fxy:"\<forall>n. \<not> dist (f (x n)) (f (y n)) < e"
      unfolding x_def and y_def using fa by auto
    have 1:"\<And>(x::'a) y. dist (x - y) 0 = dist x y" unfolding dist_norm by auto
    have 2:"\<And>(x::'b) y. dist (x - y) 0 = dist x y" unfolding dist_norm by auto
    { fix e::real assume "e>0"
      then obtain N::nat where "N \<noteq> 0" and N:"0 < inverse (real N) \<and> inverse (real N) < e" unfolding real_arch_inv[of e]   by auto
      { fix n::nat assume "n\<ge>N"
	hence "inverse (real n + 1) < inverse (real N)" using real_of_nat_ge_zero and `N\<noteq>0` by auto
	also have "\<dots> < e" using N by auto
	finally have "inverse (real n + 1) < e" by auto
	hence "dist (x n - y n) 0 < e" unfolding 1 using xy0[THEN spec[where x=n]] by auto  }
      hence "\<exists>N. \<forall>n\<ge>N. dist (x n - y n) 0 < e" by auto  }
    hence "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (f (x n) - f (y n)) 0 < e" using `?rhs`[THEN spec[where x=x], THEN spec[where x=y]] and xyn unfolding Lim_sequentially by auto
    hence False unfolding 2 using fxy and `e>0` by auto  }
  thus ?lhs unfolding uniformly_continuous_on_def by blast
qed

text{* The usual transformation theorems. *}

lemma continuous_transform_within:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "0 < d" "x \<in> s" "\<forall>x' \<in> s. dist x' x < d --> f x' = g x'"
          "continuous (at x within s) f"
  shows "continuous (at x within s) g"
proof-
  { fix e::real assume "e>0"
    then obtain d' where d':"d'>0" "\<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d' \<longrightarrow> dist (f xa) (f x) < e" using assms(4) unfolding continuous_within Lim_within by auto
    { fix x' assume "x'\<in>s" "0 < dist x' x" "dist x' x < (min d d')"
      hence "dist (f x') (g x) < e" using assms(2,3) apply(erule_tac x=x in ballE) using d' by auto  }
    hence "\<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < (min d d') \<longrightarrow> dist (f xa) (g x) < e" by blast
    hence "\<exists>d>0. \<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (g x) < e" using `d>0` `d'>0` by(rule_tac x="min d d'" in exI)auto  }
  hence "(f ---> g x) (at x within s)" unfolding Lim_within using assms(1) by auto
  thus ?thesis unfolding continuous_within using Lim_transform_within[of d s x f g "g x"] using assms by blast
qed

lemma continuous_transform_at:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "0 < d" "\<forall>x'. dist x' x < d --> f x' = g x'"
          "continuous (at x) f"
  shows "continuous (at x) g"
proof-
  { fix e::real assume "e>0"
    then obtain d' where d':"d'>0" "\<forall>xa. 0 < dist xa x \<and> dist xa x < d' \<longrightarrow> dist (f xa) (f x) < e" using assms(3) unfolding continuous_at Lim_at by auto
    { fix x' assume "0 < dist x' x" "dist x' x < (min d d')"
      hence "dist (f x') (g x) < e" using assms(2) apply(erule_tac x=x in allE) using d' by auto
    }
    hence "\<forall>xa. 0 < dist xa x \<and> dist xa x < (min d d') \<longrightarrow> dist (f xa) (g x) < e" by blast
    hence "\<exists>d>0. \<forall>xa. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (g x) < e" using `d>0` `d'>0` by(rule_tac x="min d d'" in exI)auto
  }
  hence "(f ---> g x) (at x)" unfolding Lim_at using assms(1) by auto
  thus ?thesis unfolding continuous_at using Lim_transform_at[of d x f g "g x"] using assms by blast
qed

text{* Combination results for pointwise continuity. *}

lemma continuous_const: "continuous net (\<lambda>x. c)"
  by (auto simp add: continuous_def Lim_const)

lemma continuous_cmul:
  fixes f :: "'a::metric_space \<Rightarrow> real ^ 'n::finite"
  shows "continuous net f ==> continuous net (\<lambda>x. c *\<^sub>R f x)"
  by (auto simp add: continuous_def Lim_cmul)

lemma continuous_neg:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "continuous net f ==> continuous net (\<lambda>x. -(f x))"
  by (auto simp add: continuous_def Lim_neg)

lemma continuous_add:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "continuous net f \<Longrightarrow> continuous net g \<Longrightarrow> continuous net (\<lambda>x. f x + g x)"
  by (auto simp add: continuous_def Lim_add)

lemma continuous_sub:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "continuous net f \<Longrightarrow> continuous net g \<Longrightarrow> continuous net (\<lambda>x. f x - g x)"
  by (auto simp add: continuous_def Lim_sub)

text{* Same thing for setwise continuity. *}

lemma continuous_on_const:
 "continuous_on s (\<lambda>x. c)"
  unfolding continuous_on_eq_continuous_within using continuous_const by blast

lemma continuous_on_cmul:
  fixes f :: "'a::metric_space \<Rightarrow> real ^ _"
  shows "continuous_on s f ==>  continuous_on s (\<lambda>x. c *\<^sub>R (f x))"
  unfolding continuous_on_eq_continuous_within using continuous_cmul by blast

lemma continuous_on_neg:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. - f x)"
  unfolding continuous_on_eq_continuous_within using continuous_neg by blast

lemma continuous_on_add:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "continuous_on s f \<Longrightarrow> continuous_on s g
           \<Longrightarrow> continuous_on s (\<lambda>x. f x + g x)"
  unfolding continuous_on_eq_continuous_within using continuous_add by blast

lemma continuous_on_sub:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "continuous_on s f \<Longrightarrow> continuous_on s g
           \<Longrightarrow> continuous_on s (\<lambda>x. f x - g x)"
  unfolding continuous_on_eq_continuous_within using continuous_sub by blast

text{* Same thing for uniform continuity, using sequential formulations. *}

lemma uniformly_continuous_on_const:
 "uniformly_continuous_on s (\<lambda>x. c)"
  unfolding uniformly_continuous_on_def by simp

lemma uniformly_continuous_on_cmul:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real ^ _"
  assumes "uniformly_continuous_on s f"
  shows "uniformly_continuous_on s (\<lambda>x. c *\<^sub>R f(x))"
proof-
  { fix x y assume "((\<lambda>n. f (x n) - f (y n)) ---> 0) sequentially"
    hence "((\<lambda>n. c *\<^sub>R f (x n) - c *\<^sub>R f (y n)) ---> 0) sequentially"
      using Lim_cmul[of "(\<lambda>n. f (x n) - f (y n))" 0 sequentially c]
      unfolding scaleR_zero_right scaleR_right_diff_distrib by auto
  }
  thus ?thesis using assms unfolding uniformly_continuous_on_sequentially by auto
qed

lemma dist_minus:
  fixes x y :: "'a::real_normed_vector"
  shows "dist (- x) (- y) = dist x y"
  unfolding dist_norm minus_diff_minus norm_minus_cancel ..

lemma uniformly_continuous_on_neg:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "uniformly_continuous_on s f
         ==> uniformly_continuous_on s (\<lambda>x. -(f x))"
  unfolding uniformly_continuous_on_def dist_minus .

lemma uniformly_continuous_on_add:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector" (* FIXME: generalize 'a *)
  assumes "uniformly_continuous_on s f" "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. f x + g x)"
proof-
  {  fix x y assume "((\<lambda>n. f (x n) - f (y n)) ---> 0) sequentially"
                    "((\<lambda>n. g (x n) - g (y n)) ---> 0) sequentially"
    hence "((\<lambda>xa. f (x xa) - f (y xa) + (g (x xa) - g (y xa))) ---> 0 + 0) sequentially"
      using Lim_add[of "\<lambda> n. f (x n) - f (y n)" 0  sequentially "\<lambda> n. g (x n) - g (y n)" 0] by auto
    hence "((\<lambda>n. f (x n) + g (x n) - (f (y n) + g (y n))) ---> 0) sequentially" unfolding Lim_sequentially and add_diff_add [symmetric] by auto  }
  thus ?thesis using assms unfolding uniformly_continuous_on_sequentially by auto
qed

lemma uniformly_continuous_on_sub:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector" (* FIXME: generalize 'a *)
  shows "uniformly_continuous_on s f \<Longrightarrow> uniformly_continuous_on s g
           ==> uniformly_continuous_on s  (\<lambda>x. f x - g x)"
  unfolding ab_diff_minus
  using uniformly_continuous_on_add[of s f "\<lambda>x. - g x"]
  using uniformly_continuous_on_neg[of s g] by auto

text{* Identity function is continuous in every sense. *}

lemma continuous_within_id:
 "continuous (at a within s) (\<lambda>x. x)"
  unfolding continuous_within Lim_within by auto

lemma continuous_at_id:
 "continuous (at a) (\<lambda>x. x)"
  unfolding continuous_at Lim_at by auto

lemma continuous_on_id:
 "continuous_on s (\<lambda>x. x)"
  unfolding continuous_on Lim_within by auto

lemma uniformly_continuous_on_id:
 "uniformly_continuous_on s (\<lambda>x. x)"
  unfolding uniformly_continuous_on_def by auto

text{* Continuity of all kinds is preserved under composition. *}

lemma continuous_within_compose:
  assumes "continuous (at x within s) f"   "continuous (at (f x) within f ` s) g"
  shows "continuous (at x within s) (g o f)"
proof-
  { fix e::real assume "e>0"
    with assms(2)[unfolded continuous_within Lim_within] obtain d  where "d>0" and d:"\<forall>xa\<in>f ` s. 0 < dist xa (f x) \<and> dist xa (f x) < d \<longrightarrow> dist (g xa) (g (f x)) < e" by auto
    from assms(1)[unfolded continuous_within Lim_within] obtain d' where "d'>0" and d':"\<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d' \<longrightarrow> dist (f xa) (f x) < d" using `d>0` by auto
    { fix y assume as:"y\<in>s"  "0 < dist y x"  "dist y x < d'"
      hence "dist (f y) (f x) < d" using d'[THEN bspec[where x=y]] by (auto simp add:dist_commute)
      hence "dist (g (f y)) (g (f x)) < e" using as(1) d[THEN bspec[where x="f y"]] unfolding dist_nz[THEN sym] using `e>0` by auto   }
    hence "\<exists>d>0. \<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (g (f xa)) (g (f x)) < e" using `d'>0` by auto  }
  thus ?thesis unfolding continuous_within Lim_within by auto
qed

lemma continuous_at_compose:
  assumes "continuous (at x) f"  "continuous (at (f x)) g"
  shows "continuous (at x) (g o f)"
proof-
  have " continuous (at (f x) within range f) g" using assms(2) using continuous_within_subset[of "f x" UNIV g "range f", unfolded within_UNIV] by auto
  thus ?thesis using assms(1) using continuous_within_compose[of x UNIV f g, unfolded within_UNIV] by auto
qed

lemma continuous_on_compose:
 "continuous_on s f \<Longrightarrow> continuous_on (f ` s) g \<Longrightarrow> continuous_on s (g o f)"
  unfolding continuous_on_eq_continuous_within using continuous_within_compose[of _ s f g] by auto

lemma uniformly_continuous_on_compose:
  assumes "uniformly_continuous_on s f"  "uniformly_continuous_on (f ` s) g"
  shows "uniformly_continuous_on s (g o f)"
proof-
  { fix e::real assume "e>0"
    then obtain d where "d>0" and d:"\<forall>x\<in>f ` s. \<forall>x'\<in>f ` s. dist x' x < d \<longrightarrow> dist (g x') (g x) < e" using assms(2) unfolding uniformly_continuous_on_def by auto
    obtain d' where "d'>0" "\<forall>x\<in>s. \<forall>x'\<in>s. dist x' x < d' \<longrightarrow> dist (f x') (f x) < d" using `d>0` using assms(1) unfolding uniformly_continuous_on_def by auto
    hence "\<exists>d>0. \<forall>x\<in>s. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist ((g \<circ> f) x') ((g \<circ> f) x) < e" using `d>0` using d by auto  }
  thus ?thesis using assms unfolding uniformly_continuous_on_def by auto
qed

text{* Continuity in terms of open preimages. *}

lemma continuous_at_open:
 "continuous (at x) f \<longleftrightarrow> (\<forall>t. open t \<and> f x \<in> t --> (\<exists>s. open s \<and> x \<in> s \<and> (\<forall>x' \<in> s. (f x') \<in> t)))" (is "?lhs = ?rhs")
proof
  assume ?lhs
  { fix t assume as: "open t" "f x \<in> t"
    then obtain e where "e>0" and e:"ball (f x) e \<subseteq> t" unfolding open_contains_ball by auto

    obtain d where "d>0" and d:"\<forall>y. 0 < dist y x \<and> dist y x < d \<longrightarrow> dist (f y) (f x) < e" using `e>0` using `?lhs`[unfolded continuous_at Lim_at open_dist] by auto

    have "open (ball x d)" using open_ball by auto
    moreover have "x \<in> ball x d" unfolding centre_in_ball using `d>0` by simp
    moreover
    { fix x' assume "x'\<in>ball x d" hence "f x' \<in> t"
	using e[unfolded subset_eq Ball_def mem_ball, THEN spec[where x="f x'"]]    d[THEN spec[where x=x']]
	unfolding mem_ball apply (auto simp add: dist_commute)
	unfolding dist_nz[THEN sym] using as(2) by auto  }
    hence "\<forall>x'\<in>ball x d. f x' \<in> t" by auto
    ultimately have "\<exists>s. open s \<and> x \<in> s \<and> (\<forall>x'\<in>s. f x' \<in> t)"
      apply(rule_tac x="ball x d" in exI) by simp  }
  thus ?rhs by auto
next
  assume ?rhs
  { fix e::real assume "e>0"
    then obtain s where s: "open s"  "x \<in> s"  "\<forall>x'\<in>s. f x' \<in> ball (f x) e" using `?rhs`[unfolded continuous_at Lim_at, THEN spec[where x="ball (f x) e"]]
      unfolding centre_in_ball[of "f x" e, THEN sym] by auto
    then obtain d where "d>0" and d:"ball x d \<subseteq> s" unfolding open_contains_ball by auto
    { fix y assume "0 < dist y x \<and> dist y x < d"
      hence "dist (f y) (f x) < e" using d[unfolded subset_eq Ball_def mem_ball, THEN spec[where x=y]]
	using s(3)[THEN bspec[where x=y], unfolded mem_ball] by (auto simp add: dist_commute)  }
    hence "\<exists>d>0. \<forall>xa. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (f x) < e" using `d>0` by auto  }
  thus ?lhs unfolding continuous_at Lim_at by auto
qed

lemma continuous_on_open:
 "continuous_on s f \<longleftrightarrow>
        (\<forall>t. openin (subtopology euclidean (f ` s)) t
            --> openin (subtopology euclidean s) {x \<in> s. f x \<in> t})" (is "?lhs = ?rhs")
proof
  assume ?lhs
  { fix t assume as:"openin (subtopology euclidean (f ` s)) t"
    have "{x \<in> s. f x \<in> t} \<subseteq> s" using as[unfolded openin_euclidean_subtopology_iff] by auto
    moreover
    { fix x assume as':"x\<in>{x \<in> s. f x \<in> t}"
      then obtain e where e: "e>0" "\<forall>x'\<in>f ` s. dist x' (f x) < e \<longrightarrow> x' \<in> t" using as[unfolded openin_euclidean_subtopology_iff, THEN conjunct2, THEN bspec[where x="f x"]] by auto
      from this(1) obtain d where d: "d>0" "\<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (f x) < e" using `?lhs`[unfolded continuous_on Lim_within, THEN bspec[where x=x]] using as' by auto
      have "\<exists>e>0. \<forall>x'\<in>s. dist x' x < e \<longrightarrow> x' \<in> {x \<in> s. f x \<in> t}" using d e unfolding dist_nz[THEN sym] by (rule_tac x=d in exI, auto)  }
    ultimately have "openin (subtopology euclidean s) {x \<in> s. f x \<in> t}" unfolding openin_euclidean_subtopology_iff by auto  }
  thus ?rhs unfolding continuous_on Lim_within using openin by auto
next
  assume ?rhs
  { fix e::real and x assume "x\<in>s" "e>0"
    { fix xa x' assume "dist (f xa) (f x) < e" "xa \<in> s" "x' \<in> s" "dist (f xa) (f x') < e - dist (f xa) (f x)"
      hence "dist (f x') (f x) < e" using dist_triangle[of "f x'" "f x" "f xa"]
	by (auto simp add: dist_commute)  }
    hence "ball (f x) e \<inter> f ` s \<subseteq> f ` s \<and> (\<forall>xa\<in>ball (f x) e \<inter> f ` s. \<exists>ea>0. \<forall>x'\<in>f ` s. dist x' xa < ea \<longrightarrow> x' \<in> ball (f x) e \<inter> f ` s)" apply auto
      apply(rule_tac x="e - dist (f xa) (f x)" in exI) using `e>0` by (auto simp add: dist_commute)
    hence "\<forall>xa\<in>{xa \<in> s. f xa \<in> ball (f x) e \<inter> f ` s}. \<exists>ea>0. \<forall>x'\<in>s. dist x' xa < ea \<longrightarrow> x' \<in> {xa \<in> s. f xa \<in> ball (f x) e \<inter> f ` s}"
      using `?rhs`[unfolded openin_euclidean_subtopology_iff, THEN spec[where x="ball (f x) e \<inter> f ` s"]] by auto
    hence "\<exists>d>0. \<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (f x) < e" apply(erule_tac x=x in ballE) apply auto using `e>0` `x\<in>s` by (auto simp add: dist_commute)  }
  thus ?lhs unfolding continuous_on Lim_within by auto
qed

(* ------------------------------------------------------------------------- *)
(* Similarly in terms of closed sets.                                        *)
(* ------------------------------------------------------------------------- *)

lemma continuous_on_closed:
 "continuous_on s f \<longleftrightarrow>  (\<forall>t. closedin (subtopology euclidean (f ` s)) t  --> closedin (subtopology euclidean s) {x \<in> s. f x \<in> t})" (is "?lhs = ?rhs")
proof
  assume ?lhs
  { fix t
    have *:"s - {x \<in> s. f x \<in> f ` s - t} = {x \<in> s. f x \<in> t}" by auto
    have **:"f ` s - (f ` s - (f ` s - t)) = f ` s - t" by auto
    assume as:"closedin (subtopology euclidean (f ` s)) t"
    hence "closedin (subtopology euclidean (f ` s)) (f ` s - (f ` s - t))" unfolding closedin_def topspace_euclidean_subtopology unfolding ** by auto
    hence "closedin (subtopology euclidean s) {x \<in> s. f x \<in> t}" using `?lhs`[unfolded continuous_on_open, THEN spec[where x="(f ` s) - t"]]
      unfolding openin_closedin_eq topspace_euclidean_subtopology unfolding * by auto  }
  thus ?rhs by auto
next
  assume ?rhs
  { fix t
    have *:"s - {x \<in> s. f x \<in> f ` s - t} = {x \<in> s. f x \<in> t}" by auto
    assume as:"openin (subtopology euclidean (f ` s)) t"
    hence "openin (subtopology euclidean s) {x \<in> s. f x \<in> t}" using `?rhs`[THEN spec[where x="(f ` s) - t"]]
      unfolding openin_closedin_eq topspace_euclidean_subtopology *[THEN sym] closedin_subtopology by auto }
  thus ?lhs unfolding continuous_on_open by auto
qed

text{* Half-global and completely global cases.                                  *}

lemma continuous_open_in_preimage:
  assumes "continuous_on s f"  "open t"
  shows "openin (subtopology euclidean s) {x \<in> s. f x \<in> t}"
proof-
  have *:"\<forall>x. x \<in> s \<and> f x \<in> t \<longleftrightarrow> x \<in> s \<and> f x \<in> (t \<inter> f ` s)" by auto
  have "openin (subtopology euclidean (f ` s)) (t \<inter> f ` s)"
    using openin_open_Int[of t "f ` s", OF assms(2)] unfolding openin_open by auto
  thus ?thesis using assms(1)[unfolded continuous_on_open, THEN spec[where x="t \<inter> f ` s"]] using * by auto
qed

lemma continuous_closed_in_preimage:
  assumes "continuous_on s f"  "closed t"
  shows "closedin (subtopology euclidean s) {x \<in> s. f x \<in> t}"
proof-
  have *:"\<forall>x. x \<in> s \<and> f x \<in> t \<longleftrightarrow> x \<in> s \<and> f x \<in> (t \<inter> f ` s)" by auto
  have "closedin (subtopology euclidean (f ` s)) (t \<inter> f ` s)"
    using closedin_closed_Int[of t "f ` s", OF assms(2)] unfolding Int_commute by auto
  thus ?thesis
    using assms(1)[unfolded continuous_on_closed, THEN spec[where x="t \<inter> f ` s"]] using * by auto
qed

lemma continuous_open_preimage:
  assumes "continuous_on s f" "open s" "open t"
  shows "open {x \<in> s. f x \<in> t}"
proof-
  obtain T where T: "open T" "{x \<in> s. f x \<in> t} = s \<inter> T"
    using continuous_open_in_preimage[OF assms(1,3)] unfolding openin_open by auto
  thus ?thesis using open_Int[of s T, OF assms(2)] by auto
qed

lemma continuous_closed_preimage:
  assumes "continuous_on s f" "closed s" "closed t"
  shows "closed {x \<in> s. f x \<in> t}"
proof-
  obtain T where T: "closed T" "{x \<in> s. f x \<in> t} = s \<inter> T"
    using continuous_closed_in_preimage[OF assms(1,3)] unfolding closedin_closed by auto
  thus ?thesis using closed_Int[of s T, OF assms(2)] by auto
qed

lemma continuous_open_preimage_univ:
  "\<forall>x. continuous (at x) f \<Longrightarrow> open s \<Longrightarrow> open {x. f x \<in> s}"
  using continuous_open_preimage[of UNIV f s] open_UNIV continuous_at_imp_continuous_on by auto

lemma continuous_closed_preimage_univ:
  "(\<forall>x. continuous (at x) f) \<Longrightarrow> closed s ==> closed {x. f x \<in> s}"
  using continuous_closed_preimage[of UNIV f s] closed_UNIV continuous_at_imp_continuous_on by auto

text{* Equality of continuous functions on closure and related results.          *}

lemma continuous_closed_in_preimage_constant:
 "continuous_on s f ==> closedin (subtopology euclidean s) {x \<in> s. f x = a}"
  using continuous_closed_in_preimage[of s f "{a}"] closed_sing by auto

lemma continuous_closed_preimage_constant:
 "continuous_on s f \<Longrightarrow> closed s ==> closed {x \<in> s. f x = a}"
  using continuous_closed_preimage[of s f "{a}"] closed_sing by auto

lemma continuous_constant_on_closure:
  assumes "continuous_on (closure s) f"
          "\<forall>x \<in> s. f x = a"
  shows "\<forall>x \<in> (closure s). f x = a"
    using continuous_closed_preimage_constant[of "closure s" f a]
    assms closure_minimal[of s "{x \<in> closure s. f x = a}"] closure_subset unfolding subset_eq by auto

lemma image_closure_subset:
  assumes "continuous_on (closure s) f"  "closed t"  "(f ` s) \<subseteq> t"
  shows "f ` (closure s) \<subseteq> t"
proof-
  have "s \<subseteq> {x \<in> closure s. f x \<in> t}" using assms(3) closure_subset by auto
  moreover have "closed {x \<in> closure s. f x \<in> t}"
    using continuous_closed_preimage[OF assms(1)] and assms(2) by auto
  ultimately have "closure s = {x \<in> closure s . f x \<in> t}"
    using closure_minimal[of s "{x \<in> closure s. f x \<in> t}"] by auto
  thus ?thesis by auto
qed

lemma continuous_on_closure_norm_le:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "continuous_on (closure s) f"  "\<forall>y \<in> s. norm(f y) \<le> b"  "x \<in> (closure s)"
  shows "norm(f x) \<le> b"
proof-
  have *:"f ` s \<subseteq> cball 0 b" using assms(2)[unfolded mem_cball_0[THEN sym]] by auto
  show ?thesis
    using image_closure_subset[OF assms(1) closed_cball[of 0 b] *] assms(3)
    unfolding subset_eq apply(erule_tac x="f x" in ballE) by (auto simp add: dist_norm)
qed

text{* Making a continuous function avoid some value in a neighbourhood.         *}

lemma continuous_within_avoid:
  assumes "continuous (at x within s) f"  "x \<in> s"  "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y \<in> s. dist x y < e --> f y \<noteq> a"
proof-
  obtain d where "d>0" and d:"\<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (f x) < dist (f x) a"
    using assms(1)[unfolded continuous_within Lim_within, THEN spec[where x="dist (f x) a"]] assms(3)[unfolded dist_nz] by auto
  { fix y assume " y\<in>s"  "dist x y < d"
    hence "f y \<noteq> a" using d[THEN bspec[where x=y]] assms(3)[unfolded dist_nz]
      apply auto unfolding dist_nz[THEN sym] by (auto simp add: dist_commute) }
  thus ?thesis using `d>0` by auto
qed

lemma continuous_at_avoid:
  assumes "continuous (at x) f"  "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> f y \<noteq> a"
using assms using continuous_within_avoid[of x UNIV f a, unfolded within_UNIV] by auto

lemma continuous_on_avoid:
  assumes "continuous_on s f"  "x \<in> s"  "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y \<in> s. dist x y < e \<longrightarrow> f y \<noteq> a"
using assms(1)[unfolded continuous_on_eq_continuous_within, THEN bspec[where x=x], OF assms(2)]  continuous_within_avoid[of x s f a]  assms(2,3) by auto

lemma continuous_on_open_avoid:
  assumes "continuous_on s f"  "open s"  "x \<in> s"  "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> f y \<noteq> a"
using assms(1)[unfolded continuous_on_eq_continuous_at[OF assms(2)], THEN bspec[where x=x], OF assms(3)]  continuous_at_avoid[of x f a]  assms(3,4) by auto

text{* Proving a function is constant by proving open-ness of level set.         *}

lemma continuous_levelset_open_in_cases:
 "connected s \<Longrightarrow> continuous_on s f \<Longrightarrow>
        openin (subtopology euclidean s) {x \<in> s. f x = a}
        ==> (\<forall>x \<in> s. f x \<noteq> a) \<or> (\<forall>x \<in> s. f x = a)"
unfolding connected_clopen using continuous_closed_in_preimage_constant by auto

lemma continuous_levelset_open_in:
 "connected s \<Longrightarrow> continuous_on s f \<Longrightarrow>
        openin (subtopology euclidean s) {x \<in> s. f x = a} \<Longrightarrow>
        (\<exists>x \<in> s. f x = a)  ==> (\<forall>x \<in> s. f x = a)"
using continuous_levelset_open_in_cases[of s f ]
by meson

lemma continuous_levelset_open:
  assumes "connected s"  "continuous_on s f"  "open {x \<in> s. f x = a}"  "\<exists>x \<in> s.  f x = a"
  shows "\<forall>x \<in> s. f x = a"
using continuous_levelset_open_in[OF assms(1,2), of a, unfolded openin_open] using assms (3,4) by auto

text{* Some arithmetical combinations (more to prove).                           *}

lemma open_scaling[intro]:
  fixes s :: "'a::real_normed_vector set"
  assumes "c \<noteq> 0"  "open s"
  shows "open((\<lambda>x. c *\<^sub>R x) ` s)"
proof-
  { fix x assume "x \<in> s"
    then obtain e where "e>0" and e:"\<forall>x'. dist x' x < e \<longrightarrow> x' \<in> s" using assms(2)[unfolded open_dist, THEN bspec[where x=x]] by auto
    have "e * abs c > 0" using assms(1)[unfolded zero_less_abs_iff[THEN sym]] using real_mult_order[OF `e>0`] by auto
    moreover
    { fix y assume "dist y (c *\<^sub>R x) < e * \<bar>c\<bar>"
      hence "norm ((1 / c) *\<^sub>R y - x) < e" unfolding dist_norm
	using norm_scaleR[of c "(1 / c) *\<^sub>R y - x", unfolded scaleR_right_diff_distrib, unfolded scaleR_scaleR] assms(1)
	  assms(1)[unfolded zero_less_abs_iff[THEN sym]] by (simp del:zero_less_abs_iff)
      hence "y \<in> op *\<^sub>R c ` s" using rev_image_eqI[of "(1 / c) *\<^sub>R y" s y "op *\<^sub>R c"]  e[THEN spec[where x="(1 / c) *\<^sub>R y"]]  assms(1) unfolding dist_norm scaleR_scaleR by auto  }
    ultimately have "\<exists>e>0. \<forall>x'. dist x' (c *\<^sub>R x) < e \<longrightarrow> x' \<in> op *\<^sub>R c ` s" apply(rule_tac x="e * abs c" in exI) by auto  }
  thus ?thesis unfolding open_dist by auto
qed

lemma minus_image_eq_vimage:
  fixes A :: "'a::ab_group_add set"
  shows "(\<lambda>x. - x) ` A = (\<lambda>x. - x) -` A"
  by (auto intro!: image_eqI [where f="\<lambda>x. - x"])

lemma open_negations:
  fixes s :: "'a::real_normed_vector set"
  shows "open s ==> open ((\<lambda> x. -x) ` s)"
  unfolding scaleR_minus1_left [symmetric]
  by (rule open_scaling, auto)

lemma open_translation:
  fixes s :: "'a::real_normed_vector set"
  assumes "open s"  shows "open((\<lambda>x. a + x) ` s)"
proof-
  { fix x have "continuous (at x) (\<lambda>x. x - a)" using continuous_sub[of "at x" "\<lambda>x. x" "\<lambda>x. a"] continuous_at_id[of x] continuous_const[of "at x" a] by auto  }
  moreover have "{x. x - a \<in> s}  = op + a ` s" apply auto unfolding image_iff apply(rule_tac x="x - a" in bexI) by auto
  ultimately show ?thesis using continuous_open_preimage_univ[of "\<lambda>x. x - a" s] using assms by auto
qed

lemma open_affinity:
  fixes s :: "(real ^ _) set"
  assumes "open s"  "c \<noteq> 0"
  shows "open ((\<lambda>x. a + c *\<^sub>R x) ` s)"
proof-
  have *:"(\<lambda>x. a + c *\<^sub>R x) = (\<lambda>x. a + x) \<circ> (\<lambda>x. c *\<^sub>R x)" unfolding o_def ..
  have "op + a ` op *\<^sub>R c ` s = (op + a \<circ> op *\<^sub>R c) ` s" by auto
  thus ?thesis using assms open_translation[of "op *\<^sub>R c ` s" a] unfolding * by auto
qed

lemma interior_translation:
  fixes s :: "'a::real_normed_vector set"
  shows "interior ((\<lambda>x. a + x) ` s) = (\<lambda>x. a + x) ` (interior s)"
proof (rule set_ext, rule)
  fix x assume "x \<in> interior (op + a ` s)"
  then obtain e where "e>0" and e:"ball x e \<subseteq> op + a ` s" unfolding mem_interior by auto
  hence "ball (x - a) e \<subseteq> s" unfolding subset_eq Ball_def mem_ball dist_norm apply auto apply(erule_tac x="a + xa" in allE) unfolding ab_group_add_class.diff_diff_eq[THEN sym] by auto
  thus "x \<in> op + a ` interior s" unfolding image_iff apply(rule_tac x="x - a" in bexI) unfolding mem_interior using `e > 0` by auto
next
  fix x assume "x \<in> op + a ` interior s"
  then obtain y e where "e>0" and e:"ball y e \<subseteq> s" and y:"x = a + y" unfolding image_iff Bex_def mem_interior by auto
  { fix z have *:"a + y - z = y + a - z" by auto
    assume "z\<in>ball x e"
    hence "z - a \<in> s" using e[unfolded subset_eq, THEN bspec[where x="z - a"]] unfolding mem_ball dist_norm y ab_group_add_class.diff_diff_eq2 * by auto
    hence "z \<in> op + a ` s" unfolding image_iff by(auto intro!: bexI[where x="z - a"])  }
  hence "ball x e \<subseteq> op + a ` s" unfolding subset_eq by auto
  thus "x \<in> interior (op + a ` s)" unfolding mem_interior using `e>0` by auto
qed

subsection {* Preservation of compactness and connectedness under continuous function.  *}

lemma compact_continuous_image:
  assumes "continuous_on s f"  "compact s"
  shows "compact(f ` s)"
proof-
  { fix x assume x:"\<forall>n::nat. x n \<in> f ` s"
    then obtain y where y:"\<forall>n. y n \<in> s \<and> x n = f (y n)" unfolding image_iff Bex_def using choice[of "\<lambda>n xa. xa \<in> s \<and> x n = f xa"] by auto
    then obtain l r where "l\<in>s" and r:"subseq r" and lr:"((y \<circ> r) ---> l) sequentially" using assms(2)[unfolded compact_def, THEN spec[where x=y]] by auto
    { fix e::real assume "e>0"
      then obtain d where "d>0" and d:"\<forall>x'\<in>s. dist x' l < d \<longrightarrow> dist (f x') (f l) < e" using assms(1)[unfolded continuous_on_def, THEN bspec[where x=l], OF `l\<in>s`] by auto
      then obtain N::nat where N:"\<forall>n\<ge>N. dist ((y \<circ> r) n) l < d" using lr[unfolded Lim_sequentially, THEN spec[where x=d]] by auto
      { fix n::nat assume "n\<ge>N" hence "dist ((x \<circ> r) n) (f l) < e" using N[THEN spec[where x=n]] d[THEN bspec[where x="y (r n)"]] y[THEN spec[where x="r n"]] by auto  }
      hence "\<exists>N. \<forall>n\<ge>N. dist ((x \<circ> r) n) (f l) < e" by auto  }
    hence "\<exists>l\<in>f ` s. \<exists>r. subseq r \<and> ((x \<circ> r) ---> l) sequentially" unfolding Lim_sequentially using r lr `l\<in>s` by auto  }
  thus ?thesis unfolding compact_def by auto
qed

lemma connected_continuous_image:
  assumes "continuous_on s f"  "connected s"
  shows "connected(f ` s)"
proof-
  { fix T assume as: "T \<noteq> {}"  "T \<noteq> f ` s"  "openin (subtopology euclidean (f ` s)) T"  "closedin (subtopology euclidean (f ` s)) T"
    have "{x \<in> s. f x \<in> T} = {} \<or> {x \<in> s. f x \<in> T} = s"
      using assms(1)[unfolded continuous_on_open, THEN spec[where x=T]]
      using assms(1)[unfolded continuous_on_closed, THEN spec[where x=T]]
      using assms(2)[unfolded connected_clopen, THEN spec[where x="{x \<in> s. f x \<in> T}"]] as(3,4) by auto
    hence False using as(1,2)
      using as(4)[unfolded closedin_def topspace_euclidean_subtopology] by auto }
  thus ?thesis unfolding connected_clopen by auto
qed

text{* Continuity implies uniform continuity on a compact domain.                *}

lemma compact_uniformly_continuous:
  assumes "continuous_on s f"  "compact s"
  shows "uniformly_continuous_on s f"
proof-
    { fix x assume x:"x\<in>s"
      hence "\<forall>xa. \<exists>y. 0 < xa \<longrightarrow> (y > 0 \<and> (\<forall>x'\<in>s. dist x' x < y \<longrightarrow> dist (f x') (f x) < xa))" using assms(1)[unfolded continuous_on_def, THEN bspec[where x=x]] by auto
      hence "\<exists>fa. \<forall>xa>0. \<forall>x'\<in>s. fa xa > 0 \<and> (dist x' x < fa xa \<longrightarrow> dist (f x') (f x) < xa)" using choice[of "\<lambda>e d. e>0 \<longrightarrow> d>0 \<and>(\<forall>x'\<in>s. (dist x' x < d \<longrightarrow> dist (f x') (f x) < e))"] by auto  }
    then have "\<forall>x\<in>s. \<exists>y. \<forall>xa. 0 < xa \<longrightarrow> (\<forall>x'\<in>s. y xa > 0 \<and> (dist x' x < y xa \<longrightarrow> dist (f x') (f x) < xa))" by auto
    then obtain d where d:"\<forall>e>0. \<forall>x\<in>s. \<forall>x'\<in>s. d x e > 0 \<and> (dist x' x < d x e \<longrightarrow> dist (f x') (f x) < e)"
      using bchoice[of s "\<lambda>x fa. \<forall>xa>0. \<forall>x'\<in>s. fa xa > 0 \<and> (dist x' x < fa xa \<longrightarrow> dist (f x') (f x) < xa)"] by blast

  { fix e::real assume "e>0"

    { fix x assume "x\<in>s" hence "x \<in> ball x (d x (e / 2))" unfolding centre_in_ball using d[THEN spec[where x="e/2"]] using `e>0` by auto  }
    hence "s \<subseteq> \<Union>{ball x (d x (e / 2)) |x. x \<in> s}" unfolding subset_eq by auto
    moreover
    { fix b assume "b\<in>{ball x (d x (e / 2)) |x. x \<in> s}" hence "open b" by auto  }
    ultimately obtain ea where "ea>0" and ea:"\<forall>x\<in>s. \<exists>b\<in>{ball x (d x (e / 2)) |x. x \<in> s}. ball x ea \<subseteq> b" using heine_borel_lemma[OF assms(2), of "{ball x (d x (e / 2)) | x. x\<in>s }"] by auto

    { fix x y assume "x\<in>s" "y\<in>s" and as:"dist y x < ea"
      obtain z where "z\<in>s" and z:"ball x ea \<subseteq> ball z (d z (e / 2))" using ea[THEN bspec[where x=x]] and `x\<in>s` by auto
      hence "x\<in>ball z (d z (e / 2))" using `ea>0` unfolding subset_eq by auto
      hence "dist (f z) (f x) < e / 2" using d[THEN spec[where x="e/2"]] and `e>0` and `x\<in>s` and `z\<in>s`
	by (auto  simp add: dist_commute)
      moreover have "y\<in>ball z (d z (e / 2))" using as and `ea>0` and z[unfolded subset_eq]
	by (auto simp add: dist_commute)
      hence "dist (f z) (f y) < e / 2" using d[THEN spec[where x="e/2"]] and `e>0` and `y\<in>s` and `z\<in>s`
	by (auto  simp add: dist_commute)
      ultimately have "dist (f y) (f x) < e" using dist_triangle_half_r[of "f z" "f x" e "f y"]
	by (auto simp add: dist_commute)  }
    then have "\<exists>d>0. \<forall>x\<in>s. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e" using `ea>0` by auto  }
  thus ?thesis unfolding uniformly_continuous_on_def by auto
qed

text{* Continuity of inverse function on compact domain. *}

lemma continuous_on_inverse:
  fixes f :: "'a::heine_borel \<Rightarrow> 'b::heine_borel"
    (* TODO: can this be generalized more? *)
  assumes "continuous_on s f"  "compact s"  "\<forall>x \<in> s. g (f x) = x"
  shows "continuous_on (f ` s) g"
proof-
  have *:"g ` f ` s = s" using assms(3) by (auto simp add: image_iff)
  { fix t assume t:"closedin (subtopology euclidean (g ` f ` s)) t"
    then obtain T where T: "closed T" "t = s \<inter> T" unfolding closedin_closed unfolding * by auto
    have "continuous_on (s \<inter> T) f" using continuous_on_subset[OF assms(1), of "s \<inter> t"]
      unfolding T(2) and Int_left_absorb by auto
    moreover have "compact (s \<inter> T)"
      using assms(2) unfolding compact_eq_bounded_closed
      using bounded_subset[of s "s \<inter> T"] and T(1) by auto
    ultimately have "closed (f ` t)" using T(1) unfolding T(2)
      using compact_continuous_image [of "s \<inter> T" f] unfolding compact_eq_bounded_closed by auto
    moreover have "{x \<in> f ` s. g x \<in> t} = f ` s \<inter> f ` t" using assms(3) unfolding T(2) by auto
    ultimately have "closedin (subtopology euclidean (f ` s)) {x \<in> f ` s. g x \<in> t}"
      unfolding closedin_closed by auto  }
  thus ?thesis unfolding continuous_on_closed by auto
qed

subsection{* A uniformly convergent limit of continuous functions is continuous.       *}

lemma norm_triangle_lt:
  fixes x y :: "'a::real_normed_vector"
  shows "norm x + norm y < e \<Longrightarrow> norm (x + y) < e"
by (rule le_less_trans [OF norm_triangle_ineq])

lemma continuous_uniform_limit:
  fixes f :: "'a \<Rightarrow> 'b::metric_space \<Rightarrow> 'c::real_normed_vector"
  assumes "\<not> (trivial_limit net)"  "eventually (\<lambda>n. continuous_on s (f n)) net"
  "\<forall>e>0. eventually (\<lambda>n. \<forall>x \<in> s. norm(f n x - g x) < e) net"
  shows "continuous_on s g"
proof-
  { fix x and e::real assume "x\<in>s" "e>0"
    have "eventually (\<lambda>n. \<forall>x\<in>s. norm (f n x - g x) < e / 3) net" using `e>0` assms(3)[THEN spec[where x="e/3"]] by auto
    then obtain n where n:"\<forall>xa\<in>s. norm (f n xa - g xa) < e / 3"  "continuous_on s (f n)"
      using eventually_and[of "(\<lambda>n. \<forall>x\<in>s. norm (f n x - g x) < e / 3)" "(\<lambda>n. continuous_on s (f n))" net] assms(1,2) eventually_happens by blast
    have "e / 3 > 0" using `e>0` by auto
    then obtain d where "d>0" and d:"\<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f n x') (f n x) < e / 3"
      using n(2)[unfolded continuous_on_def, THEN bspec[where x=x], OF `x\<in>s`, THEN spec[where x="e/3"]] by blast
    { fix y assume "y\<in>s" "dist y x < d"
      hence "dist (f n y) (f n x) < e / 3" using d[THEN bspec[where x=y]] by auto
      hence "norm (f n y - g x) < 2 * e / 3" using norm_triangle_lt[of "f n y - f n x" "f n x - g x" "2*e/3"]
	using n(1)[THEN bspec[where x=x], OF `x\<in>s`] unfolding dist_norm unfolding ab_group_add_class.ab_diff_minus by auto
      hence "dist (g y) (g x) < e" unfolding dist_norm using n(1)[THEN bspec[where x=y], OF `y\<in>s`]
	unfolding norm_minus_cancel[of "f n y - g y", THEN sym] using norm_triangle_lt[of "f n y - g x" "g y - f n y" e] by (auto simp add: uminus_add_conv_diff)  }
    hence "\<exists>d>0. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (g x') (g x) < e" using `d>0` by auto  }
  thus ?thesis unfolding continuous_on_def by auto
qed

subsection{* Topological properties of linear functions.                               *}

lemma linear_lim_0: fixes f::"real^'a::finite \<Rightarrow> real^'b::finite"
  assumes "linear f" shows "(f ---> 0) (at (0))"
proof-
  obtain B where "B>0" and B:"\<forall>x. norm (f x) \<le> B * norm x" using linear_bounded_pos[OF assms] by auto
  { fix e::real assume "e>0"
    { fix x::"real^'a" assume "norm x < e / B"
      hence "B * norm x < e" using `B>0` using mult_strict_right_mono[of "norm x" " e / B" B] unfolding real_mult_commute by auto
      hence "norm (f x) < e" using B[THEN spec[where x=x]] `B>0` using order_le_less_trans[of "norm (f x)" "B * norm x" e] by auto   }
    moreover have "e / B > 0" using `e>0` `B>0` divide_pos_pos by auto
    ultimately have "\<exists>d>0. \<forall>x. 0 < dist x 0 \<and> dist x 0 < d \<longrightarrow> dist (f x) 0 < e" unfolding dist_norm by auto  }
  thus ?thesis unfolding Lim_at by auto
qed

lemma bounded_linear_continuous_at:
  assumes "bounded_linear f"  shows "continuous (at a) f"
  unfolding continuous_at using assms
  apply (rule bounded_linear.tendsto)
  apply (rule Lim_at_id [unfolded id_def])
  done

lemma linear_continuous_at:
  fixes f :: "real ^ _ \<Rightarrow> real ^ _"
  assumes "linear f"  shows "continuous (at a) f"
  using assms unfolding linear_conv_bounded_linear
  by (rule bounded_linear_continuous_at)

lemma linear_continuous_within:
  fixes f :: "real ^ _ \<Rightarrow> real ^ _"
  shows "linear f ==> continuous (at x within s) f"
  using continuous_at_imp_continuous_within[of x f s] using linear_continuous_at[of f] by auto

lemma linear_continuous_on:
  fixes f :: "real ^ _ \<Rightarrow> real ^ _"
  shows "linear f ==> continuous_on s f"
  using continuous_at_imp_continuous_on[of s f] using linear_continuous_at[of f] by auto

text{* Also bilinear functions, in composition form.                             *}

lemma bilinear_continuous_at_compose:
  fixes f :: "real ^ _ \<Rightarrow> real ^ _"
  shows "continuous (at x) f \<Longrightarrow> continuous (at x) g \<Longrightarrow> bilinear h
        ==> continuous (at x) (\<lambda>x. h (f x) (g x))"
  unfolding continuous_at using Lim_bilinear[of f "f x" "(at x)" g "g x" h] by auto

lemma bilinear_continuous_within_compose:
  fixes h :: "real ^ _ \<Rightarrow> real ^ _ \<Rightarrow> real ^ _"
  shows "continuous (at x within s) f \<Longrightarrow> continuous (at x within s) g \<Longrightarrow> bilinear h
        ==> continuous (at x within s) (\<lambda>x. h (f x) (g x))"
  unfolding continuous_within using Lim_bilinear[of f "f x"] by auto

lemma bilinear_continuous_on_compose:
  fixes h :: "real ^ _ \<Rightarrow> real ^ _ \<Rightarrow> real ^ _"
  shows "continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> bilinear h
             ==> continuous_on s (\<lambda>x. h (f x) (g x))"
  unfolding continuous_on_eq_continuous_within apply auto apply(erule_tac x=x in ballE) apply auto apply(erule_tac x=x in ballE) apply auto
  using bilinear_continuous_within_compose[of _ s f g h] by auto

subsection{* Topological stuff lifted from and dropped to R                            *}


lemma open_real:
  fixes s :: "real set" shows
 "open s \<longleftrightarrow>
        (\<forall>x \<in> s. \<exists>e>0. \<forall>x'. abs(x' - x) < e --> x' \<in> s)" (is "?lhs = ?rhs")
  unfolding open_dist dist_norm by simp

lemma islimpt_approachable_real:
  fixes s :: "real set"
  shows "x islimpt s \<longleftrightarrow> (\<forall>e>0.  \<exists>x'\<in> s. x' \<noteq> x \<and> abs(x' - x) < e)"
  unfolding islimpt_approachable dist_norm by simp

lemma closed_real:
  fixes s :: "real set"
  shows "closed s \<longleftrightarrow>
        (\<forall>x. (\<forall>e>0.  \<exists>x' \<in> s. x' \<noteq> x \<and> abs(x' - x) < e)
            --> x \<in> s)"
  unfolding closed_limpt islimpt_approachable dist_norm by simp

lemma continuous_at_real_range:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  shows "continuous (at x) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0.
        \<forall>x'. norm(x' - x) < d --> abs(f x' - f x) < e)"
  unfolding continuous_at unfolding Lim_at
  unfolding dist_nz[THEN sym] unfolding dist_norm apply auto
  apply(erule_tac x=e in allE) apply auto apply (rule_tac x=d in exI) apply auto apply (erule_tac x=x' in allE) apply auto
  apply(erule_tac x=e in allE) by auto

lemma continuous_on_real_range:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  shows "continuous_on s f \<longleftrightarrow> (\<forall>x \<in> s. \<forall>e>0. \<exists>d>0. (\<forall>x' \<in> s. norm(x' - x) < d --> abs(f x' - f x) < e))"
  unfolding continuous_on_def dist_norm by simp

lemma continuous_at_norm: "continuous (at x) norm"
  unfolding continuous_at by (intro tendsto_intros)

lemma continuous_on_norm: "continuous_on s norm"
unfolding continuous_on by (intro ballI tendsto_intros)

lemma continuous_at_component: "continuous (at a) (\<lambda>x. x $ i)"
unfolding continuous_at by (intro tendsto_intros)

lemma continuous_on_component: "continuous_on s (\<lambda>x. x $ i)"
unfolding continuous_on by (intro ballI tendsto_intros)

lemma continuous_at_infnorm: "continuous (at x) infnorm"
  unfolding continuous_at Lim_at o_def unfolding dist_norm
  apply auto apply (rule_tac x=e in exI) apply auto
  using order_trans[OF real_abs_sub_infnorm infnorm_le_norm, of _ x] by (metis xt1(7))

text{* Hence some handy theorems on distance, diameter etc. of/from a set.       *}

lemma compact_attains_sup:
  fixes s :: "real set"
  assumes "compact s"  "s \<noteq> {}"
  shows "\<exists>x \<in> s. \<forall>y \<in> s. y \<le> x"
proof-
  from assms(1) have a:"bounded s" "closed s" unfolding compact_eq_bounded_closed by auto
  { fix e::real assume as: "\<forall>x\<in>s. x \<le> rsup s" "rsup s \<notin> s"  "0 < e" "\<forall>x'\<in>s. x' = rsup s \<or> \<not> rsup s - x' < e"
    have "isLub UNIV s (rsup s)" using rsup[OF assms(2)] unfolding setle_def using as(1) by auto
    moreover have "isUb UNIV s (rsup s - e)" unfolding isUb_def unfolding setle_def using as(4,2) by auto
    ultimately have False using isLub_le_isUb[of UNIV s "rsup s" "rsup s - e"] using `e>0` by auto  }
  thus ?thesis using bounded_has_rsup(1)[OF a(1) assms(2)] using a(2)[unfolded closed_real, THEN spec[where x="rsup s"]]
    apply(rule_tac x="rsup s" in bexI) by auto
qed

lemma compact_attains_inf:
  fixes s :: "real set"
  assumes "compact s" "s \<noteq> {}"  shows "\<exists>x \<in> s. \<forall>y \<in> s. x \<le> y"
proof-
  from assms(1) have a:"bounded s" "closed s" unfolding compact_eq_bounded_closed by auto
  { fix e::real assume as: "\<forall>x\<in>s. x \<ge> rinf s"  "rinf s \<notin> s"  "0 < e"
      "\<forall>x'\<in>s. x' = rinf s \<or> \<not> abs (x' - rinf s) < e"
    have "isGlb UNIV s (rinf s)" using rinf[OF assms(2)] unfolding setge_def using as(1) by auto
    moreover
    { fix x assume "x \<in> s"
      hence *:"abs (x - rinf s) = x - rinf s" using as(1)[THEN bspec[where x=x]] by auto
      have "rinf s + e \<le> x" using as(4)[THEN bspec[where x=x]] using as(2) `x\<in>s` unfolding * by auto }
    hence "isLb UNIV s (rinf s + e)" unfolding isLb_def and setge_def by auto
    ultimately have False using isGlb_le_isLb[of UNIV s "rinf s" "rinf s + e"] using `e>0` by auto  }
  thus ?thesis using bounded_has_rinf(1)[OF a(1) assms(2)] using a(2)[unfolded closed_real, THEN spec[where x="rinf s"]]
    apply(rule_tac x="rinf s" in bexI) by auto
qed

lemma continuous_attains_sup:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  shows "compact s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> continuous_on s f
        ==> (\<exists>x \<in> s. \<forall>y \<in> s.  f y \<le> f x)"
  using compact_attains_sup[of "f ` s"]
  using compact_continuous_image[of s f] by auto

lemma continuous_attains_inf:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  shows "compact s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> continuous_on s f
        \<Longrightarrow> (\<exists>x \<in> s. \<forall>y \<in> s. f x \<le> f y)"
  using compact_attains_inf[of "f ` s"]
  using compact_continuous_image[of s f] by auto

lemma distance_attains_sup:
  assumes "compact s" "s \<noteq> {}"
  shows "\<exists>x \<in> s. \<forall>y \<in> s. dist a y \<le> dist a x"
proof (rule continuous_attains_sup [OF assms])
  { fix x assume "x\<in>s"
    have "(dist a ---> dist a x) (at x within s)"
      by (intro tendsto_dist tendsto_const Lim_at_within Lim_ident_at)
  }
  thus "continuous_on s (dist a)"
    unfolding continuous_on ..
qed

text{* For *minimal* distance, we only need closure, not compactness.            *}

lemma distance_attains_inf:
  fixes a :: "'a::heine_borel"
  assumes "closed s"  "s \<noteq> {}"
  shows "\<exists>x \<in> s. \<forall>y \<in> s. dist a x \<le> dist a y"
proof-
  from assms(2) obtain b where "b\<in>s" by auto
  let ?B = "cball a (dist b a) \<inter> s"
  have "b \<in> ?B" using `b\<in>s` by (simp add: dist_commute)
  hence "?B \<noteq> {}" by auto
  moreover
  { fix x assume "x\<in>?B"
    fix e::real assume "e>0"
    { fix x' assume "x'\<in>?B" and as:"dist x' x < e"
      from as have "\<bar>dist a x' - dist a x\<bar> < e"
        unfolding abs_less_iff minus_diff_eq
        using dist_triangle2 [of a x' x]
        using dist_triangle [of a x x']
        by arith
    }
    hence "\<exists>d>0. \<forall>x'\<in>?B. dist x' x < d \<longrightarrow> \<bar>dist a x' - dist a x\<bar> < e"
      using `e>0` by auto
  }
  hence "continuous_on (cball a (dist b a) \<inter> s) (dist a)"
    unfolding continuous_on Lim_within dist_norm real_norm_def
    by fast
  moreover have "compact ?B"
    using compact_cball[of a "dist b a"]
    unfolding compact_eq_bounded_closed
    using bounded_Int and closed_Int and assms(1) by auto
  ultimately obtain x where "x\<in>cball a (dist b a) \<inter> s" "\<forall>y\<in>cball a (dist b a) \<inter> s. dist a x \<le> dist a y"
    using continuous_attains_inf[of ?B "dist a"] by fastsimp
  thus ?thesis by fastsimp
qed

subsection{* We can now extend limit compositions to consider the scalar multiplier.   *}

lemma Lim_mul:
  fixes f :: "'a \<Rightarrow> real ^ _"
  assumes "(c ---> d) net"  "(f ---> l) net"
  shows "((\<lambda>x. c(x) *\<^sub>R f x) ---> (d *\<^sub>R l)) net"
  unfolding smult_conv_scaleR using assms by (rule scaleR.tendsto)

lemma Lim_vmul:
  fixes c :: "'a \<Rightarrow> real" and v :: "'b::real_normed_vector"
  shows "(c ---> d) net ==> ((\<lambda>x. c(x) *\<^sub>R v) ---> d *\<^sub>R v) net"
  by (intro tendsto_intros)

lemma continuous_vmul:
  fixes c :: "'a::metric_space \<Rightarrow> real" and v :: "'b::real_normed_vector"
  shows "continuous net c ==> continuous net (\<lambda>x. c(x) *\<^sub>R v)"
  unfolding continuous_def using Lim_vmul[of c] by auto

lemma continuous_mul:
  fixes c :: "'a::metric_space \<Rightarrow> real"
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "continuous net c \<Longrightarrow> continuous net f
             ==> continuous net (\<lambda>x. c(x) *\<^sub>R f x) "
  unfolding continuous_def by (intro tendsto_intros)

lemma continuous_on_vmul:
  fixes c :: "'a::metric_space \<Rightarrow> real" and v :: "'b::real_normed_vector"
  shows "continuous_on s c ==> continuous_on s (\<lambda>x. c(x) *\<^sub>R v)"
  unfolding continuous_on_eq_continuous_within using continuous_vmul[of _ c] by auto

lemma continuous_on_mul:
  fixes c :: "'a::metric_space \<Rightarrow> real"
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "continuous_on s c \<Longrightarrow> continuous_on s f
             ==> continuous_on s (\<lambda>x. c(x) *\<^sub>R f x)"
  unfolding continuous_on_eq_continuous_within using continuous_mul[of _ c] by auto

text{* And so we have continuity of inverse.                                     *}

lemma Lim_inv:
  fixes f :: "'a \<Rightarrow> real"
  assumes "(f ---> l) (net::'a net)"  "l \<noteq> 0"
  shows "((inverse o f) ---> inverse l) net"
  unfolding o_def using assms by (rule tendsto_inverse)

lemma continuous_inv:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  shows "continuous net f \<Longrightarrow> f(netlimit net) \<noteq> 0
           ==> continuous net (inverse o f)"
  unfolding continuous_def using Lim_inv by auto

lemma continuous_at_within_inv:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_field"
  assumes "continuous (at a within s) f" "f a \<noteq> 0"
  shows "continuous (at a within s) (inverse o f)"
  using assms unfolding continuous_within o_def
  by (intro tendsto_intros)

lemma continuous_at_inv:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_field"
  shows "continuous (at a) f \<Longrightarrow> f a \<noteq> 0
         ==> continuous (at a) (inverse o f) "
  using within_UNIV[THEN sym, of "at a"] using continuous_at_within_inv[of a UNIV] by auto

subsection{* Preservation properties for pasted sets.                                  *}

lemma bounded_pastecart:
  fixes s :: "('a::real_normed_vector ^ _) set" (* FIXME: generalize to metric_space *)
  assumes "bounded s" "bounded t"
  shows "bounded { pastecart x y | x y . (x \<in> s \<and> y \<in> t)}"
proof-
  obtain a b where ab:"\<forall>x\<in>s. norm x \<le> a" "\<forall>x\<in>t. norm x \<le> b" using assms[unfolded bounded_iff] by auto
  { fix x y assume "x\<in>s" "y\<in>t"
    hence "norm x \<le> a" "norm y \<le> b" using ab by auto
    hence "norm (pastecart x y) \<le> a + b" using norm_pastecart[of x y] by auto }
  thus ?thesis unfolding bounded_iff by auto
qed

lemma bounded_Times:
  assumes "bounded s" "bounded t" shows "bounded (s \<times> t)"
proof-
  obtain x y a b where "\<forall>z\<in>s. dist x z \<le> a" "\<forall>z\<in>t. dist y z \<le> b"
    using assms [unfolded bounded_def] by auto
  then have "\<forall>z\<in>s \<times> t. dist (x, y) z \<le> sqrt (a\<twosuperior> + b\<twosuperior>)"
    by (auto simp add: dist_Pair_Pair real_sqrt_le_mono add_mono power_mono)
  thus ?thesis unfolding bounded_any_center [where a="(x, y)"] by auto
qed

lemma closed_pastecart:
  fixes s :: "(real ^ 'a::finite) set" (* FIXME: generalize *)
  assumes "closed s"  "closed t"
  shows "closed {pastecart x y | x y . x \<in> s \<and> y \<in> t}"
proof-
  { fix x l assume as:"\<forall>n::nat. x n \<in> {pastecart x y |x y. x \<in> s \<and> y \<in> t}"  "(x ---> l) sequentially"
    { fix n::nat have "fstcart (x n) \<in> s" "sndcart (x n) \<in> t" using as(1)[THEN spec[where x=n]] by auto } note * = this
    moreover
    { fix e::real assume "e>0"
      then obtain N::nat where N:"\<forall>n\<ge>N. dist (x n) l < e" using as(2)[unfolded Lim_sequentially, THEN spec[where x=e]] by auto
      { fix n::nat assume "n\<ge>N"
	hence "dist (fstcart (x n)) (fstcart l) < e" "dist (sndcart (x n)) (sndcart l) < e"
	  using N[THEN spec[where x=n]] dist_fstcart[of "x n" l] dist_sndcart[of "x n" l] by auto   }
      hence "\<exists>N. \<forall>n\<ge>N. dist (fstcart (x n)) (fstcart l) < e" "\<exists>N. \<forall>n\<ge>N. dist (sndcart (x n)) (sndcart l) < e" by auto  }
    ultimately have "fstcart l \<in> s" "sndcart l \<in> t"
      using assms(1)[unfolded closed_sequential_limits, THEN spec[where x="\<lambda>n. fstcart (x n)"], THEN spec[where x="fstcart l"]]
      using assms(2)[unfolded closed_sequential_limits, THEN spec[where x="\<lambda>n. sndcart (x n)"], THEN spec[where x="sndcart l"]]
      unfolding Lim_sequentially by auto
    hence "l \<in> {pastecart x y |x y. x \<in> s \<and> y \<in> t}" using pastecart_fst_snd[THEN sym, of l] by auto  }
  thus ?thesis unfolding closed_sequential_limits by auto
qed

lemma compact_pastecart:
  fixes s t :: "(real ^ _) set"
  shows "compact s \<Longrightarrow> compact t ==> compact {pastecart x y | x y . x \<in> s \<and> y \<in> t}"
  unfolding compact_eq_bounded_closed using bounded_pastecart[of s t] closed_pastecart[of s t] by auto

lemma mem_Times_iff: "x \<in> A \<times> B \<longleftrightarrow> fst x \<in> A \<and> snd x \<in> B"
by (induct x) simp

lemma compact_Times: "compact s \<Longrightarrow> compact t \<Longrightarrow> compact (s \<times> t)"
unfolding compact_def
apply clarify
apply (drule_tac x="fst \<circ> f" in spec)
apply (drule mp, simp add: mem_Times_iff)
apply (clarify, rename_tac l1 r1)
apply (drule_tac x="snd \<circ> f \<circ> r1" in spec)
apply (drule mp, simp add: mem_Times_iff)
apply (clarify, rename_tac l2 r2)
apply (rule_tac x="(l1, l2)" in rev_bexI, simp)
apply (rule_tac x="r1 \<circ> r2" in exI)
apply (rule conjI, simp add: subseq_def)
apply (drule_tac r=r2 in lim_subseq [COMP swap_prems_rl], assumption)
apply (drule (1) tendsto_Pair) back
apply (simp add: o_def)
done

text{* Hence some useful properties follow quite easily.                         *}

lemma compact_scaleR_image:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"  shows "compact ((\<lambda>x. scaleR c x) ` s)"
proof-
  let ?f = "\<lambda>x. scaleR c x"
  have *:"bounded_linear ?f" by (rule scaleR.bounded_linear_right)
  show ?thesis using compact_continuous_image[of s ?f] continuous_at_imp_continuous_on[of s ?f]
    using bounded_linear_continuous_at[OF *] assms by auto
qed

lemma compact_scaling:
  fixes s :: "(real ^ _) set"
  assumes "compact s"  shows "compact ((\<lambda>x. c *\<^sub>R x) ` s)"
  using assms unfolding smult_conv_scaleR by (rule compact_scaleR_image)

lemma compact_negations:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"  shows "compact ((\<lambda>x. -x) ` s)"
  using compact_scaleR_image [OF assms, of "- 1"] by auto

lemma compact_sums:
  fixes s t :: "'a::real_normed_vector set"
  assumes "compact s"  "compact t"  shows "compact {x + y | x y. x \<in> s \<and> y \<in> t}"
proof-
  have *:"{x + y | x y. x \<in> s \<and> y \<in> t} = (\<lambda>z. fst z + snd z) ` (s \<times> t)"
    apply auto unfolding image_iff apply(rule_tac x="(xa, y)" in bexI) by auto
  have "continuous_on (s \<times> t) (\<lambda>z. fst z + snd z)"
    unfolding continuous_on by (rule ballI) (intro tendsto_intros)
  thus ?thesis unfolding * using compact_continuous_image compact_Times [OF assms] by auto
qed

lemma compact_differences:
  fixes s t :: "'a::real_normed_vector set"
  assumes "compact s" "compact t"  shows "compact {x - y | x y. x \<in> s \<and> y \<in> t}"
proof-
  have "{x - y | x y. x\<in>s \<and> y \<in> t} =  {x + y | x y. x \<in> s \<and> y \<in> (uminus ` t)}"
    apply auto apply(rule_tac x= xa in exI) apply auto apply(rule_tac x=xa in exI) by auto
  thus ?thesis using compact_sums[OF assms(1) compact_negations[OF assms(2)]] by auto
qed

lemma compact_translation:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"  shows "compact ((\<lambda>x. a + x) ` s)"
proof-
  have "{x + y |x y. x \<in> s \<and> y \<in> {a}} = (\<lambda>x. a + x) ` s" by auto
  thus ?thesis using compact_sums[OF assms compact_sing[of a]] by auto
qed

lemma compact_affinity:
  fixes s :: "(real ^ _) set"
  assumes "compact s"  shows "compact ((\<lambda>x. a + c *\<^sub>R x) ` s)"
proof-
  have "op + a ` op *\<^sub>R c ` s = (\<lambda>x. a + c *\<^sub>R x) ` s" by auto
  thus ?thesis using compact_translation[OF compact_scaling[OF assms], of a c] by auto
qed

text{* Hence we get the following.                                               *}

lemma compact_sup_maxdistance:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"  "s \<noteq> {}"
  shows "\<exists>x\<in>s. \<exists>y\<in>s. \<forall>u\<in>s. \<forall>v\<in>s. norm(u - v) \<le> norm(x - y)"
proof-
  have "{x - y | x y . x\<in>s \<and> y\<in>s} \<noteq> {}" using `s \<noteq> {}` by auto
  then obtain x where x:"x\<in>{x - y |x y. x \<in> s \<and> y \<in> s}"  "\<forall>y\<in>{x - y |x y. x \<in> s \<and> y \<in> s}. norm y \<le> norm x"
    using compact_differences[OF assms(1) assms(1)]
    using distance_attains_sup[where 'a="'a", unfolded dist_norm, of "{x - y | x y . x\<in>s \<and> y\<in>s}" 0] by(auto simp add: norm_minus_cancel)
  from x(1) obtain a b where "a\<in>s" "b\<in>s" "x = a - b" by auto
  thus ?thesis using x(2)[unfolded `x = a - b`] by blast
qed

text{* We can state this in terms of diameter of a set.                          *}

definition "diameter s = (if s = {} then 0::real else rsup {norm(x - y) | x y. x \<in> s \<and> y \<in> s})"
  (* TODO: generalize to class metric_space *)

lemma diameter_bounded:
  assumes "bounded s"
  shows "\<forall>x\<in>s. \<forall>y\<in>s. norm(x - y) \<le> diameter s"
        "\<forall>d>0. d < diameter s --> (\<exists>x\<in>s. \<exists>y\<in>s. norm(x - y) > d)"
proof-
  let ?D = "{norm (x - y) |x y. x \<in> s \<and> y \<in> s}"
  obtain a where a:"\<forall>x\<in>s. norm x \<le> a" using assms[unfolded bounded_iff] by auto
  { fix x y assume "x \<in> s" "y \<in> s"
    hence "norm (x - y) \<le> 2 * a" using norm_triangle_ineq[of x "-y", unfolded norm_minus_cancel] a[THEN bspec[where x=x]] a[THEN bspec[where x=y]] by (auto simp add: ring_simps)  }
  note * = this
  { fix x y assume "x\<in>s" "y\<in>s"  hence "s \<noteq> {}" by auto
    have lub:"isLub UNIV ?D (rsup ?D)" using * rsup[of ?D] using `s\<noteq>{}` unfolding setle_def by auto
    have "norm(x - y) \<le> diameter s" unfolding diameter_def using `s\<noteq>{}` *[OF `x\<in>s` `y\<in>s`] `x\<in>s` `y\<in>s` isLubD1[OF lub] unfolding setle_def by auto  }
  moreover
  { fix d::real assume "d>0" "d < diameter s"
    hence "s\<noteq>{}" unfolding diameter_def by auto
    hence lub:"isLub UNIV ?D (rsup ?D)" using * rsup[of ?D] unfolding setle_def by auto
    have "\<exists>d' \<in> ?D. d' > d"
    proof(rule ccontr)
      assume "\<not> (\<exists>d'\<in>{norm (x - y) |x y. x \<in> s \<and> y \<in> s}. d < d')"
      hence as:"\<forall>d'\<in>?D. d' \<le> d" apply auto apply(erule_tac x="norm (x - y)" in allE) by auto
      hence "isUb UNIV ?D d" unfolding isUb_def unfolding setle_def by auto
      thus False using `d < diameter s` `s\<noteq>{}` isLub_le_isUb[OF lub, of d] unfolding diameter_def  by auto
    qed
    hence "\<exists>x\<in>s. \<exists>y\<in>s. norm(x - y) > d" by auto  }
  ultimately show "\<forall>x\<in>s. \<forall>y\<in>s. norm(x - y) \<le> diameter s"
        "\<forall>d>0. d < diameter s --> (\<exists>x\<in>s. \<exists>y\<in>s. norm(x - y) > d)" by auto
qed

lemma diameter_bounded_bound:
 "bounded s \<Longrightarrow> x \<in> s \<Longrightarrow> y \<in> s ==> norm(x - y) \<le> diameter s"
  using diameter_bounded by blast

lemma diameter_compact_attained:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"  "s \<noteq> {}"
  shows "\<exists>x\<in>s. \<exists>y\<in>s. (norm(x - y) = diameter s)"
proof-
  have b:"bounded s" using assms(1) by (rule compact_imp_bounded)
  then obtain x y where xys:"x\<in>s" "y\<in>s" and xy:"\<forall>u\<in>s. \<forall>v\<in>s. norm (u - v) \<le> norm (x - y)" using compact_sup_maxdistance[OF assms] by auto
  hence "diameter s \<le> norm (x - y)" using rsup_le[of "{norm (x - y) |x y. x \<in> s \<and> y \<in> s}" "norm (x - y)"]
    unfolding setle_def and diameter_def by auto
  thus ?thesis using diameter_bounded(1)[OF b, THEN bspec[where x=x], THEN bspec[where x=y], OF xys] and xys by auto
qed

text{* Related results with closure as the conclusion.                           *}

lemma closed_scaleR_image:
  fixes s :: "'a::real_normed_vector set"
  assumes "closed s" shows "closed ((\<lambda>x. scaleR c x) ` s)"
proof(cases "s={}")
  case True thus ?thesis by auto
next
  case False
  show ?thesis
  proof(cases "c=0")
    have *:"(\<lambda>x. 0) ` s = {0}" using `s\<noteq>{}` by auto
    case True thus ?thesis apply auto unfolding * using closed_sing by auto
  next
    case False
    { fix x l assume as:"\<forall>n::nat. x n \<in> scaleR c ` s"  "(x ---> l) sequentially"
      { fix n::nat have "scaleR (1 / c) (x n) \<in> s"
          using as(1)[THEN spec[where x=n]]
          using `c\<noteq>0` by (auto simp add: vector_smult_assoc)
      }
      moreover
      { fix e::real assume "e>0"
	hence "0 < e *\<bar>c\<bar>"  using `c\<noteq>0` mult_pos_pos[of e "abs c"] by auto
	then obtain N where "\<forall>n\<ge>N. dist (x n) l < e * \<bar>c\<bar>"
          using as(2)[unfolded Lim_sequentially, THEN spec[where x="e * abs c"]] by auto
	hence "\<exists>N. \<forall>n\<ge>N. dist (scaleR (1 / c) (x n)) (scaleR (1 / c) l) < e"
          unfolding dist_norm unfolding scaleR_right_diff_distrib[THEN sym]
	  using mult_imp_div_pos_less[of "abs c" _ e] `c\<noteq>0` by auto  }
      hence "((\<lambda>n. scaleR (1 / c) (x n)) ---> scaleR (1 / c) l) sequentially" unfolding Lim_sequentially by auto
      ultimately have "l \<in> scaleR c ` s"
        using assms[unfolded closed_sequential_limits, THEN spec[where x="\<lambda>n. scaleR (1/c) (x n)"], THEN spec[where x="scaleR (1/c) l"]]
	unfolding image_iff using `c\<noteq>0` apply(rule_tac x="scaleR (1 / c) l" in bexI) by auto  }
    thus ?thesis unfolding closed_sequential_limits by fast
  qed
qed

lemma closed_scaling:
  fixes s :: "(real ^ _) set"
  assumes "closed s" shows "closed ((\<lambda>x. c *\<^sub>R x) ` s)"
  using assms unfolding smult_conv_scaleR by (rule closed_scaleR_image)

lemma closed_negations:
  fixes s :: "'a::real_normed_vector set"
  assumes "closed s"  shows "closed ((\<lambda>x. -x) ` s)"
  using closed_scaleR_image[OF assms, of "- 1"] by simp

lemma compact_closed_sums:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"  "closed t"  shows "closed {x + y | x y. x \<in> s \<and> y \<in> t}"
proof-
  let ?S = "{x + y |x y. x \<in> s \<and> y \<in> t}"
  { fix x l assume as:"\<forall>n. x n \<in> ?S"  "(x ---> l) sequentially"
    from as(1) obtain f where f:"\<forall>n. x n = fst (f n) + snd (f n)"  "\<forall>n. fst (f n) \<in> s"  "\<forall>n. snd (f n) \<in> t"
      using choice[of "\<lambda>n y. x n = (fst y) + (snd y) \<and> fst y \<in> s \<and> snd y \<in> t"] by auto
    obtain l' r where "l'\<in>s" and r:"subseq r" and lr:"(((\<lambda>n. fst (f n)) \<circ> r) ---> l') sequentially"
      using assms(1)[unfolded compact_def, THEN spec[where x="\<lambda> n. fst (f n)"]] using f(2) by auto
    have "((\<lambda>n. snd (f (r n))) ---> l - l') sequentially"
      using Lim_sub[OF lim_subseq[OF r as(2)] lr] and f(1) unfolding o_def by auto
    hence "l - l' \<in> t"
      using assms(2)[unfolded closed_sequential_limits, THEN spec[where x="\<lambda> n. snd (f (r n))"], THEN spec[where x="l - l'"]]
      using f(3) by auto
    hence "l \<in> ?S" using `l' \<in> s` apply auto apply(rule_tac x=l' in exI) apply(rule_tac x="l - l'" in exI) by auto
  }
  thus ?thesis unfolding closed_sequential_limits by fast
qed

lemma closed_compact_sums:
  fixes s t :: "'a::real_normed_vector set"
  assumes "closed s"  "compact t"
  shows "closed {x + y | x y. x \<in> s \<and> y \<in> t}"
proof-
  have "{x + y |x y. x \<in> t \<and> y \<in> s} = {x + y |x y. x \<in> s \<and> y \<in> t}" apply auto
    apply(rule_tac x=y in exI) apply auto apply(rule_tac x=y in exI) by auto
  thus ?thesis using compact_closed_sums[OF assms(2,1)] by simp
qed

lemma compact_closed_differences:
  fixes s t :: "'a::real_normed_vector set"
  assumes "compact s"  "closed t"
  shows "closed {x - y | x y. x \<in> s \<and> y \<in> t}"
proof-
  have "{x + y |x y. x \<in> s \<and> y \<in> uminus ` t} =  {x - y |x y. x \<in> s \<and> y \<in> t}"
    apply auto apply(rule_tac x=xa in exI) apply auto apply(rule_tac x=xa in exI) by auto
  thus ?thesis using compact_closed_sums[OF assms(1) closed_negations[OF assms(2)]] by auto
qed

lemma closed_compact_differences:
  fixes s t :: "'a::real_normed_vector set"
  assumes "closed s" "compact t"
  shows "closed {x - y | x y. x \<in> s \<and> y \<in> t}"
proof-
  have "{x + y |x y. x \<in> s \<and> y \<in> uminus ` t} = {x - y |x y. x \<in> s \<and> y \<in> t}"
    apply auto apply(rule_tac x=xa in exI) apply auto apply(rule_tac x=xa in exI) by auto
 thus ?thesis using closed_compact_sums[OF assms(1) compact_negations[OF assms(2)]] by simp
qed

lemma closed_translation:
  fixes a :: "'a::real_normed_vector"
  assumes "closed s"  shows "closed ((\<lambda>x. a + x) ` s)"
proof-
  have "{a + y |y. y \<in> s} = (op + a ` s)" by auto
  thus ?thesis using compact_closed_sums[OF compact_sing[of a] assms] by auto
qed

lemma translation_UNIV:
  fixes a :: "'a::ab_group_add" shows "range (\<lambda>x. a + x) = UNIV"
  apply (auto simp add: image_iff) apply(rule_tac x="x - a" in exI) by auto

lemma translation_diff:
  fixes a :: "'a::ab_group_add"
  shows "(\<lambda>x. a + x) ` (s - t) = ((\<lambda>x. a + x) ` s) - ((\<lambda>x. a + x) ` t)"
  by auto

lemma closure_translation:
  fixes a :: "'a::real_normed_vector"
  shows "closure ((\<lambda>x. a + x) ` s) = (\<lambda>x. a + x) ` (closure s)"
proof-
  have *:"op + a ` (UNIV - s) = UNIV - op + a ` s"
    apply auto unfolding image_iff apply(rule_tac x="x - a" in bexI) by auto
  show ?thesis unfolding closure_interior translation_diff translation_UNIV
    using interior_translation[of a "UNIV - s"] unfolding * by auto
qed

lemma frontier_translation:
  fixes a :: "'a::real_normed_vector"
  shows "frontier((\<lambda>x. a + x) ` s) = (\<lambda>x. a + x) ` (frontier s)"
  unfolding frontier_def translation_diff interior_translation closure_translation by auto

subsection{* Separation between points and sets.                                       *}

lemma separate_point_closed:
  fixes s :: "'a::heine_borel set"
  shows "closed s \<Longrightarrow> a \<notin> s  ==> (\<exists>d>0. \<forall>x\<in>s. d \<le> dist a x)"
proof(cases "s = {}")
  case True
  thus ?thesis by(auto intro!: exI[where x=1])
next
  case False
  assume "closed s" "a \<notin> s"
  then obtain x where "x\<in>s" "\<forall>y\<in>s. dist a x \<le> dist a y" using `s \<noteq> {}` distance_attains_inf [of s a] by blast
  with `x\<in>s` show ?thesis using dist_pos_lt[of a x] and`a \<notin> s` by blast
qed

lemma separate_compact_closed:
  fixes s t :: "'a::{heine_borel, real_normed_vector} set"
    (* TODO: does this generalize to heine_borel? *)
  assumes "compact s" and "closed t" and "s \<inter> t = {}"
  shows "\<exists>d>0. \<forall>x\<in>s. \<forall>y\<in>t. d \<le> dist x y"
proof-
  have "0 \<notin> {x - y |x y. x \<in> s \<and> y \<in> t}" using assms(3) by auto
  then obtain d where "d>0" and d:"\<forall>x\<in>{x - y |x y. x \<in> s \<and> y \<in> t}. d \<le> dist 0 x"
    using separate_point_closed[OF compact_closed_differences[OF assms(1,2)], of 0] by auto
  { fix x y assume "x\<in>s" "y\<in>t"
    hence "x - y \<in> {x - y |x y. x \<in> s \<and> y \<in> t}" by auto
    hence "d \<le> dist (x - y) 0" using d[THEN bspec[where x="x - y"]] using dist_commute
      by (auto  simp add: dist_commute)
    hence "d \<le> dist x y" unfolding dist_norm by auto  }
  thus ?thesis using `d>0` by auto
qed

lemma separate_closed_compact:
  fixes s t :: "'a::{heine_borel, real_normed_vector} set"
  assumes "closed s" and "compact t" and "s \<inter> t = {}"
  shows "\<exists>d>0. \<forall>x\<in>s. \<forall>y\<in>t. d \<le> dist x y"
proof-
  have *:"t \<inter> s = {}" using assms(3) by auto
  show ?thesis using separate_compact_closed[OF assms(2,1) *]
    apply auto apply(rule_tac x=d in exI) apply auto apply (erule_tac x=y in ballE)
    by (auto simp add: dist_commute)
qed

(* A cute way of denoting open and closed intervals using overloading.       *)

lemma interval: fixes a :: "'a::ord^'n::finite" shows
  "{a <..< b} = {x::'a^'n. \<forall>i. a$i < x$i \<and> x$i < b$i}" and
  "{a .. b} = {x::'a^'n. \<forall>i. a$i \<le> x$i \<and> x$i \<le> b$i}"
  by (auto simp add: expand_set_eq vector_less_def vector_less_eq_def)

lemma mem_interval: fixes a :: "'a::ord^'n::finite" shows
  "x \<in> {a<..<b} \<longleftrightarrow> (\<forall>i. a$i < x$i \<and> x$i < b$i)"
  "x \<in> {a .. b} \<longleftrightarrow> (\<forall>i. a$i \<le> x$i \<and> x$i \<le> b$i)"
  using interval[of a b] by(auto simp add: expand_set_eq vector_less_def vector_less_eq_def)

lemma mem_interval_1: fixes x :: "real^1" shows
 "(x \<in> {a .. b} \<longleftrightarrow> dest_vec1 a \<le> dest_vec1 x \<and> dest_vec1 x \<le> dest_vec1 b)"
 "(x \<in> {a<..<b} \<longleftrightarrow> dest_vec1 a < dest_vec1 x \<and> dest_vec1 x < dest_vec1 b)"
by(simp_all add: Cart_eq vector_less_def vector_less_eq_def dest_vec1_def forall_1)

lemma interval_eq_empty: fixes a :: "real^'n::finite" shows
 "({a <..< b} = {} \<longleftrightarrow> (\<exists>i. b$i \<le> a$i))" (is ?th1) and
 "({a  ..  b} = {} \<longleftrightarrow> (\<exists>i. b$i < a$i))" (is ?th2)
proof-
  { fix i x assume as:"b$i \<le> a$i" and x:"x\<in>{a <..< b}"
    hence "a $ i < x $ i \<and> x $ i < b $ i" unfolding mem_interval by auto
    hence "a$i < b$i" by auto
    hence False using as by auto  }
  moreover
  { assume as:"\<forall>i. \<not> (b$i \<le> a$i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    { fix i
      have "a$i < b$i" using as[THEN spec[where x=i]] by auto
      hence "a$i < ((1/2) *\<^sub>R (a+b)) $ i" "((1/2) *\<^sub>R (a+b)) $ i < b$i"
	unfolding vector_smult_component and vector_add_component
	by (auto simp add: less_divide_eq_number_of1)  }
    hence "{a <..< b} \<noteq> {}" using mem_interval(1)[of "?x" a b] by auto  }
  ultimately show ?th1 by blast

  { fix i x assume as:"b$i < a$i" and x:"x\<in>{a .. b}"
    hence "a $ i \<le> x $ i \<and> x $ i \<le> b $ i" unfolding mem_interval by auto
    hence "a$i \<le> b$i" by auto
    hence False using as by auto  }
  moreover
  { assume as:"\<forall>i. \<not> (b$i < a$i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    { fix i
      have "a$i \<le> b$i" using as[THEN spec[where x=i]] by auto
      hence "a$i \<le> ((1/2) *\<^sub>R (a+b)) $ i" "((1/2) *\<^sub>R (a+b)) $ i \<le> b$i"
	unfolding vector_smult_component and vector_add_component
	by (auto simp add: less_divide_eq_number_of1)  }
    hence "{a .. b} \<noteq> {}" using mem_interval(2)[of "?x" a b] by auto  }
  ultimately show ?th2 by blast
qed

lemma interval_ne_empty: fixes a :: "real^'n::finite" shows
  "{a  ..  b} \<noteq> {} \<longleftrightarrow> (\<forall>i. a$i \<le> b$i)" and
  "{a <..< b} \<noteq> {} \<longleftrightarrow> (\<forall>i. a$i < b$i)"
  unfolding interval_eq_empty[of a b] by (auto simp add: not_less not_le) (* BH: Why doesn't just "auto" work here? *)

lemma subset_interval_imp: fixes a :: "real^'n::finite" shows
 "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> {c .. d} \<subseteq> {a .. b}" and
 "(\<forall>i. a$i < c$i \<and> d$i < b$i) \<Longrightarrow> {c .. d} \<subseteq> {a<..<b}" and
 "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> {c<..<d} \<subseteq> {a .. b}" and
 "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> {c<..<d} \<subseteq> {a<..<b}"
  unfolding subset_eq[unfolded Ball_def] unfolding mem_interval
  by (auto intro: order_trans less_le_trans le_less_trans less_imp_le) (* BH: Why doesn't just "auto" work here? *)

lemma interval_sing: fixes a :: "'a::linorder^'n::finite" shows
 "{a .. a} = {a} \<and> {a<..<a} = {}"
apply(auto simp add: expand_set_eq vector_less_def vector_less_eq_def Cart_eq)
apply (simp add: order_eq_iff)
apply (auto simp add: not_less less_imp_le)
done

lemma interval_open_subset_closed:  fixes a :: "'a::preorder^'n::finite" shows
 "{a<..<b} \<subseteq> {a .. b}"
proof(simp add: subset_eq, rule)
  fix x
  assume x:"x \<in>{a<..<b}"
  { fix i
    have "a $ i \<le> x $ i"
      using x order_less_imp_le[of "a$i" "x$i"]
      by(simp add: expand_set_eq vector_less_def vector_less_eq_def Cart_eq)
  }
  moreover
  { fix i
    have "x $ i \<le> b $ i"
      using x order_less_imp_le[of "x$i" "b$i"]
      by(simp add: expand_set_eq vector_less_def vector_less_eq_def Cart_eq)
  }
  ultimately
  show "a \<le> x \<and> x \<le> b"
    by(simp add: expand_set_eq vector_less_def vector_less_eq_def Cart_eq)
qed

lemma subset_interval: fixes a :: "real^'n::finite" shows
 "{c .. d} \<subseteq> {a .. b} \<longleftrightarrow> (\<forall>i. c$i \<le> d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th1) and
 "{c .. d} \<subseteq> {a<..<b} \<longleftrightarrow> (\<forall>i. c$i \<le> d$i) --> (\<forall>i. a$i < c$i \<and> d$i < b$i)" (is ?th2) and
 "{c<..<d} \<subseteq> {a .. b} \<longleftrightarrow> (\<forall>i. c$i < d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th3) and
 "{c<..<d} \<subseteq> {a<..<b} \<longleftrightarrow> (\<forall>i. c$i < d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th4)
proof-
  show ?th1 unfolding subset_eq and Ball_def and mem_interval by (auto intro: order_trans)
  show ?th2 unfolding subset_eq and Ball_def and mem_interval by (auto intro: le_less_trans less_le_trans order_trans less_imp_le)
  { assume as: "{c<..<d} \<subseteq> {a .. b}" "\<forall>i. c$i < d$i"
    hence "{c<..<d} \<noteq> {}" unfolding interval_eq_empty by (auto, drule_tac x=i in spec, simp) (* BH: Why doesn't just "auto" work? *)
    fix i
    (** TODO combine the following two parts as done in the HOL_light version. **)
    { let ?x = "(\<chi> j. (if j=i then ((min (a$j) (d$j))+c$j)/2 else (c$j+d$j)/2))::real^'n"
      assume as2: "a$i > c$i"
      { fix j
	have "c $ j < ?x $ j \<and> ?x $ j < d $ j" unfolding Cart_lambda_beta
	  apply(cases "j=i") using as(2)[THEN spec[where x=j]]
	  by (auto simp add: less_divide_eq_number_of1 as2)  }
      hence "?x\<in>{c<..<d}" unfolding mem_interval by auto
      moreover
      have "?x\<notin>{a .. b}"
	unfolding mem_interval apply auto apply(rule_tac x=i in exI)
	using as(2)[THEN spec[where x=i]] and as2
	by (auto simp add: less_divide_eq_number_of1)
      ultimately have False using as by auto  }
    hence "a$i \<le> c$i" by(rule ccontr)auto
    moreover
    { let ?x = "(\<chi> j. (if j=i then ((max (b$j) (c$j))+d$j)/2 else (c$j+d$j)/2))::real^'n"
      assume as2: "b$i < d$i"
      { fix j
	have "d $ j > ?x $ j \<and> ?x $ j > c $ j" unfolding Cart_lambda_beta
	  apply(cases "j=i") using as(2)[THEN spec[where x=j]]
	  by (auto simp add: less_divide_eq_number_of1 as2)  }
      hence "?x\<in>{c<..<d}" unfolding mem_interval by auto
      moreover
      have "?x\<notin>{a .. b}"
	unfolding mem_interval apply auto apply(rule_tac x=i in exI)
	using as(2)[THEN spec[where x=i]] and as2
	by (auto simp add: less_divide_eq_number_of1)
      ultimately have False using as by auto  }
    hence "b$i \<ge> d$i" by(rule ccontr)auto
    ultimately
    have "a$i \<le> c$i \<and> d$i \<le> b$i" by auto
  } note part1 = this
  thus ?th3 unfolding subset_eq and Ball_def and mem_interval apply auto apply (erule_tac x=ia in allE, simp)+ by (erule_tac x=i in allE, erule_tac x=i in allE, simp)+
  { assume as:"{c<..<d} \<subseteq> {a<..<b}" "\<forall>i. c$i < d$i"
    fix i
    from as(1) have "{c<..<d} \<subseteq> {a..b}" using interval_open_subset_closed[of a b] by auto
    hence "a$i \<le> c$i \<and> d$i \<le> b$i" using part1 and as(2) by auto  } note * = this
  thus ?th4 unfolding subset_eq and Ball_def and mem_interval apply auto apply (erule_tac x=ia in allE, simp)+ by (erule_tac x=i in allE, erule_tac x=i in allE, simp)+
qed

lemma disjoint_interval: fixes a::"real^'n::finite" shows
  "{a .. b} \<inter> {c .. d} = {} \<longleftrightarrow> (\<exists>i. (b$i < a$i \<or> d$i < c$i \<or> b$i < c$i \<or> d$i < a$i))" (is ?th1) and
  "{a .. b} \<inter> {c<..<d} = {} \<longleftrightarrow> (\<exists>i. (b$i < a$i \<or> d$i \<le> c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th2) and
  "{a<..<b} \<inter> {c .. d} = {} \<longleftrightarrow> (\<exists>i. (b$i \<le> a$i \<or> d$i < c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th3) and
  "{a<..<b} \<inter> {c<..<d} = {} \<longleftrightarrow> (\<exists>i. (b$i \<le> a$i \<or> d$i \<le> c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th4)
proof-
  let ?z = "(\<chi> i. ((max (a$i) (c$i)) + (min (b$i) (d$i))) / 2)::real^'n"
  show ?th1 ?th2 ?th3 ?th4
  unfolding expand_set_eq and Int_iff and empty_iff and mem_interval and all_conj_distrib[THEN sym] and eq_False
  apply (auto elim!: allE[where x="?z"])
  apply ((rule_tac x=x in exI, force) | (rule_tac x=i in exI, force))+
  done
qed

lemma inter_interval: fixes a :: "'a::linorder^'n::finite" shows
 "{a .. b} \<inter> {c .. d} =  {(\<chi> i. max (a$i) (c$i)) .. (\<chi> i. min (b$i) (d$i))}"
  unfolding expand_set_eq and Int_iff and mem_interval
  by (auto simp add: less_divide_eq_number_of1 intro!: bexI)

(* Moved interval_open_subset_closed a bit upwards *)

lemma open_interval_lemma: fixes x :: "real" shows
 "a < x \<Longrightarrow> x < b ==> (\<exists>d>0. \<forall>x'. abs(x' - x) < d --> a < x' \<and> x' < b)"
  by(rule_tac x="min (x - a) (b - x)" in exI, auto)

lemma open_interval: fixes a :: "real^'n::finite" shows "open {a<..<b}"
proof-
  { fix x assume x:"x\<in>{a<..<b}"
    { fix i
      have "\<exists>d>0. \<forall>x'. abs (x' - (x$i)) < d \<longrightarrow> a$i < x' \<and> x' < b$i"
	using x[unfolded mem_interval, THEN spec[where x=i]]
	using open_interval_lemma[of "a$i" "x$i" "b$i"] by auto  }

    hence "\<forall>i. \<exists>d>0. \<forall>x'. abs (x' - (x$i)) < d \<longrightarrow> a$i < x' \<and> x' < b$i" by auto
    then obtain d where d:"\<forall>i. 0 < d i \<and> (\<forall>x'. \<bar>x' - x $ i\<bar> < d i \<longrightarrow> a $ i < x' \<and> x' < b $ i)"
      using bchoice[of "UNIV" "\<lambda>i d. d>0 \<and> (\<forall>x'. \<bar>x' - x $ i\<bar> < d \<longrightarrow> a $ i < x' \<and> x' < b $ i)"] by auto

    let ?d = "Min (range d)"
    have **:"finite (range d)" "range d \<noteq> {}" by auto
    have "?d>0" unfolding Min_gr_iff[OF **] using d by auto
    moreover
    { fix x' assume as:"dist x' x < ?d"
      { fix i
	have "\<bar>x'$i - x $ i\<bar> < d i"
	  using norm_bound_component_lt[OF as[unfolded dist_norm], of i]
	  unfolding vector_minus_component and Min_gr_iff[OF **] by auto
	hence "a $ i < x' $ i" "x' $ i < b $ i" using d[THEN spec[where x=i]] by auto  }
      hence "a < x' \<and> x' < b" unfolding vector_less_def by auto  }
    ultimately have "\<exists>e>0. \<forall>x'. dist x' x < e \<longrightarrow> x' \<in> {a<..<b}" by (auto, rule_tac x="?d" in exI, simp)
  }
  thus ?thesis unfolding open_dist using open_interval_lemma by auto
qed

lemma closed_interval: fixes a :: "real^'n::finite" shows "closed {a .. b}"
proof-
  { fix x i assume as:"\<forall>e>0. \<exists>x'\<in>{a..b}. x' \<noteq> x \<and> dist x' x < e"(* and xab:"a$i > x$i \<or> b$i < x$i"*)
    { assume xa:"a$i > x$i"
      with as obtain y where y:"y\<in>{a..b}" "y \<noteq> x" "dist y x < a$i - x$i" by(erule_tac x="a$i - x$i" in allE)auto
      hence False unfolding mem_interval and dist_norm
	using component_le_norm[of "y-x" i, unfolded vector_minus_component] and xa by(auto elim!: allE[where x=i])
    } hence "a$i \<le> x$i" by(rule ccontr)auto
    moreover
    { assume xb:"b$i < x$i"
      with as obtain y where y:"y\<in>{a..b}" "y \<noteq> x" "dist y x < x$i - b$i" by(erule_tac x="x$i - b$i" in allE)auto
      hence False unfolding mem_interval and dist_norm
	using component_le_norm[of "y-x" i, unfolded vector_minus_component] and xb by(auto elim!: allE[where x=i])
    } hence "x$i \<le> b$i" by(rule ccontr)auto
    ultimately
    have "a $ i \<le> x $ i \<and> x $ i \<le> b $ i" by auto }
  thus ?thesis unfolding closed_limpt islimpt_approachable mem_interval by auto
qed

lemma interior_closed_interval: fixes a :: "real^'n::finite" shows
 "interior {a .. b} = {a<..<b}" (is "?L = ?R")
proof(rule subset_antisym)
  show "?R \<subseteq> ?L" using interior_maximal[OF interval_open_subset_closed open_interval] by auto
next
  { fix x assume "\<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> {a..b}"
    then obtain s where s:"open s" "x \<in> s" "s \<subseteq> {a..b}" by auto
    then obtain e where "e>0" and e:"\<forall>x'. dist x' x < e \<longrightarrow> x' \<in> {a..b}" unfolding open_dist and subset_eq by auto
    { fix i
      have "dist (x - (e / 2) *\<^sub>R basis i) x < e"
	   "dist (x + (e / 2) *\<^sub>R basis i) x < e"
	unfolding dist_norm apply auto
	unfolding norm_minus_cancel using norm_basis[of i] and `e>0` by auto
      hence "a $ i \<le> (x - (e / 2) *\<^sub>R basis i) $ i"
                    "(x + (e / 2) *\<^sub>R basis i) $ i \<le> b $ i"
	using e[THEN spec[where x="x - (e/2) *\<^sub>R basis i"]]
	and   e[THEN spec[where x="x + (e/2) *\<^sub>R basis i"]]
	unfolding mem_interval by (auto elim!: allE[where x=i])
      hence "a $ i < x $ i" and "x $ i < b $ i"
	unfolding vector_minus_component and vector_add_component
	unfolding vector_smult_component and basis_component using `e>0` by auto   }
    hence "x \<in> {a<..<b}" unfolding mem_interval by auto  }
  thus "?L \<subseteq> ?R" unfolding interior_def and subset_eq by auto
qed

lemma bounded_closed_interval: fixes a :: "real^'n::finite" shows
 "bounded {a .. b}"
proof-
  let ?b = "\<Sum>i\<in>UNIV. \<bar>a$i\<bar> + \<bar>b$i\<bar>"
  { fix x::"real^'n" assume x:"\<forall>i. a $ i \<le> x $ i \<and> x $ i \<le> b $ i"
    { fix i
      have "\<bar>x$i\<bar> \<le> \<bar>a$i\<bar> + \<bar>b$i\<bar>" using x[THEN spec[where x=i]] by auto  }
    hence "(\<Sum>i\<in>UNIV. \<bar>x $ i\<bar>) \<le> ?b" by(rule setsum_mono)
    hence "norm x \<le> ?b" using norm_le_l1[of x] by auto  }
  thus ?thesis unfolding interval and bounded_iff by auto
qed

lemma bounded_interval: fixes a :: "real^'n::finite" shows
 "bounded {a .. b} \<and> bounded {a<..<b}"
  using bounded_closed_interval[of a b]
  using interval_open_subset_closed[of a b]
  using bounded_subset[of "{a..b}" "{a<..<b}"]
  by simp

lemma not_interval_univ: fixes a :: "real^'n::finite" shows
 "({a .. b} \<noteq> UNIV) \<and> ({a<..<b} \<noteq> UNIV)"
  using bounded_interval[of a b]
  by auto

lemma compact_interval: fixes a :: "real^'n::finite" shows
 "compact {a .. b}"
  using bounded_closed_imp_compact using bounded_interval[of a b] using closed_interval[of a b] by auto

lemma open_interval_midpoint: fixes a :: "real^'n::finite"
  assumes "{a<..<b} \<noteq> {}" shows "((1/2) *\<^sub>R (a + b)) \<in> {a<..<b}"
proof-
  { fix i
    have "a $ i < ((1 / 2) *\<^sub>R (a + b)) $ i \<and> ((1 / 2) *\<^sub>R (a + b)) $ i < b $ i"
      using assms[unfolded interval_ne_empty, THEN spec[where x=i]]
      unfolding vector_smult_component and vector_add_component
      by(auto simp add: less_divide_eq_number_of1)  }
  thus ?thesis unfolding mem_interval by auto
qed

lemma open_closed_interval_convex: fixes x :: "real^'n::finite"
  assumes x:"x \<in> {a<..<b}" and y:"y \<in> {a .. b}" and e:"0 < e" "e \<le> 1"
  shows "(e *\<^sub>R x + (1 - e) *\<^sub>R y) \<in> {a<..<b}"
proof-
  { fix i
    have "a $ i = e * a$i + (1 - e) * a$i" unfolding left_diff_distrib by simp
    also have "\<dots> < e * x $ i + (1 - e) * y $ i" apply(rule add_less_le_mono)
      using e unfolding mult_less_cancel_left and mult_le_cancel_left apply simp_all
      using x unfolding mem_interval  apply simp
      using y unfolding mem_interval  apply simp
      done
    finally have "a $ i < (e *\<^sub>R x + (1 - e) *\<^sub>R y) $ i" by auto
    moreover {
    have "b $ i = e * b$i + (1 - e) * b$i" unfolding left_diff_distrib by simp
    also have "\<dots> > e * x $ i + (1 - e) * y $ i" apply(rule add_less_le_mono)
      using e unfolding mult_less_cancel_left and mult_le_cancel_left apply simp_all
      using x unfolding mem_interval  apply simp
      using y unfolding mem_interval  apply simp
      done
    finally have "(e *\<^sub>R x + (1 - e) *\<^sub>R y) $ i < b $ i" by auto
    } ultimately have "a $ i < (e *\<^sub>R x + (1 - e) *\<^sub>R y) $ i \<and> (e *\<^sub>R x + (1 - e) *\<^sub>R y) $ i < b $ i" by auto }
  thus ?thesis unfolding mem_interval by auto
qed

lemma closure_open_interval: fixes a :: "real^'n::finite"
  assumes "{a<..<b} \<noteq> {}"
  shows "closure {a<..<b} = {a .. b}"
proof-
  have ab:"a < b" using assms[unfolded interval_ne_empty] unfolding vector_less_def by auto
  let ?c = "(1 / 2) *\<^sub>R (a + b)"
  { fix x assume as:"x \<in> {a .. b}"
    def f == "\<lambda>n::nat. x + (inverse (real n + 1)) *\<^sub>R (?c - x)"
    { fix n assume fn:"f n < b \<longrightarrow> a < f n \<longrightarrow> f n = x" and xc:"x \<noteq> ?c"
      have *:"0 < inverse (real n + 1)" "inverse (real n + 1) \<le> 1" unfolding inverse_le_1_iff by auto
      have "(inverse (real n + 1)) *\<^sub>R ((1 / 2) *\<^sub>R (a + b)) + (1 - inverse (real n + 1)) *\<^sub>R x =
	x + (inverse (real n + 1)) *\<^sub>R (((1 / 2) *\<^sub>R (a + b)) - x)"
        by (auto simp add: algebra_simps)
      hence "f n < b" and "a < f n" using open_closed_interval_convex[OF open_interval_midpoint[OF assms] as *] unfolding f_def by auto
      hence False using fn unfolding f_def using xc by(auto simp add: vector_mul_lcancel vector_ssub_ldistrib)  }
    moreover
    { assume "\<not> (f ---> x) sequentially"
      { fix e::real assume "e>0"
	hence "\<exists>N::nat. inverse (real (N + 1)) < e" using real_arch_inv[of e] apply (auto simp add: Suc_pred') apply(rule_tac x="n - 1" in exI) by auto
	then obtain N::nat where "inverse (real (N + 1)) < e" by auto
	hence "\<forall>n\<ge>N. inverse (real n + 1) < e" by (auto, metis Suc_le_mono le_SucE less_imp_inverse_less nat_le_real_less order_less_trans real_of_nat_Suc real_of_nat_Suc_gt_zero)
	hence "\<exists>N::nat. \<forall>n\<ge>N. inverse (real n + 1) < e" by auto  }
      hence "((\<lambda>n. inverse (real n + 1)) ---> 0) sequentially"
	unfolding Lim_sequentially by(auto simp add: dist_norm)
      hence "(f ---> x) sequentially" unfolding f_def
	using Lim_add[OF Lim_const, of "\<lambda>n::nat. (inverse (real n + 1)) *\<^sub>R ((1 / 2) *\<^sub>R (a + b) - x)" 0 sequentially x]
	using Lim_vmul[of "\<lambda>n::nat. inverse (real n + 1)" 0 sequentially "((1 / 2) *\<^sub>R (a + b) - x)"] by auto  }
    ultimately have "x \<in> closure {a<..<b}"
      using as and open_interval_midpoint[OF assms] unfolding closure_def unfolding islimpt_sequential by(cases "x=?c")auto  }
  thus ?thesis using closure_minimal[OF interval_open_subset_closed closed_interval, of a b] by blast
qed

lemma bounded_subset_open_interval_symmetric: fixes s::"(real^'n::finite) set"
  assumes "bounded s"  shows "\<exists>a. s \<subseteq> {-a<..<a}"
proof-
  obtain b where "b>0" and b:"\<forall>x\<in>s. norm x \<le> b" using assms[unfolded bounded_pos] by auto
  def a \<equiv> "(\<chi> i. b+1)::real^'n"
  { fix x assume "x\<in>s"
    fix i
    have "(-a)$i < x$i" and "x$i < a$i" using b[THEN bspec[where x=x], OF `x\<in>s`] and component_le_norm[of x i]
      unfolding vector_uminus_component and a_def and Cart_lambda_beta by auto
  }
  thus ?thesis by(auto intro: exI[where x=a] simp add: vector_less_def)
qed

lemma bounded_subset_open_interval:
  fixes s :: "(real ^ 'n::finite) set"
  shows "bounded s ==> (\<exists>a b. s \<subseteq> {a<..<b})"
  by (auto dest!: bounded_subset_open_interval_symmetric)

lemma bounded_subset_closed_interval_symmetric:
  fixes s :: "(real ^ 'n::finite) set"
  assumes "bounded s" shows "\<exists>a. s \<subseteq> {-a .. a}"
proof-
  obtain a where "s \<subseteq> {- a<..<a}" using bounded_subset_open_interval_symmetric[OF assms] by auto
  thus ?thesis using interval_open_subset_closed[of "-a" a] by auto
qed

lemma bounded_subset_closed_interval:
  fixes s :: "(real ^ 'n::finite) set"
  shows "bounded s ==> (\<exists>a b. s \<subseteq> {a .. b})"
  using bounded_subset_closed_interval_symmetric[of s] by auto

lemma frontier_closed_interval:
  fixes a b :: "real ^ _"
  shows "frontier {a .. b} = {a .. b} - {a<..<b}"
  unfolding frontier_def unfolding interior_closed_interval and closure_closed[OF closed_interval] ..

lemma frontier_open_interval:
  fixes a b :: "real ^ _"
  shows "frontier {a<..<b} = (if {a<..<b} = {} then {} else {a .. b} - {a<..<b})"
proof(cases "{a<..<b} = {}")
  case True thus ?thesis using frontier_empty by auto
next
  case False thus ?thesis unfolding frontier_def and closure_open_interval[OF False] and interior_open[OF open_interval] by auto
qed

lemma inter_interval_mixed_eq_empty: fixes a :: "real^'n::finite"
  assumes "{c<..<d} \<noteq> {}"  shows "{a<..<b} \<inter> {c .. d} = {} \<longleftrightarrow> {a<..<b} \<inter> {c<..<d} = {}"
  unfolding closure_open_interval[OF assms, THEN sym] unfolding open_inter_closure_eq_empty[OF open_interval] ..


(* Some special cases for intervals in R^1.                                  *)

lemma all_1: "(\<forall>x::1. P x) \<longleftrightarrow> P 1"
  by (metis num1_eq_iff)

lemma ex_1: "(\<exists>x::1. P x) \<longleftrightarrow> P 1"
  by auto (metis num1_eq_iff)

lemma interval_cases_1: fixes x :: "real^1" shows
 "x \<in> {a .. b} ==> x \<in> {a<..<b} \<or> (x = a) \<or> (x = b)"
  by(simp add:  Cart_eq vector_less_def vector_less_eq_def all_1, auto)

lemma in_interval_1: fixes x :: "real^1" shows
 "(x \<in> {a .. b} \<longleftrightarrow> dest_vec1 a \<le> dest_vec1 x \<and> dest_vec1 x \<le> dest_vec1 b) \<and>
  (x \<in> {a<..<b} \<longleftrightarrow> dest_vec1 a < dest_vec1 x \<and> dest_vec1 x < dest_vec1 b)"
by(simp add: Cart_eq vector_less_def vector_less_eq_def all_1 dest_vec1_def)

lemma interval_eq_empty_1: fixes a :: "real^1" shows
  "{a .. b} = {} \<longleftrightarrow> dest_vec1 b < dest_vec1 a"
  "{a<..<b} = {} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a"
  unfolding interval_eq_empty and ex_1 and dest_vec1_def by auto

lemma subset_interval_1: fixes a :: "real^1" shows
 "({a .. b} \<subseteq> {c .. d} \<longleftrightarrow>  dest_vec1 b < dest_vec1 a \<or>
                dest_vec1 c \<le> dest_vec1 a \<and> dest_vec1 a \<le> dest_vec1 b \<and> dest_vec1 b \<le> dest_vec1 d)"
 "({a .. b} \<subseteq> {c<..<d} \<longleftrightarrow>  dest_vec1 b < dest_vec1 a \<or>
                dest_vec1 c < dest_vec1 a \<and> dest_vec1 a \<le> dest_vec1 b \<and> dest_vec1 b < dest_vec1 d)"
 "({a<..<b} \<subseteq> {c .. d} \<longleftrightarrow>  dest_vec1 b \<le> dest_vec1 a \<or>
                dest_vec1 c \<le> dest_vec1 a \<and> dest_vec1 a < dest_vec1 b \<and> dest_vec1 b \<le> dest_vec1 d)"
 "({a<..<b} \<subseteq> {c<..<d} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a \<or>
                dest_vec1 c \<le> dest_vec1 a \<and> dest_vec1 a < dest_vec1 b \<and> dest_vec1 b \<le> dest_vec1 d)"
  unfolding subset_interval[of a b c d] unfolding all_1 and dest_vec1_def by auto

lemma eq_interval_1: fixes a :: "real^1" shows
 "{a .. b} = {c .. d} \<longleftrightarrow>
          dest_vec1 b < dest_vec1 a \<and> dest_vec1 d < dest_vec1 c \<or>
          dest_vec1 a = dest_vec1 c \<and> dest_vec1 b = dest_vec1 d"
using set_eq_subset[of "{a .. b}" "{c .. d}"]
using subset_interval_1(1)[of a b c d]
using subset_interval_1(1)[of c d a b]
by auto (* FIXME: slow *)

lemma disjoint_interval_1: fixes a :: "real^1" shows
  "{a .. b} \<inter> {c .. d} = {} \<longleftrightarrow> dest_vec1 b < dest_vec1 a \<or> dest_vec1 d < dest_vec1 c  \<or>  dest_vec1 b < dest_vec1 c \<or> dest_vec1 d < dest_vec1 a"
  "{a .. b} \<inter> {c<..<d} = {} \<longleftrightarrow> dest_vec1 b < dest_vec1 a \<or> dest_vec1 d \<le> dest_vec1 c  \<or>  dest_vec1 b \<le> dest_vec1 c \<or> dest_vec1 d \<le> dest_vec1 a"
  "{a<..<b} \<inter> {c .. d} = {} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a \<or> dest_vec1 d < dest_vec1 c  \<or>  dest_vec1 b \<le> dest_vec1 c \<or> dest_vec1 d \<le> dest_vec1 a"
  "{a<..<b} \<inter> {c<..<d} = {} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a \<or> dest_vec1 d \<le> dest_vec1 c  \<or>  dest_vec1 b \<le> dest_vec1 c \<or> dest_vec1 d \<le> dest_vec1 a"
  unfolding disjoint_interval and dest_vec1_def ex_1 by auto

lemma open_closed_interval_1: fixes a :: "real^1" shows
 "{a<..<b} = {a .. b} - {a, b}"
  unfolding expand_set_eq apply simp unfolding vector_less_def and vector_less_eq_def and all_1 and dest_vec1_eq[THEN sym] and dest_vec1_def by auto

lemma closed_open_interval_1: "dest_vec1 (a::real^1) \<le> dest_vec1 b ==> {a .. b} = {a<..<b} \<union> {a,b}"
  unfolding expand_set_eq apply simp unfolding vector_less_def and vector_less_eq_def and all_1 and dest_vec1_eq[THEN sym] and dest_vec1_def by auto

(* Some stuff for half-infinite intervals too; FIXME: notation?  *)

lemma closed_interval_left: fixes b::"real^'n::finite"
  shows "closed {x::real^'n. \<forall>i. x$i \<le> b$i}"
proof-
  { fix i
    fix x::"real^'n" assume x:"\<forall>e>0. \<exists>x'\<in>{x. \<forall>i. x $ i \<le> b $ i}. x' \<noteq> x \<and> dist x' x < e"
    { assume "x$i > b$i"
      then obtain y where "y $ i \<le> b $ i"  "y \<noteq> x"  "dist y x < x$i - b$i" using x[THEN spec[where x="x$i - b$i"]] by auto
      hence False using component_le_norm[of "y - x" i] unfolding dist_norm and vector_minus_component by auto   }
    hence "x$i \<le> b$i" by(rule ccontr)auto  }
  thus ?thesis unfolding closed_limpt unfolding islimpt_approachable by blast
qed

lemma closed_interval_right: fixes a::"real^'n::finite"
  shows "closed {x::real^'n. \<forall>i. a$i \<le> x$i}"
proof-
  { fix i
    fix x::"real^'n" assume x:"\<forall>e>0. \<exists>x'\<in>{x. \<forall>i. a $ i \<le> x $ i}. x' \<noteq> x \<and> dist x' x < e"
    { assume "a$i > x$i"
      then obtain y where "a $ i \<le> y $ i"  "y \<noteq> x"  "dist y x < a$i - x$i" using x[THEN spec[where x="a$i - x$i"]] by auto
      hence False using component_le_norm[of "y - x" i] unfolding dist_norm and vector_minus_component by auto   }
    hence "a$i \<le> x$i" by(rule ccontr)auto  }
  thus ?thesis unfolding closed_limpt unfolding islimpt_approachable by blast
qed

subsection{* Intervals in general, including infinite and mixtures of open and closed. *}

definition "is_interval s \<longleftrightarrow> (\<forall>a\<in>s. \<forall>b\<in>s. \<forall>x. (\<forall>i. ((a$i \<le> x$i \<and> x$i \<le> b$i) \<or> (b$i \<le> x$i \<and> x$i \<le> a$i)))  \<longrightarrow> x \<in> s)"

lemma is_interval_interval: "is_interval {a .. b::real^'n::finite}" (is ?th1) "is_interval {a<..<b}" (is ?th2) proof - 
  have *:"\<And>x y z::real. x < y \<Longrightarrow> y < z \<Longrightarrow> x < z" by auto
  show ?th1 ?th2  unfolding is_interval_def mem_interval Ball_def atLeastAtMost_iff
    by(meson real_le_trans le_less_trans less_le_trans *)+ qed

lemma is_interval_empty:
 "is_interval {}"
  unfolding is_interval_def
  by simp

lemma is_interval_univ:
 "is_interval UNIV"
  unfolding is_interval_def
  by simp

subsection{* Closure of halfspaces and hyperplanes.                                    *}

lemma Lim_dot: fixes f :: "real^'m \<Rightarrow> real^'n::finite"
  assumes "(f ---> l) net"  shows "((\<lambda>y. a \<bullet> (f y)) ---> a \<bullet> l) net"
  unfolding dot_def by (intro tendsto_intros assms)

lemma continuous_at_dot:
  fixes x :: "real ^ _"
  shows "continuous (at x) (\<lambda>y. a \<bullet> y)"
proof-
  have "((\<lambda>x. x) ---> x) (at x)" unfolding Lim_at by auto
  thus ?thesis unfolding continuous_at and o_def using Lim_dot[of "\<lambda>x. x" x "at x" a] by auto
qed

lemma continuous_on_dot:
  fixes s :: "(real ^ _) set"
  shows "continuous_on s (\<lambda>y. a \<bullet> y)"
  using continuous_at_imp_continuous_on[of s "\<lambda>y. a \<bullet> y"]
  using continuous_at_dot
  by auto

lemma continuous_on_inner:
  fixes s :: "(real ^ _) set"
  shows "continuous_on s (inner a)"
  unfolding continuous_on by (rule ballI) (intro tendsto_intros)

lemma closed_halfspace_le: fixes a::"real^'n::finite"
  shows "closed {x. inner a x \<le> b}"
proof-
  have *:"{x \<in> UNIV. inner a x \<in> {r. \<exists>x. inner a x = r \<and> r \<le> b}} = {x. inner a x \<le> b}" by auto
  let ?T = "{..b}"
  have "closed ?T" by (rule closed_real_atMost)
  moreover have "{r. \<exists>x. inner a x = r \<and> r \<le> b} = range (inner a) \<inter> ?T"
    unfolding image_def by auto
  ultimately have "\<exists>T. closed T \<and> {r. \<exists>x. inner a x = r \<and> r \<le> b} = range (inner a) \<inter> T" by fast
  hence "closedin euclidean {x \<in> UNIV. inner a x \<in> {r. \<exists>x. inner a x = r \<and> r \<le> b}}"
    using continuous_on_inner[of UNIV a, unfolded continuous_on_closed subtopology_UNIV] unfolding closedin_closed
    by (fast elim!: allE[where x="{r. (\<exists>x. inner a x = r \<and> r \<le> b)}"])
  thus ?thesis unfolding closed_closedin[THEN sym] and * by auto
qed

lemma closed_halfspace_ge: "closed {x::real^_. inner a x \<ge> b}"
  using closed_halfspace_le[of "-a" "-b"] unfolding inner_minus_left by auto

lemma closed_hyperplane: "closed {x::real^_. inner a x = b}"
proof-
  have "{x. inner a x = b} = {x. inner a x \<ge> b} \<inter> {x. inner a x \<le> b}" by auto
  thus ?thesis using closed_halfspace_le[of a b] and closed_halfspace_ge[of b a] using closed_Int by auto
qed

lemma closed_halfspace_component_le:
  shows "closed {x::real^'n::finite. x$i \<le> a}"
  using closed_halfspace_le[of "(basis i)::real^'n" a] unfolding inner_basis[OF assms] by auto

lemma closed_halfspace_component_ge:
  shows "closed {x::real^'n::finite. x$i \<ge> a}"
  using closed_halfspace_ge[of a "(basis i)::real^'n"] unfolding inner_basis[OF assms] by auto

text{* Openness of halfspaces.                                                   *}

lemma open_halfspace_lt: "open {x::real^_. inner a x < b}"
proof-
  have "UNIV - {x. b \<le> inner a x} = {x. inner a x < b}" by auto
  thus ?thesis using closed_halfspace_ge[unfolded closed_def Compl_eq_Diff_UNIV, of b a] by auto
qed

lemma open_halfspace_gt: "open {x::real^_. inner a x > b}"
proof-
  have "UNIV - {x. b \<ge> inner a x} = {x. inner a x > b}" by auto
  thus ?thesis using closed_halfspace_le[unfolded closed_def Compl_eq_Diff_UNIV, of a b] by auto
qed

lemma open_halfspace_component_lt:
  shows "open {x::real^'n::finite. x$i < a}"
  using open_halfspace_lt[of "(basis i)::real^'n" a] unfolding inner_basis[OF assms] by auto

lemma open_halfspace_component_gt:
  shows "open {x::real^'n::finite. x$i  > a}"
  using open_halfspace_gt[of a "(basis i)::real^'n"] unfolding inner_basis[OF assms] by auto

text{* This gives a simple derivation of limit component bounds.                 *}

lemma Lim_component_le: fixes f :: "'a \<Rightarrow> real^'n::finite"
  assumes "(f ---> l) net" "\<not> (trivial_limit net)"  "eventually (\<lambda>x. f(x)$i \<le> b) net"
  shows "l$i \<le> b"
proof-
  { fix x have "x \<in> {x::real^'n. inner (basis i) x \<le> b} \<longleftrightarrow> x$i \<le> b" unfolding inner_basis by auto } note * = this
  show ?thesis using Lim_in_closed_set[of "{x. inner (basis i) x \<le> b}" f net l] unfolding *
    using closed_halfspace_le[of "(basis i)::real^'n" b] and assms(1,2,3) by auto
qed

lemma Lim_component_ge: fixes f :: "'a \<Rightarrow> real^'n::finite"
  assumes "(f ---> l) net"  "\<not> (trivial_limit net)"  "eventually (\<lambda>x. b \<le> (f x)$i) net"
  shows "b \<le> l$i"
proof-
  { fix x have "x \<in> {x::real^'n. inner (basis i) x \<ge> b} \<longleftrightarrow> x$i \<ge> b" unfolding inner_basis by auto } note * = this
  show ?thesis using Lim_in_closed_set[of "{x. inner (basis i) x \<ge> b}" f net l] unfolding *
    using closed_halfspace_ge[of b "(basis i)::real^'n"] and assms(1,2,3) by auto
qed

lemma Lim_component_eq: fixes f :: "'a \<Rightarrow> real^'n::finite"
  assumes net:"(f ---> l) net" "~(trivial_limit net)" and ev:"eventually (\<lambda>x. f(x)$i = b) net"
  shows "l$i = b"
  using ev[unfolded order_eq_iff eventually_and] using Lim_component_ge[OF net, of b i] and Lim_component_le[OF net, of i b] by auto

lemma Lim_drop_le: fixes f :: "'a \<Rightarrow> real^1" shows
  "(f ---> l) net \<Longrightarrow> ~(trivial_limit net) \<Longrightarrow> eventually (\<lambda>x. dest_vec1 (f x) \<le> b) net ==> dest_vec1 l \<le> b"
  using Lim_component_le[of f l net 1 b] unfolding dest_vec1_def by auto

lemma Lim_drop_ge: fixes f :: "'a \<Rightarrow> real^1" shows
 "(f ---> l) net \<Longrightarrow> ~(trivial_limit net) \<Longrightarrow> eventually (\<lambda>x. b \<le> dest_vec1 (f x)) net ==> b \<le> dest_vec1 l"
  using Lim_component_ge[of f l net b 1] unfolding dest_vec1_def by auto

text{* Limits relative to a union.                                               *}

lemma eventually_within_Un:
  "eventually P (net within (s \<union> t)) \<longleftrightarrow>
    eventually P (net within s) \<and> eventually P (net within t)"
  unfolding Limits.eventually_within
  by (auto elim!: eventually_rev_mp)

lemma Lim_within_union:
 "(f ---> l) (net within (s \<union> t)) \<longleftrightarrow>
  (f ---> l) (net within s) \<and> (f ---> l) (net within t)"
  unfolding tendsto_def
  by (auto simp add: eventually_within_Un)

lemma continuous_on_union:
  assumes "closed s" "closed t" "continuous_on s f" "continuous_on t f"
  shows "continuous_on (s \<union> t) f"
  using assms unfolding continuous_on unfolding Lim_within_union
  unfolding Lim unfolding trivial_limit_within unfolding closed_limpt by auto

lemma continuous_on_cases: fixes g :: "real^'m::finite \<Rightarrow> real ^'n::finite"
  assumes "closed s" "closed t" "continuous_on s f" "continuous_on t g"
          "\<forall>x. (x\<in>s \<and> \<not> P x) \<or> (x \<in> t \<and> P x) \<longrightarrow> f x = g x"
  shows "continuous_on (s \<union> t) (\<lambda>x. if P x then f x else g x)"
proof-
  let ?h = "(\<lambda>x. if P x then f x else g x)"
  have "\<forall>x\<in>s. f x = (if P x then f x else g x)" using assms(5) by auto
  hence "continuous_on s ?h" using continuous_on_eq[of s f ?h] using assms(3) by auto
  moreover
  have "\<forall>x\<in>t. g x = (if P x then f x else g x)" using assms(5) by auto
  hence "continuous_on t ?h" using continuous_on_eq[of t g ?h] using assms(4) by auto
  ultimately show ?thesis using continuous_on_union[OF assms(1,2), of ?h] by auto
qed


text{* Some more convenient intermediate-value theorem formulations.             *}

lemma connected_ivt_hyperplane: fixes y :: "real^'n::finite"
  assumes "connected s" "x \<in> s" "y \<in> s" "inner a x \<le> b" "b \<le> inner a y"
  shows "\<exists>z \<in> s. inner a z = b"
proof(rule ccontr)
  assume as:"\<not> (\<exists>z\<in>s. inner a z = b)"
  let ?A = "{x::real^'n. inner a x < b}"
  let ?B = "{x::real^'n. inner a x > b}"
  have "open ?A" "open ?B" using open_halfspace_lt and open_halfspace_gt by auto
  moreover have "?A \<inter> ?B = {}" by auto
  moreover have "s \<subseteq> ?A \<union> ?B" using as by auto
  ultimately show False using assms(1)[unfolded connected_def not_ex, THEN spec[where x="?A"], THEN spec[where x="?B"]] and assms(2-5) by auto
qed

lemma connected_ivt_component: fixes x::"real^'n::finite" shows
 "connected s \<Longrightarrow> x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> x$k \<le> a \<Longrightarrow> a \<le> y$k \<Longrightarrow> (\<exists>z\<in>s.  z$k = a)"
  using connected_ivt_hyperplane[of s x y "(basis k)::real^'n" a] by (auto simp add: inner_basis)

text{* Also more convenient formulations of monotone convergence.                *}

lemma bounded_increasing_convergent: fixes s::"nat \<Rightarrow> real^1"
  assumes "bounded {s n| n::nat. True}"  "\<forall>n. dest_vec1(s n) \<le> dest_vec1(s(Suc n))"
  shows "\<exists>l. (s ---> l) sequentially"
proof-
  obtain a where a:"\<forall>n. \<bar>dest_vec1 (s n)\<bar> \<le>  a" using assms(1)[unfolded bounded_iff abs_dest_vec1] by auto
  { fix m::nat
    have "\<And> n. n\<ge>m \<longrightarrow> dest_vec1 (s m) \<le> dest_vec1 (s n)"
      apply(induct_tac n) apply simp using assms(2) apply(erule_tac x="na" in allE) by(auto simp add: not_less_eq_eq)  }
  hence "\<forall>m n. m \<le> n \<longrightarrow> dest_vec1 (s m) \<le> dest_vec1 (s n)" by auto
  then obtain l where "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<bar>dest_vec1 (s n) - l\<bar> < e" using convergent_bounded_monotone[OF a] unfolding monoseq_def by auto
  thus ?thesis unfolding Lim_sequentially apply(rule_tac x="vec1 l" in exI)
    unfolding dist_norm unfolding abs_dest_vec1 and dest_vec1_sub by auto
qed

subsection{* Basic homeomorphism definitions.                                          *}

definition "homeomorphism s t f g \<equiv>
     (\<forall>x\<in>s. (g(f x) = x)) \<and> (f ` s = t) \<and> continuous_on s f \<and>
     (\<forall>y\<in>t. (f(g y) = y)) \<and> (g ` t = s) \<and> continuous_on t g"

definition homeomorphic :: "((real^'a::finite) set) \<Rightarrow> ((real^'b::finite) set) \<Rightarrow> bool" (infixr "homeomorphic" 60) where
  homeomorphic_def: "s homeomorphic t \<equiv> (\<exists>f g. homeomorphism s t f g)"

lemma homeomorphic_refl: "s homeomorphic s"
  unfolding homeomorphic_def
  unfolding homeomorphism_def
  using continuous_on_id
  apply(rule_tac x = "(\<lambda>x::real^'a.x)" in exI)
  apply(rule_tac x = "(\<lambda>x::real^'b.x)" in exI)
  by blast

lemma homeomorphic_sym:
 "s homeomorphic t \<longleftrightarrow> t homeomorphic s"
unfolding homeomorphic_def
unfolding homeomorphism_def
by blast

lemma homeomorphic_trans:
  assumes "s homeomorphic t" "t homeomorphic u" shows "s homeomorphic u"
proof-
  obtain f1 g1 where fg1:"\<forall>x\<in>s. g1 (f1 x) = x"  "f1 ` s = t" "continuous_on s f1" "\<forall>y\<in>t. f1 (g1 y) = y" "g1 ` t = s" "continuous_on t g1"
    using assms(1) unfolding homeomorphic_def homeomorphism_def by auto
  obtain f2 g2 where fg2:"\<forall>x\<in>t. g2 (f2 x) = x"  "f2 ` t = u" "continuous_on t f2" "\<forall>y\<in>u. f2 (g2 y) = y" "g2 ` u = t" "continuous_on u g2"
    using assms(2) unfolding homeomorphic_def homeomorphism_def by auto

  { fix x assume "x\<in>s" hence "(g1 \<circ> g2) ((f2 \<circ> f1) x) = x" using fg1(1)[THEN bspec[where x=x]] and fg2(1)[THEN bspec[where x="f1 x"]] and fg1(2) by auto }
  moreover have "(f2 \<circ> f1) ` s = u" using fg1(2) fg2(2) by auto
  moreover have "continuous_on s (f2 \<circ> f1)" using continuous_on_compose[OF fg1(3)] and fg2(3) unfolding fg1(2) by auto
  moreover { fix y assume "y\<in>u" hence "(f2 \<circ> f1) ((g1 \<circ> g2) y) = y" using fg2(4)[THEN bspec[where x=y]] and fg1(4)[THEN bspec[where x="g2 y"]] and fg2(5) by auto }
  moreover have "(g1 \<circ> g2) ` u = s" using fg1(5) fg2(5) by auto
  moreover have "continuous_on u (g1 \<circ> g2)" using continuous_on_compose[OF fg2(6)] and fg1(6)  unfolding fg2(5) by auto
  ultimately show ?thesis unfolding homeomorphic_def homeomorphism_def apply(rule_tac x="f2 \<circ> f1" in exI) apply(rule_tac x="g1 \<circ> g2" in exI) by auto
qed

lemma homeomorphic_minimal:
 "s homeomorphic t \<longleftrightarrow>
    (\<exists>f g. (\<forall>x\<in>s. f(x) \<in> t \<and> (g(f(x)) = x)) \<and>
           (\<forall>y\<in>t. g(y) \<in> s \<and> (f(g(y)) = y)) \<and>
           continuous_on s f \<and> continuous_on t g)"
unfolding homeomorphic_def homeomorphism_def
apply auto apply (rule_tac x=f in exI) apply (rule_tac x=g in exI)
apply auto apply (rule_tac x=f in exI) apply (rule_tac x=g in exI) apply auto
unfolding image_iff
apply(erule_tac x="g x" in ballE) apply(erule_tac x="x" in ballE)
apply auto apply(rule_tac x="g x" in bexI) apply auto
apply(erule_tac x="f x" in ballE) apply(erule_tac x="x" in ballE)
apply auto apply(rule_tac x="f x" in bexI) by auto

subsection{* Relatively weak hypotheses if a set is compact.                           *}

definition "inv_on f s = (\<lambda>x. SOME y. y\<in>s \<and> f y = x)"

lemma assumes "inj_on f s" "x\<in>s"
  shows "inv_on f s (f x) = x"
 using assms unfolding inj_on_def inv_on_def by auto

lemma homeomorphism_compact:
  fixes f :: "real ^ _ \<Rightarrow> real ^ _"
  assumes "compact s" "continuous_on s f"  "f ` s = t"  "inj_on f s"
  shows "\<exists>g. homeomorphism s t f g"
proof-
  def g \<equiv> "\<lambda>x. SOME y. y\<in>s \<and> f y = x"
  have g:"\<forall>x\<in>s. g (f x) = x" using assms(3) assms(4)[unfolded inj_on_def] unfolding g_def by auto
  { fix y assume "y\<in>t"
    then obtain x where x:"f x = y" "x\<in>s" using assms(3) by auto
    hence "g (f x) = x" using g by auto
    hence "f (g y) = y" unfolding x(1)[THEN sym] by auto  }
  hence g':"\<forall>x\<in>t. f (g x) = x" by auto
  moreover
  { fix x
    have "x\<in>s \<Longrightarrow> x \<in> g ` t" using g[THEN bspec[where x=x]] unfolding image_iff using assms(3) by(auto intro!: bexI[where x="f x"])
    moreover
    { assume "x\<in>g ` t"
      then obtain y where y:"y\<in>t" "g y = x" by auto
      then obtain x' where x':"x'\<in>s" "f x' = y" using assms(3) by auto
      hence "x \<in> s" unfolding g_def using someI2[of "\<lambda>b. b\<in>s \<and> f b = y" x' "\<lambda>x. x\<in>s"] unfolding y(2)[THEN sym] and g_def by auto }
    ultimately have "x\<in>s \<longleftrightarrow> x \<in> g ` t" by auto  }
  hence "g ` t = s" by auto
  ultimately
  show ?thesis unfolding homeomorphism_def homeomorphic_def
    apply(rule_tac x=g in exI) using g and assms(3) and continuous_on_inverse[OF assms(2,1), of g, unfolded assms(3)] and assms(2) by auto
qed

lemma homeomorphic_compact:
 "compact s \<Longrightarrow> continuous_on s f \<Longrightarrow> (f ` s = t) \<Longrightarrow> inj_on f s
          \<Longrightarrow> s homeomorphic t"
  unfolding homeomorphic_def by(metis homeomorphism_compact)

text{* Preservation of topological properties.                                   *}

lemma homeomorphic_compactness:
 "s homeomorphic t ==> (compact s \<longleftrightarrow> compact t)"
unfolding homeomorphic_def homeomorphism_def
by (metis compact_continuous_image)

text{* Results on translation, scaling etc.                                      *}

lemma homeomorphic_scaling:
  assumes "c \<noteq> 0"  shows "s homeomorphic ((\<lambda>x. c *\<^sub>R x) ` s)"
  unfolding homeomorphic_minimal
  apply(rule_tac x="\<lambda>x. c *\<^sub>R x" in exI)
  apply(rule_tac x="\<lambda>x. (1 / c) *\<^sub>R x" in exI)
  using assms apply auto
  using continuous_on_cmul[OF continuous_on_id] by auto

lemma homeomorphic_translation:
 "s homeomorphic ((\<lambda>x. a + x) ` s)"
  unfolding homeomorphic_minimal
  apply(rule_tac x="\<lambda>x. a + x" in exI)
  apply(rule_tac x="\<lambda>x. -a + x" in exI)
  using continuous_on_add[OF continuous_on_const continuous_on_id] by auto

lemma homeomorphic_affinity:
  assumes "c \<noteq> 0"  shows "s homeomorphic ((\<lambda>x. a + c *\<^sub>R x) ` s)"
proof-
  have *:"op + a ` op *\<^sub>R c ` s = (\<lambda>x. a + c *\<^sub>R x) ` s" by auto
  show ?thesis
    using homeomorphic_trans
    using homeomorphic_scaling[OF assms, of s]
    using homeomorphic_translation[of "(\<lambda>x. c *\<^sub>R x) ` s" a] unfolding * by auto
qed

lemma homeomorphic_balls: fixes a b ::"real^'a::finite"
  assumes "0 < d"  "0 < e"
  shows "(ball a d) homeomorphic  (ball b e)" (is ?th)
        "(cball a d) homeomorphic (cball b e)" (is ?cth)
proof-
  have *:"\<bar>e / d\<bar> > 0" "\<bar>d / e\<bar> >0" using assms using divide_pos_pos by auto
  show ?th unfolding homeomorphic_minimal
    apply(rule_tac x="\<lambda>x. b + (e/d) *\<^sub>R (x - a)" in exI)
    apply(rule_tac x="\<lambda>x. a + (d/e) *\<^sub>R (x - b)" in exI)
    using assms apply (auto simp add: dist_commute)
    unfolding dist_norm
    apply (auto simp add: pos_divide_less_eq mult_strict_left_mono)
    unfolding continuous_on
    by (intro ballI tendsto_intros, simp, assumption)+
next
  have *:"\<bar>e / d\<bar> > 0" "\<bar>d / e\<bar> >0" using assms using divide_pos_pos by auto
  show ?cth unfolding homeomorphic_minimal
    apply(rule_tac x="\<lambda>x. b + (e/d) *\<^sub>R (x - a)" in exI)
    apply(rule_tac x="\<lambda>x. a + (d/e) *\<^sub>R (x - b)" in exI)
    using assms apply (auto simp add: dist_commute)
    unfolding dist_norm
    apply (auto simp add: pos_divide_le_eq)
    unfolding continuous_on
    by (intro ballI tendsto_intros, simp, assumption)+
qed

text{* "Isometry" (up to constant bounds) of injective linear map etc.           *}

lemma cauchy_isometric:
  fixes x :: "nat \<Rightarrow> real ^ 'n::finite"
  assumes e:"0 < e" and s:"subspace s" and f:"linear f" and normf:"\<forall>x\<in>s. norm(f x) \<ge> e * norm(x)" and xs:"\<forall>n::nat. x n \<in> s" and cf:"Cauchy(f o x)"
  shows "Cauchy x"
proof-
  { fix d::real assume "d>0"
    then obtain N where N:"\<forall>n\<ge>N. norm (f (x n) - f (x N)) < e * d"
      using cf[unfolded cauchy o_def dist_norm, THEN spec[where x="e*d"]] and e and mult_pos_pos[of e d] by auto
    { fix n assume "n\<ge>N"
      hence "norm (f (x n - x N)) < e * d" using N[THEN spec[where x=n]] unfolding linear_sub[OF f, THEN sym] by auto
      moreover have "e * norm (x n - x N) \<le> norm (f (x n - x N))"
	using subspace_sub[OF s, of "x n" "x N"] using xs[THEN spec[where x=N]] and xs[THEN spec[where x=n]]
	using normf[THEN bspec[where x="x n - x N"]] by auto
      ultimately have "norm (x n - x N) < d" using `e>0`
	using mult_left_less_imp_less[of e "norm (x n - x N)" d] by auto   }
    hence "\<exists>N. \<forall>n\<ge>N. norm (x n - x N) < d" by auto }
  thus ?thesis unfolding cauchy and dist_norm by auto
qed

lemma complete_isometric_image:
  fixes f :: "real ^ _ \<Rightarrow> real ^ _"
  assumes "0 < e" and s:"subspace s" and f:"linear f" and normf:"\<forall>x\<in>s. norm(f x) \<ge> e * norm(x)" and cs:"complete s"
  shows "complete(f ` s)"
proof-
  { fix g assume as:"\<forall>n::nat. g n \<in> f ` s" and cfg:"Cauchy g"
    then obtain x where "\<forall>n. x n \<in> s \<and> g n = f (x n)" unfolding image_iff and Bex_def
      using choice[of "\<lambda> n xa. xa \<in> s \<and> g n = f xa"] by auto
    hence x:"\<forall>n. x n \<in> s"  "\<forall>n. g n = f (x n)" by auto
    hence "f \<circ> x = g" unfolding expand_fun_eq by auto
    then obtain l where "l\<in>s" and l:"(x ---> l) sequentially"
      using cs[unfolded complete_def, THEN spec[where x="x"]]
      using cauchy_isometric[OF `0<e` s f normf] and cfg and x(1) by auto
    hence "\<exists>l\<in>f ` s. (g ---> l) sequentially"
      using linear_continuous_at[OF f, unfolded continuous_at_sequentially, THEN spec[where x=x], of l]
      unfolding `f \<circ> x = g` by auto  }
  thus ?thesis unfolding complete_def by auto
qed

lemma dist_0_norm:
  fixes x :: "'a::real_normed_vector"
  shows "dist 0 x = norm x"
unfolding dist_norm by simp

lemma injective_imp_isometric: fixes f::"real^'m::finite \<Rightarrow> real^'n::finite"
  assumes s:"closed s"  "subspace s"  and f:"linear f" "\<forall>x\<in>s. (f x = 0) \<longrightarrow> (x = 0)"
  shows "\<exists>e>0. \<forall>x\<in>s. norm (f x) \<ge> e * norm(x)"
proof(cases "s \<subseteq> {0::real^'m}")
  case True
  { fix x assume "x \<in> s"
    hence "x = 0" using True by auto
    hence "norm x \<le> norm (f x)" by auto  }
  thus ?thesis by(auto intro!: exI[where x=1])
next
  case False
  then obtain a where a:"a\<noteq>0" "a\<in>s" by auto
  from False have "s \<noteq> {}" by auto
  let ?S = "{f x| x. (x \<in> s \<and> norm x = norm a)}"
  let ?S' = "{x::real^'m. x\<in>s \<and> norm x = norm a}"
  let ?S'' = "{x::real^'m. norm x = norm a}"

  have "?S'' = frontier(cball 0 (norm a))" unfolding frontier_cball and dist_norm by (auto simp add: norm_minus_cancel)
  hence "compact ?S''" using compact_frontier[OF compact_cball, of 0 "norm a"] by auto
  moreover have "?S' = s \<inter> ?S''" by auto
  ultimately have "compact ?S'" using closed_inter_compact[of s ?S''] using s(1) by auto
  moreover have *:"f ` ?S' = ?S" by auto
  ultimately have "compact ?S" using compact_continuous_image[OF linear_continuous_on[OF f(1)], of ?S'] by auto
  hence "closed ?S" using compact_imp_closed by auto
  moreover have "?S \<noteq> {}" using a by auto
  ultimately obtain b' where "b'\<in>?S" "\<forall>y\<in>?S. norm b' \<le> norm y" using distance_attains_inf[of ?S 0] unfolding dist_0_norm by auto
  then obtain b where "b\<in>s" and ba:"norm b = norm a" and b:"\<forall>x\<in>{x \<in> s. norm x = norm a}. norm (f b) \<le> norm (f x)" unfolding *[THEN sym] unfolding image_iff by auto

  let ?e = "norm (f b) / norm b"
  have "norm b > 0" using ba and a and norm_ge_zero by auto
  moreover have "norm (f b) > 0" using f(2)[THEN bspec[where x=b], OF `b\<in>s`] using `norm b >0` unfolding zero_less_norm_iff by auto
  ultimately have "0 < norm (f b) / norm b" by(simp only: divide_pos_pos)
  moreover
  { fix x assume "x\<in>s"
    hence "norm (f b) / norm b * norm x \<le> norm (f x)"
    proof(cases "x=0")
      case True thus "norm (f b) / norm b * norm x \<le> norm (f x)" by auto
    next
      case False
      hence *:"0 < norm a / norm x" using `a\<noteq>0` unfolding zero_less_norm_iff[THEN sym] by(simp only: divide_pos_pos)
      have "\<forall>c. \<forall>x\<in>s. c *\<^sub>R x \<in> s" using s[unfolded subspace_def smult_conv_scaleR] by auto
      hence "(norm a / norm x) *\<^sub>R x \<in> {x \<in> s. norm x = norm a}" using `x\<in>s` and `x\<noteq>0` by auto
      thus "norm (f b) / norm b * norm x \<le> norm (f x)" using b[THEN bspec[where x="(norm a / norm x) *\<^sub>R x"]]
	unfolding linear_cmul[OF f(1), unfolded smult_conv_scaleR] and ba using `x\<noteq>0` `a\<noteq>0`
	by (auto simp add: real_mult_commute pos_le_divide_eq pos_divide_le_eq)
    qed }
  ultimately
  show ?thesis by auto
qed

lemma closed_injective_image_subspace:
  fixes s :: "(real ^ _) set"
  assumes "subspace s" "linear f" "\<forall>x\<in>s. f x = 0 --> x = 0" "closed s"
  shows "closed(f ` s)"
proof-
  obtain e where "e>0" and e:"\<forall>x\<in>s. e * norm x \<le> norm (f x)" using injective_imp_isometric[OF assms(4,1,2,3)] by auto
  show ?thesis using complete_isometric_image[OF `e>0` assms(1,2) e] and assms(4)
    unfolding complete_eq_closed[THEN sym] by auto
qed

subsection{* Some properties of a canonical subspace.                                  *}

lemma subspace_substandard:
 "subspace {x::real^'n. (\<forall>i. P i \<longrightarrow> x$i = 0)}"
  unfolding subspace_def by(auto simp add: vector_add_component vector_smult_component elim!: ballE)

lemma closed_substandard:
 "closed {x::real^'n::finite. \<forall>i. P i --> x$i = 0}" (is "closed ?A")
proof-
  let ?D = "{i. P i}"
  let ?Bs = "{{x::real^'n. inner (basis i) x = 0}| i. i \<in> ?D}"
  { fix x
    { assume "x\<in>?A"
      hence x:"\<forall>i\<in>?D. x $ i = 0" by auto
      hence "x\<in> \<Inter> ?Bs" by(auto simp add: inner_basis x) }
    moreover
    { assume x:"x\<in>\<Inter>?Bs"
      { fix i assume i:"i \<in> ?D"
	then obtain B where BB:"B \<in> ?Bs" and B:"B = {x::real^'n. inner (basis i) x = 0}" by auto
	hence "x $ i = 0" unfolding B using x unfolding inner_basis by auto  }
      hence "x\<in>?A" by auto }
    ultimately have "x\<in>?A \<longleftrightarrow> x\<in> \<Inter>?Bs" by auto }
  hence "?A = \<Inter> ?Bs" by auto
  thus ?thesis by(auto simp add: closed_Inter closed_hyperplane)
qed

lemma dim_substandard:
  shows "dim {x::real^'n::finite. \<forall>i. i \<notin> d \<longrightarrow> x$i = 0} = card d" (is "dim ?A = _")
proof-
  let ?D = "UNIV::'n set"
  let ?B = "(basis::'n\<Rightarrow>real^'n) ` d"

    let ?bas = "basis::'n \<Rightarrow> real^'n"

  have "?B \<subseteq> ?A" by auto

  moreover
  { fix x::"real^'n" assume "x\<in>?A"
    with finite[of d]
    have "x\<in> span ?B"
    proof(induct d arbitrary: x)
      case empty hence "x=0" unfolding Cart_eq by auto
      thus ?case using subspace_0[OF subspace_span[of "{}"]] by auto
    next
      case (insert k F)
      hence *:"\<forall>i. i \<notin> insert k F \<longrightarrow> x $ i = 0" by auto
      have **:"F \<subseteq> insert k F" by auto
      def y \<equiv> "x - x$k *\<^sub>R basis k"
      have y:"x = y + (x$k) *\<^sub>R basis k" unfolding y_def by auto
      { fix i assume i':"i \<notin> F"
	hence "y $ i = 0" unfolding y_def unfolding vector_minus_component
	  and vector_smult_component and basis_component
	  using *[THEN spec[where x=i]] by auto }
      hence "y \<in> span (basis ` (insert k F))" using insert(3)
	using span_mono[of "?bas ` F" "?bas ` (insert k F)"]
	using image_mono[OF **, of basis] by auto
      moreover
      have "basis k \<in> span (?bas ` (insert k F))" by(rule span_superset, auto)
      hence "x$k *\<^sub>R basis k \<in> span (?bas ` (insert k F))"
        using span_mul [where 'a=real, unfolded smult_conv_scaleR] by auto
      ultimately
      have "y + x$k *\<^sub>R basis k \<in> span (?bas ` (insert k F))"
	using span_add by auto
      thus ?case using y by auto
    qed
  }
  hence "?A \<subseteq> span ?B" by auto

  moreover
  { fix x assume "x \<in> ?B"
    hence "x\<in>{(basis i)::real^'n |i. i \<in> ?D}" using assms by auto  }
  hence "independent ?B" using independent_mono[OF independent_stdbasis, of ?B] and assms by auto

  moreover
  have "d \<subseteq> ?D" unfolding subset_eq using assms by auto
  hence *:"inj_on (basis::'n\<Rightarrow>real^'n) d" using subset_inj_on[OF basis_inj, of "d"] by auto
  have "?B hassize (card d)" unfolding hassize_def and card_image[OF *] by auto

  ultimately show ?thesis using dim_unique[of "basis ` d" ?A] by auto
qed

text{* Hence closure and completeness of all subspaces.                          *}

lemma closed_subspace_lemma: "n \<le> card (UNIV::'n::finite set) \<Longrightarrow> \<exists>A::'n set. card A = n"
apply (induct n)
apply (rule_tac x="{}" in exI, simp)
apply clarsimp
apply (subgoal_tac "\<exists>x. x \<notin> A")
apply (erule exE)
apply (rule_tac x="insert x A" in exI, simp)
apply (subgoal_tac "A \<noteq> UNIV", auto)
done

lemma closed_subspace: fixes s::"(real^'n::finite) set"
  assumes "subspace s" shows "closed s"
proof-
  have "dim s \<le> card (UNIV :: 'n set)" using dim_subset_univ by auto
  then obtain d::"'n set" where t: "card d = dim s"
    using closed_subspace_lemma by auto
  let ?t = "{x::real^'n. \<forall>i. i \<notin> d \<longrightarrow> x$i = 0}"
  obtain f where f:"linear f"  "f ` ?t = s" "inj_on f ?t"
    using subspace_isomorphism[OF subspace_substandard[of "\<lambda>i. i \<notin> d"] assms]
    using dim_substandard[of d] and t by auto
  have "\<forall>x\<in>?t. f x = 0 \<longrightarrow> x = 0" using linear_0[OF f(1)] using f(3)[unfolded inj_on_def]
    by(erule_tac x=0 in ballE) auto
  moreover have "closed ?t" using closed_substandard .
  moreover have "subspace ?t" using subspace_substandard .
  ultimately show ?thesis using closed_injective_image_subspace[of ?t f]
    unfolding f(2) using f(1) by auto
qed

lemma complete_subspace:
  fixes s :: "(real ^ _) set" shows "subspace s ==> complete s"
  using complete_eq_closed closed_subspace
  by auto

lemma dim_closure:
  fixes s :: "(real ^ _) set"
  shows "dim(closure s) = dim s" (is "?dc = ?d")
proof-
  have "?dc \<le> ?d" using closure_minimal[OF span_inc, of s]
    using closed_subspace[OF subspace_span, of s]
    using dim_subset[of "closure s" "span s"] unfolding dim_span by auto
  thus ?thesis using dim_subset[OF closure_subset, of s] by auto
qed

text{* Affine transformations of intervals.                                      *}

lemma affinity_inverses:
  assumes m0: "m \<noteq> (0::'a::field)"
  shows "(\<lambda>x. m *s x + c) o (\<lambda>x. inverse(m) *s x + (-(inverse(m) *s c))) = id"
  "(\<lambda>x. inverse(m) *s x + (-(inverse(m) *s c))) o (\<lambda>x. m *s x + c) = id"
  using m0
apply (auto simp add: expand_fun_eq vector_add_ldistrib vector_smult_assoc)
by (simp add: vector_smult_lneg[symmetric] vector_smult_assoc vector_sneg_minus1[symmetric])

lemma real_affinity_le:
 "0 < (m::'a::ordered_field) ==> (m * x + c \<le> y \<longleftrightarrow> x \<le> inverse(m) * y + -(c / m))"
  by (simp add: field_simps inverse_eq_divide)

lemma real_le_affinity:
 "0 < (m::'a::ordered_field) ==> (y \<le> m * x + c \<longleftrightarrow> inverse(m) * y + -(c / m) \<le> x)"
  by (simp add: field_simps inverse_eq_divide)

lemma real_affinity_lt:
 "0 < (m::'a::ordered_field) ==> (m * x + c < y \<longleftrightarrow> x < inverse(m) * y + -(c / m))"
  by (simp add: field_simps inverse_eq_divide)

lemma real_lt_affinity:
 "0 < (m::'a::ordered_field) ==> (y < m * x + c \<longleftrightarrow> inverse(m) * y + -(c / m) < x)"
  by (simp add: field_simps inverse_eq_divide)

lemma real_affinity_eq:
 "(m::'a::ordered_field) \<noteq> 0 ==> (m * x + c = y \<longleftrightarrow> x = inverse(m) * y + -(c / m))"
  by (simp add: field_simps inverse_eq_divide)

lemma real_eq_affinity:
 "(m::'a::ordered_field) \<noteq> 0 ==> (y = m * x + c  \<longleftrightarrow> inverse(m) * y + -(c / m) = x)"
  by (simp add: field_simps inverse_eq_divide)

lemma vector_affinity_eq:
  assumes m0: "(m::'a::field) \<noteq> 0"
  shows "m *s x + c = y \<longleftrightarrow> x = inverse m *s y + -(inverse m *s c)"
proof
  assume h: "m *s x + c = y"
  hence "m *s x = y - c" by (simp add: ring_simps)
  hence "inverse m *s (m *s x) = inverse m *s (y - c)" by simp
  then show "x = inverse m *s y + - (inverse m *s c)"
    using m0 by (simp add: vector_smult_assoc vector_ssub_ldistrib)
next
  assume h: "x = inverse m *s y + - (inverse m *s c)"
  show "m *s x + c = y" unfolding h diff_minus[symmetric]
    using m0 by (simp add: vector_smult_assoc vector_ssub_ldistrib)
qed

lemma vector_eq_affinity:
 "(m::'a::field) \<noteq> 0 ==> (y = m *s x + c \<longleftrightarrow> inverse(m) *s y + -(inverse(m) *s c) = x)"
  using vector_affinity_eq[where m=m and x=x and y=y and c=c]
  by metis

lemma image_affinity_interval: fixes m::real
  fixes a b c :: "real^'n::finite"
  shows "(\<lambda>x. m *\<^sub>R x + c) ` {a .. b} =
            (if {a .. b} = {} then {}
            else (if 0 \<le> m then {m *\<^sub>R a + c .. m *\<^sub>R b + c}
            else {m *\<^sub>R b + c .. m *\<^sub>R a + c}))"
proof(cases "m=0")
  { fix x assume "x \<le> c" "c \<le> x"
    hence "x=c" unfolding vector_less_eq_def and Cart_eq by (auto intro: order_antisym) }
  moreover case True
  moreover have "c \<in> {m *\<^sub>R a + c..m *\<^sub>R b + c}" unfolding True by(auto simp add: vector_less_eq_def)
  ultimately show ?thesis by auto
next
  case False
  { fix y assume "a \<le> y" "y \<le> b" "m > 0"
    hence "m *\<^sub>R a + c \<le> m *\<^sub>R y + c"  "m *\<^sub>R y + c \<le> m *\<^sub>R b + c"
      unfolding vector_less_eq_def by(auto simp add: vector_smult_component vector_add_component)
  } moreover
  { fix y assume "a \<le> y" "y \<le> b" "m < 0"
    hence "m *\<^sub>R b + c \<le> m *\<^sub>R y + c"  "m *\<^sub>R y + c \<le> m *\<^sub>R a + c"
      unfolding vector_less_eq_def by(auto simp add: vector_smult_component vector_add_component mult_left_mono_neg elim!:ballE)
  } moreover
  { fix y assume "m > 0"  "m *\<^sub>R a + c \<le> y"  "y \<le> m *\<^sub>R b + c"
    hence "y \<in> (\<lambda>x. m *\<^sub>R x + c) ` {a..b}"
      unfolding image_iff Bex_def mem_interval vector_less_eq_def
      apply(auto simp add: vector_smult_component vector_add_component vector_minus_component vector_smult_assoc pth_3[symmetric]
	intro!: exI[where x="(1 / m) *\<^sub>R (y - c)"])
      by(auto simp add: pos_le_divide_eq pos_divide_le_eq real_mult_commute diff_le_iff)
  } moreover
  { fix y assume "m *\<^sub>R b + c \<le> y" "y \<le> m *\<^sub>R a + c" "m < 0"
    hence "y \<in> (\<lambda>x. m *\<^sub>R x + c) ` {a..b}"
      unfolding image_iff Bex_def mem_interval vector_less_eq_def
      apply(auto simp add: vector_smult_component vector_add_component vector_minus_component vector_smult_assoc pth_3[symmetric]
	intro!: exI[where x="(1 / m) *\<^sub>R (y - c)"])
      by(auto simp add: neg_le_divide_eq neg_divide_le_eq real_mult_commute diff_le_iff)
  }
  ultimately show ?thesis using False by auto
qed

lemma image_smult_interval:"(\<lambda>x. m *\<^sub>R (x::real^'n::finite)) ` {a..b} =
  (if {a..b} = {} then {} else if 0 \<le> m then {m *\<^sub>R a..m *\<^sub>R b} else {m *\<^sub>R b..m *\<^sub>R a})"
  using image_affinity_interval[of m 0 a b] by auto

subsection{* Banach fixed point theorem (not really topological...) *}

lemma banach_fix:
  assumes s:"complete s" "s \<noteq> {}" and c:"0 \<le> c" "c < 1" and f:"(f ` s) \<subseteq> s" and
          lipschitz:"\<forall>x\<in>s. \<forall>y\<in>s. dist (f x) (f y) \<le> c * dist x y"
  shows "\<exists>! x\<in>s. (f x = x)"
proof-
  have "1 - c > 0" using c by auto

  from s(2) obtain z0 where "z0 \<in> s" by auto
  def z \<equiv> "\<lambda>n. (f ^^ n) z0"
  { fix n::nat
    have "z n \<in> s" unfolding z_def
    proof(induct n) case 0 thus ?case using `z0 \<in>s` by auto
    next case Suc thus ?case using f by auto qed }
  note z_in_s = this

  def d \<equiv> "dist (z 0) (z 1)"

  have fzn:"\<And>n. f (z n) = z (Suc n)" unfolding z_def by auto
  { fix n::nat
    have "dist (z n) (z (Suc n)) \<le> (c ^ n) * d"
    proof(induct n)
      case 0 thus ?case unfolding d_def by auto
    next
      case (Suc m)
      hence "c * dist (z m) (z (Suc m)) \<le> c ^ Suc m * d"
	using `0 \<le> c` using mult_mono1_class.mult_mono1[of "dist (z m) (z (Suc m))" "c ^ m * d" c] by auto
      thus ?case using lipschitz[THEN bspec[where x="z m"], OF z_in_s, THEN bspec[where x="z (Suc m)"], OF z_in_s]
	unfolding fzn and mult_le_cancel_left by auto
    qed
  } note cf_z = this

  { fix n m::nat
    have "(1 - c) * dist (z m) (z (m+n)) \<le> (c ^ m) * d * (1 - c ^ n)"
    proof(induct n)
      case 0 show ?case by auto
    next
      case (Suc k)
      have "(1 - c) * dist (z m) (z (m + Suc k)) \<le> (1 - c) * (dist (z m) (z (m + k)) + dist (z (m + k)) (z (Suc (m + k))))"
	using dist_triangle and c by(auto simp add: dist_triangle)
      also have "\<dots> \<le> (1 - c) * (dist (z m) (z (m + k)) + c ^ (m + k) * d)"
	using cf_z[of "m + k"] and c by auto
      also have "\<dots> \<le> c ^ m * d * (1 - c ^ k) + (1 - c) * c ^ (m + k) * d"
	using Suc by (auto simp add: ring_simps)
      also have "\<dots> = (c ^ m) * (d * (1 - c ^ k) + (1 - c) * c ^ k * d)"
	unfolding power_add by (auto simp add: ring_simps)
      also have "\<dots> \<le> (c ^ m) * d * (1 - c ^ Suc k)"
	using c by (auto simp add: ring_simps)
      finally show ?case by auto
    qed
  } note cf_z2 = this
  { fix e::real assume "e>0"
    hence "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (z m) (z n) < e"
    proof(cases "d = 0")
      case True
      hence "\<And>n. z n = z0" using cf_z2[of 0] and c unfolding z_def by (auto simp add: pos_prod_le[OF `1 - c > 0`])
      thus ?thesis using `e>0` by auto
    next
      case False hence "d>0" unfolding d_def using zero_le_dist[of "z 0" "z 1"]
	by (metis False d_def real_less_def)
      hence "0 < e * (1 - c) / d" using `e>0` and `1-c>0`
	using divide_pos_pos[of "e * (1 - c)" d] and mult_pos_pos[of e "1 - c"] by auto
      then obtain N where N:"c ^ N < e * (1 - c) / d" using real_arch_pow_inv[of "e * (1 - c) / d" c] and c by auto
      { fix m n::nat assume "m>n" and as:"m\<ge>N" "n\<ge>N"
	have *:"c ^ n \<le> c ^ N" using `n\<ge>N` and c using power_decreasing[OF `n\<ge>N`, of c] by auto
	have "1 - c ^ (m - n) > 0" using c and power_strict_mono[of c 1 "m - n"] using `m>n` by auto
	hence **:"d * (1 - c ^ (m - n)) / (1 - c) > 0"
	  using real_mult_order[OF `d>0`, of "1 - c ^ (m - n)"]
	  using divide_pos_pos[of "d * (1 - c ^ (m - n))" "1 - c"]
	  using `0 < 1 - c` by auto

	have "dist (z m) (z n) \<le> c ^ n * d * (1 - c ^ (m - n)) / (1 - c)"
	  using cf_z2[of n "m - n"] and `m>n` unfolding pos_le_divide_eq[OF `1-c>0`]
	  by (auto simp add: real_mult_commute dist_commute)
	also have "\<dots> \<le> c ^ N * d * (1 - c ^ (m - n)) / (1 - c)"
	  using mult_right_mono[OF * order_less_imp_le[OF **]]
	  unfolding real_mult_assoc by auto
	also have "\<dots> < (e * (1 - c) / d) * d * (1 - c ^ (m - n)) / (1 - c)"
	  using mult_strict_right_mono[OF N **] unfolding real_mult_assoc by auto
	also have "\<dots> = e * (1 - c ^ (m - n))" using c and `d>0` and `1 - c > 0` by auto
	also have "\<dots> \<le> e" using c and `1 - c ^ (m - n) > 0` and `e>0` using mult_right_le_one_le[of e "1 - c ^ (m - n)"] by auto
	finally have  "dist (z m) (z n) < e" by auto
      } note * = this
      { fix m n::nat assume as:"N\<le>m" "N\<le>n"
	hence "dist (z n) (z m) < e"
	proof(cases "n = m")
	  case True thus ?thesis using `e>0` by auto
	next
	  case False thus ?thesis using as and *[of n m] *[of m n] unfolding nat_neq_iff by (auto simp add: dist_commute)
	qed }
      thus ?thesis by auto
    qed
  }
  hence "Cauchy z" unfolding cauchy_def by auto
  then obtain x where "x\<in>s" and x:"(z ---> x) sequentially" using s(1)[unfolded compact_def complete_def, THEN spec[where x=z]] and z_in_s by auto

  def e \<equiv> "dist (f x) x"
  have "e = 0" proof(rule ccontr)
    assume "e \<noteq> 0" hence "e>0" unfolding e_def using zero_le_dist[of "f x" x]
      by (metis dist_eq_0_iff dist_nz e_def)
    then obtain N where N:"\<forall>n\<ge>N. dist (z n) x < e / 2"
      using x[unfolded Lim_sequentially, THEN spec[where x="e/2"]] by auto
    hence N':"dist (z N) x < e / 2" by auto

    have *:"c * dist (z N) x \<le> dist (z N) x" unfolding mult_le_cancel_right2
      using zero_le_dist[of "z N" x] and c
      by (metis dist_eq_0_iff dist_nz order_less_asym real_less_def)
    have "dist (f (z N)) (f x) \<le> c * dist (z N) x" using lipschitz[THEN bspec[where x="z N"], THEN bspec[where x=x]]
      using z_in_s[of N] `x\<in>s` using c by auto
    also have "\<dots> < e / 2" using N' and c using * by auto
    finally show False unfolding fzn
      using N[THEN spec[where x="Suc N"]] and dist_triangle_half_r[of "z (Suc N)" "f x" e x]
      unfolding e_def by auto
  qed
  hence "f x = x" unfolding e_def by auto
  moreover
  { fix y assume "f y = y" "y\<in>s"
    hence "dist x y \<le> c * dist x y" using lipschitz[THEN bspec[where x=x], THEN bspec[where x=y]]
      using `x\<in>s` and `f x = x` by auto
    hence "dist x y = 0" unfolding mult_le_cancel_right1
      using c and zero_le_dist[of x y] by auto
    hence "y = x" by auto
  }
  ultimately show ?thesis unfolding Bex1_def using `x\<in>s` by blast+
qed

subsection{* Edelstein fixed point theorem.                                            *}

lemma edelstein_fix:
  fixes s :: "'a::real_normed_vector set"
  assumes s:"compact s" "s \<noteq> {}" and gs:"(g ` s) \<subseteq> s"
      and dist:"\<forall>x\<in>s. \<forall>y\<in>s. x \<noteq> y \<longrightarrow> dist (g x) (g y) < dist x y"
  shows "\<exists>! x\<in>s. g x = x"
proof(cases "\<exists>x\<in>s. g x \<noteq> x")
  obtain x where "x\<in>s" using s(2) by auto
  case False hence g:"\<forall>x\<in>s. g x = x" by auto
  { fix y assume "y\<in>s"
    hence "x = y" using `x\<in>s` and dist[THEN bspec[where x=x], THEN bspec[where x=y]]
      unfolding g[THEN bspec[where x=x], OF `x\<in>s`]
      unfolding g[THEN bspec[where x=y], OF `y\<in>s`] by auto  }
  thus ?thesis unfolding Bex1_def using `x\<in>s` and g by blast+
next
  case True
  then obtain x where [simp]:"x\<in>s" and "g x \<noteq> x" by auto
  { fix x y assume "x \<in> s" "y \<in> s"
    hence "dist (g x) (g y) \<le> dist x y"
      using dist[THEN bspec[where x=x], THEN bspec[where x=y]] by auto } note dist' = this
  def y \<equiv> "g x"
  have [simp]:"y\<in>s" unfolding y_def using gs[unfolded image_subset_iff] and `x\<in>s` by blast
  def f \<equiv> "\<lambda>n. g ^^ n"
  have [simp]:"\<And>n z. g (f n z) = f (Suc n) z" unfolding f_def by auto
  have [simp]:"\<And>z. f 0 z = z" unfolding f_def by auto
  { fix n::nat and z assume "z\<in>s"
    have "f n z \<in> s" unfolding f_def
    proof(induct n)
      case 0 thus ?case using `z\<in>s` by simp
    next
      case (Suc n) thus ?case using gs[unfolded image_subset_iff] by auto
    qed } note fs = this
  { fix m n ::nat assume "m\<le>n"
    fix w z assume "w\<in>s" "z\<in>s"
    have "dist (f n w) (f n z) \<le> dist (f m w) (f m z)" using `m\<le>n`
    proof(induct n)
      case 0 thus ?case by auto
    next
      case (Suc n)
      thus ?case proof(cases "m\<le>n")
	case True thus ?thesis using Suc(1)
	  using dist'[OF fs fs, OF `w\<in>s` `z\<in>s`, of n n] by auto
      next
	case False hence mn:"m = Suc n" using Suc(2) by simp
	show ?thesis unfolding mn  by auto
      qed
    qed } note distf = this

  def h \<equiv> "\<lambda>n. (f n x, f n y)"
  let ?s2 = "s \<times> s"
  obtain l r where "l\<in>?s2" and r:"subseq r" and lr:"((h \<circ> r) ---> l) sequentially"
    using compact_Times [OF s(1) s(1), unfolded compact_def, THEN spec[where x=h]] unfolding  h_def
    using fs[OF `x\<in>s`] and fs[OF `y\<in>s`] by blast
  def a \<equiv> "fst l" def b \<equiv> "snd l"
  have lab:"l = (a, b)" unfolding a_def b_def by simp
  have [simp]:"a\<in>s" "b\<in>s" unfolding a_def b_def using `l\<in>?s2` by auto

  have lima:"((fst \<circ> (h \<circ> r)) ---> a) sequentially"
   and limb:"((snd \<circ> (h \<circ> r)) ---> b) sequentially"
    using lr
    unfolding o_def a_def b_def by (simp_all add: tendsto_intros)

  { fix n::nat
    have *:"\<And>fx fy (x::'a) y. dist fx fy \<le> dist x y \<Longrightarrow> \<not> (dist (fx - fy) (a - b) < dist a b - dist x y)" unfolding dist_norm by norm
    { fix x y :: 'a
      have "dist (-x) (-y) = dist x y" unfolding dist_norm
	using norm_minus_cancel[of "x - y"] by (auto simp add: uminus_add_conv_diff) } note ** = this

    { assume as:"dist a b > dist (f n x) (f n y)"
      then obtain Na Nb where "\<forall>m\<ge>Na. dist (f (r m) x) a < (dist a b - dist (f n x) (f n y)) / 2"
	and "\<forall>m\<ge>Nb. dist (f (r m) y) b < (dist a b - dist (f n x) (f n y)) / 2"
	using lima limb unfolding h_def Lim_sequentially by (fastsimp simp del: less_divide_eq_number_of1)
      hence "dist (f (r (Na + Nb + n)) x - f (r (Na + Nb + n)) y) (a - b) < dist a b - dist (f n x) (f n y)"
	apply(erule_tac x="Na+Nb+n" in allE)
	apply(erule_tac x="Na+Nb+n" in allE) apply simp
	using dist_triangle_add_half[of a "f (r (Na + Nb + n)) x" "dist a b - dist (f n x) (f n y)"
          "-b"  "- f (r (Na + Nb + n)) y"]
	unfolding ** unfolding group_simps(12) by (auto simp add: dist_commute)
      moreover
      have "dist (f (r (Na + Nb + n)) x - f (r (Na + Nb + n)) y) (a - b) \<ge> dist a b - dist (f n x) (f n y)"
	using distf[of n "r (Na+Nb+n)", OF _ `x\<in>s` `y\<in>s`]
	using subseq_bigger[OF r, of "Na+Nb+n"]
	using *[of "f (r (Na + Nb + n)) x" "f (r (Na + Nb + n)) y" "f n x" "f n y"] by auto
      ultimately have False by simp
    }
    hence "dist a b \<le> dist (f n x) (f n y)" by(rule ccontr)auto }
  note ab_fn = this

  have [simp]:"a = b" proof(rule ccontr)
    def e \<equiv> "dist a b - dist (g a) (g b)"
    assume "a\<noteq>b" hence "e > 0" unfolding e_def using dist by fastsimp
    hence "\<exists>n. dist (f n x) a < e/2 \<and> dist (f n y) b < e/2"
      using lima limb unfolding Lim_sequentially
      apply (auto elim!: allE[where x="e/2"]) apply(rule_tac x="r (max N Na)" in exI) unfolding h_def by fastsimp
    then obtain n where n:"dist (f n x) a < e/2 \<and> dist (f n y) b < e/2" by auto
    have "dist (f (Suc n) x) (g a) \<le> dist (f n x) a"
      using dist[THEN bspec[where x="f n x"], THEN bspec[where x="a"]] and fs by auto
    moreover have "dist (f (Suc n) y) (g b) \<le> dist (f n y) b"
      using dist[THEN bspec[where x="f n y"], THEN bspec[where x="b"]] and fs by auto
    ultimately have "dist (f (Suc n) x) (g a) + dist (f (Suc n) y) (g b) < e" using n by auto
    thus False unfolding e_def using ab_fn[of "Suc n"] by norm
  qed

  have [simp]:"\<And>n. f (Suc n) x = f n y" unfolding f_def y_def by(induct_tac n)auto
  { fix x y assume "x\<in>s" "y\<in>s" moreover
    fix e::real assume "e>0" ultimately
    have "dist y x < e \<longrightarrow> dist (g y) (g x) < e" using dist by fastsimp }
  hence "continuous_on s g" unfolding continuous_on_def by auto

  hence "((snd \<circ> h \<circ> r) ---> g a) sequentially" unfolding continuous_on_sequentially
    apply (rule allE[where x="\<lambda>n. (fst \<circ> h \<circ> r) n"]) apply (erule ballE[where x=a])
    using lima unfolding h_def o_def using fs[OF `x\<in>s`] by (auto simp add: y_def)
  hence "g a = a" using Lim_unique[OF trivial_limit_sequentially limb, of "g a"]
    unfolding `a=b` and o_assoc by auto
  moreover
  { fix x assume "x\<in>s" "g x = x" "x\<noteq>a"
    hence "False" using dist[THEN bspec[where x=a], THEN bspec[where x=x]]
      using `g a = a` and `a\<in>s` by auto  }
  ultimately show "\<exists>!x\<in>s. g x = x" unfolding Bex1_def using `a\<in>s` by blast
qed

end
