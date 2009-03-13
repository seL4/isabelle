(* Title:      Topology
   Author:     Amine Chaieb, University of Cambridge
   Author:     Robert Himmelmann, TU Muenchen
*)

header {* Elementary topology in Euclidean space. *}

theory Topology_Euclidean_Space
  imports SEQ Euclidean_Space
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
definition "open S \<longleftrightarrow> (\<forall>x \<in> S. \<exists>e >0. \<forall>x'. dist x' x < e \<longrightarrow> x' \<in> S)"
definition "closed S \<longleftrightarrow> open(UNIV - S)"
definition "euclidean = topology open"

lemma open_empty[intro,simp]: "open {}" by (simp add: open_def)
lemma open_UNIV[intro,simp]:  "open UNIV"
  by (simp add: open_def, rule exI[where x="1"], auto)

lemma open_inter[intro]: assumes S: "open S" and T: "open T"
  shows "open (S \<inter> T)"
proof-
  note thS = S[unfolded open_def, rule_format]
  note thT = T[unfolded open_def, rule_format]
  {fix x assume x: "x \<in> S\<inter>T"
    hence xS: "x \<in> S" and xT: "x \<in> T" by simp_all
    from thS[OF xS] obtain eS where eS: "eS > 0" "\<forall>x'. dist x' x < eS \<longrightarrow> x' \<in> S" by blast
    from thT[OF xT] obtain eT where eT: "eT > 0" "\<forall>x'. dist x' x < eT \<longrightarrow> x' \<in> T" by blast
    from real_lbound_gt_zero[OF eS(1) eT(1)] obtain e where e: "e > 0" "e < eS" "e < eT" by blast
    { fix x' assume d: "dist x' x < e"
      hence dS: "dist x' x < eS" and dT: "dist x' x < eT" using e by arith+
      from eS(2)[rule_format, OF dS] eT(2)[rule_format, OF dT] have "x' \<in> S\<inter>T" by blast}
    hence "\<exists>e >0. \<forall>x'. dist x' x < e \<longrightarrow> x' \<in> (S\<inter>T)" using e by blast}
  then show ?thesis unfolding open_def by blast
qed

lemma open_Union[intro]: "(\<forall>S\<in>K. open S) \<Longrightarrow> open (\<Union> K)"
  by (simp add: open_def) metis

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
  by (simp add: closed_def closedin_def topspace_euclidean open_openin)

lemma open_Un[intro]: "open S \<Longrightarrow> open T \<Longrightarrow> open (S\<union>T)"
  by (auto simp add: open_openin)

lemma open_subopen: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> S)"
  by (simp add: open_openin openin_subopen[symmetric])

lemma closed_empty[intro, simp]: "closed {}" by (simp add: closed_closedin)

lemma closed_UNIV[simp,intro]: "closed UNIV"
  by (simp add: closed_closedin topspace_euclidean[symmetric])

lemma closed_Un[intro]: "closed S \<Longrightarrow> closed T \<Longrightarrow> closed (S\<union>T)"
  by (auto simp add: closed_closedin)

lemma closed_Int[intro]: "closed S \<Longrightarrow> closed T \<Longrightarrow> closed (S\<inter>T)"
  by (auto simp add: closed_closedin)

lemma closed_Inter[intro]: assumes H: "\<forall>S \<in>K. closed S" shows "closed (\<Inter>K)"
  using H
  unfolding closed_closedin
  apply (cases "K = {}")
  apply (simp add: closed_closedin[symmetric])
  apply (rule closedin_Inter, auto)
  done

lemma open_closed: "open S \<longleftrightarrow> closed (UNIV - S)"
  by (simp add: open_openin closed_closedin topspace_euclidean openin_closedin_eq)

lemma closed_open: "closed S \<longleftrightarrow> open(UNIV - S)"
  by (simp add: open_openin closed_closedin topspace_euclidean closedin_def)

lemma open_diff[intro]: "open S \<Longrightarrow> closed T \<Longrightarrow> open (S - T)"
  by (auto simp add: open_openin closed_closedin)

lemma closed_diff[intro]: "closed S \<Longrightarrow> open T \<Longrightarrow> closed(S-T)"
  by (auto simp add: open_openin closed_closedin)

lemma open_Inter[intro]: assumes fS: "finite S" and h: "\<forall>T\<in>S. open T" shows "open (\<Inter>S)"
  using h by (induct rule: finite_induct[OF fS], auto)

lemma closed_Union[intro]: assumes fS: "finite S" and h: "\<forall>T\<in>S. closed T" shows "closed (\<Union>S)"
  using h by (induct rule: finite_induct[OF fS], auto)

subsection{* Open and closed balls. *}

definition "ball x e = {y. dist x y < e}"
definition "cball x e = {y. dist x y \<le> e}"

lemma mem_ball[simp]: "y \<in> ball x e \<longleftrightarrow> dist x y < e" by (simp add: ball_def)
lemma mem_cball[simp]: "y \<in> cball x e \<longleftrightarrow> dist x y \<le> e" by (simp add: cball_def)
lemma mem_ball_0[simp]: "x \<in> ball 0 e \<longleftrightarrow> norm x < e" by (simp add: dist_def)
lemma mem_cball_0[simp]: "x \<in> cball 0 e \<longleftrightarrow> norm x \<le> e" by (simp add: dist_def)
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
  unfolding open_def ball_def Collect_def Ball_def mem_def
  unfolding dist_sym
  apply clarify
  apply (rule_tac x="e - dist xa x" in exI)
  using dist_triangle_alt[where z=x]
  apply (clarsimp simp add: diff_less_iff)
  apply atomize
  apply (erule_tac x="x'" in allE)
  apply (erule_tac x="xa" in allE)
  by arith

lemma centre_in_ball[simp]: "x \<in> ball x e \<longleftrightarrow> e > 0" by (metis mem_ball dist_refl)
lemma open_contains_ball: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. ball x e \<subseteq> S)"
  unfolding open_def subset_eq mem_ball Ball_def dist_sym ..

lemma open_contains_ball_eq: "open S \<Longrightarrow> \<forall>x. x\<in>S \<longleftrightarrow> (\<exists>e>0. ball x e \<subseteq> S)"
  by (metis open_contains_ball subset_eq centre_in_ball)

lemma ball_eq_empty[simp]: "ball x e = {} \<longleftrightarrow> e \<le> 0"
  unfolding mem_ball expand_set_eq
  apply (simp add: not_less)
  by (metis dist_pos_le order_trans dist_refl)

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

lemma openin_euclidean_subtopology_iff: "openin (subtopology euclidean U) S
  \<longleftrightarrow> S \<subseteq> U \<and> (\<forall>x\<in>S. \<exists>e>0. \<forall>x'\<in>U. dist x' x < e \<longrightarrow> x'\<in> S)" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume ?lhs hence ?rhs unfolding openin_subtopology open_openin[symmetric]
      by (simp add: open_def) blast}
  moreover
  {assume SU: "S \<subseteq> U" and H: "\<And>x. x \<in> S \<Longrightarrow> \<exists>e>0. \<forall>x'\<in>U. dist x' x < e \<longrightarrow> x' \<in> S"
    from H obtain d where d: "\<And>x . x\<in> S \<Longrightarrow> d x > 0 \<and> (\<forall>x' \<in> U. dist x' x < d x \<longrightarrow> x' \<in> S)"
      by metis
    let ?T = "\<Union>{B. \<exists>x\<in>S. B = ball x (d x)}"
    have oT: "open ?T" by auto
    { fix x assume "x\<in>S"
      hence "x \<in> \<Union>{B. \<exists>x\<in>S. B = ball x (d x)}"
	apply simp apply(rule_tac x="ball x(d x)" in exI) apply auto
	unfolding dist_refl using d[of x] by auto
      hence "x\<in> ?T \<inter> U" using SU and `x\<in>S` by auto  }
    moreover
    { fix y assume "y\<in>?T"
      then obtain B where "y\<in>B" "B\<in>{B. \<exists>x\<in>S. B = ball x (d x)}" by auto
      then obtain x where "x\<in>S" and x:"y \<in> ball x (d x)" by auto
      assume "y\<in>U"
      hence "y\<in>S" using d[OF `x\<in>S`] and x by(auto simp add: dist_sym) }
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
unfolding connected_def openin_open by blast

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
    (is " _ \<longleftrightarrow> \<not> (\<exists>e2 e1. ?P e2 e1)") apply (simp add: closed_def) by metis

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

lemma hausdorff:
  assumes xy: "x \<noteq> y"
  shows "\<exists>U V. open U \<and> open V \<and> x\<in> U \<and> y \<in> V \<and> (U \<inter> V = {})" (is "\<exists>U V. ?P U V")
proof-
  let ?U = "ball x (dist x y / 2)"
  let ?V = "ball y (dist x y / 2)"
  have th0: "\<And>d x y z. (d x z :: real) <= d x y + d y z \<Longrightarrow> d y z = d z y
               ==> ~(d x y * 2 < d x z \<and> d z y * 2 < d x z)" by arith
  have "?P ?U ?V" using dist_pos_lt[OF xy] th0[of dist,OF dist_triangle dist_sym]
    by (auto simp add: dist_refl expand_set_eq Arith_Tools.less_divide_eq_number_of1)
  then show ?thesis by blast
qed

lemma separation_t2: "x \<noteq> y \<longleftrightarrow> (\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {})"
  using hausdorff[of x y] by blast

lemma separation_t1: "x \<noteq> y \<longleftrightarrow> (\<exists>U V. open U \<and> open V \<and> x \<in>U \<and> y\<notin> U \<and> x\<notin>V \<and> y\<in>V)"
  using separation_t2[of x y] by blast

lemma separation_t0: "x \<noteq> y \<longleftrightarrow> (\<exists>U. open U \<and> ~(x\<in>U \<longleftrightarrow> y\<in>U))" by(metis separation_t1)

subsection{* Limit points *}

definition islimpt:: "real ^'n \<Rightarrow> (real^'n) set \<Rightarrow> bool" (infixr "islimpt" 60) where
  islimpt_def: "x islimpt S \<longleftrightarrow> (\<forall>T. x\<in>T \<longrightarrow> open T \<longrightarrow> (\<exists>y\<in>S. y\<in>T \<and> y\<noteq>x))"

  (* FIXME: Sure this form is OK????*)
lemma islimptE: assumes "x islimpt S" and "x \<in> T" and "open T"
  obtains "(\<exists>y\<in>S. y\<in>T \<and> y\<noteq>x)"
  using assms unfolding islimpt_def by auto

lemma islimpt_subset: "x islimpt S \<Longrightarrow> S \<subseteq> T ==> x islimpt T" by (auto simp add: islimpt_def)
lemma islimpt_approachable: "x islimpt S \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e)"
  unfolding islimpt_def
  apply auto
  apply(erule_tac x="ball x e" in allE)
  apply (auto simp add: dist_refl)
  apply(rule_tac x=y in bexI) apply (auto simp add: dist_sym)
  by (metis open_def dist_sym open_ball centre_in_ball mem_ball)

lemma islimpt_approachable_le: "x islimpt S \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in> S. x' \<noteq> x \<and> dist x' x <= e)"
  unfolding islimpt_approachable
  using approachable_lt_le[where f="\<lambda>x'. dist x' x" and P="\<lambda>x'. \<not> (x'\<in>S \<and> x'\<noteq>x)"]
  by metis

lemma islimpt_UNIV[simp, intro]: "(x:: real ^'n) islimpt UNIV"
proof-
  {
    fix e::real assume ep: "e>0"
    from vector_choose_size[of "e/2"] ep have "\<exists>(c:: real ^'n). norm c = e/2" by auto
    then obtain c ::"real^'n" where c: "norm c = e/2" by blast
    let ?x = "x + c"
    have "?x \<noteq> x" using c ep by (auto simp add: norm_eq_0_imp)
    moreover have "dist ?x x < e" using c ep apply simp by norm
    ultimately have "\<exists>x'. x' \<noteq> x\<and> dist x' x < e" by blast}
  then show ?thesis unfolding islimpt_approachable by blast
qed

lemma closed_limpt: "closed S \<longleftrightarrow> (\<forall>x. x islimpt S \<longrightarrow> x \<in> S)"
  unfolding closed_def
  apply (subst open_subopen)
  apply (simp add: islimpt_def subset_eq)
  by (metis DiffE DiffI UNIV_I insertCI insert_absorb mem_def)

lemma islimpt_EMPTY[simp]: "\<not> x islimpt {}"
  unfolding islimpt_approachable apply auto by ferrack

lemma closed_positive_orthant: "closed {x::real^'n. \<forall>i\<in>{1.. dimindex(UNIV:: 'n set)}. 0 \<le>x$i}"
proof-
  let ?U = "{1 .. dimindex(UNIV :: 'n set)}"
  let ?O = "{x::real^'n. \<forall>i\<in>?U. x$i\<ge>0}"
  {fix x:: "real^'n" and i::nat assume H: "\<forall>e>0. \<exists>x'\<in>?O. x' \<noteq> x \<and> dist x' x < e" and i: "i \<in> ?U"
    and xi: "x$i < 0"
    from xi have th0: "-x$i > 0" by arith
    from H[rule_format, OF th0] obtain x' where x': "x' \<in>?O" "x' \<noteq> x" "dist x' x < -x $ i" by blast
      have th:" \<And>b a (x::real). abs x <= b \<Longrightarrow> b <= a ==> ~(a + x < 0)" by arith
      have th': "\<And>x (y::real). x < 0 \<Longrightarrow> 0 <= y ==> abs x <= abs (y - x)" by arith
      have th1: "\<bar>x$i\<bar> \<le> \<bar>(x' - x)$i\<bar>" using i x'(1) xi
	apply (simp only: vector_component)
	by (rule th') auto
      have th2: "\<bar>dist x x'\<bar> \<ge> \<bar>(x' - x)$i\<bar>" using  component_le_norm[OF i, of "x'-x"]
	apply (simp add: dist_def) by norm
      from th[OF th1 th2] x'(3) have False by (simp add: dist_sym dist_pos_le) }
  then show ?thesis unfolding closed_limpt islimpt_approachable
    unfolding not_le[symmetric] by blast
qed

lemma finite_set_avoid: assumes fS: "finite S" shows  "\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<longrightarrow> d <= dist a x"
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

lemma islimpt_finite: assumes fS: "finite S" shows "\<not> a islimpt S"
  unfolding islimpt_approachable
  using finite_set_avoid[OF fS, of a] by (metis dist_sym  not_le)

lemma islimpt_Un: "x islimpt (S \<union> T) \<longleftrightarrow> x islimpt S \<or> x islimpt T"
  apply (rule iffI)
  defer
  apply (metis Un_upper1 Un_upper2 islimpt_subset)
  unfolding islimpt_approachable
  apply auto
  apply (erule_tac x="min e ea" in allE)
  apply auto
  done

lemma discrete_imp_closed:
  assumes e: "0 < e" and d: "\<forall>x \<in> S. \<forall>y \<in> S. norm(y - x) < e \<longrightarrow> y = x"
  shows "closed S"
proof-
  {fix x assume C: "\<forall>e>0. \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e"
    from e have e2: "e/2 > 0" by arith
    from C[rule_format, OF e2] obtain y where y: "y \<in> S" "y\<noteq>x" "dist y x < e/2" by blast
    let ?m = "min (e/2) (dist x y) "
    from e2 y(2) have mp: "?m > 0" by (simp add: dist_nz[THEN sym])
    from C[rule_format, OF mp] obtain z where z: "z \<in> S" "z\<noteq>x" "dist z x < ?m" by blast
    have th: "norm (z - y) < e" using z y by norm
    from d[rule_format, OF y(1) z(1) th] y z
    have False by (auto simp add: dist_sym)}
  then show ?thesis by (metis islimpt_approachable closed_limpt)
qed

subsection{* Interior of a Set *}
definition "interior S = {x. \<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> S}"

lemma interior_eq: "interior S = S \<longleftrightarrow> open S"
  apply (simp add: expand_set_eq interior_def)
  apply (subst (2) open_subopen) by blast

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
  by (metis Int_mono interior_subset open_inter open_interior open_subset_interior)

lemma interior_limit_point[intro]: assumes x: "x \<in> interior S" shows "x islimpt S"
proof-
  from x obtain e where e: "e>0" "\<forall>x'. dist x x' < e \<longrightarrow> x' \<in> S"
    unfolding mem_interior subset_eq Ball_def mem_ball by blast
  {fix d::real assume d: "d>0"
    let ?m = "min d e / 2"
    have mde2: "?m \<ge> 0" using e(1) d(1) by arith
    from vector_choose_dist[OF mde2, of x]
    obtain y where y: "dist x y = ?m" by blast
    have th: "dist x y < e" "dist x y < d" unfolding y using e(1) d(1) by arith+
    have "\<exists>x'\<in>S. x'\<noteq> x \<and> dist x' x < d"
      apply (rule bexI[where x=y])
      using e th y by (auto simp add: dist_sym)}
  then show ?thesis unfolding islimpt_approachable by blast
qed

lemma interior_closed_Un_empty_interior:
  assumes cS: "closed S" and iT: "interior T = {}"
  shows "interior(S \<union> T) = interior S"
proof-
  have "interior S \<subseteq> interior (S\<union>T)"
    by (rule subset_interior, blast)
  moreover
  {fix x e assume e: "e > 0" "\<forall>x' \<in> ball x e. x'\<in>(S\<union>T)"
    {fix y assume y: "y \<in> ball x e"
      {fix d::real assume d: "d > 0"
	let ?k = "min d (e - dist x y)"
	have kp: "?k > 0" using d e(1) y[unfolded mem_ball] by norm
	have "?k/2 \<ge> 0" using kp by simp
	then obtain w where w: "dist y w = ?k/ 2" by (metis vector_choose_dist)
	from iT[unfolded expand_set_eq mem_interior]
	have "\<not> ball w (?k/4) \<subseteq> T" using kp by (auto simp add: Arith_Tools.less_divide_eq_number_of1)
	then obtain z where z: "dist w z < ?k/4" "z \<notin> T" by (auto simp add: subset_eq)
	have "z \<notin> T \<and> z\<noteq> y \<and> dist z y < d \<and> dist x z < e" using z apply simp
	  using w e(1) d apply (auto simp only: dist_sym)
	  apply (auto simp add: min_def cong del: if_weak_cong)
	  apply (cases "d \<le> e - dist x y", auto simp add: ring_simps cong del: if_weak_cong)
	  apply norm
	  apply (cases "d \<le> e - dist x y", auto simp add: ring_simps not_le not_less cong del: if_weak_cong)
	  apply norm
	  apply norm
	  apply (cases "d \<le> e - dist x y", auto simp add: ring_simps not_le not_less cong del: if_weak_cong)
	  apply norm
	  apply norm
	  done
	then have "\<exists>z. z \<notin> T \<and> z\<noteq> y \<and> dist z y < d \<and> dist x z < e" by blast
	then have "\<exists>x' \<in>S. x'\<noteq>y \<and> dist x' y < d" using e by auto}
      then have "y\<in>S" by (metis islimpt_approachable cS closed_limpt) }
    then have "x \<in> interior S" unfolding mem_interior using e(1) by blast}
  hence "interior (S\<union>T) \<subseteq> interior S" unfolding mem_interior Ball_def subset_eq by blast
  ultimately show ?thesis by blast
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
      by blast
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
      by blast
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

lemma open_inter_closure_subset: "open S \<Longrightarrow> (S \<inter> (closure T)) \<subseteq> closure(S \<inter> T)"
proof
  fix x
  assume as: "open S" "x \<in> S \<inter> closure T"
  { assume *:"x islimpt T"
    { fix e::real
      assume "e > 0"
      from as `open S` obtain e' where "e' > 0" and e':"\<forall>x'. dist x' x < e' \<longrightarrow> x' \<in> S"
	unfolding open_def
	by auto
      let ?e = "min e e'"
      from `e>0` `e'>0` have "?e > 0"
	by simp
      then obtain y where y:"y\<in>T" "y \<noteq> x \<and> dist y x < ?e"
	using islimpt_approachable[of x T] using *
	by blast
      hence "\<exists>x'\<in>S \<inter> T. x' \<noteq> x \<and> dist x' x < e" using e'
	using y
	by(rule_tac x=y in bexI, simp+)
    }
    hence "x islimpt S \<inter> T"
      using islimpt_approachable[of x "S \<inter> T"]
      by blast
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
  by (simp add: frontier_def closed_diff closed_closure)

lemma frontier_closures: "frontier S = (closure S) \<inter> (closure(UNIV - S))"
  by (auto simp add: frontier_def interior_closure)

lemma frontier_straddle: "a \<in> frontier S \<longleftrightarrow> (\<forall>e>0. (\<exists>x\<in>S. dist a x < e) \<and> (\<exists>x. x \<notin> S \<and> dist a x < e))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  { fix e::real
    assume "e > 0"
    let ?rhse = "(\<exists>x\<in>S. dist a x < e) \<and> (\<exists>x. x \<notin> S \<and> dist a x < e)"
    { assume "a\<in>S"
      have "\<exists>x\<in>S. dist a x < e" using dist_refl[of a] `e>0` `a\<in>S` by(rule_tac x=a in bexI) auto
      moreover have "\<exists>x. x \<notin> S \<and> dist a x < e" using `?lhs` `a\<in>S`
	unfolding frontier_closures closure_def islimpt_def using dist_refl[of a] `e>0`
	by (auto, erule_tac x="ball a e" in allE, auto)
      ultimately have ?rhse by auto
    }
    moreover
    { assume "a\<notin>S"
      hence ?rhse using `?lhs`
	unfolding frontier_closures closure_def islimpt_def
	using open_ball[of a e] dist_refl[of a] `e > 0`
	by (auto, erule_tac x = "ball a e" in allE, auto)
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
  unfolding open_closed by auto

subsection{* A variant of nets (Slightly non-standard but good for our purposes). *}

typedef (open) 'a net =
  "{g :: 'a \<Rightarrow> 'a \<Rightarrow> bool. \<forall>x y. (\<forall>z. g z x \<longrightarrow> g z y) \<or> (\<forall>z. g z y \<longrightarrow> g z x)}"
  morphisms "netord" "mknet" by blast
lemma net: "(\<forall>z. netord n z x \<longrightarrow> netord n z y) \<or> (\<forall>z. netord n z y \<longrightarrow> netord n z x)"
  using netord[of n] by auto

lemma oldnet: "netord n x x \<Longrightarrow> netord n y y \<Longrightarrow>
  \<exists>z. netord n z z \<and> (\<forall>w. netord n w z \<longrightarrow> netord n w x \<and> netord n w y)"
  by (metis net)

lemma net_dilemma:
 "\<exists>a. (\<exists>x. netord net x a) \<and> (\<forall>x. netord net x a \<longrightarrow> P x) \<Longrightarrow>
         \<exists>b. (\<exists>x. netord net x b) \<and> (\<forall>x. netord net x b \<longrightarrow> Q x)
         \<Longrightarrow> \<exists>c. (\<exists>x. netord net x c) \<and> (\<forall>x. netord net x c \<longrightarrow> P x \<and> Q x)"
  by (metis net)

subsection{* Common nets and The "within" modifier for nets. *}

definition "at a = mknet(\<lambda>x y. 0 < dist x a \<and> dist x a <= dist y a)"
definition "at_infinity = mknet(\<lambda>x y. norm x \<ge> norm y)"
definition "sequentially = mknet(\<lambda>(m::nat) n. m >= n)"

definition within :: "'a net \<Rightarrow> 'a set \<Rightarrow> 'a net" (infixr "within" 70) where
  within_def: "net within S = mknet (\<lambda>x y. netord net x y \<and> x \<in> S)"

definition indirection :: "real ^'n \<Rightarrow> real ^'n \<Rightarrow> (real ^'n) net" (infixr "indirection" 70) where
  indirection_def: "a indirection v = (at a) within {b. \<exists>c\<ge>0. b - a = c*s v}"

text{* Prove That They are all nets. *}

lemma mknet_inverse': "netord (mknet r) = r \<longleftrightarrow> (\<forall>x y. (\<forall>z. r z x \<longrightarrow> r z y) \<or> (\<forall>z. r z y \<longrightarrow> r z x))"
  using mknet_inverse[of r] apply (auto simp add: netord_inverse) by (metis net)

method_setup net = {*
 let
  val ss1 = HOL_basic_ss addsimps [@{thm expand_fun_eq} RS sym]
  val ss2 = HOL_basic_ss addsimps [@{thm mknet_inverse'}]
  fun tac ths = ObjectLogic.full_atomize_tac THEN' Simplifier.simp_tac (ss1 addsimps ths) THEN' Simplifier.asm_full_simp_tac ss2
  in Method.thms_args (SIMPLE_METHOD' o tac) end

*} "Reduces goals about net"

lemma at: "\<And>x y. netord (at a) x y \<longleftrightarrow> 0 < dist x a \<and> dist x a <= dist y a"
  apply (net at_def)
  by (metis dist_sym real_le_linear real_le_trans)

lemma at_infinity:
 "\<And>x y. netord at_infinity x y \<longleftrightarrow> norm x >= norm y"
  apply (net at_infinity_def)
  apply (metis real_le_linear real_le_trans)
  done

lemma sequentially: "\<And>m n. netord sequentially m n \<longleftrightarrow> m >= n"
  apply (net sequentially_def)
  apply (metis linorder_linear min_max.le_supI2 min_max.sup_absorb1)
  done

lemma within: "netord (n within S) x y \<longleftrightarrow> netord n x y \<and> x \<in> S"
proof-
  have "\<forall>x y. (\<forall>z. netord n z x \<and> z \<in> S \<longrightarrow> netord n z y) \<or> (\<forall>z. netord n z y \<and> z \<in> S \<longrightarrow> netord n z x)"
    by (metis net)
  thus ?thesis
    unfolding within_def
    using mknet_inverse[of "\<lambda>x y. netord n x y \<and> x \<in> S"]
    by simp
qed

lemma in_direction: "netord (a indirection v) x y \<longleftrightarrow> 0 < dist x a \<and> dist x a \<le> dist y a \<and> (\<exists>c \<ge> 0. x - a = c *s v)"
  by (simp add: within at indirection_def)

lemma within_UNIV: "at x within UNIV = at x"
  by (simp add: within_def at_def netord_inverse)

subsection{* Identify Trivial limits, where we can't approach arbitrarily closely. *}


definition "trivial_limit (net:: 'a net) \<longleftrightarrow>
  (\<forall>(a::'a) b. a = b) \<or> (\<exists>(a::'a) b. a \<noteq> b \<and> (\<forall>x. ~(netord (net) x a) \<and> ~(netord(net) x b)))"


lemma trivial_limit_within: "trivial_limit (at (a::real^'n) within S) \<longleftrightarrow> ~(a islimpt S)"
proof-
  {assume "\<forall>(a::real^'n) b. a = b" hence "\<not> a islimpt S"
      apply (simp add: islimpt_approachable_le)
      by (rule exI[where x=1], auto)}
  moreover
  {fix b c assume bc: "b \<noteq> c" "\<forall>x. \<not> netord (at a within S) x b \<and> \<not> netord (at a within S) x c"
    have "dist a b > 0 \<or> dist a c > 0" using bc by (auto simp add: within at dist_nz[THEN sym])
    then have "\<not> a islimpt S"
      using bc
      unfolding within at dist_nz islimpt_approachable_le
      by(auto simp add: dist_triangle dist_sym dist_eq_0[THEN sym]) }
  moreover
  {assume "\<not> a islimpt S"
    then obtain e where e: "e > 0" "\<forall>x' \<in> S. x' \<noteq> a \<longrightarrow> dist x' a > e"
      unfolding islimpt_approachable_le by (auto simp add: not_le)
    from e vector_choose_dist[of e a] obtain b where b: "dist a b = e" by auto
    from b e(1) have "a \<noteq> b" by (simp add: dist_nz)
    moreover have "\<forall>x. \<not> ((0 < dist x a \<and> dist x a \<le> dist a a) \<and> x \<in> S) \<and>
                 \<not> ((0 < dist x a \<and> dist x a \<le> dist b a) \<and> x \<in> S)"
      using e(2) b by (auto simp add: dist_refl dist_sym)
    ultimately have "trivial_limit (at a within S)"  unfolding trivial_limit_def within at
      by blast}
  ultimately show ?thesis unfolding trivial_limit_def by blast
qed

lemma trivial_limit_at: "~(trivial_limit (at a))"
  apply (subst within_UNIV[symmetric])
  by (simp add: trivial_limit_within islimpt_UNIV)

lemma trivial_limit_at_infinity: "~(trivial_limit (at_infinity :: ('a::{norm,zero_neq_one}) net))"
  apply (simp add: trivial_limit_def at_infinity)
  by (metis order_refl zero_neq_one)

lemma trivial_limit_sequentially:  "~(trivial_limit sequentially)"
  by (auto simp add: trivial_limit_def sequentially)

subsection{* Some property holds "sufficiently close" to the limit point. *}

definition "eventually P net \<longleftrightarrow> trivial_limit net \<or> (\<exists>y. (\<exists>x. netord net x y) \<and> (\<forall>x. netord net x y \<longrightarrow> P x))"

lemma eventually_happens: "eventually P net ==> trivial_limit net \<or> (\<exists>x. P x)"
  by (metis eventually_def)

lemma eventually_within_le: "eventually P (at a within S) \<longleftrightarrow>
        (\<exists>d>0. \<forall>x\<in>S. 0 < dist x a \<and> dist x a <= d \<longrightarrow> P x)" (is "?lhs = ?rhs")
proof
  assume "?lhs"
  moreover
  { assume "\<not> a islimpt S"
    then obtain e where "e>0" and e:"\<forall>x'\<in>S. \<not> (x' \<noteq> a \<and> dist x' a \<le> e)" unfolding islimpt_approachable_le by auto
    hence  "?rhs" apply auto apply (rule_tac x=e in exI) by auto  }
  moreover
  { assume "\<exists>y. (\<exists>x. netord (at a within S) x y) \<and> (\<forall>x. netord (at a within S) x y \<longrightarrow> P x)"
    then obtain x y where xy:"netord (at a within S) x y \<and> (\<forall>x. netord (at a within S) x y \<longrightarrow> P x)" by auto
    hence "?rhs" unfolding within at by auto
  }
  ultimately show "?rhs" unfolding eventually_def trivial_limit_within by auto
next
  assume "?rhs"
  then obtain d where "d>0" and d:"\<forall>x\<in>S. 0 < dist x a \<and> dist x a \<le> d \<longrightarrow> P x" by auto
  thus "?lhs"
    unfolding eventually_def trivial_limit_within islimpt_approachable_le within at unfolding dist_nz[THEN sym] by (clarsimp, rule_tac x=d in exI, auto)
qed

lemma eventually_within:  " eventually P (at a within S) \<longleftrightarrow>
        (\<exists>d>0. \<forall>x\<in>S. 0 < dist x a \<and> dist x a < d \<longrightarrow> P x)"
proof-
  { fix d
    assume "d>0" "\<forall>x\<in>S. 0 < dist x a \<and> dist x a < d \<longrightarrow> P x"
    hence "\<forall>x\<in>S. 0 < dist x a \<and> dist x a \<le> (d/2) \<longrightarrow> P x" using order_less_imp_le by auto
  }
  thus ?thesis unfolding eventually_within_le using approachable_lt_le
    by (auto, rule_tac x="d/2" in exI, auto)
qed

lemma eventually_at: "eventually P (at a) \<longleftrightarrow> (\<exists>d>0. \<forall>x. 0 < dist x a \<and> dist x a < d \<longrightarrow> P x)"
  apply (subst within_UNIV[symmetric])
  by (simp add: eventually_within)

lemma eventually_sequentially: "eventually P sequentially \<longleftrightarrow> (\<exists>N. \<forall>n\<ge>N. P n)"
  apply (simp add: eventually_def sequentially trivial_limit_sequentially)
apply (metis dlo_simps(7) dlo_simps(9) le_maxI2 min_max.le_iff_sup min_max.sup_absorb1 order_antisym_conv) done

(* FIXME Declare this with P::'a::some_type \<Rightarrow> bool *)
lemma eventually_at_infinity: "eventually (P::(real^'n \<Rightarrow> bool)) at_infinity \<longleftrightarrow> (\<exists>b. \<forall>x. norm x >= b \<longrightarrow> P x)" (is "?lhs = ?rhs")
proof
  assume "?lhs" thus "?rhs"
    unfolding eventually_def at_infinity
    by (auto simp add: trivial_limit_at_infinity)
next
  assume "?rhs"
  then obtain b where b:"\<forall>x. b \<le> norm x \<longrightarrow> P x" and "b\<ge>0"
    by (metis norm_ge_zero real_le_linear real_le_trans)
  obtain y::"real^'n" where y:"norm y = b" using `b\<ge>0`
    using vector_choose_size[of b] by auto
  thus "?lhs" unfolding eventually_def at_infinity using b y by auto
qed

lemma always_eventually: "(\<forall>(x::'a::zero_neq_one). P x) ==> eventually P net"
  apply (auto simp add: eventually_def trivial_limit_def )
  by (rule exI[where x=0], rule exI[where x=1], rule zero_neq_one)

text{* Combining theorems for "eventually" *}

lemma eventually_and: " eventually (\<lambda>x. P x \<and> Q x) net \<longleftrightarrow> eventually P net \<and> eventually Q net"
  apply (simp add: eventually_def)
  apply (cases "trivial_limit net")
  using net_dilemma[of net P Q] by auto

lemma eventually_mono: "(\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow> eventually P net  \<Longrightarrow> eventually Q net"
  by (metis eventually_def)

lemma eventually_mp: "eventually (\<lambda>x. P x \<longrightarrow> Q x) net \<Longrightarrow> eventually P net \<Longrightarrow> eventually Q net"
  apply (atomize(full))
  unfolding imp_conjL[symmetric] eventually_and[symmetric]
  by (auto simp add: eventually_def)

lemma eventually_false: "eventually (\<lambda>x. False) net \<longleftrightarrow> trivial_limit net"
  by (auto simp add: eventually_def)

lemma not_eventually: "(\<forall>x. \<not> P x ) \<Longrightarrow> ~(trivial_limit net) ==> ~(eventually P net)"
  by (auto simp add: eventually_def)

subsection{* Limits, defined as vacuously true when the limit is trivial. *}

definition tendsto:: "('a \<Rightarrow> real ^'n) \<Rightarrow> real ^'n \<Rightarrow> 'a net \<Rightarrow> bool" (infixr "--->" 55) where
  tendsto_def: "(f ---> l) net  \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) net)"

lemma tendstoD: "(f ---> l) net \<Longrightarrow> e>0 \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) net"
  unfolding tendsto_def by auto

  text{* Notation Lim to avoid collition with lim defined in analysis *}
definition "Lim net f = (THE l. (f ---> l) net)"

lemma Lim:
 "(f ---> l) net \<longleftrightarrow>
        trivial_limit net \<or>
        (\<forall>e>0. \<exists>y. (\<exists>x. netord net x y) \<and>
                           (\<forall>x. netord(net) x y \<longrightarrow> dist (f x) l < e))"
  by (auto simp add: tendsto_def eventually_def)


text{* Show that they yield usual definitions in the various cases. *}

lemma Lim_within_le: "(f ---> l)(at a within S) \<longleftrightarrow>
           (\<forall>e>0. \<exists>d>0. \<forall>x\<in>S. 0 < dist x a  \<and> dist x a  <= d \<longrightarrow> dist (f x) l < e)"
  by (auto simp add: tendsto_def eventually_within_le)

lemma Lim_within: "(f ---> l) (at a within S) \<longleftrightarrow>
        (\<forall>e >0. \<exists>d>0. \<forall>x \<in> S. 0 < dist x a  \<and> dist x a  < d  \<longrightarrow> dist (f x) l < e)"
  by (auto simp add: tendsto_def eventually_within)

lemma Lim_at: "(f ---> l) (at a) \<longleftrightarrow>
        (\<forall>e >0. \<exists>d>0. \<forall>x. 0 < dist x a  \<and> dist x a  < d  \<longrightarrow> dist (f x) l < e)"
  by (auto simp add: tendsto_def eventually_at)

lemma Lim_at_infinity:
  "(f ---> l) at_infinity \<longleftrightarrow> (\<forall>e>0. \<exists>b. \<forall>x::real^'n. norm x >= b \<longrightarrow> dist (f x) l < e)"
  by (auto simp add: tendsto_def eventually_at_infinity)

lemma Lim_sequentially:
 "(S ---> l) sequentially \<longleftrightarrow>
          (\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (S n) l < e)"
  by (auto simp add: tendsto_def eventually_sequentially)

lemma Lim_eventually: "eventually (\<lambda>x. f x = l) net \<Longrightarrow> (f ---> l) net"
  by (auto simp add: eventually_def Lim dist_refl)

text{* The expected monotonicity property. *}

lemma Lim_within_empty:  "(f ---> l) (at x within {})"
  by (simp add: Lim_within_le)

lemma Lim_within_subset: "(f ---> l) (at a within S) \<Longrightarrow> T \<subseteq> S \<Longrightarrow> (f ---> l) (at a within T)"
  apply (auto simp add: Lim_within_le)
  by (metis subset_eq)

lemma Lim_Un: assumes "(f ---> l) (at x within S)" "(f ---> l) (at x within T)"
  shows "(f ---> l) (at x within (S \<union> T))"
proof-
  { fix e::real assume "e>0"
    obtain d1 where d1:"d1>0" "\<forall>xa\<in>T. 0 < dist xa x \<and> dist xa x < d1 \<longrightarrow> dist (f xa) l < e" using assms unfolding Lim_within using `e>0` by auto
    obtain d2 where d2:"d2>0" "\<forall>xa\<in>S. 0 < dist xa x \<and> dist xa x < d2 \<longrightarrow> dist (f xa) l < e" using assms unfolding Lim_within using `e>0` by auto
    have "\<exists>d>0. \<forall>xa\<in>S \<union> T. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) l < e" using d1 d2
      by (rule_tac x="min d1 d2" in exI)auto
  }
  thus ?thesis unfolding Lim_within by auto
qed

lemma Lim_Un_univ:
 "(f ---> l) (at x within S) \<Longrightarrow> (f ---> l) (at x within T) \<Longrightarrow>  S \<union> T = (UNIV::(real^'n) set)
        ==> (f ---> l) (at x)"
  by (metis Lim_Un within_UNIV)

text{* Interrelations between restricted and unrestricted limits. *}

lemma Lim_at_within: "(f ---> l)(at a) ==> (f ---> l)(at a within S)"
  apply (simp add: Lim_at Lim_within)
  by metis

lemma Lim_within_open:
  assumes"a \<in> S" "open S"
  shows "(f ---> l)(at a within S) \<longleftrightarrow> (f ---> l)(at a)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  { fix e::real assume "e>0"
    obtain d  where d:  "d >0" "\<forall>x\<in>S. 0 < dist x a \<and> dist x a < d \<longrightarrow> dist (f x) l < e" using `?lhs` `e>0` unfolding Lim_within by auto
    obtain d' where d': "d'>0" "\<forall>x. dist x a < d' \<longrightarrow> x \<in> S" using assms  unfolding open_def by auto
    from d d' have "\<exists>d>0. \<forall>x. 0 < dist x a \<and> dist x a < d \<longrightarrow> dist (f x) l < e" by (rule_tac x= "min d d'" in exI)auto
  }
  thus ?rhs unfolding Lim_at by auto
next
  assume ?rhs
  { fix e::real assume "e>0"
    then obtain d where "d>0" and d:"\<forall>x. 0 < dist x a \<and> dist x a < d \<longrightarrow> dist (f x) l < e" using `?rhs` unfolding Lim_at by auto
    hence "\<exists>d>0. \<forall>x. 0 < dist x a \<and> dist x a < d \<longrightarrow> dist (f x) l < e" using `d>0` by auto
  }
  thus ?lhs using Lim_at_within[of f l a S] by (auto simp add: Lim_at)
qed

text{* Another limit point characterization. *}

lemma islimpt_sequential:
 "x islimpt S \<longleftrightarrow> (\<exists>f. (\<forall>n::nat. f n \<in> S -{x}) \<and> (f ---> x) sequentially)" (is "?lhs = ?rhs")
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
  then obtain f::"nat\<Rightarrow>real^'a"  where f:"(\<forall>n. f n \<in> S - {x})" "(\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (f n) x < e)" unfolding Lim_sequentially by auto
  { fix e::real assume "e>0"
    then obtain N where "dist (f N) x < e" using f(2) by auto
    moreover have "f N\<in>S" "f N \<noteq> x" using f(1) by auto
    ultimately have "\<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e" by auto
  }
  thus ?lhs unfolding islimpt_approachable by auto
qed

text{* Basic arithmetical combining theorems for limits. *}

lemma Lim_linear: fixes f :: "('a \<Rightarrow> real^'n)" and h :: "(real^'n \<Rightarrow> real^'m)"
  assumes "(f ---> l) net" "linear h"
  shows "((\<lambda>x. h (f x)) ---> h l) net"
proof (cases "trivial_limit net")
  case True
  thus ?thesis unfolding tendsto_def unfolding eventually_def by auto
next
  case False note cas = this
  obtain b where b: "b>0" "\<forall>x. norm (h x) \<le> b * norm x" using assms(2) using linear_bounded_pos[of h] by auto
  { fix e::real assume "e >0"
    hence "e/b > 0" using `b>0` by (metis divide_pos_pos)
    then have "(\<exists>y. (\<exists>x. netord net x y) \<and> (\<forall>x. netord net x y \<longrightarrow> dist (f x) l < e/b))" using assms `e>0` cas
      unfolding tendsto_def unfolding eventually_def by auto
    then obtain y where y: "\<exists>x. netord net x y" "\<forall>x. netord net x y \<longrightarrow> dist (f x) l < e/b" by auto
    { fix x
      have "netord net x y \<longrightarrow> dist (h (f x)) (h l) < e"
	using y(2) b unfolding dist_def	using linear_sub[of h "f x" l] `linear h`
	apply auto by (metis b(1) b(2) dist_def dist_sym less_le_not_le linorder_not_le mult_imp_div_pos_le real_mult_commute xt1(7))
    }
    hence " (\<exists>y. (\<exists>x. netord net x y) \<and> (\<forall>x. netord net x y \<longrightarrow> dist (h (f x)) (h l) < e))" using y
      by(rule_tac x="y" in exI) auto
  }
  thus ?thesis unfolding tendsto_def eventually_def using `b>0` by auto
qed

lemma Lim_const: "((\<lambda>x. a) ---> a) net"
  by (auto simp add: Lim dist_refl trivial_limit_def)

lemma Lim_cmul: "(f ---> l) net ==> ((\<lambda>x. c *s f x) ---> c *s l) net"
  apply (rule Lim_linear[where f = f])
  apply simp
  apply (rule linear_compose_cmul)
  apply (rule linear_id[unfolded id_def])
  done

lemma Lim_neg: "(f ---> l) net ==> ((\<lambda>x. -(f x)) ---> -l) net"
  apply (simp add: Lim dist_def  group_simps)
  apply (subst minus_diff_eq[symmetric])
  unfolding norm_minus_cancel by simp

lemma Lim_add: fixes f :: "'a \<Rightarrow> real^'n" shows
 "(f ---> l) net \<Longrightarrow> (g ---> m) net \<Longrightarrow> ((\<lambda>x. f(x) + g(x)) ---> l + m) net"
proof-
  assume as:"(f ---> l) net" "(g ---> m) net"
  { fix e::real
    assume "e>0"
    hence *:"eventually (\<lambda>x. dist (f x) l < e/2) net"
            "eventually (\<lambda>x. dist (g x) m < e/2) net" using as
      by (auto intro: tendstoD simp del: Arith_Tools.less_divide_eq_number_of1)
    hence "eventually (\<lambda>x. dist (f x + g x) (l + m) < e) net"
    proof(cases "trivial_limit net")
      case True
      thus ?thesis unfolding eventually_def by auto
    next
      case False
      hence fl:"(\<exists>y. (\<exists>x. netord net x y) \<and> (\<forall>x. netord net x y \<longrightarrow> dist (f x) l < e / 2))" and
	    gl:"(\<exists>y. (\<exists>x. netord net x y) \<and> (\<forall>x. netord net x y \<longrightarrow> dist (g x) m < e / 2))"
	using * unfolding eventually_def by auto
      obtain c where c:"(\<exists>x. netord net x c)" "(\<forall>x. netord net x c \<longrightarrow> dist (f x) l < e / 2 \<and> dist (g x) m < e / 2)"
	using net_dilemma[of net, OF fl gl] by auto
      { fix x assume "netord net x c"
	with c(2) have " dist (f x + g x) (l + m) < e" using dist_triangle_add[of "f x" "g x" l m] by auto
      }
      with c show ?thesis unfolding eventually_def by auto
    qed
  }
  thus ?thesis unfolding tendsto_def by auto
qed

lemma Lim_sub: "(f ---> l) net \<Longrightarrow> (g ---> m) net \<Longrightarrow> ((\<lambda>x. f(x) - g(x)) ---> l - m) net"
  unfolding diff_minus
  by (simp add: Lim_add Lim_neg)

lemma Lim_null: "(f ---> l) net \<longleftrightarrow> ((\<lambda>x. f(x) - l) ---> 0) net" by (simp add: Lim dist_def)
lemma Lim_null_norm: "(f ---> 0) net \<longleftrightarrow> ((\<lambda>x. vec1(norm(f x))) ---> 0) net"
  by (simp add: Lim dist_def norm_vec1)

lemma Lim_null_comparison:
  assumes "eventually (\<lambda>x. norm(f x) <= g x) net" "((\<lambda>x. vec1(g x)) ---> 0) net"
  shows "(f ---> 0) net"
proof(simp add: tendsto_def, rule+)
  fix e::real assume "0<e"
  { fix x
    assume "norm (f x) \<le> g x" "dist (vec1 (g x)) 0 < e"
    hence "dist (f x) 0 < e"  unfolding vec_def using dist_vec1[of "g x" "0"]
      by (vector dist_def norm_vec1 dist_refl real_vector_norm_def dot_def vec1_def)
  }
  thus "eventually (\<lambda>x. dist (f x) 0 < e) net"
    using eventually_and[of "\<lambda>x. norm(f x) <= g x" "\<lambda>x. dist (vec1 (g x)) 0 < e" net]
    using eventually_mono[of "(\<lambda>x. norm (f x) \<le> g x \<and> dist (vec1 (g x)) 0 < e)" "(\<lambda>x. dist (f x) 0 < e)" net]
    using assms `e>0` unfolding tendsto_def by auto
qed

lemma Lim_component: "(f ---> l) net \<Longrightarrow> i \<in> {1 .. dimindex(UNIV:: 'n set)}
                      ==> ((\<lambda>a. vec1((f a :: real ^'n)$i)) ---> vec1(l$i)) net"
  apply (simp add: Lim dist_def vec1_sub[symmetric] norm_vec1  vector_minus_component[symmetric] del: One_nat_def)
  apply auto
  apply (erule_tac x=e in allE)
  apply clarify
  apply (rule_tac x=y in exI)
  apply auto
  apply (rule order_le_less_trans)
  apply (rule component_le_norm)
  by auto

lemma Lim_transform_bound:
  assumes "eventually (\<lambda>n. norm(f n) <= norm(g n)) net"  "(g ---> 0) net"
  shows "(f ---> 0) net"
proof(simp add: tendsto_def, rule+)
  fix e::real assume "e>0"
  { fix x
    assume "norm (f x) \<le> norm (g x)" "dist (g x) 0 < e"
    hence "dist (f x) 0 < e" by norm}
  thus "eventually (\<lambda>x. dist (f x) 0 < e) net"
    using eventually_and[of "\<lambda>x. norm (f x) \<le> norm (g x)" "\<lambda>x. dist (g x) 0 < e" net]
    using eventually_mono[of "\<lambda>x. norm (f x) \<le> norm (g x) \<and> dist (g x) 0 < e" "\<lambda>x. dist (f x) 0 < e" net]
    using assms `e>0` unfolding tendsto_def by blast
qed

text{* Deducing things about the limit from the elements. *}

lemma Lim_in_closed_set:
  assumes "closed S" "eventually (\<lambda>x. f(x) \<in> S) net"  "\<not>(trivial_limit net)" "(f ---> l) net"
  shows "l \<in> S"
proof-
  { assume "l \<notin> S"
    obtain e where e:"e>0" "ball l e \<subseteq> UNIV - S" using assms(1) `l \<notin> S` unfolding closed_def open_contains_ball by auto
    hence *:"\<forall>x. dist l x < e \<longrightarrow> x \<notin> S" by auto
    obtain y where "(\<exists>x. netord net x y) \<and> (\<forall>x. netord net x y \<longrightarrow> dist (f x) l < e)"
      using assms(3,4) `e>0` unfolding tendsto_def eventually_def by blast
    hence "(\<exists>x. netord net x y) \<and> (\<forall>x. netord net x y \<longrightarrow> f x \<notin> S)"  using * by (auto simp add: dist_sym)
    hence False using assms(2,3)
      using eventually_and[of "(\<lambda>x. f x \<in> S)" "(\<lambda>x. f x \<notin> S)"] not_eventually[of "(\<lambda>x. f x \<in> S \<and> f x \<notin> S)" net]
      unfolding eventually_def by blast
  }
  thus ?thesis by blast
qed

text{* Need to prove closed(cball(x,e)) before deducing this as a corollary. *}

lemma Lim_norm_ubound:
  assumes "\<not>(trivial_limit net)" "(f ---> l) net" "eventually (\<lambda>x. norm(f x) <= e) net"
  shows "norm(l) <= e"
proof-
  obtain y where y: "\<exists>x. netord net x y"  "\<forall>x. netord net x y \<longrightarrow> norm (f x) \<le> e" using assms(1,3) unfolding eventually_def by auto
  show ?thesis
  proof(rule ccontr)
    assume "\<not> norm l \<le> e"
    then obtain z where z: "\<exists>x. netord net x z"  "\<forall>x. netord net x z \<longrightarrow> dist (f x) l < norm l - e"
      using assms(2)[unfolded Lim] using assms(1) apply simp apply(erule_tac x="norm l - e" in allE) by auto
    obtain w where w:"netord net w z"  "netord net w y" using net[of net] using z(1) y(1) by blast
    hence "dist (f w) l < norm l - e \<and> norm (f w) <= e" using z(2) y(2) by auto
    thus False using `\<not> norm l \<le> e` by norm
  qed
qed

lemma Lim_norm_lbound:
  assumes "\<not> (trivial_limit net)"  "(f ---> l) net"  "eventually (\<lambda>x. e <= norm(f x)) net"
  shows "e \<le> norm l"
proof-
  obtain y where y: "\<exists>x. netord net x y"  "\<forall>x. netord net x y \<longrightarrow> e \<le> norm (f x)" using assms(1,3) unfolding eventually_def by auto
  show ?thesis
  proof(rule ccontr)
    assume "\<not> e \<le> norm l"
    then obtain z where z: "\<exists>x. netord net x z"  "\<forall>x. netord net x z \<longrightarrow> dist (f x) l < e - norm l"
      using assms(2)[unfolded Lim] using assms(1) apply simp apply(erule_tac x="e - norm l" in allE) by auto
    obtain w where w:"netord net w z"  "netord net w y" using net[of net] using z(1) y(1) by blast
    hence "dist (f w) l < e - norm l \<and> e \<le> norm (f w)" using z(2) y(2) by auto
    thus False using `\<not> e \<le> norm l` by norm
  qed
qed

text{* Uniqueness of the limit, when nontrivial. *}

lemma Lim_unique:
  fixes l::"real^'a" and net::"'b::zero_neq_one net"
  assumes "\<not>(trivial_limit net)"  "(f ---> l) net"  "(f ---> l') net"
  shows "l = l'"
proof-
  { fix e::real assume "e>0"
    hence "eventually (\<lambda>x. norm (0::real^'a) \<le> e) net" unfolding norm_0 using always_eventually[of _ net] by auto
    hence "norm (l - l') \<le> e" using Lim_norm_ubound[of net "\<lambda>x. 0" "l-l'"] using assms using Lim_sub[of f l net f l'] by auto
  } note * = this
  { assume "norm (l - l') > 0"
    hence "norm (l - l') = 0" using *[of "(norm (l - l')) /2"] using norm_ge_zero[of "l - l'"] by simp
  }
  hence "l = l'" using norm_ge_zero[of "l - l'"] unfolding le_less and dist_nz[of l l', unfolded dist_def, THEN sym] by auto
  thus ?thesis using assms using Lim_sub[of f l net f l'] by simp
qed

lemma tendsto_Lim:
 "~(trivial_limit (net::('b::zero_neq_one net))) \<Longrightarrow> (f ---> l) net ==> Lim net f = l"
  unfolding Lim_def using Lim_unique[of net f] by auto

text{* Limit under bilinear function (surprisingly tedious, but important) *}

lemma norm_bound_lemma:
  "0 < e \<Longrightarrow> \<exists>d>0. \<forall>(x'::real^'b) y'::real^'a. norm(x' - (x::real^'b)) < d \<and> norm(y' - y) < d \<longrightarrow> norm(x') * norm(y' - y) + norm(x' - x) * norm(y) < e"
proof-
  assume e: "0 < e"
  have th1: "(2 * norm x + 2 * norm y + 2) > 0" using norm_ge_zero[of x] norm_ge_zero[of y] by norm
  hence th0: "0 < e / (2 * norm x + 2 * norm y + 2)"  using `e>0` using divide_pos_pos by auto
  moreover
  { fix x' y'
    assume h: "norm (x' - x) < 1" "norm (x' - x) < e / (2 * norm x + 2 * norm y + 2)"
      "norm (y' - y) < 1" "norm (y' - y) < e / (2 * norm x + 2 * norm y + 2)"
    have th: "\<And>a b (c::real). a \<ge> 0 \<Longrightarrow> c \<ge> 0 \<Longrightarrow> a + (b + c) < e ==> b < e " by arith
    from h have thx: "norm (x' - x) * norm y < e / 2"
      using th0 th1 apply (simp add: field_simps)
      apply (rule th) defer defer apply assumption
      by (simp_all add: norm_ge_zero zero_le_mult_iff)

    have "norm x' - norm x < 1" apply(rule le_less_trans)
      using h(1) using norm_triangle_ineq2[of x' x] by auto
    hence *:"norm x' < 1 + norm x"  by auto

    have thy: "norm (y' - y) * norm x' < e / (2 * norm x + 2 * norm y + 2) * (1 + norm x)"
      using mult_strict_mono'[OF h(4) * norm_ge_zero norm_ge_zero] by auto
    also have "\<dots> \<le> e/2" apply simp unfolding divide_le_eq
      using th1 th0 `e>0` apply auto
      unfolding mult_assoc and real_mult_le_cancel_iff2[OF `e>0`] by auto

    finally have "norm x' * norm (y' - y) + norm (x' - x) * norm y < e"
      using thx and e by (simp add: field_simps)  }
  ultimately show ?thesis apply(rule_tac x="min 1 (e / 2 / (norm x + norm y + 1))" in exI) by auto
qed

lemma Lim_bilinear:
  fixes net :: "'a net" and h:: "real ^'m \<Rightarrow> real ^'n \<Rightarrow> real ^'p"
  assumes "(f ---> l) net" and "(g ---> m) net" and "bilinear h"
  shows "((\<lambda>x. h (f x) (g x)) ---> (h l m)) net"
proof(cases "trivial_limit net")
  case True thus "((\<lambda>x. h (f x) (g x)) ---> h l m) net" unfolding Lim ..
next
  case False note ntriv = this
  obtain B where "B>0" and B:"\<forall>x y. norm (h x y) \<le> B * norm x * norm y" using bilinear_bounded_pos[OF assms(3)] by auto
  { fix e::real assume "e>0"
    obtain d where "d>0" and d:"\<forall>x' y'. norm (x' - l) < d \<and> norm (y' - m) < d \<longrightarrow> norm x' * norm (y' - m) + norm (x' - l) * norm m < e / B" using `B>0` `e>0`
      using norm_bound_lemma[of "e / B" l m] using divide_pos_pos by auto

    have *:"\<And>x y. h (f x) (g x) - h l m = h (f x) (g x - m) + h (f x - l) m"
      unfolding bilinear_rsub[OF assms(3)]
      unfolding bilinear_lsub[OF assms(3)] by auto

    { fix x assume "dist (f x) l < d \<and> dist (g x) m < d"
      hence **:"norm (f x) * norm (g x - m) + norm (f x - l) * norm m < e / B"
	using d[THEN spec[where x="f x"], THEN spec[where x="g x"]] unfolding dist_def  by auto
      have "norm (h (f x) (g x - m)) + norm (h (f x - l) m) \<le> B * norm (f x) * norm (g x - m) + B * norm (f x - l) * norm m"
	using B[THEN spec[where x="f x"], THEN spec[where x="g x - m"]]
	using B[THEN spec[where x="f x - l"], THEN spec[where x="m"]] by auto
      also have "\<dots> < e" using ** and `B>0` by(auto simp add: field_simps)
      finally have "dist (h (f x) (g x)) (h l m) < e" unfolding dist_def and * using norm_triangle_lt by auto
    }
    moreover
    obtain c where "(\<exists>x. netord net x c) \<and> (\<forall>x. netord net x c \<longrightarrow> dist (f x) l < d \<and> dist (g x) m < d)"
      using net_dilemma[of net "\<lambda>x. dist (f x) l < d" "\<lambda>x. dist (g x) m < d"] using assms(1,2) unfolding Lim using False and `d>0` by (auto elim!: allE[where x=d])
    ultimately have "\<exists>y. (\<exists>x. netord net x y) \<and> (\<forall>x. netord net x y \<longrightarrow> dist (h (f x) (g x)) (h l m) < e)" by auto  }
  thus "((\<lambda>x. h (f x) (g x)) ---> h l m) net" unfolding Lim by auto
qed

text{* These are special for limits out of the same vector space. *}

lemma Lim_within_id: "(id ---> a) (at a within s)" by (auto simp add: Lim_within id_def)
lemma Lim_at_id: "(id ---> a) (at a)"
apply (subst within_UNIV[symmetric]) by (simp add: Lim_within_id)

lemma Lim_at_zero: "(f ---> l) (at (a::real^'a)) \<longleftrightarrow> ((\<lambda>x. f(a + x)) ---> l) (at 0)" (is "?lhs = ?rhs")
proof
  assume "?lhs"
  { fix e::real assume "e>0"
    with `?lhs` obtain d where d:"d>0" "\<forall>x. 0 < dist x a \<and> dist x a < d \<longrightarrow> dist (f x) l < e" unfolding Lim_at by auto
    { fix x::"real^'a" assume "0 < dist x 0 \<and> dist x 0 < d"
      hence "dist (f (a + x)) l < e" using d
      apply(erule_tac x="x+a" in allE) by(auto simp add: comm_monoid_add.mult_commute dist_def dist_sym)
    }
    hence "\<exists>d>0. \<forall>x. 0 < dist x 0 \<and> dist x 0 < d \<longrightarrow> dist (f (a + x)) l < e" using d(1) by auto
  }
  thus "?rhs" unfolding Lim_at by auto
next
  assume "?rhs"
  { fix e::real assume "e>0"
    with `?rhs` obtain d where d:"d>0" "\<forall>x. 0 < dist x 0 \<and> dist x 0 < d \<longrightarrow> dist (f (a + x)) l < e"
      unfolding Lim_at by auto
    { fix x::"real^'a" assume "0 < dist x a \<and> dist x a < d"
      hence "dist (f x) l < e" using d apply(erule_tac x="x-a" in allE)
	by(auto simp add: comm_monoid_add.mult_commute dist_def dist_sym)
    }
    hence "\<exists>d>0. \<forall>x. 0 < dist x a \<and> dist x a < d \<longrightarrow> dist (f x) l < e" using d(1) by auto
  }
  thus "?lhs" unfolding Lim_at by auto
qed

text{* It's also sometimes useful to extract the limit point from the net.  *}

definition "netlimit net = (SOME a. \<forall>x. ~(netord net x a))"

lemma netlimit_within: assumes"~(trivial_limit (at a within S))"
  shows "(netlimit (at a within S) = a)"
proof-
  { fix x assume "x \<noteq> a"
    then obtain y where y:"dist y a \<le> dist a a \<and> 0 < dist y a \<and> y \<in> S \<or> dist y a \<le> dist x a \<and> 0 < dist y a \<and> y \<in> S" using assms unfolding trivial_limit_def within at by blast
    assume "\<forall>y. \<not> netord (at a within S) y x"
    hence "x = a" using y unfolding within at by (auto simp add: dist_refl dist_nz)
  }
  moreover
  have "\<forall>y. \<not> netord (at a within S) y a"  using assms unfolding trivial_limit_def within at by (auto simp add: dist_refl)
  ultimately show ?thesis unfolding netlimit_def using some_equality[of "\<lambda>x. \<forall>y. \<not> netord (at a within S) y x"] by blast
qed

lemma netlimit_at: "netlimit(at a) = a"
  apply (subst within_UNIV[symmetric])
  using netlimit_within[of a UNIV]
  by (simp add: trivial_limit_at within_UNIV)

text{* Transformation of limit. *}

lemma Lim_transform: assumes "((\<lambda>x. f x - g x) ---> 0) net" "(f ---> l) net"
  shows "(g ---> l) net"
proof-
  from assms have "((\<lambda>x. f x - g x - f x) ---> 0 - l) net" using Lim_sub[of "\<lambda>x. f x - g x" 0 net f l] by auto
  thus "?thesis" using Lim_neg [of "\<lambda> x. - g x" "-l" net] by auto
qed

lemma Lim_transform_eventually:  "eventually (\<lambda>x. f x = g x) net \<Longrightarrow> (f ---> l) net ==> (g ---> l) net"
  using Lim_eventually[of "\<lambda>x. f x - g x" 0 net] Lim_transform[of f g net l] by auto

lemma Lim_transform_within:
  assumes "0 < d" "(\<forall>x'\<in>S. 0 < dist x' x \<and> dist x' x < d \<longrightarrow> f x' = g x')"
          "(f ---> l) (at x within S)"
  shows   "(g ---> l) (at x within S)"
proof-
  have "((\<lambda>x. f x - g x) ---> 0) (at x within S)" unfolding Lim_within[of "\<lambda>x. f x - g x" 0 x S] using assms(1,2) by auto
  thus ?thesis using Lim_transform[of f g "at x within S" l] using assms(3) by auto
qed

lemma Lim_transform_at: "0 < d \<Longrightarrow> (\<forall>x'. 0 < dist x' x \<and> dist x' x < d \<longrightarrow> f x' = g x') \<Longrightarrow>
  (f ---> l) (at x) ==> (g ---> l) (at x)"
  apply (subst within_UNIV[symmetric])
  using Lim_transform_within[of d UNIV x f g l]
  by (auto simp add: within_UNIV)

text{* Common case assuming being away from some crucial point like 0. *}

lemma Lim_transform_away_within:
  fixes f:: "real ^'m \<Rightarrow> real ^'n"
  assumes "a\<noteq>b" "\<forall>x\<in> S. x \<noteq> a \<and> x \<noteq> b \<longrightarrow> f x = g x"
  and "(f ---> l) (at a within S)"
  shows "(g ---> l) (at a within S)"
proof-
  have "\<forall>x'\<in>S. 0 < dist x' a \<and> dist x' a < dist a b \<longrightarrow> f x' = g x'" using assms(2)
    apply auto apply(erule_tac x=x' in ballE) by (auto simp add: dist_sym dist_refl)
  thus ?thesis using Lim_transform_within[of "dist a b" S a f g l] using assms(1,3) unfolding dist_nz by auto
qed

lemma Lim_transform_away_at:
  fixes f:: "real ^'m \<Rightarrow> real ^'n"
  assumes ab: "a\<noteq>b" and fg: "\<forall>x. x \<noteq> a \<and> x \<noteq> b \<longrightarrow> f x = g x"
  and fl: "(f ---> l) (at a)"
  shows "(g ---> l) (at a)"
  using Lim_transform_away_within[OF ab, of UNIV f g l] fg fl
  by (auto simp add: within_UNIV)

text{* Alternatively, within an open set. *}

lemma Lim_transform_within_open:
  fixes f:: "real ^'m \<Rightarrow> real ^'n"
  assumes "open S"  "a \<in> S"  "\<forall>x\<in>S. x \<noteq> a \<longrightarrow> f x = g x"  "(f ---> l) (at a)"
  shows "(g ---> l) (at a)"
proof-
  from assms(1,2) obtain e::real where "e>0" and e:"ball a e \<subseteq> S" unfolding open_contains_ball by auto
  hence "\<forall>x'. 0 < dist x' a \<and> dist x' a < e \<longrightarrow> f x' = g x'" using assms(3)
    unfolding ball_def subset_eq apply auto apply(erule_tac x=x' in allE) apply(erule_tac x=x' in ballE) by(auto simp add: dist_refl dist_sym)
  thus ?thesis using Lim_transform_at[of e a f g l] `e>0` assms(4) by auto
qed

text{* A congruence rule allowing us to transform limits assuming not at point. *}

lemma Lim_cong_within[cong add]:
 "(\<And>x. x \<noteq> a \<Longrightarrow> f x = g x) ==> ((\<lambda>x. f x) ---> l) (at a within S) \<longleftrightarrow> ((g ---> l) (at a within S))"
  by (simp add: Lim_within dist_nz[symmetric])

lemma Lim_cong_at[cong add]:
 "(\<And>x. x \<noteq> a ==> f x = g x) ==> (((\<lambda>x. f x) ---> l) (at a) \<longleftrightarrow> ((g ---> l) (at a)))"
  by (simp add: Lim_at dist_nz[symmetric])

text{* Useful lemmas on closure and set of possible sequential limits.*}

lemma closure_sequential:
 "l \<in> closure S \<longleftrightarrow> (\<exists>x. (\<forall>n. x n \<in> S) \<and> (x ---> l) sequentially)" (is "?lhs = ?rhs")
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
 "closed S \<longleftrightarrow> (\<forall>x l. (\<forall>n. x n \<in> S) \<and> (x ---> l) sequentially \<longrightarrow> l \<in> S)"
  unfolding closed_limpt
  by (metis closure_sequential closure_closed closed_limpt islimpt_sequential mem_delete)

lemma closure_approachable: "x \<in> closure S \<longleftrightarrow> (\<forall>e>0. \<exists>y\<in>S. dist y x < e)"
  apply (auto simp add: closure_def islimpt_approachable)
  by (metis dist_refl)

lemma closed_approachable: "closed S ==> (\<forall>e>0. \<exists>y\<in>S. dist y x < e) \<longleftrightarrow> x \<in> S"
  by (metis closure_closed closure_approachable)

text{* Some other lemmas about sequences. *}

lemma seq_offset: "(f ---> l) sequentially ==> ((\<lambda>i. f( i + k)) ---> l) sequentially"
  apply (auto simp add: Lim_sequentially)
  by (metis trans_le_add1 )

lemma seq_offset_neg: "(f ---> l) sequentially ==> ((\<lambda>i. f(i - k)) ---> l) sequentially"
  apply (simp add: Lim_sequentially)
  apply (subgoal_tac "\<And>N k (n::nat). N + k <= n ==> N <= n - k")
  apply metis
  by arith

lemma seq_offset_rev: "((\<lambda>i. f(i + k)) ---> l) sequentially ==> (f ---> l) sequentially"
  apply (simp add: Lim_sequentially)
  apply (subgoal_tac "\<And>N k (n::nat). N + k <= n ==> N <= n - k \<and> (n - k) + k = n")
  by metis arith

lemma seq_harmonic: "((\<lambda>n. vec1(inverse (real n))) ---> 0) sequentially"
proof-
  { fix e::real assume "e>0"
    hence "\<exists>N::nat. \<forall>n::nat\<ge>N. inverse (real n) < e"
      using real_arch_inv[of e] apply auto apply(rule_tac x=n in exI)
      by (metis dlo_simps(4) le_imp_inverse_le linorder_not_less real_of_nat_gt_zero_cancel_iff real_of_nat_less_iff xt1(7))
  }
  thus ?thesis unfolding Lim_sequentially dist_def apply simp unfolding norm_vec1 by auto
qed

text{* More properties of closed balls. *}

lemma closed_cball: "closed(cball x e)"
proof-
  { fix xa::"nat\<Rightarrow>real^'a" and l assume as: "\<forall>n. dist x (xa n) \<le> e" "(xa ---> l) sequentially"
    from as(2) have "((\<lambda>n. x - xa n) ---> x - l) sequentially" using Lim_sub[of "\<lambda>n. x" x sequentially xa l] Lim_const[of x sequentially] by auto
    moreover from as(1) have "eventually (\<lambda>n. norm (x - xa n) \<le> e) sequentially" unfolding eventually_sequentially dist_def by auto
    ultimately have "dist x l \<le> e"
      unfolding dist_def
      using Lim_norm_ubound[of sequentially _ "x - l" e] using trivial_limit_sequentially by auto
  }
  thus ?thesis unfolding closed_sequential_limits by auto
qed

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
  apply (simp add: interior_def)
  by (metis open_contains_cball subset_trans ball_subset_cball centre_in_ball open_ball)

lemma islimpt_ball: "y islimpt ball x e \<longleftrightarrow> 0 < e \<and> y \<in> cball x e" (is "?lhs = ?rhs")
proof
  assume "?lhs"
  { assume "e \<le> 0"
    hence *:"ball x e = {}" using ball_eq_empty[of x e] by auto
    have False using `?lhs` unfolding * using islimpt_EMPTY[of y] by auto
  }
  hence "e > 0" by (metis dlo_simps(3))
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
	case True hence False using `d \<le> dist x y` `d>0` dist_refl[of x] by auto
	thus "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d" by auto
      next
	case False

	have "dist x (y - (d / (2 * dist y x)) *s (y - x))
	      = norm (x - y + (d / (2 * norm (y - x))) *s (y - x))"
	  unfolding mem_cball mem_ball dist_def diff_diff_eq2 diff_add_eq[THEN sym] by auto
	also have "\<dots> = \<bar>- 1 + d / (2 * norm (x - y))\<bar> * norm (x - y)"
	  using vector_sadd_rdistrib[of "- 1" "d / (2 * norm (y - x))", THEN sym, of "y - x"]
	  unfolding vector_smult_lneg vector_smult_lid
	  by (auto simp add: dist_sym[unfolded dist_def] norm_mul)
	also have "\<dots> = \<bar>- norm (x - y) + d / 2\<bar>"
	  unfolding abs_mult_pos[of "norm (x - y)", OF norm_ge_zero[of "x - y"]]
	  unfolding real_add_mult_distrib using `x\<noteq>y`[unfolded dist_nz, unfolded dist_def] by auto
	also have "\<dots> \<le> e - d/2" using `d \<le> dist x y` and `d>0` and `?rhs` by(auto simp add: dist_def)
	finally have "y - (d / (2 * dist y x)) *s (y - x) \<in> ball x e" using `d>0` by auto

	moreover

	have "(d / (2*dist y x)) *s (y - x) \<noteq> 0"
	  using `x\<noteq>y`[unfolded dist_nz] `d>0` unfolding vector_mul_eq_0 by (auto simp add: dist_sym dist_refl)
	moreover
	have "dist (y - (d / (2 * dist y x)) *s (y - x)) y < d" unfolding dist_def apply simp unfolding norm_minus_cancel norm_mul
	  using `d>0` `x\<noteq>y`[unfolded dist_nz] dist_sym[of x y]
	  unfolding dist_def by auto
	ultimately show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d" by (rule_tac  x="y - (d / (2*dist y x)) *s (y - x)" in bexI) auto
      qed
    next
      case False hence "d > dist x y" by auto
      show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
      proof(cases "x=y")
	case True
	obtain z where **:"dist y z = (min e d) / 2" using vector_choose_dist[of "(min e d) / 2" y]
	  using `d > 0` `e>0` by (auto simp add: dist_refl)
	show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
	  apply(rule_tac x=z in bexI) unfolding `x=y` dist_sym dist_refl dist_nz using **  `d > 0` `e>0` by auto
      next
	case False thus "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
	  using `d>0` `d > dist x y` `?rhs` by(rule_tac x=x in bexI, auto simp add: dist_refl)
      qed
    qed  }
  thus "?lhs" unfolding mem_cball islimpt_approachable mem_ball by auto
qed

lemma closure_ball: "0 < e ==> (closure(ball x e) = cball x e)"
  apply (simp add: closure_def islimpt_ball expand_set_eq)
  by arith

lemma interior_cball: "interior(cball x e) = ball x e"
proof(cases "e\<ge>0")
  case False note cs = this
  from cs have "ball x e = {}" using ball_empty[of e x] by auto moreover
  { fix y assume "y \<in> cball x e"
    hence False unfolding mem_cball using dist_nz[of x y] cs by (auto simp add: dist_refl)  }
  hence "cball x e = {}" by auto
  hence "interior (cball x e) = {}" using interior_empty by auto
  ultimately show ?thesis by blast
next
  case True note cs = this
  have "ball x e \<subseteq> cball x e" using ball_subset_cball by auto moreover
  { fix S y assume as: "S \<subseteq> cball x e" "open S" "y\<in>S"
    then obtain d where "d>0" and d:"\<forall>x'. dist x' y < d \<longrightarrow> x' \<in> S" unfolding open_def by blast

    then obtain xa where xa:"dist y xa = d / 2" using vector_choose_dist[of "d/2" y] by auto
    hence xa_y:"xa \<noteq> y" using dist_nz[of y xa] using `d>0` by auto
    have "xa\<in>S" using d[THEN spec[where x=xa]] using xa apply(auto simp add: dist_sym) unfolding dist_nz[THEN sym] using xa_y by auto
    hence xa_cball:"xa \<in> cball x e" using as(1) by auto

    hence "y \<in> ball x e" proof(cases "x = y")
      case True
      hence "e>0" using xa_y[unfolded dist_nz] xa_cball[unfolded mem_cball] by (auto simp add: dist_sym)
      thus "y \<in> ball x e" using `x = y ` by simp
    next
      case False
      have "dist (y + (d / 2 / dist y x) *s (y - x)) y < d" unfolding dist_def
	using `d>0` norm_ge_zero[of "y - x"] `x \<noteq> y` by auto
      hence *:"y + (d / 2 / dist y x) *s (y - x) \<in> cball x e" using d as(1)[unfolded subset_eq] by blast
      have "y - x \<noteq> 0" using `x \<noteq> y` by auto
      hence **:"d / (2 * norm (y - x)) > 0" unfolding zero_less_norm_iff[THEN sym]
	using `d>0` divide_pos_pos[of d "2*norm (y - x)"] by auto

      have "dist (y + (d / 2 / dist y x) *s (y - x)) x = norm (y + (d / (2 * norm (y - x))) *s y - (d / (2 * norm (y - x))) *s x - x)"
	by (auto simp add: dist_def vector_ssub_ldistrib add_diff_eq)
      also have "\<dots> = norm ((1 + d / (2 * norm (y - x))) *s (y - x))"
	by (auto simp add: vector_sadd_rdistrib vector_smult_lid ring_simps vector_sadd_rdistrib vector_ssub_ldistrib)
      also have "\<dots> = \<bar>1 + d / (2 * norm (y - x))\<bar> * norm (y - x)" using ** by auto
      also have "\<dots> = (dist y x) + d/2"using ** by (auto simp add: left_distrib dist_def)
      finally have "e \<ge> dist x y +d/2" using *[unfolded mem_cball] by (auto simp add: dist_sym)
      thus "y \<in> ball x e" unfolding mem_ball using `d>0` by auto
    qed  }
  hence "\<forall>S \<subseteq> cball x e. open S \<longrightarrow> S \<subseteq> ball x e" by auto
  ultimately show ?thesis using interior_unique[of "ball x e" "cball x e"] using open_ball[of x e] by auto
qed

lemma frontier_ball: "0 < e ==> frontier(ball a e) = {x. dist a x = e}"
  apply (simp add: frontier_def closure_ball interior_open open_ball order_less_imp_le)
  apply (simp add: expand_set_eq)
  by arith

lemma frontier_cball: "frontier(cball a e) = {x. dist a x = e}"
  apply (simp add: frontier_def interior_cball closed_cball closure_closed order_less_imp_le)
  apply (simp add: expand_set_eq)
  by arith

lemma cball_eq_empty: "(cball x e = {}) \<longleftrightarrow> e < 0"
  apply (simp add: expand_set_eq not_le)
  by (metis dist_pos_le dist_refl order_less_le_trans)
lemma cball_empty: "e < 0 ==> cball x e = {}" by (simp add: cball_eq_empty)

lemma cball_eq_sing: "(cball x e = {x}) \<longleftrightarrow> e = 0"
proof-
  { assume as:"\<forall>xa. (dist x xa \<le> e) = (xa = x)"
    hence "e \<ge> 0" apply (erule_tac x=x in allE) by (auto simp add: dist_pos_le dist_refl)
    then obtain y where y:"dist x y = e" using vector_choose_dist[of e] by auto
    hence "e = 0" using as apply(erule_tac x=y in allE) by (auto simp add: dist_pos_le dist_refl)
  }
  thus ?thesis unfolding expand_set_eq mem_cball by (auto simp add: dist_refl dist_nz dist_le_0)
qed

lemma cball_sing:  "e = 0 ==> cball x e = {x}" by (simp add: cball_eq_sing)

text{* For points in the interior, localization of limits makes no difference.   *}

lemma eventually_within_interior: assumes "x \<in> interior S"
  shows "eventually P (at x within S) \<longleftrightarrow> eventually P (at x)" (is "?lhs = ?rhs")
proof-
  from assms obtain e where e:"e>0" "\<forall>y. dist x y < e \<longrightarrow> y \<in> S" unfolding mem_interior ball_def subset_eq by auto
  { assume "?lhs" then obtain d where "d>0" "\<forall>xa\<in>S. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> P xa" unfolding eventually_within by auto
    hence "?rhs" unfolding eventually_at using e by (auto simp add: dist_sym intro!: add exI[of _ "min e d"])
  } moreover
  { assume "?rhs" hence "?lhs" unfolding eventually_within eventually_at by auto
  } ultimately
  show "?thesis" by auto
qed

lemma lim_within_interior: "x \<in> interior S  ==> ((f ---> l) (at x within S) \<longleftrightarrow> (f ---> l) (at x))"
  by (simp add: tendsto_def eventually_within_interior)

lemma netlimit_within_interior: assumes "x \<in> interior S"
  shows "netlimit(at x within S) = x" (is "?lhs = ?rhs")
proof-
  from assms obtain e::real where e:"e>0" "ball x e \<subseteq> S" using open_interior[of S] unfolding open_contains_ball using interior_subset[of S] by auto
  hence "\<not> trivial_limit (at x within S)" using islimpt_subset[of x "ball x e" S] unfolding trivial_limit_within islimpt_ball centre_in_cball by auto
  thus ?thesis using netlimit_within by auto
qed

subsection{* Boundedness. *}

  (* FIXME: This has to be unified with BSEQ!! *)
definition "bounded S \<longleftrightarrow> (\<exists>a. \<forall>(x::real^'n) \<in> S. norm x <= a)"

lemma bounded_empty[simp]: "bounded {}" by (simp add: bounded_def)
lemma bounded_subset: "bounded T \<Longrightarrow> S \<subseteq> T ==> bounded S"
  by (metis bounded_def subset_eq)

lemma bounded_interior[intro]: "bounded S ==> bounded(interior S)"
  by (metis bounded_subset interior_subset)

lemma bounded_closure[intro]: assumes "bounded S" shows "bounded(closure S)"
proof-
  from assms obtain a where a:"\<forall>x\<in>S. norm x \<le> a" unfolding bounded_def by auto
  { fix x assume "x\<in>closure S"
    then obtain xa where xa:"\<forall>n. xa n \<in> S"  "(xa ---> x) sequentially" unfolding closure_sequential by auto
    moreover have "\<exists>y. \<exists>x. netord sequentially x y" using trivial_limit_sequentially unfolding trivial_limit_def by blast
    hence "\<exists>y. (\<exists>x. netord sequentially x y) \<and> (\<forall>x. netord sequentially x y \<longrightarrow> norm (xa x) \<le> a)" unfolding sequentially_def using a xa(1) by auto
    ultimately have "norm x \<le> a" using Lim_norm_ubound[of sequentially xa x a] trivial_limit_sequentially unfolding eventually_def by auto
  }
  thus ?thesis unfolding bounded_def by auto
qed

lemma bounded_cball[simp,intro]: "bounded (cball x e)"
  apply (simp add: bounded_def)
  apply (rule exI[where x="norm x + e"])
  apply (simp add: Ball_def)
  by norm

lemma bounded_ball[simp,intro]: "bounded(ball x e)"
  by (metis ball_subset_cball bounded_cball bounded_subset)

lemma finite_imp_bounded[intro]: assumes "finite S" shows "bounded S"
proof-
  { fix x F assume as:"bounded F"
    then obtain a where "\<forall>x\<in>F. norm x \<le> a" unfolding bounded_def by auto
    hence "bounded (insert x F)" unfolding bounded_def by(auto intro!: add exI[of _ "max a (norm x)"])
  }
  thus ?thesis using finite_induct[of S bounded]  using bounded_empty assms by auto
qed

lemma bounded_Un[simp]: "bounded (S \<union> T) \<longleftrightarrow> bounded S \<and> bounded T"
  apply (auto simp add: bounded_def)
  by (rule_tac x="max a aa" in exI, auto)

lemma bounded_Union[intro]: "finite F \<Longrightarrow> (\<forall>S\<in>F. bounded S) \<Longrightarrow> bounded(\<Union>F)"
  by (induct rule: finite_induct[of F], auto)

lemma bounded_pos: "bounded S \<longleftrightarrow> (\<exists>b>0. \<forall>x\<in> S. norm x <= b)"
  apply (simp add: bounded_def)
  apply (subgoal_tac "\<And>x (y::real). 0 < 1 + abs y \<and> (x <= y \<longrightarrow> x <= 1 + abs y)")
  by metis arith

lemma bounded_Int[intro]: "bounded S \<or> bounded T \<Longrightarrow> bounded (S \<inter> T)"
  by (metis Int_lower1 Int_lower2 bounded_subset)

lemma bounded_diff[intro]: "bounded S ==> bounded (S - T)"
apply (metis Diff_subset bounded_subset)
done

lemma bounded_insert[intro]:"bounded(insert x S) \<longleftrightarrow> bounded S"
  by (metis Diff_cancel Un_empty_right Un_insert_right bounded_Un bounded_subset finite.emptyI finite_imp_bounded infinite_remove subset_insertI)

lemma bot_bounded_UNIV[simp, intro]: "~(bounded (UNIV:: (real^'n) set))"
proof(auto simp add: bounded_pos not_le)
  fix b::real  assume b: "b >0"
  have b1: "b +1 \<ge> 0" using b by simp
  then obtain x:: "real^'n" where "norm x = b + 1" using vector_choose_size[of "b+1"] by blast
  hence "norm x > b" using b by simp
  then show "\<exists>(x::real^'n). b < norm x"  by blast
qed

lemma bounded_linear_image:
  fixes f :: "real^'m \<Rightarrow> real^'n"
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

lemma bounded_scaling: "bounded S \<Longrightarrow> bounded ((\<lambda>x. c *s x) ` S)"
  apply (rule bounded_linear_image, assumption)
  by (rule linear_compose_cmul, rule linear_id[unfolded id_def])

lemma bounded_translation: assumes "bounded S" shows "bounded ((\<lambda>x. a + x) ` S)"
proof-
  from assms obtain b where b:"b>0" "\<forall>x\<in>S. norm x \<le> b" unfolding bounded_pos by auto
  { fix x assume "x\<in>S"
    hence "norm (a + x) \<le> b + norm a" using norm_triangle_ineq[of a x] b by auto
  }
  thus ?thesis unfolding bounded_pos using norm_ge_zero[of a] b(1) using add_strict_increasing[of b 0 "norm a"]
    by (auto intro!: add exI[of _ "b + norm a"])
qed


text{* Some theorems on sups and infs using the notion "bounded". *}

lemma bounded_vec1: "bounded(vec1 ` S) \<longleftrightarrow>  (\<exists>a. \<forall>x\<in>S. abs x <= a)"
  by (simp add: bounded_def forall_vec1 norm_vec1 vec1_in_image_vec1)

lemma bounded_has_rsup: assumes "bounded(vec1 ` S)" "S \<noteq> {}"
  shows "\<forall>x\<in>S. x <= rsup S" and "\<forall>b. (\<forall>x\<in>S. x <= b) \<longrightarrow> rsup S <= b"
proof
  fix x assume "x\<in>S"
  from assms(1) obtain a where a:"\<forall>x\<in>S. \<bar>x\<bar> \<le> a" unfolding bounded_vec1 by auto
  hence *:"S *<= a" using setleI[of S a] by (metis abs_le_interval_iff mem_def)
  thus "x \<le> rsup S" using rsup[OF `S\<noteq>{}`] using assms(1)[unfolded bounded_vec1] using isLubD2[of UNIV S "rsup S" x] using `x\<in>S` by auto
next
  show "\<forall>b. (\<forall>x\<in>S. x \<le> b) \<longrightarrow> rsup S \<le> b" using assms
  using rsup[of S, unfolded isLub_def isUb_def leastP_def setle_def setge_def]
  apply (auto simp add: bounded_vec1)
  by (auto simp add: isLub_def isUb_def leastP_def setle_def setge_def)
qed

lemma rsup_insert: assumes "bounded (vec1 ` S)"
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
  assumes "bounded(vec1 ` S)"  "S \<noteq> {}"
  shows "\<forall>x\<in>S. x >= rinf S" and "\<forall>b. (\<forall>x\<in>S. x >= b) \<longrightarrow> rinf S >= b"
proof
  fix x assume "x\<in>S"
  from assms(1) obtain a where a:"\<forall>x\<in>S. \<bar>x\<bar> \<le> a" unfolding bounded_vec1 by auto
  hence *:"- a <=* S" using setgeI[of S "-a"] unfolding abs_le_interval_iff by auto
  thus "x \<ge> rinf S" using rinf[OF `S\<noteq>{}`] using isGlbD2[of UNIV S "rinf S" x] using `x\<in>S` by auto
next
  show "\<forall>b. (\<forall>x\<in>S. x >= b) \<longrightarrow> rinf S \<ge> b" using assms
  using rinf[of S, unfolded isGlb_def isLb_def greatestP_def setle_def setge_def]
  apply (auto simp add: bounded_vec1)
  by (auto simp add: isGlb_def isLb_def greatestP_def setle_def setge_def)
qed

(* TODO: Move this to RComplete.thy -- would need to include Glb into RComplete *)
lemma real_isGlb_unique: "[| isGlb R S x; isGlb R S y |] ==> x = (y::real)"
  apply (frule isGlb_isLb)
  apply (frule_tac x = y in isGlb_isLb)
  apply (blast intro!: order_antisym dest!: isGlb_le_isLb)
  done

lemma rinf_insert: assumes "bounded (vec1 ` S)"
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

definition "compact S \<longleftrightarrow>
   (\<forall>(f::nat \<Rightarrow> real^'n). (\<forall>n. f n \<in> S) \<longrightarrow>
       (\<exists>l\<in>S. \<exists>r. (\<forall>m n. m < n \<longrightarrow> r m < r n) \<and> ((f o r) ---> l) sequentially))"

lemma monotone_bigger: fixes r::"nat\<Rightarrow>nat"
  assumes "\<forall>m n::nat. m < n --> r m < r n"
  shows "n \<le> r n"
proof(induct n)
  show "0 \<le> r 0" by auto
next
  fix n assume "n \<le> r n"
  moreover have "r n < r (Suc n)" using assms by auto
  ultimately show "Suc n \<le> r (Suc n)" by auto
qed

lemma lim_subsequence: "\<forall>m n. m < n \<longrightarrow> r m < r n \<Longrightarrow> (s ---> l) sequentially \<Longrightarrow> ((s o r) ---> l) sequentially"
unfolding Lim_sequentially by (simp, metis  monotone_bigger le_trans)

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
  assumes "\<forall>m n. m \<le> n --> s m \<le> s n" and "\<forall>n. abs(s n) \<le> b"
  shows "\<exists> l. \<forall>e::real>0. \<exists> N. \<forall>n \<ge> N.  abs(s n - l) < e"
proof-
  have "isUb UNIV (range s) b" using assms(2) and abs_le_D1 unfolding isUb_def and setle_def by auto
  then obtain t where t:"isLub UNIV (range s) t" using reals_complete[of "range s" ] by auto
  { fix e::real assume "e>0" and as:"\<forall>N. \<exists>n\<ge>N. \<not> \<bar>s n - t\<bar> < e"
    { fix n::nat
      obtain N where "N\<ge>n" and n:"\<bar>s N - t\<bar> \<ge> e" using as[THEN spec[where x=n]] by auto
      have "t \<ge> s N" using isLub_isUb[OF t, unfolded isUb_def setle_def] by auto
      with n have "s N \<le> t - e" using `e>0` by auto
      hence "s n \<le> t - e" using assms(1)[THEN spec[where x=n], THEN spec[where x=N]] using `n\<le>N` by auto  }
    hence "isUb UNIV (range s) (t - e)" unfolding isUb_def and setle_def by auto
    hence False using isLub_le_isUb[OF t, of "t - e"] and `e>0` by auto  }
  thus ?thesis by blast
qed

lemma convergent_bounded_monotone: fixes s::"nat \<Rightarrow> real"
  assumes "\<forall>n. abs(s n) \<le> b" and "(\<forall>m n. m \<le> n --> s m \<le> s n) \<or> (\<forall>m n. m \<le> n --> s n \<le> s m)"
  shows "\<exists>l. \<forall>e::real>0. \<exists>N. \<forall>n\<ge>N. abs(s n - l) < e"
  using convergent_bounded_increasing[of s b] assms using convergent_bounded_increasing[of "\<lambda>n. - s n" b]
  apply auto unfolding minus_add_distrib[THEN sym, unfolded diff_minus[THEN sym]]
  unfolding abs_minus_cancel by(rule_tac x="-l" in exI)auto

lemma compact_real_lemma:
 assumes "\<forall>n::nat. abs(s n) \<le> b"
  shows "\<exists>l r. (\<forall>m n::nat. m < n --> r m < r n) \<and>
           (\<forall>e>0::real. \<exists>N. \<forall>n\<ge>N. (abs(s (r n) - l) < e))"
proof-
  obtain r where r:"\<forall>m n::nat. m < n \<longrightarrow> r m < r n"
    "(\<forall>m n. m \<le> n \<longrightarrow> s (r m) \<le> s (r n)) \<or> (\<forall>m n. m \<le> n \<longrightarrow> s (r n) \<le> s (r m))"
    using seq_monosub[of s] by (auto simp add: subseq_def monoseq_def)
  thus ?thesis using convergent_bounded_monotone[of "s o r" b] and assms by auto
qed

lemma compact_lemma:
  assumes "bounded s" and "\<forall>n. (x::nat \<Rightarrow>real^'a) n \<in> s"
  shows "\<forall>d\<in>{1.. dimindex(UNIV::'a set)}.
        \<exists>l::(real^'a). \<exists> r. (\<forall>n m::nat. m < n --> r m < r n) \<and>
        (\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>i\<in>{1..d}. \<bar>x (r n) $ i - l $ i\<bar> < e)"
proof-
  obtain b where b:"\<forall>x\<in>s. norm x \<le> b" using assms(1)[unfolded bounded_def] by auto
  { { fix i assume i:"i\<in>{1.. dimindex(UNIV::'a set)}"
      { fix n::nat
	have "\<bar>x n $ i\<bar> \<le> b" using b[THEN bspec[where x="x n"]] and component_le_norm[of i "x n"] and assms(2)[THEN spec[where x=n]] and i by auto }
      hence "\<forall>n. \<bar>x n $ i\<bar> \<le> b" by auto
    } note b' = this

    fix d assume "d\<in>{1.. dimindex(UNIV::'a set)}"
    hence "\<exists>l::(real^'a). \<exists> r. (\<forall>n m::nat. m < n --> r m < r n) \<and>
        (\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>i\<in>{1..d}. \<bar>x (r n) $ i - l $ i\<bar> < e)"
    proof(induct d) case 0 thus ?case by auto
      (* The induction really starts at Suc 0 *)
    next case (Suc d)
      show ?case proof(cases "d = 0")
	case True hence "Suc d = Suc 0" by auto
	obtain l r where r:"\<forall>m n::nat. m < n \<longrightarrow> r m < r n" and lr:"\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<bar>x (r n) $ 1 - l\<bar> < e" using b' and dimindex_ge_1[of "UNIV::'a set"]
	  using compact_real_lemma[of "\<lambda>i. (x i)$1" b] by auto
	thus ?thesis apply(rule_tac x="vec l" in exI) apply(rule_tac x=r in exI)
	  unfolding `Suc d = Suc 0` apply auto
	  unfolding vec_component[OF Suc(2)[unfolded `Suc d = Suc 0`]] by auto
      next
	case False hence d:"d \<in>{1.. dimindex(UNIV::'a set)}" using Suc(2) by auto
	obtain l1::"real^'a" and r1 where r1:"\<forall>n m::nat. m < n \<longrightarrow> r1 m < r1 n" and lr1:"\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>i\<in>{1..d}. \<bar>x (r1 n) $ i - l1 $ i\<bar> < e"
	  using Suc(1)[OF d] by auto
	obtain l2 r2 where r2:"\<forall>m n::nat. m < n \<longrightarrow> r2 m < r2 n" and lr2:"\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<bar>(x \<circ> r1) (r2 n) $ (Suc d) - l2\<bar> < e"
	  using b'[OF Suc(2)] and compact_real_lemma[of "\<lambda>i. ((x \<circ> r1) i)$(Suc d)" b] by auto
	def r \<equiv> "r1 \<circ> r2" have r:"\<forall>m n. m < n \<longrightarrow> r m < r n" unfolding r_def o_def using r1 and r2 by auto
	moreover
	def l \<equiv> "(\<chi> i. if i = Suc d then l2 else l1$i)::real^'a"
	{ fix e::real assume "e>0"
	  from lr1 obtain N1 where N1:"\<forall>n\<ge>N1. \<forall>i\<in>{1..d}. \<bar>x (r1 n) $ i - l1 $ i\<bar> < e" using `e>0` by blast
	  from lr2 obtain N2 where N2:"\<forall>n\<ge>N2. \<bar>(x \<circ> r1) (r2 n) $ (Suc d) - l2\<bar> < e" using `e>0` by blast
	  { fix n assume n:"n\<ge> N1 + N2"
	    fix i assume i:"i\<in>{1..Suc d}" hence i':"i\<in>{1.. dimindex(UNIV::'a set)}" using Suc by auto
	    hence "\<bar>x (r n) $ i - l $ i\<bar> < e"
	      using N2[THEN spec[where x="n"]] and n
 	      using N1[THEN spec[where x="r2 n"]] and n
	      using monotone_bigger[OF r] and i
	      unfolding l_def and r_def and Cart_lambda_beta'[OF i']
	      using monotone_bigger[OF r2, of n] by auto  }
	  hence "\<exists>N. \<forall>n\<ge>N. \<forall>i\<in>{1..Suc d}. \<bar>x (r n) $ i - l $ i\<bar> < e" by blast	}
	ultimately show ?thesis by auto
      qed
    qed  }
  thus ?thesis by auto
qed

lemma bounded_closed_imp_compact: fixes s::"(real^'a) set"
  assumes "bounded s" and "closed s"
  shows "compact s"
proof-
  let ?d = "dimindex (UNIV::'a set)"
  { fix f assume as:"\<forall>n::nat. f n \<in> s"
    obtain l::"real^'a" and r where r:"\<forall>n m::nat. m < n \<longrightarrow> r m < r n"
      and lr:"\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>i\<in>{1..?d}. \<bar>f (r n) $ i - l $ i\<bar> < e"
      using compact_lemma[OF assms(1) as, THEN bspec[where x="?d"]] and dimindex_ge_1[of "UNIV::'a set"] by auto
    { fix e::real assume "e>0"
      hence "0 < e / (real_of_nat ?d)" using dimindex_nonzero[of "UNIV::'a set"] using divide_pos_pos[of e, of "real_of_nat ?d"] by auto
      then obtain N::nat where N:"\<forall>n\<ge>N. \<forall>i\<in>{1..?d}. \<bar>f (r n) $ i - l $ i\<bar> < e / (real_of_nat ?d)" using lr[THEN spec[where x="e / (real_of_nat ?d)"]] by blast
      { fix n assume n:"n\<ge>N"
	have "1 \<in> {1..?d}" using dimindex_nonzero[of "UNIV::'a set"] by auto
	hence "finite {1..?d}"  "{1..?d} \<noteq> {}" by auto
	moreover
	{ fix i assume i:"i \<in> {1..?d}"
	  hence "\<bar>((f \<circ> r) n - l) $ i\<bar> < e / real_of_nat ?d" using `n\<ge>N` using N[THEN spec[where x=n]]
	    apply auto apply(erule_tac x=i in ballE) unfolding vector_minus_component[OF i] by auto  }
	ultimately have "(\<Sum>i = 1..?d. \<bar>((f \<circ> r) n - l) $ i\<bar>)
	  < (\<Sum>i = 1..?d. e / real_of_nat ?d)"
	  using setsum_strict_mono[of "{1..?d}" "\<lambda>i. \<bar>((f \<circ> r) n - l) $ i\<bar>" "\<lambda>i. e / (real_of_nat ?d)"] by auto
	hence "(\<Sum>i = 1..?d. \<bar>((f \<circ> r) n - l) $ i\<bar>) < e" unfolding setsum_constant using dimindex_nonzero[of "UNIV::'a set"] by auto
	hence "dist ((f \<circ> r) n) l < e" unfolding dist_def using norm_le_l1[of "(f \<circ> r) n - l"] by auto  }
      hence "\<exists>N. \<forall>n\<ge>N. dist ((f \<circ> r) n) l < e" by auto  }
    hence *:"((f \<circ> r) ---> l) sequentially" unfolding Lim_sequentially by auto
    moreover have "l\<in>s"
      using assms(2)[unfolded closed_sequential_limits, THEN spec[where x="f \<circ> r"], THEN spec[where x=l]] and * and as by auto
    ultimately have "\<exists>l\<in>s. \<exists>r. (\<forall>m n. m < n \<longrightarrow> r m < r n) \<and> ((f \<circ> r) ---> l) sequentially" using r by auto  }
  thus ?thesis unfolding compact_def by auto
qed

subsection{* Completeness. *}

  (* FIXME: Unify this with Cauchy from SEQ!!!!!*)

definition cauchy_def:"cauchy s \<longleftrightarrow> (\<forall>e>0. \<exists>N. \<forall>m n. m \<ge> N \<and> n \<ge> N --> dist(s m)(s n) < e)"

definition complete_def:"complete s \<longleftrightarrow> (\<forall>f::(nat=>real^'a). (\<forall>n. f n \<in> s) \<and> cauchy f
                      --> (\<exists>l \<in> s. (f ---> l) sequentially))"

lemma cauchy: "cauchy s \<longleftrightarrow> (\<forall>e>0.\<exists> N::nat. \<forall>n\<ge>N. dist(s n)(s N) < e)" (is "?lhs = ?rhs")
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
 "(s ---> l) sequentially ==> cauchy s"
proof(simp only: cauchy_def, rule, rule)
  fix e::real assume "e>0" "(s ---> l) sequentially"
  then obtain N::nat where N:"\<forall>n\<ge>N. dist (s n) l < e/2" unfolding Lim_sequentially by(erule_tac x="e/2" in allE) auto
  thus "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (s m) (s n) < e"  using dist_triangle_half_l[of _ l e _] by (rule_tac x=N in exI) auto
qed

lemma cauchy_imp_bounded: assumes "cauchy s" shows "bounded {y. (\<exists>n::nat. y = s n)}"
proof-
  from assms obtain N::nat where "\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (s m) (s n) < 1" unfolding cauchy_def apply(erule_tac x= 1 in allE) by auto
  hence N:"\<forall>n. N \<le> n \<longrightarrow> dist (s N) (s n) < 1" by auto
  { fix n::nat assume "n\<ge>N"
    hence "norm (s n) \<le> norm (s N) + 1" using N apply(erule_tac x=n in allE) unfolding dist_def
      using norm_triangle_sub[of "s N" "s n"] by (auto, metis dist_def dist_sym le_add_right_mono norm_triangle_sub real_less_def)
  }
  hence "\<forall>n\<ge>N. norm (s n) \<le> norm (s N) + 1" by auto
  moreover
  have "bounded (s ` {0..N})" using finite_imp_bounded[of "s ` {1..N}"] by auto
  then obtain a where a:"\<forall>x\<in>s ` {0..N}. norm x \<le> a" unfolding bounded_def by auto
  ultimately show "?thesis" unfolding bounded_def
    apply(rule_tac x="max a (norm (s N) + 1)" in exI) apply auto
    apply(erule_tac x=n in allE) apply(erule_tac x=n in ballE) by auto
qed

lemma compact_imp_complete: assumes "compact s" shows "complete s"
proof-
  { fix f assume as: "(\<forall>n::nat. f n \<in> s)" "cauchy f"
    from as(1) obtain l r where lr: "l\<in>s" "(\<forall>m n. m < n \<longrightarrow> r m < r n)" "((f \<circ> r) ---> l) sequentially" using assms unfolding compact_def by blast

    { fix n :: nat have lr':"n \<le> r n"
    proof (induct n)
      show "0 \<le> r 0" using lr(2) by blast
    next fix na assume "na \<le> r na" moreover have "na < Suc na \<longrightarrow> r na < r (Suc na)" using lr(2) by blast
      ultimately show "Suc na \<le> r (Suc na)" by auto
    qed } note lr' = this

    { fix e::real assume "e>0"
      from as(2) obtain N where N:"\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (f m) (f n) < e/2" unfolding cauchy_def using `e>0` apply (erule_tac x="e/2" in allE) by auto
      from lr(3)[unfolded Lim_sequentially, THEN spec[where x="e/2"]] obtain M where M:"\<forall>n\<ge>M. dist ((f \<circ> r) n) l < e/2" using `e>0` by auto
      { fix n::nat assume n:"n \<ge> max N M"
	have "dist ((f \<circ> r) n) l < e/2" using n M by auto
	moreover have "r n \<ge> N" using lr'[of n] n by auto
	hence "dist (f n) ((f \<circ> r) n) < e / 2" using N using n by auto
	ultimately have "dist (f n) l < e" using dist_triangle_half_r[of "f (r n)" "f n" e l] by (auto simp add: dist_sym)  }
      hence "\<exists>N. \<forall>n\<ge>N. dist (f n) l < e" by blast  }
    hence "\<exists>l\<in>s. (f ---> l) sequentially" using `l\<in>s` unfolding Lim_sequentially by auto  }
  thus ?thesis unfolding complete_def by auto
qed

lemma complete_univ:
 "complete UNIV"
proof(simp add: complete_def, rule, rule)
  fix f::"nat \<Rightarrow> real^'n" assume "cauchy f"
  hence "bounded (f`UNIV)" using cauchy_imp_bounded[of f] unfolding image_def by auto
  hence "compact (closure (f`UNIV))"  using bounded_closed_imp_compact[of "closure (range f)"] by auto
  hence "complete (closure (range f))" using compact_imp_complete by auto
  thus "\<exists>l. (f ---> l) sequentially" unfolding complete_def[of "closure (range f)"] using `cauchy f` unfolding closure_def  by auto
qed

lemma complete_eq_closed: "complete s \<longleftrightarrow> closed s" (is "?lhs = ?rhs")
proof
  assume ?lhs
  { fix x assume "x islimpt s"
    then obtain f where f:"\<forall>n. f n \<in> s - {x}" "(f ---> x) sequentially" unfolding islimpt_sequential by auto
    then obtain l where l: "l\<in>s" "(f ---> l) sequentially" using `?lhs`[unfolded complete_def]  using convergent_imp_cauchy[of f x] by auto
    hence "x \<in> s"  using Lim_unique[of sequentially f l x] trivial_limit_sequentially f(2) by auto  }
  thus ?rhs unfolding closed_limpt by auto
next
  assume ?rhs
  { fix f assume as:"\<forall>n::nat. f n \<in> s" "cauchy f"
    then obtain l where "(f ---> l) sequentially" using complete_univ[unfolded complete_def, THEN spec[where x=f]] by auto
    hence "\<exists>l\<in>s. (f ---> l) sequentially" using `?rhs`[unfolded closed_sequential_limits, THEN spec[where x=f], THEN spec[where x=l]] using as(1) by auto  }
  thus ?lhs unfolding complete_def by auto
qed

lemma convergent_eq_cauchy: "(\<exists>l. (s ---> l) sequentially) \<longleftrightarrow> cauchy s" (is "?lhs = ?rhs")
proof
  assume ?lhs then obtain l where "(s ---> l) sequentially" by auto
  thus ?rhs using convergent_imp_cauchy by auto
next
  assume ?rhs thus ?lhs using complete_univ[unfolded complete_def, THEN spec[where x=s]] by auto
qed

lemma convergent_imp_bounded: "(s ---> l) sequentially ==> bounded (s ` (UNIV::(nat set)))"
  using convergent_eq_cauchy[of s]
  using cauchy_imp_bounded[of s]
  unfolding image_def
  by auto

subsection{* Total boundedness. *}

fun helper_1::"((real^'n) set) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real^'n" where
  "helper_1 s e n = (SOME y::real^'n. y \<in> s \<and> (\<forall>m<n. \<not> (dist (helper_1 s e m) y < e)))"
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
  then obtain l r where "l\<in>s" and r:"\<forall>m n. m < n \<longrightarrow> r m < r n" and "((x \<circ> r) ---> l) sequentially" using assms(1)[unfolded compact_def, THEN spec[where x=x]] by auto
  from this(3) have "cauchy (x \<circ> r)" using convergent_imp_cauchy by auto
  then obtain N::nat where N:"\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist ((x \<circ> r) m) ((x \<circ> r) n) < e" unfolding cauchy_def using `e>0` by auto
  show False
    using N[THEN spec[where x=N], THEN spec[where x="N+1"]]
    using r[THEN spec[where x=N], THEN spec[where x="N+1"]]
    using x[THEN spec[where x="r (N+1)"], THEN spec[where x="r (N)"]] by auto
qed

subsection{* Heine-Borel theorem (following Burkill \& Burkill vol. 2) *}

lemma heine_borel_lemma: fixes s::"(real^'n) set"
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

  then obtain l r where l:"l\<in>s" and r:"\<forall>m n. m < n \<longrightarrow> r m < r n" and lr:"((f \<circ> r) ---> l) sequentially"
    using assms(1)[unfolded compact_def, THEN spec[where x=f]] by auto

  obtain b where "l\<in>b" "b\<in>t" using assms(2) and l by auto
  then obtain e where "e>0" and e:"\<forall>z. dist z l < e \<longrightarrow> z\<in>b"
    using assms(3)[THEN bspec[where x=b]] unfolding open_def by auto

  then obtain N1 where N1:"\<forall>n\<ge>N1. dist ((f \<circ> r) n) l < e / 2"
    using lr[unfolded Lim_sequentially, THEN spec[where x="e/2"]] by auto

  obtain N2::nat where N2:"N2>0" "inverse (real N2) < e /2" using real_arch_inv[of "e/2"] and `e>0` by auto
  have N2':"inverse (real (r (N1 + N2) +1 )) < e/2"
    apply(rule order_less_trans) apply(rule less_imp_inverse_less) using N2
    using monotone_bigger[OF r, of "N1 + N2"] by auto

  def x \<equiv> "(f (r (N1 + N2)))"
  have x:"\<not> ball x (inverse (real (r (N1 + N2) + 1))) \<subseteq> b" unfolding x_def
    using f[THEN spec[where x="r (N1 + N2)"]] using `b\<in>t` by auto
  have "\<exists>y\<in>ball x (inverse (real (r (N1 + N2) + 1))). y\<notin>b" apply(rule ccontr) using x by auto
  then obtain y where y:"y \<in> ball x (inverse (real (r (N1 + N2) + 1)))" "y \<notin> b" by auto

  have "dist x l < e/2" using N1 unfolding x_def o_def by auto
  hence "dist y l < e" using y N2' using dist_triangle[of y l x]by (auto simp add:dist_sym)

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

primrec helper_2::"(real \<Rightarrow> real^'n) \<Rightarrow> nat \<Rightarrow> real ^'n" where
  "helper_2 beyond 0 = beyond 0" |
  "helper_2 beyond (Suc n) = beyond (norm (helper_2 beyond n) + 1 )"

lemma bolzano_weierstrass_imp_bounded: fixes s::"(real^'n) set"
  assumes "\<forall>t. infinite t \<and> t \<subseteq> s --> (\<exists>x \<in> s. x islimpt t)"
  shows "bounded s"
proof(rule ccontr)
  assume "\<not> bounded s"
  then obtain beyond where "\<forall>a. beyond a \<in>s \<and> \<not> norm (beyond a) \<le> a"
    unfolding bounded_def apply simp using choice[of "\<lambda>a x. x\<in>s \<and> \<not> norm x \<le> a"] by auto
  hence beyond:"\<And>a. beyond a \<in>s" "\<And>a. norm (beyond a) > a" unfolding linorder_not_le by auto
  def x \<equiv> "helper_2 beyond"

  { fix m n ::nat assume "m<n"
    hence "norm (x m) + 1 < norm (x n)"
    proof(induct n)
      case 0 thus ?case by auto
    next
      case (Suc n)
      have *:"norm (x n) + 1 < norm (x (Suc n))" unfolding x_def and helper_2.simps
	using beyond(2)[of "norm (helper_2 beyond n) + 1"] by auto
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
      hence "1 < norm (x n) - norm (x m)" using *[of m n] by auto
      thus ?thesis unfolding dist_sym[of "x m" "x n"] unfolding dist_def using norm_triangle_sub[of "x n" "x m"] by auto
    next
      case False hence "n<m" using `m\<noteq>n` by auto
      hence "1 < norm (x m) - norm (x n)" using *[of n m] by auto
      thus ?thesis unfolding dist_sym[of "x n" "x m"] unfolding dist_def using norm_triangle_sub[of "x m" "x n"] by auto
    qed  } note ** = this
  { fix a b assume "x a = x b" "a \<noteq> b"
    hence False using **[of a b] unfolding dist_eq_0[THEN sym] by auto  }
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
  assumes "\<forall>n::nat. (f n  \<noteq> l)"  "(f ---> l) sequentially"
  shows "infinite {y::real^'a. (\<exists> n. y = f n)}"
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
  assumes "\<forall>n::nat. (f n \<noteq> l)"  "(f ---> l) sequentially"  "l' islimpt {y.  (\<exists>n. y = f n)}"
  shows "l' = l"
proof(rule ccontr)
  def e \<equiv> "dist l' l"
  assume "l' \<noteq> l" hence "e>0" unfolding dist_nz e_def by auto
  then obtain N::nat where N:"\<forall>n\<ge>N. dist (f n) l < e / 2"
    using assms(2)[unfolded Lim_sequentially, THEN spec[where x="e/2"]] by auto
  def d \<equiv> "Min (insert (e/2) ((\<lambda>n. if dist (f n) l' = 0 then e/2 else dist (f n) l') ` {0 .. N}))"
  have "d>0" using `e>0` unfolding d_def e_def using dist_pos_le[of _ l', unfolded order_le_less] by auto
  obtain k where k:"f k \<noteq> l'"  "dist (f k) l' < d" using `d>0` and assms(3)[unfolded islimpt_approachable, THEN spec[where x="d"]] by auto
  have "k\<ge>N" using k(1)[unfolded dist_nz] using k(2)[unfolded d_def]
    by force
  hence "dist l' l < e" using N[THEN spec[where x=k]] using k(2)[unfolded d_def] and dist_triangle_half_r[of "f k" l' e l] by auto
  thus False unfolding e_def by auto
qed

lemma bolzano_weierstrass_imp_closed:
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
  thus ?thesis unfolding closed_sequential_limits by auto
qed

text{* Hence express everything as an equivalence.   *}

lemma compact_eq_heine_borel: "compact s \<longleftrightarrow>
           (\<forall>f. (\<forall>t \<in> f. open t) \<and> s \<subseteq> (\<Union> f)
               --> (\<exists>f'. f' \<subseteq> f \<and> finite f' \<and> s \<subseteq> (\<Union> f')))" (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs using compact_imp_heine_borel[of s] by blast
next
  assume ?rhs
  hence "\<forall>t. infinite t \<and> t \<subseteq> s \<longrightarrow> (\<exists>x\<in>s. x islimpt t)" using heine_borel_imp_bolzano_weierstrass[of s] by blast
  thus ?lhs using bolzano_weierstrass_imp_bounded[of s] bolzano_weierstrass_imp_closed[of s] bounded_closed_imp_compact[of s] by blast
qed

lemma compact_eq_bolzano_weierstrass:
        "compact s \<longleftrightarrow> (\<forall>t. infinite t \<and> t \<subseteq> s --> (\<exists>x \<in> s. x islimpt t))" (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs unfolding compact_eq_heine_borel using heine_borel_imp_bolzano_weierstrass[of s] by auto
next
  assume ?rhs thus ?lhs using bolzano_weierstrass_imp_bounded bolzano_weierstrass_imp_closed bounded_closed_imp_compact by auto
qed

lemma compact_eq_bounded_closed:
 "compact s \<longleftrightarrow> bounded s \<and> closed s"  (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs unfolding compact_eq_bolzano_weierstrass using bolzano_weierstrass_imp_bounded bolzano_weierstrass_imp_closed by auto
next
  assume ?rhs thus ?lhs using bounded_closed_imp_compact by auto
qed

lemma compact_imp_bounded:
 "compact s ==> bounded s"
  unfolding compact_eq_bounded_closed
  by simp

lemma compact_imp_closed:
 "compact s ==> closed s"
  unfolding compact_eq_bounded_closed
  by simp

text{* In particular, some common special cases. *}

lemma compact_empty[simp]:
 "compact {}"
  unfolding compact_def
  by simp

  (* FIXME : Rename *)
lemma compact_union[intro]:
 "compact s \<Longrightarrow> compact t ==> compact (s \<union> t)"
  unfolding compact_eq_bounded_closed
  using bounded_Un[of s t]
  using closed_Un[of s t]
  by simp

lemma compact_inter[intro]:
 "compact s \<Longrightarrow> compact t ==> compact (s \<inter> t)"
  unfolding compact_eq_bounded_closed
  using bounded_Int[of s t]
  using closed_Int[of s t]
  by simp

lemma compact_inter_closed[intro]:
 "compact s \<Longrightarrow> closed t ==> compact (s \<inter> t)"
  unfolding compact_eq_bounded_closed
  using closed_Int[of s t]
  using bounded_subset[of "s \<inter> t" s]
  by blast

lemma closed_inter_compact[intro]:
 "closed s \<Longrightarrow> compact t ==> compact (s \<inter> t)"
proof-
  assume "closed s" "compact t"
  moreover
  have "s \<inter> t = t \<inter> s" by auto ultimately
  show ?thesis
    using compact_inter_closed[of t s]
    by auto
qed

lemma finite_imp_closed:
 "finite s ==> closed s"
proof-
  assume "finite s" hence "\<not>( \<exists>t. t \<subseteq> s \<and> infinite t)" using finite_subset by auto
  thus ?thesis using bolzano_weierstrass_imp_closed[of s] by auto
qed

lemma finite_imp_compact:
 "finite s ==> compact s"
  unfolding compact_eq_bounded_closed
  using finite_imp_closed finite_imp_bounded
  by blast

lemma compact_sing[simp]:
 "compact {a}"
  using finite_imp_compact[of "{a}"]
  by blast

lemma closed_sing[simp]:
 "closed {a}"
  using compact_eq_bounded_closed compact_sing[of a]
  by blast

lemma compact_cball[simp]:
 "compact(cball x e)"
  using compact_eq_bounded_closed bounded_cball closed_cball
  by blast

lemma compact_frontier_bounded[intro]:
 "bounded s ==> compact(frontier s)"
  unfolding frontier_def
  using compact_eq_bounded_closed
  by blast

lemma compact_frontier[intro]:
 "compact s ==> compact (frontier s)"
  using compact_eq_bounded_closed compact_frontier_bounded
  by blast

lemma frontier_subset_compact:
 "compact s ==> frontier s \<subseteq> s"
  using frontier_subset_closed compact_eq_bounded_closed
  by blast

lemma open_delete:
 "open s ==> open(s - {x})"
  using open_diff[of s "{x}"] closed_sing
  by blast

text{* Finite intersection property. I could make it an equivalence in fact. *}

lemma compact_imp_fip:
  assumes "compact s"  "\<forall>t \<in> f. closed t"
        "\<forall>f'. finite f' \<and> f' \<subseteq> f --> (s \<inter> (\<Inter> f') \<noteq> {})"
  shows "s \<inter> (\<Inter> f) \<noteq> {}"
proof
  assume as:"s \<inter> (\<Inter> f) = {}"
  hence "s \<subseteq> \<Union>op - UNIV ` f" by auto
  moreover have "Ball (op - UNIV ` f) open" using open_diff closed_diff using assms(2) by auto
  ultimately obtain f' where f':"f' \<subseteq> op - UNIV ` f"  "finite f'"  "s \<subseteq> \<Union>f'" using assms(1)[unfolded compact_eq_heine_borel, THEN spec[where x="(\<lambda>t. UNIV - t) ` f"]] by auto
  hence "finite (op - UNIV ` f') \<and> op - UNIV ` f' \<subseteq> f" by(auto simp add: Diff_Diff_Int)
  hence "s \<inter> \<Inter>op - UNIV ` f' \<noteq> {}" using assms(3)[THEN spec[where x="op - UNIV ` f'"]] by auto
  thus False using f'(3) unfolding subset_eq and Union_iff by blast
qed

subsection{* Bounded closed nest property (proof does not use Heine-Borel).            *}

lemma bounded_closed_nest:
  assumes "\<forall>n. closed(s n)" "\<forall>n. (s n \<noteq> {})"
  "(\<forall>m n. m \<le> n --> s n \<subseteq> s m)"  "bounded(s 0)"
  shows "\<exists> a::real^'a. \<forall>n::nat. a \<in> s(n)"
proof-
  from assms(2) obtain x where x:"\<forall>n::nat. x n \<in> s n" using choice[of "\<lambda>n x. x\<in> s n"] by auto
  from assms(4,1) have *:"compact (s 0)" using bounded_closed_imp_compact[of "s 0"] by auto

  then obtain l r where lr:"l\<in>s 0" "\<forall>m n. m < n \<longrightarrow> r m < r n" "((x \<circ> r) ---> l) sequentially"
    unfolding compact_def apply(erule_tac x=x in allE)  using x using assms(3) by blast

  { fix n::nat
    { fix e::real assume "e>0"
      with lr(3) obtain N where N:"\<forall>m\<ge>N. dist ((x \<circ> r) m) l < e" unfolding Lim_sequentially by auto
      hence "dist ((x \<circ> r) (max N n)) l < e" by auto
      moreover
      have "r (max N n) \<ge> n" using lr(2) using monotone_bigger[of r "max N n"] by auto
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
  shows "\<exists>a::real^'a. \<forall>n::nat. a \<in> s n"
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
  hence  "cauchy t" unfolding cauchy_def by auto
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
  shows "\<exists>a::real^'a. \<Inter> {t. (\<exists>n::nat. t = s n)} = {a}"
proof-
  obtain a where a:"\<forall>n. a \<in> s n" using decreasing_closed_nest[of s] using assms by auto
  { fix b assume b:"b \<in> \<Inter>{t. \<exists>n. t = s n}"
    { fix e::real assume "e>0"
      hence "dist a b < e" using assms(4 )using b using a by blast
    }
    hence "dist a b = 0" by (metis dist_eq_0 dist_nz real_less_def)
  }
  with a have "\<Inter>{t. \<exists>n. t = s n} = {a}"  unfolding dist_eq_0 by auto
  thus ?thesis by auto
qed

text{* Cauchy-type criteria for uniform convergence. *}

lemma uniformly_convergent_eq_cauchy: fixes s::"nat \<Rightarrow> 'b \<Rightarrow> real^'a" shows
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
  hence "\<forall>x. P x \<longrightarrow> cauchy (\<lambda>n. s n x)" unfolding cauchy_def apply auto by (erule_tac x=e in allE)auto
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
	using M[THEN spec[where x="N+M"]] and dist_triangle_half_l[of "s n x" "s (N+M) x" e "l x"] by (auto simp add: dist_sym)  }
    hence "\<exists>N. \<forall>n x. N \<le> n \<and> P x \<longrightarrow> dist(s n x)(l x) < e" by auto }
  thus ?lhs by auto
qed

lemma uniformly_cauchy_imp_uniformly_convergent:
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

definition "continuous net f \<longleftrightarrow> (f ---> f(netlimit net)) net"

lemma continuous_trivial_limit:
 "trivial_limit net ==> continuous net f"
  unfolding continuous_def tendsto_def eventually_def by auto

lemma continuous_within: "continuous (at x within s) f \<longleftrightarrow> (f ---> f(x)) (at x within s)"
  unfolding continuous_def
  unfolding tendsto_def
  using netlimit_within[of x s]
  unfolding eventually_def
  by (cases "trivial_limit (at x within s)") auto

lemma continuous_at: "continuous (at x) f \<longleftrightarrow> (f ---> f(x)) (at x)" using within_UNIV[of x]
  using continuous_within[of x UNIV f] by auto

lemma continuous_at_within:
  assumes "continuous (at x) f"  shows "continuous (at x within s) f"
proof(cases "x islimpt s")
  case True show ?thesis using assms unfolding continuous_def and netlimit_at
    using Lim_at_within[of f "f x" x s]
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
	apply (auto simp add: dist_sym mem_ball) apply(erule_tac x=xa in ballE) apply auto unfolding dist_refl using `e>0` by auto
    }
    hence "\<exists>d>0. f ` (ball x d \<inter> s) \<subseteq> ball (f x) e" using `d>0` unfolding subset_eq ball_def by (auto simp add: dist_sym)  }
  thus ?rhs by auto
next
  assume ?rhs thus ?lhs unfolding continuous_within Lim_within ball_def subset_eq
    apply (auto simp add: dist_sym) apply(erule_tac x=e in allE) by auto
qed

lemma continuous_at_ball: fixes f::"real^'a \<Rightarrow> real^'a"
  shows "continuous (at x) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. f ` (ball x d) \<subseteq> ball (f x) e)" (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs unfolding continuous_at Lim_at subset_eq Ball_def Bex_def image_iff mem_ball
    apply auto apply(erule_tac x=e in allE) apply auto apply(rule_tac x=d in exI) apply auto apply(erule_tac x=xa in allE) apply (auto simp add: dist_refl dist_sym dist_nz)
    unfolding dist_nz[THEN sym] by (auto simp add: dist_refl)
next
  assume ?rhs thus ?lhs unfolding continuous_at Lim_at subset_eq Ball_def Bex_def image_iff mem_ball
    apply auto apply(erule_tac x=e in allE) apply auto apply(rule_tac x=d in exI) apply auto apply(erule_tac x="f xa" in allE) by (auto simp add: dist_refl dist_sym dist_nz)
qed

text{* For setwise continuity, just start from the epsilon-delta definitions. *}

definition "continuous_on s f \<longleftrightarrow> (\<forall>x \<in> s. \<forall>e>0. \<exists>d::real>0. \<forall>x' \<in> s. dist x' x < d --> dist (f x') (f x) < e)"


definition "uniformly_continuous_on s f \<longleftrightarrow>
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
  hence "eventually (\<lambda>xa. dist (f xa) (f x) < e) (at x)" using assms unfolding continuous_at tendsto_def by auto
  then obtain d where d:"d>0" "\<forall>xa. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (f x) < e" unfolding eventually_at by auto
  { fix x' assume "\<not> 0 < dist x' x"
    hence "x=x'"
      using dist_nz[of x' x] by auto
    hence "dist (f x') (f x) < e" using dist_refl[of "f x'"] `e>0` by auto
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
      hence "dist (f x') (f x) < e" using dist_refl[of "f x'"] `e>0` d `x'\<in>s` dist_eq_0[of x' x] dist_pos_le[of x' x] as(2) by (metis dist_eq_0 dist_nz) }
    hence "\<exists>d>0. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e" using `d>0` by (auto simp add: dist_refl)
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
  { fix x::"nat \<Rightarrow> real^'a" assume x:"\<forall>n. x n \<in> s" "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (x n) a < e"
    fix e::real assume "e>0"
    from `?lhs` obtain d where "d>0" and d:"\<forall>x\<in>s. 0 < dist x a \<and> dist x a < d \<longrightarrow> dist (f x) (f a) < e" unfolding continuous_within Lim_within using `e>0` by auto
    from x(2) `d>0` obtain N where N:"\<forall>n\<ge>N. dist (x n) a < d" by auto
    hence "\<exists>N. \<forall>n\<ge>N. dist ((f \<circ> x) n) (f a) < e"
      apply(rule_tac  x=N in exI) using N d  apply auto using x(1)
      apply(erule_tac x=n in allE) apply(erule_tac x=n in allE)
      apply(erule_tac x="x n" in ballE)  apply auto unfolding dist_nz[THEN sym] apply auto unfolding dist_refl using `e>0` by auto
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
 "uniformly_continuous_on s f \<longleftrightarrow> (\<forall>x y. (\<forall>n. x n \<in> s) \<and> (\<forall>n. y n \<in> s) \<and>
                    ((\<lambda>n. x n - y n) ---> 0) sequentially
                    \<longrightarrow> ((\<lambda>n. f(x n) - f(y n)) ---> 0) sequentially)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  { fix x y assume x:"\<forall>n. x n \<in> s" and y:"\<forall>n. y n \<in> s" and xy:"((\<lambda>n. x n - y n) ---> 0) sequentially"
    { fix e::real assume "e>0"
      then obtain d where "d>0" and d:"\<forall>x\<in>s. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e"
	using `?lhs`[unfolded uniformly_continuous_on_def, THEN spec[where x=e]] by auto
      obtain N where N:"\<forall>n\<ge>N. norm (x n - y n - 0) < d" using xy[unfolded Lim_sequentially dist_def] and `d>0` by auto
      { fix n assume "n\<ge>N"
	hence "norm (f (x n) - f (y n) - 0) < e"
	  using N[THEN spec[where x=n]] using d[THEN bspec[where x="x n"], THEN bspec[where x="y n"]] using x and y
	  unfolding dist_sym and dist_def by simp  }
      hence "\<exists>N. \<forall>n\<ge>N. norm (f (x n) - f (y n) - 0) < e"  by auto  }
    hence "((\<lambda>n. f(x n) - f(y n)) ---> 0) sequentially" unfolding Lim_sequentially and dist_def by auto  }
  thus ?rhs by auto
next
  assume ?rhs
  { assume "\<not> ?lhs"
    then obtain e where "e>0" "\<forall>d>0. \<exists>x\<in>s. \<exists>x'\<in>s. dist x' x < d \<and> \<not> dist (f x') (f x) < e" unfolding uniformly_continuous_on_def by auto
    then obtain fa where fa:"\<forall>x.  0 < x \<longrightarrow> fst (fa x) \<in> s \<and> snd (fa x) \<in> s \<and> dist (fst (fa x)) (snd (fa x)) < x \<and> \<not> dist (f (fst (fa x))) (f (snd (fa x))) < e"
      using choice[of "\<lambda>d x. d>0 \<longrightarrow> fst x \<in> s \<and> snd x \<in> s \<and> dist (snd x) (fst x) < d \<and> \<not> dist (f (snd x)) (f (fst x)) < e"] unfolding Bex_def
      by (auto simp add: dist_sym)
    def x \<equiv> "\<lambda>n::nat. fst (fa (inverse (real n + 1)))"
    def y \<equiv> "\<lambda>n::nat. snd (fa (inverse (real n + 1)))"
    have xyn:"\<forall>n. x n \<in> s \<and> y n \<in> s" and xy0:"\<forall>n. dist (x n) (y n) < inverse (real n + 1)" and fxy:"\<forall>n. \<not> dist (f (x n)) (f (y n)) < e"
      unfolding x_def and y_def using fa by auto
    have *:"\<And>x y. dist (x - y) 0 = dist x y" unfolding dist_def by auto
    { fix e::real assume "e>0"
      then obtain N::nat where "N \<noteq> 0" and N:"0 < inverse (real N) \<and> inverse (real N) < e" unfolding real_arch_inv[of e]   by auto
      { fix n::nat assume "n\<ge>N"
	hence "inverse (real n + 1) < inverse (real N)" using real_of_nat_ge_zero and `N\<noteq>0` by auto
	also have "\<dots> < e" using N by auto
	finally have "inverse (real n + 1) < e" by auto
	hence "dist (x n - y n) 0 < e" unfolding * using xy0[THEN spec[where x=n]] by auto  }
      hence "\<exists>N. \<forall>n\<ge>N. dist (x n - y n) 0 < e" by auto  }
    hence "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (f (x n) - f (y n)) 0 < e" using `?rhs`[THEN spec[where x=x], THEN spec[where x=y]] and xyn unfolding Lim_sequentially by auto
    hence False unfolding * using fxy and `e>0` by auto  }
  thus ?lhs unfolding uniformly_continuous_on_def by blast
qed

text{* The usual transformation theorems. *}

lemma continuous_transform_within:
  assumes "0 < d" "x \<in> s" "\<forall>x' \<in> s. dist x' x < d --> f x' = g x'"
          "continuous (at x within s) f"
  shows "continuous (at x within s) g"
proof-
  { fix e::real assume "e>0"
    then obtain d' where d':"d'>0" "\<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d' \<longrightarrow> dist (f xa) (f x) < e" using assms(4) unfolding continuous_within Lim_within by auto
    { fix x' assume "x'\<in>s" "0 < dist x' x" "dist x' x < (min d d')"
      hence "dist (f x') (g x) < e" using assms(2,3) apply(erule_tac x=x in ballE) unfolding dist_refl using d' by auto  }
    hence "\<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < (min d d') \<longrightarrow> dist (f xa) (g x) < e" by blast
    hence "\<exists>d>0. \<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (g x) < e" using `d>0` `d'>0` by(rule_tac x="min d d'" in exI)auto  }
  hence "(f ---> g x) (at x within s)" unfolding Lim_within using assms(1) by auto
  thus ?thesis unfolding continuous_within using Lim_transform_within[of d s x f g "g x"] using assms by blast
qed

lemma continuous_transform_at:
  assumes "0 < d" "\<forall>x'. dist x' x < d --> f x' = g x'"
          "continuous (at x) f"
  shows "continuous (at x) g"
proof-
  { fix e::real assume "e>0"
    then obtain d' where d':"d'>0" "\<forall>xa. 0 < dist xa x \<and> dist xa x < d' \<longrightarrow> dist (f xa) (f x) < e" using assms(3) unfolding continuous_at Lim_at by auto
    { fix x' assume "0 < dist x' x" "dist x' x < (min d d')"
      hence "dist (f x') (g x) < e" using assms(2) apply(erule_tac x=x in allE) unfolding dist_refl using d' by auto
    }
    hence "\<forall>xa. 0 < dist xa x \<and> dist xa x < (min d d') \<longrightarrow> dist (f xa) (g x) < e" by blast
    hence "\<exists>d>0. \<forall>xa. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (g x) < e" using `d>0` `d'>0` by(rule_tac x="min d d'" in exI)auto
  }
  hence "(f ---> g x) (at x)" unfolding Lim_at using assms(1) by auto
  thus ?thesis unfolding continuous_at using Lim_transform_at[of d x f g "g x"] using assms by blast
qed

text{* Combination results for pointwise continuity. *}

lemma continuous_const: "continuous net (\<lambda>x::'a::zero_neq_one. c)"
  by(auto simp add: continuous_def Lim_const)

lemma continuous_cmul:
 "continuous net f ==> continuous net (\<lambda>x. c *s f x)"
 by(auto simp add: continuous_def Lim_cmul)

lemma continuous_neg:
 "continuous net f ==> continuous net (\<lambda>x. -(f x))"
 by(auto simp add: continuous_def Lim_neg)

lemma continuous_add:
 "continuous net f \<Longrightarrow> continuous net g
           ==> continuous net (\<lambda>x. f x + g x)"
 by(auto simp add: continuous_def Lim_add)

lemma continuous_sub:
 "continuous net f \<Longrightarrow> continuous net g
           ==> continuous net (\<lambda>x. f(x) - g(x))"
 by(auto simp add: continuous_def Lim_sub)

text{* Same thing for setwise continuity. *}

lemma continuous_on_const:
 "continuous_on s (\<lambda>x. c)"
  unfolding continuous_on_eq_continuous_within using continuous_const by blast

lemma continuous_on_cmul:
 "continuous_on s f ==>  continuous_on s (\<lambda>x. c *s (f x))"
  unfolding continuous_on_eq_continuous_within using continuous_cmul by blast

lemma continuous_on_neg:
 "continuous_on s f ==> continuous_on s (\<lambda>x. -(f x))"
  unfolding continuous_on_eq_continuous_within using continuous_neg by blast

lemma continuous_on_add:
 "continuous_on s f \<Longrightarrow> continuous_on s g
           ==> continuous_on s (\<lambda>x. f x + g x)"
  unfolding continuous_on_eq_continuous_within using continuous_add by blast

lemma continuous_on_sub:
 "continuous_on s f \<Longrightarrow> continuous_on s g
           ==> continuous_on s (\<lambda>x. f(x) - g(x))"
  unfolding continuous_on_eq_continuous_within using continuous_sub by blast

text{* Same thing for uniform continuity, using sequential formulations. *}

lemma uniformly_continuous_on_const:
 "uniformly_continuous_on s (\<lambda>x. c)"
  unfolding uniformly_continuous_on_sequentially using Lim_const[of 0] by auto

lemma uniformly_continuous_on_cmul:
  assumes "uniformly_continuous_on s f"
  shows "uniformly_continuous_on s (\<lambda>x. c *s f(x))"
proof-
  { fix x y assume "((\<lambda>n. f (x n) - f (y n)) ---> 0) sequentially"
    hence "((\<lambda>n. c *s f (x n) - c *s f (y n)) ---> 0) sequentially"
      using Lim_cmul[of "(\<lambda>n. f (x n) - f (y n))" 0 sequentially c]
      unfolding  vector_smult_rzero vector_ssub_ldistrib[of c] by auto
  }
  thus ?thesis using assms unfolding uniformly_continuous_on_sequentially by auto
qed

lemma uniformly_continuous_on_neg:
 "uniformly_continuous_on s f
         ==> uniformly_continuous_on s (\<lambda>x. -(f x))"
  using uniformly_continuous_on_cmul[of s f "-1"] unfolding pth_3 by auto

lemma uniformly_continuous_on_add:
  assumes "uniformly_continuous_on s f" "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. f(x) + g(x) ::real^'n)"
proof-
  have *:"\<And>fx fy gx gy::real^'n. fx - fy + (gx - gy) = fx + gx - (fy + gy)" by auto
  {  fix x y assume "((\<lambda>n. f (x n) - f (y n)) ---> 0) sequentially"
                    "((\<lambda>n. g (x n) - g (y n)) ---> 0) sequentially"
    hence "((\<lambda>xa. f (x xa) - f (y xa) + (g (x xa) - g (y xa))) ---> 0 + 0) sequentially"
      using Lim_add[of "\<lambda> n. f (x n) - f (y n)" 0  sequentially "\<lambda> n. g (x n) - g (y n)" 0] by auto
    hence "((\<lambda>n. f (x n) + g (x n) - (f (y n) + g (y n))) ---> 0) sequentially" unfolding Lim_sequentially and * by auto  }
  thus ?thesis using assms unfolding uniformly_continuous_on_sequentially by auto
qed

lemma uniformly_continuous_on_sub:
 "uniformly_continuous_on s f \<Longrightarrow> uniformly_continuous_on s g
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
      hence "dist (f y) (f x) < d" using d'[THEN bspec[where x=y]] by (auto simp add:dist_sym)
      hence "dist (g (f y)) (g (f x)) < e" using as(1) d[THEN bspec[where x="f y"]] unfolding dist_nz[THEN sym] using `e>0` by (auto simp add: dist_refl)   }
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

    obtain d where "d>0" and d:"\<forall>y. 0 < dist y x \<and> dist y x < d \<longrightarrow> dist (f y) (f x) < e" using `e>0` using `?lhs`[unfolded continuous_at Lim_at open_def] by auto

    have "open (ball x d)" using open_ball by auto
    moreover have "x \<in> ball x d" unfolding centre_in_ball using `d>0` by simp
    moreover
    { fix x' assume "x'\<in>ball x d" hence "f x' \<in> t"
	using e[unfolded subset_eq Ball_def mem_ball, THEN spec[where x="f x'"]]    d[THEN spec[where x=x']]
	unfolding mem_ball apply (auto simp add: dist_sym)
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
	using s(3)[THEN bspec[where x=y], unfolded mem_ball] by (auto simp add: dist_sym)  }
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
      have "\<exists>e>0. \<forall>x'\<in>s. dist x' x < e \<longrightarrow> x' \<in> {x \<in> s. f x \<in> t}" using d e unfolding dist_nz[THEN sym] by (rule_tac x=d in exI, auto simp add: dist_refl)  }
    ultimately have "openin (subtopology euclidean s) {x \<in> s. f x \<in> t}" unfolding openin_euclidean_subtopology_iff by auto  }
  thus ?rhs unfolding continuous_on Lim_within using openin by auto
next
  assume ?rhs
  { fix e::real and x assume "x\<in>s" "e>0"
    { fix xa x' assume "dist (f xa) (f x) < e" "xa \<in> s" "x' \<in> s" "dist (f xa) (f x') < e - dist (f xa) (f x)"
      hence "dist (f x') (f x) < e" using dist_triangle[of "f x'" "f x" "f xa"]
	by (auto simp add: dist_sym)  }
    hence "ball (f x) e \<inter> f ` s \<subseteq> f ` s \<and> (\<forall>xa\<in>ball (f x) e \<inter> f ` s. \<exists>ea>0. \<forall>x'\<in>f ` s. dist x' xa < ea \<longrightarrow> x' \<in> ball (f x) e \<inter> f ` s)" apply auto
      apply(rule_tac x="e - dist (f xa) (f x)" in exI) using `e>0` by (auto simp add: dist_sym)
    hence "\<forall>xa\<in>{xa \<in> s. f xa \<in> ball (f x) e \<inter> f ` s}. \<exists>ea>0. \<forall>x'\<in>s. dist x' xa < ea \<longrightarrow> x' \<in> {xa \<in> s. f xa \<in> ball (f x) e \<inter> f ` s}"
      using `?rhs`[unfolded openin_euclidean_subtopology_iff, THEN spec[where x="ball (f x) e \<inter> f ` s"]] by auto
    hence "\<exists>d>0. \<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (f x) < e" apply(erule_tac x=x in ballE) apply auto unfolding dist_refl using `e>0` `x\<in>s` by (auto simp add: dist_sym)  }
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
  thus ?thesis using open_inter[of s T, OF assms(2)] by auto
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
  assumes "continuous_on (closure s) f"  "\<forall>y \<in> s. norm(f y) \<le> b"  "x \<in> (closure s)"
  shows "norm(f x) \<le> b"
proof-
  have *:"f ` s \<subseteq> cball 0 b" using assms(2)[unfolded mem_cball_0[THEN sym]] by auto
  show ?thesis
    using image_closure_subset[OF assms(1) closed_cball[of 0 b] *] assms(3)
    unfolding subset_eq apply(erule_tac x="f x" in ballE) by (auto simp add: dist_def)
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
      apply auto unfolding dist_nz[THEN sym] by (auto simp add: dist_sym) }
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
  assumes "c \<noteq> 0"  "open s"
  shows "open((\<lambda>x. c *s x) ` s)"
proof-
  { fix x assume "x \<in> s"
    then obtain e where "e>0" and e:"\<forall>x'. dist x' x < e \<longrightarrow> x' \<in> s" using assms(2)[unfolded open_def, THEN bspec[where x=x]] by auto
    have "e * abs c > 0" using assms(1)[unfolded zero_less_abs_iff[THEN sym]] using real_mult_order[OF `e>0`] by auto
    moreover
    { fix y assume "dist y (c *s x) < e * \<bar>c\<bar>"
      hence "norm ((1 / c) *s y - x) < e" unfolding dist_def
	using norm_mul[of c "(1 / c) *s y - x", unfolded vector_ssub_ldistrib, unfolded vector_smult_assoc] assms(1)
	  mult_less_imp_less_left[of "abs c" "norm ((1 / c) *s y - x)" e, unfolded real_mult_commute[of "abs c" e]] assms(1)[unfolded zero_less_abs_iff[THEN sym]] by simp
      hence "y \<in> op *s c ` s" using rev_image_eqI[of "(1 / c) *s y" s y "op *s c"]  e[THEN spec[where x="(1 / c) *s y"]]  assms(1) unfolding dist_def vector_smult_assoc by auto  }
    ultimately have "\<exists>e>0. \<forall>x'. dist x' (c *s x) < e \<longrightarrow> x' \<in> op *s c ` s" apply(rule_tac x="e * abs c" in exI) by auto  }
  thus ?thesis unfolding open_def by auto
qed

lemma open_negations:
 "open s ==> open ((\<lambda> x. -x) ` s)" unfolding pth_3 by auto

lemma open_translation:
  assumes "open s"  shows "open((\<lambda>x. a + x) ` s)"
proof-
  { fix x have "continuous (at x) (\<lambda>x. x - a)" using continuous_sub[of "at x" "\<lambda>x. x" "\<lambda>x. a"] continuous_at_id[of x] continuous_const[of "at x" a] by auto  }
  moreover have "{x. x - a \<in> s}  = op + a ` s" apply auto unfolding image_iff apply(rule_tac x="x - a" in bexI) by auto
  ultimately show ?thesis using continuous_open_preimage_univ[of "\<lambda>x. x - a" s] using assms by auto
qed

lemma open_affinity:
  assumes "open s"  "c \<noteq> 0"
  shows "open ((\<lambda>x. a + c *s x) ` s)"
proof-
  have *:"(\<lambda>x. a + c *s x) = (\<lambda>x. a + x) \<circ> (\<lambda>x. c *s x)" unfolding o_def ..
  have "op + a ` op *s c ` s = (op + a \<circ> op *s c) ` s" by auto
  thus ?thesis using assms open_translation[of "op *s c ` s" a] unfolding * by auto
qed

lemma interior_translation: "interior ((\<lambda>x. a + x) ` s) = (\<lambda>x. a + x) ` (interior s)"
proof (rule set_ext, rule)
  fix x assume "x \<in> interior (op + a ` s)"
  then obtain e where "e>0" and e:"ball x e \<subseteq> op + a ` s" unfolding mem_interior by auto
  hence "ball (x - a) e \<subseteq> s" unfolding subset_eq Ball_def mem_ball dist_def apply auto apply(erule_tac x="a + xa" in allE) unfolding ab_group_add_class.diff_diff_eq[THEN sym] by auto
  thus "x \<in> op + a ` interior s" unfolding image_iff apply(rule_tac x="x - a" in bexI) unfolding mem_interior using `e > 0` by auto
next
  fix x assume "x \<in> op + a ` interior s"
  then obtain y e where "e>0" and e:"ball y e \<subseteq> s" and y:"x = a + y" unfolding image_iff Bex_def mem_interior by auto
  { fix z have *:"a + y - z = y + a - z" by auto
    assume "z\<in>ball x e"
    hence "z - a \<in> s" using e[unfolded subset_eq, THEN bspec[where x="z - a"]] unfolding mem_ball dist_def y ab_group_add_class.diff_diff_eq2 * by auto
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
    then obtain l r where "l\<in>s" and r:"\<forall>m n. m < n \<longrightarrow> r m < r n" and lr:"((y \<circ> r) ---> l) sequentially" using assms(2)[unfolded compact_def, THEN spec[where x=y]] by auto
    { fix e::real assume "e>0"
      then obtain d where "d>0" and d:"\<forall>x'\<in>s. dist x' l < d \<longrightarrow> dist (f x') (f l) < e" using assms(1)[unfolded continuous_on_def, THEN bspec[where x=l], OF `l\<in>s`] by auto
      then obtain N::nat where N:"\<forall>n\<ge>N. dist ((y \<circ> r) n) l < d" using lr[unfolded Lim_sequentially, THEN spec[where x=d]] by auto
      { fix n::nat assume "n\<ge>N" hence "dist ((x \<circ> r) n) (f l) < e" using N[THEN spec[where x=n]] d[THEN bspec[where x="y (r n)"]] y[THEN spec[where x="r n"]] by auto  }
      hence "\<exists>N. \<forall>n\<ge>N. dist ((x \<circ> r) n) (f l) < e" by auto  }
    hence "\<exists>l\<in>f ` s. \<exists>r. (\<forall>m n. m < n \<longrightarrow> r m < r n) \<and> ((x \<circ> r) ---> l) sequentially" unfolding Lim_sequentially using r lr `l\<in>s` by auto  }
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
	by (auto  simp add: dist_sym)
      moreover have "y\<in>ball z (d z (e / 2))" using as and `ea>0` and z[unfolded subset_eq]
	by (auto simp add: dist_sym)
      hence "dist (f z) (f y) < e / 2" using d[THEN spec[where x="e/2"]] and `e>0` and `y\<in>s` and `z\<in>s`
	by (auto  simp add: dist_sym)
      ultimately have "dist (f y) (f x) < e" using dist_triangle_half_r[of "f z" "f x" e "f y"]
	by (auto simp add: dist_sym)  }
    then have "\<exists>d>0. \<forall>x\<in>s. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e" using `ea>0` by auto  }
  thus ?thesis unfolding uniformly_continuous_on_def by auto
qed

text{* Continuity of inverse function on compact domain. *}

lemma continuous_on_inverse:
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
      using compact_continuous_image unfolding compact_eq_bounded_closed by auto
    moreover have "{x \<in> f ` s. g x \<in> t} = f ` s \<inter> f ` t" using assms(3) unfolding T(2) by auto
    ultimately have "closedin (subtopology euclidean (f ` s)) {x \<in> f ` s. g x \<in> t}"
      unfolding closedin_closed by auto  }
  thus ?thesis unfolding continuous_on_closed by auto
qed

subsection{* A uniformly convergent limit of continuous functions is continuous.       *}

lemma continuous_uniform_limit:
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
	using n(1)[THEN bspec[where x=x], OF `x\<in>s`] unfolding dist_def unfolding ab_group_add_class.ab_diff_minus by auto
      hence "dist (g y) (g x) < e" unfolding dist_def using n(1)[THEN bspec[where x=y], OF `y\<in>s`]
	unfolding norm_minus_cancel[of "f n y - g y", THEN sym] using norm_triangle_lt[of "f n y - g x" "g y - f n y" e] by (auto simp add: uminus_add_conv_diff)  }
    hence "\<exists>d>0. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (g x') (g x) < e" using `d>0` by auto  }
  thus ?thesis unfolding continuous_on_def by auto
qed

subsection{* Topological properties of linear functions.                               *}

lemma linear_lim_0: fixes f::"real^'a \<Rightarrow> real^'b"
  assumes "linear f" shows "(f ---> 0) (at (0))"
proof-
  obtain B where "B>0" and B:"\<forall>x. norm (f x) \<le> B * norm x" using linear_bounded_pos[OF assms] by auto
  { fix e::real assume "e>0"
    { fix x::"real^'a" assume "norm x < e / B"
      hence "B * norm x < e" using `B>0` using mult_strict_right_mono[of "norm x" " e / B" B] unfolding real_mult_commute by auto
      hence "norm (f x) < e" using B[THEN spec[where x=x]] `B>0` using order_le_less_trans[of "norm (f x)" "B * norm x" e] by auto   }
    moreover have "e / B > 0" using `e>0` `B>0` divide_pos_pos by auto
    ultimately have "\<exists>d>0. \<forall>x. 0 < dist x 0 \<and> dist x 0 < d \<longrightarrow> dist (f x) 0 < e" unfolding dist_def by auto  }
  thus ?thesis unfolding Lim_at by auto
qed

lemma linear_continuous_at:
  assumes "linear f"  shows "continuous (at a) f"
  unfolding continuous_at Lim_at_zero[of f "f a" a] using linear_lim_0[OF assms]
  unfolding Lim_null[of "\<lambda>x. f (a + x)"] unfolding linear_sub[OF assms, THEN sym] by auto

lemma linear_continuous_within:
 "linear f ==> continuous (at x within s) f"
  using continuous_at_imp_continuous_within[of x f s] using linear_continuous_at[of f] by auto

lemma linear_continuous_on:
 "linear f ==> continuous_on s f"
  using continuous_at_imp_continuous_on[of s f] using linear_continuous_at[of f] by auto

text{* Also bilinear functions, in composition form.                             *}

lemma bilinear_continuous_at_compose:
 "continuous (at x) f \<Longrightarrow> continuous (at x) g \<Longrightarrow> bilinear h
        ==> continuous (at x) (\<lambda>x. h (f x) (g x))"
  unfolding continuous_at using Lim_bilinear[of f "f x" "(at x)" g "g x" h] by auto

lemma bilinear_continuous_within_compose:
 "continuous (at x within s) f \<Longrightarrow> continuous (at x within s) g \<Longrightarrow> bilinear h
        ==> continuous (at x within s) (\<lambda>x. h (f x) (g x))"
  unfolding continuous_within using Lim_bilinear[of f "f x"] by auto

lemma bilinear_continuous_on_compose:
 "continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> bilinear h
             ==> continuous_on s (\<lambda>x. h (f x) (g x))"
  unfolding continuous_on_eq_continuous_within apply auto apply(erule_tac x=x in ballE) apply auto apply(erule_tac x=x in ballE) apply auto
  using bilinear_continuous_within_compose[of _ s f g h] by auto

subsection{* Topological stuff lifted from and dropped to R                            *}


lemma open_vec1:
 "open(vec1 ` s) \<longleftrightarrow>
        (\<forall>x \<in> s. \<exists>e>0. \<forall>x'. abs(x' - x) < e --> x' \<in> s)" (is "?lhs = ?rhs")
  unfolding open_def apply simp unfolding forall_vec1 dist_vec1 vec1_in_image_vec1 by simp

lemma islimpt_approachable_vec1:
 "(vec1 x) islimpt (vec1 ` s) \<longleftrightarrow>
         (\<forall>e>0.  \<exists>x'\<in> s. x' \<noteq> x \<and> abs(x' - x) < e)"
  by (auto simp add: islimpt_approachable dist_vec1 vec1_eq)

lemma closed_vec1:
 "closed (vec1 ` s) \<longleftrightarrow>
        (\<forall>x. (\<forall>e>0.  \<exists>x' \<in> s. x' \<noteq> x \<and> abs(x' - x) < e)
            --> x \<in> s)"
  unfolding closed_limpt islimpt_approachable forall_vec1 apply simp
  unfolding dist_vec1 vec1_in_image_vec1 abs_minus_commute by auto

lemma continuous_at_vec1_range:
 "continuous (at x) (vec1 o f) \<longleftrightarrow> (\<forall>e>0. \<exists>d>0.
        \<forall>x'. norm(x' - x) < d --> abs(f x' - f x) < e)"
  unfolding continuous_at unfolding Lim_at apply simp unfolding dist_vec1 unfolding dist_nz[THEN sym] unfolding dist_def apply auto
  apply(erule_tac x=e in allE) apply auto apply (rule_tac x=d in exI) apply auto apply (erule_tac x=x' in allE) apply auto
  apply(erule_tac x=e in allE) by auto

lemma continuous_on_vec1_range:
 " continuous_on s (vec1 o f) \<longleftrightarrow> (\<forall>x \<in> s. \<forall>e>0. \<exists>d>0. (\<forall>x' \<in> s. norm(x' - x) < d --> abs(f x' - f x) < e))"
  unfolding continuous_on_def apply (simp del: dist_sym) unfolding dist_vec1 unfolding dist_def ..

lemma continuous_at_vec1_norm:
 "\<forall>x. continuous (at x) (vec1 o norm)"
  unfolding continuous_at_vec1_range using real_abs_sub_norm order_le_less_trans by blast

lemma continuous_on_vec1_norm:
 "\<forall>s. continuous_on s (vec1 o norm)"
unfolding continuous_on_vec1_range norm_vec1[THEN sym] by (metis norm_vec1 order_le_less_trans real_abs_sub_norm)

lemma continuous_at_vec1_component:
  assumes "1 \<le> i" "i \<le> dimindex(UNIV::('a set))"
  shows "continuous (at (a::real^'a)) (\<lambda> x. vec1(x$i))"
proof-
  { fix e::real and x assume "0 < dist x a" "dist x a < e" "e>0"
    hence "\<bar>x $ i - a $ i\<bar> < e" using component_le_norm[of i "x - a"] vector_minus_component[of i x a] assms unfolding dist_def by auto  }
  thus ?thesis unfolding continuous_at tendsto_def eventually_at dist_vec1 by auto
qed

lemma continuous_on_vec1_component:
  assumes "i \<in> {1..dimindex (UNIV::'a set)}"  shows "continuous_on s (\<lambda> x::real^'a. vec1(x$i))"
proof-
  { fix e::real and x xa assume "x\<in>s" "e>0" "xa\<in>s" "0 < norm (xa - x) \<and> norm (xa - x) < e"
    hence "\<bar>xa $ i - x $ i\<bar> < e" using component_le_norm[of i "xa - x"] vector_minus_component[of i xa x] assms by auto  }
  thus ?thesis unfolding continuous_on Lim_within dist_vec1 unfolding dist_def by auto
qed

lemma continuous_at_vec1_infnorm:
 "continuous (at x) (vec1 o infnorm)"
  unfolding continuous_at Lim_at o_def unfolding dist_vec1 unfolding dist_def
  apply auto apply (rule_tac x=e in exI) apply auto
  using order_trans[OF real_abs_sub_infnorm infnorm_le_norm, of _ x] by (metis xt1(7))

text{* Hence some handy theorems on distance, diameter etc. of/from a set.       *}

lemma compact_attains_sup:
  assumes "compact (vec1 ` s)"  "s \<noteq> {}"
  shows "\<exists>x \<in> s. \<forall>y \<in> s. y \<le> x"
proof-
  from assms(1) have a:"bounded (vec1 ` s)" "closed (vec1 ` s)" unfolding compact_eq_bounded_closed by auto
  { fix e::real assume as: "\<forall>x\<in>s. x \<le> rsup s" "rsup s \<notin> s"  "0 < e" "\<forall>x'\<in>s. x' = rsup s \<or> \<not> rsup s - x' < e"
    have "isLub UNIV s (rsup s)" using rsup[OF assms(2)] unfolding setle_def using as(1) by auto
    moreover have "isUb UNIV s (rsup s - e)" unfolding isUb_def unfolding setle_def using as(4,2) by auto
    ultimately have False using isLub_le_isUb[of UNIV s "rsup s" "rsup s - e"] using `e>0` by auto  }
  thus ?thesis using bounded_has_rsup(1)[OF a(1) assms(2)] using a(2)[unfolded closed_vec1, THEN spec[where x="rsup s"]]
    apply(rule_tac x="rsup s" in bexI) by auto
qed

lemma compact_attains_inf:
  assumes "compact (vec1 ` s)" "s \<noteq> {}"  shows "\<exists>x \<in> s. \<forall>y \<in> s. x \<le> y"
proof-
  from assms(1) have a:"bounded (vec1 ` s)" "closed (vec1 ` s)" unfolding compact_eq_bounded_closed by auto
  { fix e::real assume as: "\<forall>x\<in>s. x \<ge> rinf s"  "rinf s \<notin> s"  "0 < e"
      "\<forall>x'\<in>s. x' = rinf s \<or> \<not> abs (x' - rinf s) < e"
    have "isGlb UNIV s (rinf s)" using rinf[OF assms(2)] unfolding setge_def using as(1) by auto
    moreover
    { fix x assume "x \<in> s"
      hence *:"abs (x - rinf s) = x - rinf s" using as(1)[THEN bspec[where x=x]] by auto
      have "rinf s + e \<le> x" using as(4)[THEN bspec[where x=x]] using as(2) `x\<in>s` unfolding * by auto }
    hence "isLb UNIV s (rinf s + e)" unfolding isLb_def and setge_def by auto
    ultimately have False using isGlb_le_isLb[of UNIV s "rinf s" "rinf s + e"] using `e>0` by auto  }
  thus ?thesis using bounded_has_rinf(1)[OF a(1) assms(2)] using a(2)[unfolded closed_vec1, THEN spec[where x="rinf s"]]
    apply(rule_tac x="rinf s" in bexI) by auto
qed

lemma continuous_attains_sup:
 "compact s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> continuous_on s (vec1 o f)
        ==> (\<exists>x \<in> s. \<forall>y \<in> s.  f y \<le> f x)"
  using compact_attains_sup[of "f ` s"]
  using compact_continuous_image[of s "vec1 \<circ> f"] unfolding image_compose by auto

lemma continuous_attains_inf:
 "compact s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> continuous_on s (vec1 o f)
        ==> (\<exists>x \<in> s. \<forall>y \<in> s. f x \<le> f y)"
  using compact_attains_inf[of "f ` s"]
  using compact_continuous_image[of s "vec1 \<circ> f"] unfolding image_compose by auto

lemma distance_attains_sup:
  assumes "compact s" "s \<noteq> {}"
  shows "\<exists>x \<in> s. \<forall>y \<in> s. dist a y \<le> dist a x"
proof-
  { fix x assume "x\<in>s" fix e::real assume "e>0"
    { fix x' assume "x'\<in>s" and as:"norm (x' - x) < e"
      hence "\<bar>norm (x' - a) - norm (x - a)\<bar> < e"
	using real_abs_sub_norm[of "x' - a" "x - a"]  by auto  }
    hence "\<exists>d>0. \<forall>x'\<in>s. norm (x' - x) < d \<longrightarrow> \<bar>dist x' a - dist x a\<bar> < e" using `e>0` unfolding dist_def by auto }
  thus ?thesis using assms
    using continuous_attains_sup[of s "\<lambda>x. dist a x"]
    unfolding continuous_on_vec1_range by (auto simp add: dist_sym)
qed

text{* For *minimal* distance, we only need closure, not compactness.            *}

lemma distance_attains_inf:
  assumes "closed s"  "s \<noteq> {}"
  shows "\<exists>x \<in> s. \<forall>y \<in> s. dist a x \<le> dist a y"
proof-
  from assms(2) obtain b where "b\<in>s" by auto
  let ?B = "cball a (dist b a) \<inter> s"
  have "b \<in> ?B" using `b\<in>s` by (simp add: dist_sym)
  hence "?B \<noteq> {}" by auto
  moreover
  { fix x assume "x\<in>?B"
    fix e::real assume "e>0"
    { fix x' assume "x'\<in>?B" and as:"norm (x' - x) < e"
      hence "\<bar>norm (x' - a) - norm (x - a)\<bar> < e"
	using real_abs_sub_norm[of "x' - a" "x - a"]  by auto  }
    hence "\<exists>d>0. \<forall>x'\<in>?B. norm (x' - x) < d \<longrightarrow> \<bar>dist x' a - dist x a\<bar> < e" using `e>0` unfolding dist_def by auto }
  hence "continuous_on (cball a (dist b a) \<inter> s) (vec1 \<circ> dist a)" unfolding continuous_on_vec1_range
    by (auto  simp add: dist_sym)
  moreover have "compact ?B" using compact_cball[of a "dist b a"] unfolding compact_eq_bounded_closed using bounded_Int and closed_Int and assms(1) by auto
  ultimately obtain x where "x\<in>cball a (dist b a) \<inter> s" "\<forall>y\<in>cball a (dist b a) \<inter> s. dist a x \<le> dist a y" using continuous_attains_inf[of ?B "dist a"] by fastsimp
  thus ?thesis by fastsimp
qed

subsection{* We can now extend limit compositions to consider the scalar multiplier.   *}

lemma Lim_mul:
  assumes "((vec1 o c) ---> vec1 d) net"  "(f ---> l) net"
  shows "((\<lambda>x. c(x) *s f x) ---> (d *s l)) net"
proof-
  have "bilinear (\<lambda>x. op *s (dest_vec1 (x::real^1)))" unfolding bilinear_def linear_def
    unfolding dest_vec1_add dest_vec1_cmul
    apply vector apply auto unfolding semiring_class.right_distrib semiring_class.left_distrib by auto
  thus ?thesis using Lim_bilinear[OF assms, of "\<lambda>x y. (dest_vec1 x) *s y"] by auto
qed

lemma Lim_vmul:
 "((vec1 o c) ---> vec1 d) net ==> ((\<lambda>x. c(x) *s v) ---> d *s v) net"
  using Lim_mul[of c d net "\<lambda>x. v" v] using Lim_const[of v] by auto

lemma continuous_vmul:
 "continuous net (vec1 o c) ==> continuous net (\<lambda>x. c(x) *s v)"
  unfolding continuous_def using Lim_vmul[of c] by auto

lemma continuous_mul:
 "continuous net (vec1 o c) \<Longrightarrow> continuous net f
             ==> continuous net (\<lambda>x. c(x) *s f x) "
  unfolding continuous_def using Lim_mul[of c] by auto

lemma continuous_on_vmul:
 "continuous_on s (vec1 o c) ==> continuous_on s (\<lambda>x. c(x) *s v)"
  unfolding continuous_on_eq_continuous_within using continuous_vmul[of _ c] by auto

lemma continuous_on_mul:
 "continuous_on s (vec1 o c) \<Longrightarrow> continuous_on s f
             ==> continuous_on s (\<lambda>x. c(x) *s f x)"
  unfolding continuous_on_eq_continuous_within using continuous_mul[of _ c] by auto

text{* And so we have continuity of inverse.                                     *}

lemma Lim_inv:
  assumes "((vec1 o f) ---> vec1 l) (net::'a net)"  "l \<noteq> 0"
  shows "((vec1 o inverse o f) ---> vec1(inverse l)) net"
proof(cases "trivial_limit net")
  case True thus ?thesis unfolding tendsto_def unfolding eventually_def by auto
next
  case False note ntriv = this
  { fix e::real assume "e>0"
    hence "0 < min (\<bar>l\<bar> / 2) (l\<twosuperior> * e / 2)" using `l\<noteq>0` mult_pos_pos[of "l^2" "e/2"] by auto
    then obtain y where y1:"\<exists>x. netord net x y" and
      y:"\<forall>x. netord net x y \<longrightarrow> dist ((vec1 \<circ> f) x) (vec1 l) < min (\<bar>l\<bar> / 2) (l\<twosuperior> * e / 2)" using ntriv
      using assms(1)[unfolded tendsto_def eventually_def, THEN spec[where x="min (abs l / 2) (l ^ 2 * e / 2)"]] by auto
    { fix x assume "netord net x y"
      hence *:"\<bar>f x - l\<bar> < min (\<bar>l\<bar> / 2) (l\<twosuperior> * e / 2)" using y[THEN spec[where x=x]] unfolding o_def dist_vec1 by auto
      hence fx0:"f x \<noteq> 0" using `l \<noteq> 0` by auto
      hence fxl0: "(f x) * l \<noteq> 0" using `l \<noteq> 0` by auto
      from * have **:"\<bar>f x - l\<bar> < l\<twosuperior> * e / 2" by auto
      have "\<bar>f x\<bar> * 2 \<ge> \<bar>l\<bar>" using * by (auto simp del: Arith_Tools.less_divide_eq_number_of1)
      hence "\<bar>f x\<bar> * 2 * \<bar>l\<bar>  \<ge> \<bar>l\<bar> * \<bar>l\<bar>" unfolding mult_le_cancel_right by auto
      hence "\<bar>f x * l\<bar> * 2  \<ge> \<bar>l\<bar>^2" unfolding real_mult_commute and power2_eq_square by auto
      hence ***:"inverse \<bar>f x * l\<bar> \<le> inverse (l\<twosuperior> / 2)" using fxl0
	using le_imp_inverse_le[of "l^2 / 2" "\<bar>f x * l\<bar>"]  by auto

      have "dist ((vec1 \<circ> inverse \<circ> f) x) (vec1 (inverse l)) < e" unfolding o_def unfolding dist_vec1
	unfolding inverse_diff_inverse[OF fx0 `l\<noteq>0`] apply simp
	unfolding mult_commute[of "inverse (f x)"]
	unfolding real_divide_def[THEN sym]
	unfolding divide_divide_eq_left
	unfolding nonzero_abs_divide[OF fxl0]
	using mult_less_le_imp_less[OF **, of "inverse \<bar>f x * l\<bar>", of "inverse (l^2 / 2)"] using *** using fx0 `l\<noteq>0`
	unfolding inverse_eq_divide using `e>0` by auto   }
    hence "(\<exists>y. (\<exists>x. netord net x y) \<and> (\<forall>x. netord net x y \<longrightarrow> dist ((vec1 \<circ> inverse \<circ> f) x) (vec1 (inverse l)) < e))"
      using y1 by auto  }
  thus ?thesis unfolding tendsto_def eventually_def by auto
qed

lemma continuous_inv:
 "continuous net (vec1 o f) \<Longrightarrow> f(netlimit net) \<noteq> 0
           ==> continuous net (vec1 o inverse o f)"
  unfolding continuous_def using Lim_inv by auto

lemma continuous_at_within_inv:
  assumes "continuous (at a within s) (vec1 o f)" "f a \<noteq> 0"
  shows "continuous (at a within s) (vec1 o inverse o f)"
proof(cases "trivial_limit (at a within s)")
  case True thus ?thesis unfolding continuous_def tendsto_def eventually_def by auto
next
  case False note cs = this
  thus ?thesis using netlimit_within[OF cs] assms(2) continuous_inv[OF assms(1)] by auto
qed

lemma continuous_at_inv:
 "continuous (at a) (vec1 o f) \<Longrightarrow> f a \<noteq> 0
         ==> continuous (at a) (vec1 o inverse o f) "
  using within_UNIV[THEN sym, of a] using continuous_at_within_inv[of a UNIV] by auto

subsection{* Preservation properties for pasted sets.                                  *}

lemma bounded_pastecart:
  assumes "bounded s" "bounded t"
  shows "bounded { pastecart x y | x y . (x \<in> s \<and> y \<in> t)}"
proof-
  obtain a b where ab:"\<forall>x\<in>s. norm x \<le> a" "\<forall>x\<in>t. norm x \<le> b" using assms[unfolded bounded_def] by auto
  { fix x y assume "x\<in>s" "y\<in>t"
    hence "norm x \<le> a" "norm y \<le> b" using ab by auto
    hence "norm (pastecart x y) \<le> a + b" using norm_pastecart[of x y] by auto }
  thus ?thesis unfolding bounded_def by auto
qed

lemma closed_pastecart:
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
 "compact s \<Longrightarrow> compact t ==> compact {pastecart x y | x y . x \<in> s \<and> y \<in> t}"
  unfolding compact_eq_bounded_closed using bounded_pastecart[of s t] closed_pastecart[of s t] by auto

text{* Hence some useful properties follow quite easily.                         *}

lemma compact_scaling:
  assumes "compact s"  shows "compact ((\<lambda>x. c *s x) ` s)"
proof-
  let ?f = "\<lambda>x. c *s x"
  have *:"linear ?f" unfolding linear_def vector_smult_assoc vector_add_ldistrib real_mult_commute by auto
  show ?thesis using compact_continuous_image[of s ?f] continuous_at_imp_continuous_on[of s ?f]
    using linear_continuous_at[OF *] assms by auto
qed

lemma compact_negations:
  assumes "compact s"  shows "compact ((\<lambda>x. -x) ` s)"
proof-
  have "uminus ` s = (\<lambda>x. -1 *s x) ` s" apply auto unfolding image_iff pth_3 by auto
  thus ?thesis using compact_scaling[OF assms, of "-1"] by auto
qed

lemma compact_sums:
  assumes "compact s"  "compact t"  shows "compact {x + y | x y. x \<in> s \<and> y \<in> t}"
proof-
  have *:"{x + y | x y. x \<in> s \<and> y \<in> t} =(\<lambda>z. fstcart z + sndcart z) ` {pastecart x y | x y.  x \<in> s \<and> y \<in> t}"
    apply auto unfolding image_iff apply(rule_tac x="pastecart xa y" in bexI) unfolding fstcart_pastecart sndcart_pastecart by auto
  have "linear (\<lambda>z::real^('a, 'a) finite_sum. fstcart z + sndcart z)" unfolding linear_def
    unfolding fstcart_add sndcart_add apply auto
    unfolding vector_add_ldistrib fstcart_cmul[THEN sym] sndcart_cmul[THEN sym] by auto
  hence "continuous_on {pastecart x y |x y. x \<in> s \<and> y \<in> t} (\<lambda>z. fstcart z + sndcart z)"
    using continuous_at_imp_continuous_on linear_continuous_at by auto
  thus ?thesis unfolding * using compact_continuous_image compact_pastecart[OF assms] by auto
qed

lemma compact_differences:
  assumes "compact s" "compact t"  shows "compact {x - y | x y. x \<in> s \<and> y \<in> t}"
proof-
  have "{x - y | x y::real^'a. x\<in>s \<and> y \<in> t} =  {x + y | x y. x \<in> s \<and> y \<in> (uminus ` t)}"
    apply auto apply(rule_tac x= xa in exI) apply auto apply(rule_tac x=xa in exI) by auto
  thus ?thesis using compact_sums[OF assms(1) compact_negations[OF assms(2)]] by auto
qed

lemma compact_translation:
  assumes "compact s"  shows "compact ((\<lambda>x. a + x) ` s)"
proof-
  have "{x + y |x y. x \<in> s \<and> y \<in> {a}} = (\<lambda>x. a + x) ` s" by auto
  thus ?thesis using compact_sums[OF assms compact_sing[of a]] by auto
qed

lemma compact_affinity:
 assumes "compact s"  shows "compact ((\<lambda>x. a + c *s x) ` s)"
proof-
  have "op + a ` op *s c ` s = (\<lambda>x. a + c *s x) ` s" by auto
  thus ?thesis using compact_translation[OF compact_scaling[OF assms], of a c] by auto
qed

text{* Hence we get the following.                                               *}

lemma compact_sup_maxdistance:
  assumes "compact s"  "s \<noteq> {}"
  shows "\<exists>x\<in>s. \<exists>y\<in>s. \<forall>u\<in>s. \<forall>v\<in>s. norm(u - v) \<le> norm(x - y)"
proof-
  have "{x - y | x y . x\<in>s \<and> y\<in>s} \<noteq> {}" using `s \<noteq> {}` by auto
  then obtain x where x:"x\<in>{x - y |x y. x \<in> s \<and> y \<in> s}"  "\<forall>y\<in>{x - y |x y. x \<in> s \<and> y \<in> s}. norm y \<le> norm x"
    using compact_differences[OF assms(1) assms(1)]
    using distance_attains_sup[unfolded dist_def, of "{x - y | x y . x\<in>s \<and> y\<in>s}" 0] by(auto simp add: norm_minus_cancel)
  from x(1) obtain a b where "a\<in>s" "b\<in>s" "x = a - b" by auto
  thus ?thesis using x(2)[unfolded `x = a - b`] by blast
qed

text{* We can state this in terms of diameter of a set.                          *}

definition "diameter s = (if s = {} then 0::real else rsup {norm(x - y) | x y. x \<in> s \<and> y \<in> s})"

lemma diameter_bounded:
  assumes "bounded s"
  shows "\<forall>x\<in>s. \<forall>y\<in>s. norm(x - y) \<le> diameter s"
        "\<forall>d>0. d < diameter s --> (\<exists>x\<in>s. \<exists>y\<in>s. norm(x - y) > d)"
proof-
  let ?D = "{norm (x - y) |x y. x \<in> s \<and> y \<in> s}"
  obtain a where a:"\<forall>x\<in>s. norm x \<le> a" using assms[unfolded bounded_def] by auto
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
  assumes "compact s"  "s \<noteq> {}"
  shows "\<exists>x\<in>s. \<exists>y\<in>s. (norm(x - y) = diameter s)"
proof-
  have b:"bounded s" using assms(1) compact_eq_bounded_closed by auto
  then obtain x y where xys:"x\<in>s" "y\<in>s" and xy:"\<forall>u\<in>s. \<forall>v\<in>s. norm (u - v) \<le> norm (x - y)" using compact_sup_maxdistance[OF assms] by auto
  hence "diameter s \<le> norm (x - y)" using rsup_le[of "{norm (x - y) |x y. x \<in> s \<and> y \<in> s}" "norm (x - y)"]
    unfolding setle_def and diameter_def by auto
  thus ?thesis using diameter_bounded(1)[OF b, THEN bspec[where x=x], THEN bspec[where x=y], OF xys] and xys by auto
qed

text{* Related results with closure as the conclusion.                           *}

lemma closed_scaling:
  assumes "closed s" shows "closed ((\<lambda>x. c *s x) ` s)"
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
    { fix x l assume as:"\<forall>n::nat. x n \<in> op *s c ` s"  "(x ---> l) sequentially"
      { fix n::nat have "(1 / c) *s x n \<in> s" using as(1)[THEN spec[where x=n]] using `c\<noteq>0` by (auto simp add: vector_smult_assoc) }
      moreover
      { fix e::real assume "e>0"
	hence "0 < e *\<bar>c\<bar>"  using `c\<noteq>0` mult_pos_pos[of e "abs c"] by auto
	then obtain N where "\<forall>n\<ge>N. dist (x n) l < e * \<bar>c\<bar>" using as(2)[unfolded Lim_sequentially, THEN spec[where x="e * abs c"]] by auto
	hence "\<exists>N. \<forall>n\<ge>N. dist ((1 / c) *s x n) ((1 / c) *s l) < e" unfolding dist_def unfolding vector_ssub_ldistrib[THEN sym] norm_mul
	  using mult_imp_div_pos_less[of "abs c" _ e] `c\<noteq>0` by auto  }
      hence "((\<lambda>n. (1 / c) *s x n) ---> (1 / c) *s l) sequentially" unfolding Lim_sequentially by auto
      ultimately have "l \<in> op *s c ` s"  using assms[unfolded closed_sequential_limits, THEN spec[where x="\<lambda>n. (1/c) *s x n"], THEN spec[where x="(1/c) *s l"]]
	unfolding image_iff using `c\<noteq>0` apply(rule_tac x="(1 / c) *s l" in bexI) apply auto unfolding vector_smult_assoc  by auto  }
    thus ?thesis unfolding closed_sequential_limits by auto
  qed
qed

lemma closed_negations:
  assumes "closed s"  shows "closed ((\<lambda>x. -x) ` s)"
  using closed_scaling[OF assms, of "-1"] unfolding  pth_3 by auto

lemma compact_closed_sums:
  assumes "compact s"  "closed t"  shows "closed {x + y | x y. x \<in> s \<and> y \<in> t}"
proof-
  let ?S = "{x + y |x y. x \<in> s \<and> y \<in> t}"
  { fix x l assume as:"\<forall>n. x n \<in> ?S"  "(x ---> l) sequentially"
    from as(1) obtain f where f:"\<forall>n. x n = fst (f n) + snd (f n)"  "\<forall>n. fst (f n) \<in> s"  "\<forall>n. snd (f n) \<in> t"
      using choice[of "\<lambda>n y. x n = (fst y) + (snd y) \<and> fst y \<in> s \<and> snd y \<in> t"] by auto
    obtain l' r where "l'\<in>s" and r:"\<forall>m n. m < n \<longrightarrow> r m < r n" and lr:"(((\<lambda>n. fst (f n)) \<circ> r) ---> l') sequentially"
      using assms(1)[unfolded compact_def, THEN spec[where x="\<lambda> n. fst (f n)"]] using f(2) by auto
    have "((\<lambda>n. snd (f (r n))) ---> l - l') sequentially"
      using Lim_sub[OF lim_subsequence[OF r as(2)] lr] and f(1) unfolding o_def by auto
    hence "l - l' \<in> t"
      using assms(2)[unfolded closed_sequential_limits, THEN spec[where x="\<lambda> n. snd (f (r n))"], THEN spec[where x="l - l'"]]
      using f(3) by auto
    hence "l \<in> ?S" using `l' \<in> s` apply auto apply(rule_tac x=l' in exI) apply(rule_tac x="l - l'" in exI) by auto
  }
  thus ?thesis unfolding closed_sequential_limits by auto
qed

lemma closed_compact_sums:
  assumes "closed s"  "compact t"
  shows "closed {x + y | x y. x \<in> s \<and> y \<in> t}"
proof-
  have "{x + y |x y. x \<in> t \<and> y \<in> s} = {x + y |x y. x \<in> s \<and> y \<in> t}" apply auto
    apply(rule_tac x=y in exI) apply auto apply(rule_tac x=y in exI) by auto
  thus ?thesis using compact_closed_sums[OF assms(2,1)] by simp
qed

lemma compact_closed_differences:
  assumes "compact s"  "closed t"
  shows "closed {x - y | x y. x \<in> s \<and> y \<in> t}"
proof-
  have "{x + y |x y. x \<in> s \<and> y \<in> uminus ` t} =  {x - y |x y. x \<in> s \<and> y \<in> t}"
    apply auto apply(rule_tac x=xa in exI) apply auto apply(rule_tac x=xa in exI) by auto
  thus ?thesis using compact_closed_sums[OF assms(1) closed_negations[OF assms(2)]] by auto
qed

lemma closed_compact_differences:
  assumes "closed s" "compact t"
  shows "closed {x - y | x y. x \<in> s \<and> y \<in> t}"
proof-
  have "{x + y |x y. x \<in> s \<and> y \<in> uminus ` t} = {x - y |x y. x \<in> s \<and> y \<in> t}"
    apply auto apply(rule_tac x=xa in exI) apply auto apply(rule_tac x=xa in exI) by auto
 thus ?thesis using closed_compact_sums[OF assms(1) compact_negations[OF assms(2)]] by simp
qed

lemma closed_translation:
  assumes "closed s"  shows "closed ((\<lambda>x. a + x) ` s)"
proof-
  have "{a + y |y. y \<in> s} = (op + a ` s)" by auto
  thus ?thesis using compact_closed_sums[OF compact_sing[of a] assms] by auto
qed

lemma translation_UNIV:
 "range (\<lambda>x::real^'a. a + x) = UNIV"
  apply (auto simp add: image_iff) apply(rule_tac x="x - a" in exI) by auto

lemma translation_diff: "(\<lambda>x::real^'a. a + x) ` (s - t) = ((\<lambda>x. a + x) ` s) - ((\<lambda>x. a + x) ` t)" by auto

lemma closure_translation:
 "closure ((\<lambda>x. a + x) ` s) = (\<lambda>x. a + x) ` (closure s)"
proof-
  have *:"op + a ` (UNIV - s) = UNIV - op + a ` s"  apply auto unfolding image_iff apply(rule_tac x="x - a" in bexI) by auto
  show ?thesis unfolding closure_interior translation_diff translation_UNIV using interior_translation[of a "UNIV - s"] unfolding * by auto
qed

lemma frontier_translation:
 "frontier((\<lambda>x. a + x) ` s) = (\<lambda>x. a + x) ` (frontier s)"
  unfolding frontier_def translation_diff interior_translation closure_translation by auto

subsection{* Separation between points and sets.                                       *}

lemma separate_point_closed:
 "closed s \<Longrightarrow> a \<notin> s  ==> (\<exists>d>0. \<forall>x\<in>s. d \<le> dist a x)"
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
  assumes "compact s" and "closed t" and "s \<inter> t = {}"
  shows "\<exists>d>0. \<forall>x\<in>s. \<forall>y\<in>t. d \<le> dist x y"
proof-
  have "0 \<notin> {x - y |x y. x \<in> s \<and> y \<in> t}" using assms(3) by auto
  then obtain d where "d>0" and d:"\<forall>x\<in>{x - y |x y. x \<in> s \<and> y \<in> t}. d \<le> dist 0 x"
    using separate_point_closed[OF compact_closed_differences[OF assms(1,2)], of 0] by auto
  { fix x y assume "x\<in>s" "y\<in>t"
    hence "x - y \<in> {x - y |x y. x \<in> s \<and> y \<in> t}" by auto
    hence "d \<le> dist (x - y) 0" using d[THEN bspec[where x="x - y"]] using dist_sym
      by (auto  simp add: dist_sym)
    hence "d \<le> dist x y" unfolding dist_def by auto  }
  thus ?thesis using `d>0` by auto
qed

lemma separate_closed_compact:
  assumes "closed s" and "compact t" and "s \<inter> t = {}"
  shows "\<exists>d>0. \<forall>x\<in>s. \<forall>y\<in>t. d \<le> dist x y"
proof-
  have *:"t \<inter> s = {}" using assms(3) by auto
  show ?thesis using separate_compact_closed[OF assms(2,1) *]
    apply auto apply(rule_tac x=d in exI) apply auto apply (erule_tac x=y in ballE)
    by (auto simp add: dist_sym)
qed

(* A cute way of denoting open and closed intervals using overloading.       *)

lemma interval: fixes a :: "'a::ord^'n" shows
  "{a <..< b} = {x::'a^'n. \<forall>i \<in> dimset a. a$i < x$i \<and> x$i < b$i}" and
  "{a .. b} = {x::'a^'n. \<forall>i \<in> dimset a. a$i \<le> x$i \<and> x$i \<le> b$i}"
  by (auto simp add: expand_set_eq vector_less_def vector_less_eq_def)

lemma mem_interval:
  "x \<in> {a<..<b} \<longleftrightarrow> (\<forall>i \<in> dimset a. a$i < x$i \<and> x$i < b$i)"
  "x \<in> {a .. b} \<longleftrightarrow> (\<forall>i \<in> dimset a. a$i \<le> x$i \<and> x$i \<le> b$i)"
  using interval[of a b]
  by(auto simp add: expand_set_eq vector_less_def vector_less_eq_def)

lemma interval_eq_empty: fixes a :: "real^'n" shows
 "({a <..< b} = {} \<longleftrightarrow> (\<exists>i \<in> dimset a. b$i \<le> a$i))" (is ?th1) and
 "({a  ..  b} = {} \<longleftrightarrow> (\<exists>i \<in> dimset a. b$i < a$i))" (is ?th2)
proof-
  { fix i x assume i:"i\<in>dimset a" and as:"b$i \<le> a$i" and x:"x\<in>{a <..< b}"
    hence "a $ i < x $ i \<and> x $ i < b $ i" unfolding mem_interval by auto
    hence "a$i < b$i" by auto
    hence False using as by auto  }
  moreover
  { assume as:"\<forall>i \<in> dimset a. \<not> (b$i \<le> a$i)"
    let ?x = "(1/2) *s (a + b)"
    { fix i assume i:"i\<in>dimset a"
      hence "a$i < b$i" using as[THEN bspec[where x=i]] by auto
      hence "a$i < ((1/2) *s (a+b)) $ i" "((1/2) *s (a+b)) $ i < b$i"
	unfolding vector_smult_component[OF i] and vector_add_component[OF i]
	by (auto simp add: Arith_Tools.less_divide_eq_number_of1)  }
    hence "{a <..< b} \<noteq> {}" using mem_interval(1)[of "?x" a b] by auto  }
  ultimately show ?th1 by blast

  { fix i x assume i:"i\<in>dimset a" and as:"b$i < a$i" and x:"x\<in>{a .. b}"
    hence "a $ i \<le> x $ i \<and> x $ i \<le> b $ i" unfolding mem_interval by auto
    hence "a$i \<le> b$i" by auto
    hence False using as by auto  }
  moreover
  { assume as:"\<forall>i \<in> dimset a. \<not> (b$i < a$i)"
    let ?x = "(1/2) *s (a + b)"
    { fix i assume i:"i\<in>dimset a"
      hence "a$i \<le> b$i" using as[THEN bspec[where x=i]] by auto
      hence "a$i \<le> ((1/2) *s (a+b)) $ i" "((1/2) *s (a+b)) $ i \<le> b$i"
	unfolding vector_smult_component[OF i] and vector_add_component[OF i]
	by (auto simp add: Arith_Tools.less_divide_eq_number_of1)  }
    hence "{a .. b} \<noteq> {}" using mem_interval(2)[of "?x" a b] by auto  }
  ultimately show ?th2 by blast
qed

lemma interval_ne_empty: fixes a :: "real^'n" shows
  "{a  ..  b} \<noteq> {} \<longleftrightarrow> (\<forall>i \<in> dimset a. a$i \<le> b$i)" and
  "{a <..< b} \<noteq> {} \<longleftrightarrow> (\<forall>i \<in> dimset a. a$i < b$i)"
  unfolding interval_eq_empty[of a b] by auto

lemma subset_interval_imp: fixes a :: "real^'n" shows
 "(\<forall>i \<in> dimset a. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> {c .. d} \<subseteq> {a .. b}" and
 "(\<forall>i \<in> dimset a. a$i < c$i \<and> d$i < b$i) \<Longrightarrow> {c .. d} \<subseteq> {a<..<b}" and
 "(\<forall>i \<in> dimset a. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> {c<..<d} \<subseteq> {a .. b}" and
 "(\<forall>i \<in> dimset a. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> {c<..<d} \<subseteq> {a<..<b}"
  unfolding subset_eq[unfolded Ball_def] unfolding mem_interval by(auto elim!: ballE)

lemma interval_sing: fixes a :: "'a::linorder^'n" shows
 "{a .. a} = {a} \<and> {a<..<a} = {}"
apply(auto simp add: expand_set_eq vector_less_def vector_less_eq_def Cart_eq)
apply (simp only: order_eq_iff)
using dimindex_ge_1[of "UNIV :: 'n set"]
apply (auto simp add: not_less )
apply (erule_tac x= 1 in ballE)
apply (rule bexI[where x=1])
apply auto
done


lemma interval_open_subset_closed:  fixes a :: "'a::preorder^'n" shows
 "{a<..<b} \<subseteq> {a .. b}"
proof(simp add: subset_eq, rule)
  fix x
  assume x:"x \<in>{a<..<b}"
  { fix i assume "i \<in> dimset a"
    hence "a $ i \<le> x $ i"
      using x order_less_imp_le[of "a$i" "x$i"]
      by(simp add: expand_set_eq vector_less_def vector_less_eq_def Cart_eq)
  }
  moreover
  { fix i assume "i \<in> dimset a"
    hence "x $ i \<le> b $ i"
      using x
      using x order_less_imp_le[of "x$i" "b$i"]
      by(simp add: expand_set_eq vector_less_def vector_less_eq_def Cart_eq)
  }
  ultimately
  show "a \<le> x \<and> x \<le> b"
    by(simp add: expand_set_eq vector_less_def vector_less_eq_def Cart_eq)
qed

lemma subset_interval: fixes a :: "real^'n" shows
 "{c .. d} \<subseteq> {a .. b} \<longleftrightarrow> (\<forall>i \<in> dimset a. c$i \<le> d$i) --> (\<forall>i \<in> dimset a. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th1) and
 "{c .. d} \<subseteq> {a<..<b} \<longleftrightarrow> (\<forall>i \<in> dimset a. c$i \<le> d$i) --> (\<forall>i \<in> dimset a. a$i < c$i \<and> d$i < b$i)" (is ?th2) and
 "{c<..<d} \<subseteq> {a .. b} \<longleftrightarrow> (\<forall>i \<in> dimset a. c$i < d$i) --> (\<forall>i \<in> dimset a. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th3) and
 "{c<..<d} \<subseteq> {a<..<b} \<longleftrightarrow> (\<forall>i \<in> dimset a. c$i < d$i) --> (\<forall>i \<in> dimset a. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th4)
proof-
  show ?th1 unfolding subset_eq and Ball_def and mem_interval apply auto by(erule_tac x=xa in allE, simp)+
  show ?th2 unfolding subset_eq and Ball_def and mem_interval apply auto by(erule_tac x=xa in allE, simp)+
  { assume as: "{c<..<d} \<subseteq> {a .. b}" "\<forall>i \<in> dimset a. c$i < d$i"
    hence "{c<..<d} \<noteq> {}" unfolding interval_eq_empty by auto
    fix i assume i:"i \<in> dimset a"
    (** TODO combine the following two parts as done in the HOL_light version. **)
    { let ?x = "(\<chi> j. (if j=i then ((min (a$j) (d$j))+c$j)/2 else (c$j+d$j)/2))::real^'n"
      assume as2: "a$i > c$i"
      { fix j assume j:"j\<in>dimset a"
	hence "c $ j < ?x $ j \<and> ?x $ j < d $ j" unfolding Cart_lambda_beta[THEN bspec[where x=j], OF j]
	  apply(cases "j=i") using as(2)[THEN bspec[where x=j], OF j]
	  by (auto simp add: Arith_Tools.less_divide_eq_number_of1 as2)  }
      hence "?x\<in>{c<..<d}" unfolding mem_interval by auto
      moreover
      have "?x\<notin>{a .. b}"
	unfolding mem_interval apply auto apply(rule_tac x=i in bexI)
	unfolding Cart_lambda_beta[THEN bspec[where x=i], OF i]
	using as(2)[THEN bspec[where x=i], OF i] and as2 and i
	by (auto simp add: Arith_Tools.less_divide_eq_number_of1)
      ultimately have False using as by auto  }
    hence "a$i \<le> c$i" by(rule ccontr)auto
    moreover
    { let ?x = "(\<chi> j. (if j=i then ((max (b$j) (c$j))+d$j)/2 else (c$j+d$j)/2))::real^'n"
      assume as2: "b$i < d$i"
      { fix j assume j:"j\<in>dimset a"
	hence "d $ j > ?x $ j \<and> ?x $ j > c $ j" unfolding Cart_lambda_beta[THEN bspec[where x=j], OF j]
	  apply(cases "j=i") using as(2)[THEN bspec[where x=j], OF j]
	  by (auto simp add: Arith_Tools.less_divide_eq_number_of1 as2)  }
      hence "?x\<in>{c<..<d}" unfolding mem_interval by auto
      moreover
      have "?x\<notin>{a .. b}"
	unfolding mem_interval apply auto apply(rule_tac x=i in bexI)
	unfolding Cart_lambda_beta[THEN bspec[where x=i], OF i]
	using as(2)[THEN bspec[where x=i], OF i] and as2 and i
	by (auto simp add: Arith_Tools.less_divide_eq_number_of1)
      ultimately have False using as by auto  }
    hence "b$i \<ge> d$i" by(rule ccontr)auto
    ultimately
    have "a$i \<le> c$i \<and> d$i \<le> b$i" by auto
  } note part1 = this
  thus ?th3 unfolding subset_eq and Ball_def and mem_interval apply auto by(erule_tac x=xa in allE, simp)+
  { assume as:"{c<..<d} \<subseteq> {a<..<b}" "\<forall>i \<in> dimset a. c$i < d$i"
    fix i assume i:"i \<in> dimset a"
    from as(1) have "{c<..<d} \<subseteq> {a..b}" using interval_open_subset_closed[of a b] by auto
    hence "a$i \<le> c$i \<and> d$i \<le> b$i" using part1 and as(2) and i by auto  } note * = this
  thus ?th4 unfolding subset_eq and Ball_def and mem_interval apply auto by(erule_tac x=xa in allE, simp)+
qed

lemma disjoint_interval: fixes a::"real^'n" shows
  "{a .. b} \<inter> {c .. d} = {} \<longleftrightarrow> (\<exists>i \<in> dimset a. (b$i < a$i \<or> d$i < c$i \<or> b$i < c$i \<or> d$i < a$i))" (is ?th1) and
  "{a .. b} \<inter> {c<..<d} = {} \<longleftrightarrow> (\<exists>i \<in> dimset a. (b$i < a$i \<or> d$i \<le> c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th2) and
  "{a<..<b} \<inter> {c .. d} = {} \<longleftrightarrow> (\<exists>i \<in> dimset a. (b$i \<le> a$i \<or> d$i < c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th3) and
  "{a<..<b} \<inter> {c<..<d} = {} \<longleftrightarrow> (\<exists>i \<in> dimset a. (b$i \<le> a$i \<or> d$i \<le> c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th4)
proof-
  let ?z = "(\<chi> i. ((max (a$i) (c$i)) + (min (b$i) (d$i))) / 2)::real^'n"
  show ?th1 ?th2 ?th3 ?th4
  unfolding expand_set_eq and Int_iff and empty_iff and mem_interval and ball_conj_distrib[THEN sym] and eq_False
  by (auto simp add: Cart_lambda_beta' Arith_Tools.less_divide_eq_number_of1 intro!: bexI elim!: allE[where x="?z"])
qed

lemma inter_interval: fixes a :: "'a::linorder^'n" shows
 "{a .. b} \<inter> {c .. d} =  {(\<chi> i. max (a$i) (c$i)) .. (\<chi> i. min (b$i) (d$i))}"
  unfolding expand_set_eq and Int_iff and mem_interval
  by (auto simp add: Cart_lambda_beta' Arith_Tools.less_divide_eq_number_of1 intro!: bexI)

(* Moved interval_open_subset_closed a bit upwards *)

lemma open_interval_lemma: fixes x :: "real" shows
 "a < x \<Longrightarrow> x < b ==> (\<exists>d>0. \<forall>x'. abs(x' - x) < d --> a < x' \<and> x' < b)"
  by(rule_tac x="min (x - a) (b - x)" in exI, auto)

lemma open_interval: fixes a :: "real^'n" shows "open {a<..<b}"
proof-
  { fix x assume x:"x\<in>{a<..<b}"
    { fix i assume "i\<in>dimset x"
      hence "\<exists>d>0. \<forall>x'. abs (x' - (x$i)) < d \<longrightarrow> a$i < x' \<and> x' < b$i"
	using x[unfolded mem_interval, THEN bspec[where x=i]]
	using open_interval_lemma[of "a$i" "x$i" "b$i"] by auto  }

    hence "\<forall>i\<in>dimset x. \<exists>d>0. \<forall>x'. abs (x' - (x$i)) < d \<longrightarrow> a$i < x' \<and> x' < b$i" by auto
    then obtain d where d:"\<forall>i\<in>dimset x. 0 < d i \<and> (\<forall>x'. \<bar>x' - x $ i\<bar> < d i \<longrightarrow> a $ i < x' \<and> x' < b $ i)"
      using bchoice[of "dimset x" "\<lambda>i d. d>0 \<and> (\<forall>x'. \<bar>x' - x $ i\<bar> < d \<longrightarrow> a $ i < x' \<and> x' < b $ i)"] by auto

    let ?d = "Min (d ` dimset x)"
    have **:"finite (d ` dimset x)" "d ` dimset x \<noteq> {}" using dimindex_ge_1[of "UNIV::'n set"] by auto
    have "?d>0" unfolding Min_gr_iff[OF **] using d by auto
    moreover
    { fix x' assume as:"dist x' x < ?d"
      { fix i assume i:"i \<in> dimset x"
	have "\<bar>x'$i - x $ i\<bar> < d i"
	  using norm_bound_component_lt[OF as[unfolded dist_def], THEN bspec[where x=i], OF i]
	  unfolding vector_minus_component[OF i] and Min_gr_iff[OF **] using i by auto
	hence "a $ i < x' $ i" "x' $ i < b $ i" using d[THEN bspec[where x=i], OF i] by auto  }
      hence "a < x' \<and> x' < b" unfolding vector_less_def by auto  }
    ultimately have "\<exists>e>0. \<forall>x'. dist x' x < e \<longrightarrow> x' \<in> {a<..<b}" by auto
  }
  thus ?thesis unfolding open_def using open_interval_lemma by auto
qed

lemma closed_interval: fixes a :: "real^'n" shows "closed {a .. b}"
proof-
  { fix x i assume i:"i\<in>dimset x" and as:"\<forall>e>0. \<exists>x'\<in>{a..b}. x' \<noteq> x \<and> dist x' x < e"(* and xab:"a$i > x$i \<or> b$i < x$i"*)
    { assume xa:"a$i > x$i"
      with as obtain y where y:"y\<in>{a..b}" "y \<noteq> x" "dist y x < a$i - x$i" by(erule_tac x="a$i - x$i" in allE)auto
      hence False unfolding mem_interval and dist_def
	using component_le_norm[OF i, of "y-x", unfolded vector_minus_component[OF i]] and i and xa by(auto elim!: ballE[where x=i])
    } hence "a$i \<le> x$i" by(rule ccontr)auto
    moreover
    { assume xb:"b$i < x$i"
      with as obtain y where y:"y\<in>{a..b}" "y \<noteq> x" "dist y x < x$i - b$i" by(erule_tac x="x$i - b$i" in allE)auto
      hence False unfolding mem_interval and dist_def
	using component_le_norm[OF i, of "y-x", unfolded vector_minus_component[OF i]] and i and xb by(auto elim!: ballE[where x=i])
    } hence "x$i \<le> b$i" by(rule ccontr)auto
    ultimately
    have "a $ i \<le> x $ i \<and> x $ i \<le> b $ i" by auto }
  thus ?thesis unfolding closed_limpt islimpt_approachable mem_interval by auto
qed

lemma interior_closed_interval: fixes a :: "real^'n" shows
 "interior {a .. b} = {a<..<b}" (is "?L = ?R")
proof(rule subset_antisym)
  show "?R \<subseteq> ?L" using interior_maximal[OF interval_open_subset_closed open_interval] by auto
next
  { fix x assume "\<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> {a..b}"
    then obtain s where s:"open s" "x \<in> s" "s \<subseteq> {a..b}" by auto
    then obtain e where "e>0" and e:"\<forall>x'. dist x' x < e \<longrightarrow> x' \<in> {a..b}" unfolding open_def and subset_eq by auto
    { fix i assume i:"i\<in>dimset x"
      have "dist (x - (e / 2) *s basis i) x < e"
	   "dist (x + (e / 2) *s basis i) x < e"
	unfolding dist_def apply auto
	unfolding norm_minus_cancel and norm_mul using norm_basis[OF i] and `e>0` by auto
      hence "a $ i \<le> (x - (e / 2) *s basis i) $ i"
                    "(x + (e / 2) *s basis i) $ i \<le> b $ i"
	using e[THEN spec[where x="x - (e/2) *s basis i"]]
	and   e[THEN spec[where x="x + (e/2) *s basis i"]]
	unfolding mem_interval using i by auto
      hence "a $ i < x $ i" and "x $ i < b $ i"
	unfolding vector_minus_component[OF i] and vector_add_component[OF i]
	unfolding vector_smult_component[OF i] and basis_component[OF i] using `e>0` by auto   }
    hence "x \<in> {a<..<b}" unfolding mem_interval by auto  }
  thus "?L \<subseteq> ?R" unfolding interior_def and subset_eq by auto
qed

lemma bounded_closed_interval: fixes a :: "real^'n" shows
 "bounded {a .. b}"
proof-
  let ?b = "\<Sum>i\<in>dimset a. \<bar>a$i\<bar> + \<bar>b$i\<bar>"
  { fix x::"real^'n" assume x:"\<forall>i\<in>dimset a. a $ i \<le> x $ i \<and> x $ i \<le> b $ i"
    { fix i assume "i\<in>dimset a"
      hence "\<bar>x$i\<bar> \<le> \<bar>a$i\<bar> + \<bar>b$i\<bar>" using x[THEN bspec[where x=i]] by auto  }
    hence "(\<Sum>i\<in>dimset a. \<bar>x $ i\<bar>) \<le> ?b" by(rule setsum_mono)auto
    hence "norm x \<le> ?b" using norm_le_l1[of x] by auto  }
  thus ?thesis unfolding interval and bounded_def by auto
qed

lemma bounded_interval: fixes a :: "real^'n" shows
 "bounded {a .. b} \<and> bounded {a<..<b}"
  using bounded_closed_interval[of a b]
  using interval_open_subset_closed[of a b]
  using bounded_subset[of "{a..b}" "{a<..<b}"]
  by simp

lemma not_interval_univ: fixes a :: "real^'n" shows
 "({a .. b} \<noteq> UNIV) \<and> ({a<..<b} \<noteq> UNIV)"
  using bounded_interval[of a b]
  by auto

lemma compact_interval: fixes a :: "real^'n" shows
 "compact {a .. b}"
  using bounded_closed_imp_compact using bounded_interval[of a b] using closed_interval[of a b] by auto

lemma open_interval_midpoint: fixes a :: "real^'n"
  assumes "{a<..<b} \<noteq> {}" shows "((1/2) *s (a + b)) \<in> {a<..<b}"
proof-
  { fix i assume i:"i\<in>dimset a"
    hence "a $ i < ((1 / 2) *s (a + b)) $ i \<and> ((1 / 2) *s (a + b)) $ i < b $ i"
      using assms[unfolded interval_ne_empty, THEN bspec[where x=i]]
      unfolding vector_smult_component[OF i] and vector_add_component[OF i]
      by(auto simp add: Arith_Tools.less_divide_eq_number_of1)  }
  thus ?thesis unfolding mem_interval by auto
qed

lemma open_closed_interval_convex: fixes x :: "real^'n"
  assumes x:"x \<in> {a<..<b}" and y:"y \<in> {a .. b}" and e:"0 < e" "e \<le> 1"
  shows "(e *s x + (1 - e) *s y) \<in> {a<..<b}"
proof-
  { fix i assume i:"i\<in>dimset a"
    have "a $ i = e * a$i + (1 - e) * a$i" unfolding left_diff_distrib by simp
    also have "\<dots> < e * x $ i + (1 - e) * y $ i" apply(rule add_less_le_mono)
      using e unfolding mult_less_cancel_left and mult_le_cancel_left apply simp_all
      using x i unfolding mem_interval  apply(erule_tac x=i in ballE) apply simp_all
      using y i unfolding mem_interval  apply(erule_tac x=i in ballE) by simp_all
    finally have "a $ i < (e *s x + (1 - e) *s y) $ i" using i by (auto simp add: vector_add_component vector_smult_component)
    moreover {
    have "b $ i = e * b$i + (1 - e) * b$i" unfolding left_diff_distrib by simp
    also have "\<dots> > e * x $ i + (1 - e) * y $ i" apply(rule add_less_le_mono)
      using e unfolding mult_less_cancel_left and mult_le_cancel_left apply simp_all
      using x i unfolding mem_interval  apply(erule_tac x=i in ballE) apply simp_all
      using y i unfolding mem_interval  apply(erule_tac x=i in ballE) by simp_all
    finally have "(e *s x + (1 - e) *s y) $ i < b $ i" using i by (auto simp add: vector_add_component vector_smult_component)
    } ultimately have "a $ i < (e *s x + (1 - e) *s y) $ i \<and> (e *s x + (1 - e) *s y) $ i < b $ i" by auto }
  thus ?thesis unfolding mem_interval by auto
qed

lemma closure_open_interval: fixes a :: "real^'n"
  assumes "{a<..<b} \<noteq> {}"
  shows "closure {a<..<b} = {a .. b}"
proof-
  have ab:"a < b" using assms[unfolded interval_ne_empty] unfolding vector_less_def by auto
  let ?c = "(1 / 2) *s (a + b)"
  { fix x assume as:"x \<in> {a .. b}"
    def f == "\<lambda>n::nat. x + (inverse (real n + 1)) *s (?c - x)"
    { fix n assume fn:"f n < b \<longrightarrow> a < f n \<longrightarrow> f n = x" and xc:"x \<noteq> ?c"
      have *:"0 < inverse (real n + 1)" "inverse (real n + 1) \<le> 1" unfolding inverse_le_1_iff by auto
      have "inverse (real n + 1) *s (1 / 2) *s (a + b) + (1 - inverse (real n + 1)) *s x =
	x + inverse (real n + 1) *s ((1 / 2) *s (a + b) - x)" by (auto simp add: vector_ssub_ldistrib vector_add_ldistrib field_simps vector_sadd_rdistrib[THEN sym])
      hence "f n < b" and "a < f n" using open_closed_interval_convex[OF open_interval_midpoint[OF assms] as *] unfolding f_def by auto
      hence False using fn unfolding f_def using xc by(auto simp add: vector_mul_lcancel vector_ssub_ldistrib)  }
    moreover
    { assume "\<not> (f ---> x) sequentially"
      { fix e::real assume "e>0"
	hence "\<exists>N::nat. inverse (real (N + 1)) < e" using real_arch_inv[of e] apply (auto simp add: Suc_pred') apply(rule_tac x="n - 1" in exI) by auto
	then obtain N::nat where "inverse (real (N + 1)) < e" by auto
	hence "\<forall>n\<ge>N. inverse (real n + 1) < e" by (auto, metis Suc_le_mono le_SucE less_imp_inverse_less nat_le_real_less order_less_trans real_of_nat_Suc real_of_nat_Suc_gt_zero)
	hence "\<exists>N::nat. \<forall>n\<ge>N. inverse (real n + 1) < e" by auto  }
      hence "((vec1 \<circ> (\<lambda>n. inverse (real n + 1))) ---> vec1 0) sequentially"
	unfolding Lim_sequentially by(auto simp add: dist_vec1)
      hence "(f ---> x) sequentially" unfolding f_def
	using Lim_add[OF Lim_const, of "\<lambda>n::nat. (inverse (real n + 1)) *s ((1 / 2) *s (a + b) - x)" 0 sequentially x]
	using Lim_vmul[of "\<lambda>n::nat. inverse (real n + 1)" 0 sequentially "((1 / 2) *s (a + b) - x)"] by auto  }
    ultimately have "x \<in> closure {a<..<b}"
      using as and open_interval_midpoint[OF assms] unfolding closure_def unfolding islimpt_sequential by(cases "x=?c")auto  }
  thus ?thesis using closure_minimal[OF interval_open_subset_closed closed_interval, of a b] by blast
qed

lemma bounded_subset_open_interval_symmetric: fixes s::"(real^'n) set"
  assumes "bounded s"  shows "\<exists>a. s \<subseteq> {-a<..<a}"
proof-
  obtain b where "b>0" and b:"\<forall>x\<in>s. norm x \<le> b" using assms[unfolded bounded_pos] by auto
  def a \<equiv> "(\<chi> i. b+1)::real^'n"
  { fix x assume "x\<in>s"
    fix i assume i:"i\<in>dimset a"
    have "(-a)$i < x$i" and "x$i < a$i" using b[THEN bspec[where x=x], OF `x\<in>s`] and component_le_norm[OF i, of x]
      unfolding vector_uminus_component[OF i] and a_def and Cart_lambda_beta'[OF i] by auto
  }
  thus ?thesis by(auto intro: exI[where x=a] simp add: vector_less_def)
qed

lemma bounded_subset_open_interval:
  "bounded s ==> (\<exists>a b. s \<subseteq> {a<..<b})"
  by(metis bounded_subset_open_interval_symmetric)

lemma bounded_subset_closed_interval_symmetric:
  assumes "bounded s" shows "\<exists>a. s \<subseteq> {-a .. a}"
proof-
  obtain a where "s \<subseteq> {- a<..<a}" using bounded_subset_open_interval_symmetric[OF assms] by auto
  thus ?thesis using interval_open_subset_closed[of "-a" a] by auto
qed

lemma bounded_subset_closed_interval:
  "bounded s ==> (\<exists>a b. s \<subseteq> {a .. b})"
  using bounded_subset_closed_interval_symmetric[of s] by auto

lemma frontier_closed_interval:
 "frontier {a .. b} = {a .. b} - {a<..<b}"
  unfolding frontier_def unfolding interior_closed_interval and closure_closed[OF closed_interval] ..

lemma frontier_open_interval:
 "frontier {a<..<b} = (if {a<..<b} = {} then {} else {a .. b} - {a<..<b})"
proof(cases "{a<..<b} = {}")
  case True thus ?thesis using frontier_empty by auto
next
  case False thus ?thesis unfolding frontier_def and closure_open_interval[OF False] and interior_open[OF open_interval] by auto
qed

lemma inter_interval_mixed_eq_empty: fixes a :: "real^'n"
  assumes "{c<..<d} \<noteq> {}"  shows "{a<..<b} \<inter> {c .. d} = {} \<longleftrightarrow> {a<..<b} \<inter> {c<..<d} = {}"
  unfolding closure_open_interval[OF assms, THEN sym] unfolding open_inter_closure_eq_empty[OF open_interval] ..


(* Some special cases for intervals in R^1.                                  *)

lemma dim1: "dimindex (UNIV::(1 set)) = 1"
unfolding dimindex_def
by simp

lemma interval_cases_1: fixes x :: "real^1" shows
 "x \<in> {a .. b} ==> x \<in> {a<..<b} \<or> (x = a) \<or> (x = b)"
  by(simp add:  Cart_eq vector_less_def vector_less_eq_def dim1, auto)

lemma in_interval_1: fixes x :: "real^1" shows
 "(x \<in> {a .. b} \<longleftrightarrow> dest_vec1 a \<le> dest_vec1 x \<and> dest_vec1 x \<le> dest_vec1 b) \<and>
  (x \<in> {a<..<b} \<longleftrightarrow> dest_vec1 a < dest_vec1 x \<and> dest_vec1 x < dest_vec1 b)"
by(simp add: Cart_eq vector_less_def vector_less_eq_def dim1 dest_vec1_def)

lemma interval_eq_empty_1: fixes a :: "real^1" shows
  "{a .. b} = {} \<longleftrightarrow> dest_vec1 b < dest_vec1 a"
  "{a<..<b} = {} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a"
  unfolding interval_eq_empty and dim1 and dest_vec1_def by auto

lemma subset_interval_1: fixes a :: "real^1" shows
 "({a .. b} \<subseteq> {c .. d} \<longleftrightarrow>  dest_vec1 b < dest_vec1 a \<or>
                dest_vec1 c \<le> dest_vec1 a \<and> dest_vec1 a \<le> dest_vec1 b \<and> dest_vec1 b \<le> dest_vec1 d)"
 "({a .. b} \<subseteq> {c<..<d} \<longleftrightarrow>  dest_vec1 b < dest_vec1 a \<or>
                dest_vec1 c < dest_vec1 a \<and> dest_vec1 a \<le> dest_vec1 b \<and> dest_vec1 b < dest_vec1 d)"
 "({a<..<b} \<subseteq> {c .. d} \<longleftrightarrow>  dest_vec1 b \<le> dest_vec1 a \<or>
                dest_vec1 c \<le> dest_vec1 a \<and> dest_vec1 a < dest_vec1 b \<and> dest_vec1 b \<le> dest_vec1 d)"
 "({a<..<b} \<subseteq> {c<..<d} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a \<or>
                dest_vec1 c \<le> dest_vec1 a \<and> dest_vec1 a < dest_vec1 b \<and> dest_vec1 b \<le> dest_vec1 d)"
  unfolding subset_interval[of a b c d] unfolding forall_dimindex_1 and dest_vec1_def by auto

lemma eq_interval_1: fixes a :: "real^1" shows
 "{a .. b} = {c .. d} \<longleftrightarrow>
          dest_vec1 b < dest_vec1 a \<and> dest_vec1 d < dest_vec1 c \<or>
          dest_vec1 a = dest_vec1 c \<and> dest_vec1 b = dest_vec1 d"
using set_eq_subset[of "{a .. b}" "{c .. d}"]
using subset_interval_1(1)[of a b c d]
using subset_interval_1(1)[of c d a b]
by auto

lemma disjoint_interval_1: fixes a :: "real^1" shows
  "{a .. b} \<inter> {c .. d} = {} \<longleftrightarrow> dest_vec1 b < dest_vec1 a \<or> dest_vec1 d < dest_vec1 c  \<or>  dest_vec1 b < dest_vec1 c \<or> dest_vec1 d < dest_vec1 a"
  "{a .. b} \<inter> {c<..<d} = {} \<longleftrightarrow> dest_vec1 b < dest_vec1 a \<or> dest_vec1 d \<le> dest_vec1 c  \<or>  dest_vec1 b \<le> dest_vec1 c \<or> dest_vec1 d \<le> dest_vec1 a"
  "{a<..<b} \<inter> {c .. d} = {} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a \<or> dest_vec1 d < dest_vec1 c  \<or>  dest_vec1 b \<le> dest_vec1 c \<or> dest_vec1 d \<le> dest_vec1 a"
  "{a<..<b} \<inter> {c<..<d} = {} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a \<or> dest_vec1 d \<le> dest_vec1 c  \<or>  dest_vec1 b \<le> dest_vec1 c \<or> dest_vec1 d \<le> dest_vec1 a"
  unfolding disjoint_interval and dest_vec1_def and dim1 by auto

lemma open_closed_interval_1: fixes a :: "real^1" shows
 "{a<..<b} = {a .. b} - {a, b}"
  unfolding expand_set_eq apply simp unfolding vector_less_def and vector_less_eq_def and dim1 and dest_vec1_eq[THEN sym] and dest_vec1_def by auto

lemma closed_open_interval_1: "dest_vec1 (a::real^1) \<le> dest_vec1 b ==> {a .. b} = {a<..<b} \<union> {a,b}"
  unfolding expand_set_eq apply simp unfolding vector_less_def and vector_less_eq_def and dim1 and dest_vec1_eq[THEN sym] and dest_vec1_def by auto

(* Some stuff for half-infinite intervals too; FIXME: notation?  *)

lemma closed_interval_left: fixes b::"real^'n"
  shows "closed {x::real^'n. \<forall>i \<in> dimset x. x$i \<le> b$i}"
proof-
  { fix i assume i:"i\<in>dimset b"
    fix x::"real^'n" assume x:"\<forall>e>0. \<exists>x'\<in>{x. \<forall>i\<in>dimset b. x $ i \<le> b $ i}. x' \<noteq> x \<and> dist x' x < e"
    { assume "x$i > b$i"
      then obtain y where "y $ i \<le> b $ i"  "y \<noteq> x"  "dist y x < x$i - b$i" using x[THEN spec[where x="x$i - b$i"]] and i by (auto, erule_tac x=i in ballE)auto
      hence False using component_le_norm[OF i, of "y - x"] unfolding dist_def and vector_minus_component[OF i] by auto   }
    hence "x$i \<le> b$i" by(rule ccontr)auto  }
  thus ?thesis unfolding closed_limpt unfolding islimpt_approachable by blast
qed

lemma closed_interval_right: fixes a::"real^'n"
  shows "closed {x::real^'n. \<forall>i \<in> dimset x. a$i \<le> x$i}"
proof-
  { fix i assume i:"i\<in>dimset a"
    fix x::"real^'n" assume x:"\<forall>e>0. \<exists>x'\<in>{x. \<forall>i\<in>dimset a. a $ i \<le> x $ i}. x' \<noteq> x \<and> dist x' x < e"
    { assume "a$i > x$i"
      then obtain y where "a $ i \<le> y $ i"  "y \<noteq> x"  "dist y x < a$i - x$i" using x[THEN spec[where x="a$i - x$i"]] and i by(auto, erule_tac x=i in ballE)auto
      hence False using component_le_norm[OF i, of "y - x"] unfolding dist_def and vector_minus_component[OF i] by auto   }
    hence "a$i \<le> x$i" by(rule ccontr)auto  }
  thus ?thesis unfolding closed_limpt unfolding islimpt_approachable by blast
qed

subsection{* Intervals in general, including infinite and mixtures of open and closed. *}

definition "is_interval s \<longleftrightarrow> (\<forall>a\<in>s. \<forall>b\<in>s. \<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> x \<in> s)"

lemma is_interval_interval: fixes a::"real^'n" shows
  "is_interval {a<..<b}" "is_interval {a .. b}"
  unfolding is_interval_def apply(auto simp add: vector_less_def vector_less_eq_def)
  apply(erule_tac x=i in ballE)+ apply simp+
  apply(erule_tac x=i in ballE)+ apply simp+
  apply(erule_tac x=i in ballE)+ apply simp+
  apply(erule_tac x=i in ballE)+ apply simp+
  done

lemma is_interval_empty:
 "is_interval {}"
  unfolding is_interval_def
  by simp

lemma is_interval_univ:
 "is_interval UNIV"
  unfolding is_interval_def
  by simp

subsection{* Closure of halfspaces and hyperplanes.                                    *}

lemma Lim_vec1_dot: fixes f :: "real^'m \<Rightarrow> real^'n"
  assumes "(f ---> l) net"  shows "((vec1 o (\<lambda>y. a \<bullet> (f y))) ---> vec1(a \<bullet> l)) net"
proof(cases "a = vec 0")
  case True thus ?thesis using dot_lzero and Lim_const[of 0 net] unfolding vec1_vec and o_def by auto
next
  case False
  { fix e::real
    assume "0 < e"  "\<forall>e>0. \<exists>y. (\<exists>x. netord net x y) \<and> (\<forall>x. netord net x y \<longrightarrow> dist l (f x) < e)"
    then obtain x y where x:"netord net x y" and y:"\<forall>x. netord net x y \<longrightarrow> dist l (f x) < e / norm a" apply(erule_tac x="e / norm a" in allE) apply auto using False using norm_ge_zero[of a] apply auto
      using divide_pos_pos[of e "norm a"] by auto
    { fix z assume "netord net z y" hence "dist l (f z) < e / norm a" using y by blast
      hence "norm a * norm (l - f z) < e" unfolding dist_def and
	pos_less_divide_eq[OF False[unfolded vec_0 zero_less_norm_iff[of a, THEN sym]]] and real_mult_commute by auto
      hence "\<bar>a \<bullet> l - a \<bullet> f z\<bar> < e" using order_le_less_trans[OF norm_cauchy_schwarz_abs[of a "l - f z"], of e] unfolding dot_rsub[symmetric] by auto  }
    hence "\<exists>y. (\<exists>x. netord net x y) \<and> (\<forall>x. netord net x y \<longrightarrow> \<bar>a \<bullet> l - a \<bullet> f x\<bar> < e)" using x by auto  }
  thus ?thesis using assms unfolding Lim apply (auto simp add: dist_sym)
    unfolding dist_vec1 by auto
qed

lemma continuous_at_vec1_dot:
 "continuous (at x) (vec1 o (\<lambda>y. a \<bullet> y))"
proof-
  have "((\<lambda>x. x) ---> x) (at x)" unfolding Lim_at by auto
  thus ?thesis unfolding continuous_at and o_def using Lim_vec1_dot[of "\<lambda>x. x" x "at x" a] by auto
qed

lemma continuous_on_vec1_dot:
 "continuous_on s (vec1 o (\<lambda>y. a \<bullet> y)) "
  using continuous_at_imp_continuous_on[of s "vec1 o (\<lambda>y. a \<bullet> y)"]
  using continuous_at_vec1_dot
  by auto

lemma closed_halfspace_le: fixes a::"real^'n"
  shows "closed {x. a \<bullet> x \<le> b}"
proof-
  have *:"{x \<in> UNIV. (vec1 \<circ> op \<bullet> a) x \<in> vec1 ` {r. \<exists>x. a \<bullet> x = r \<and> r \<le> b}} = {x. a \<bullet> x \<le> b}" by auto
  let ?T = "{x::real^1. (\<forall>i\<in>dimset x. x$i \<le> (vec1 b)$i)}"
  have "closed ?T" using closed_interval_left[of "vec1 b"] by simp
  moreover have "vec1 ` {r. \<exists>x. a \<bullet> x = r \<and> r \<le> b} = range (vec1 \<circ> op \<bullet> a) \<inter> ?T" unfolding dim1
    unfolding image_def apply auto unfolding vec1_component[unfolded One_nat_def] by auto
  ultimately have "\<exists>T. closed T \<and> vec1 ` {r. \<exists>x. a \<bullet> x = r \<and> r \<le> b} = range (vec1 \<circ> op \<bullet> a) \<inter> T" by auto
  hence "closedin euclidean {x \<in> UNIV. (vec1 \<circ> op \<bullet> a) x \<in> vec1 ` {r. \<exists>x. a \<bullet> x = r \<and> r \<le> b}}"
    using continuous_on_vec1_dot[of UNIV a, unfolded continuous_on_closed subtopology_UNIV] unfolding closedin_closed
    by (auto elim!: allE[where x="vec1 ` {r. (\<exists>x. a \<bullet> x = r \<and> r \<le> b)}"])
  thus ?thesis unfolding closed_closedin[THEN sym] and * by auto
qed

lemma closed_halfspace_ge: "closed {x. a \<bullet> x \<ge> b}"
  using closed_halfspace_le[of "-a" "-b"] unfolding dot_lneg by auto

lemma closed_hyperplane: "closed {x. a \<bullet> x = b}"
proof-
  have "{x. a \<bullet> x = b} = {x. a \<bullet> x \<ge> b} \<inter> {x. a \<bullet> x \<le> b}" by auto
  thus ?thesis using closed_halfspace_le[of a b] and closed_halfspace_ge[of b a] using closed_Int by auto
qed

lemma closed_halfspace_component_le:
  assumes "i \<in> {1 .. dimindex (UNIV::'n set)}" shows "closed {x::real^'n. x$i \<le> a}"
  using closed_halfspace_le[of "(basis i)::real^'n" a] unfolding dot_basis[OF assms] by auto

lemma closed_halfspace_component_ge:
  assumes "i \<in> {1 .. dimindex (UNIV::'n set)}" shows "closed {x::real^'n. x$i \<ge> a}"
  using closed_halfspace_ge[of a "(basis i)::real^'n"] unfolding dot_basis[OF assms] by auto

text{* Openness of halfspaces.                                                   *}

lemma open_halfspace_lt: "open {x. a \<bullet> x < b}"
proof-
  have "UNIV - {x. b \<le> a \<bullet> x} = {x. a \<bullet> x < b}" by auto
  thus ?thesis using closed_halfspace_ge[unfolded closed_def, of b a] by auto
qed

lemma open_halfspace_gt: "open {x. a \<bullet> x > b}"
proof-
  have "UNIV - {x. b \<ge> a \<bullet> x} = {x. a \<bullet> x > b}" by auto
  thus ?thesis using closed_halfspace_le[unfolded closed_def, of a b] by auto
qed

lemma open_halfspace_component_lt:
  assumes "i \<in> {1 .. dimindex(UNIV::'n set)}" shows "open {x::real^'n. x$i < a}"
  using open_halfspace_lt[of "(basis i)::real^'n" a] unfolding dot_basis[OF assms] by auto

lemma open_halfspace_component_gt:
  assumes "i \<in> {1 .. dimindex(UNIV::'n set)}" shows "open {x::real^'n. x$i  > a}"
  using open_halfspace_gt[of a "(basis i)::real^'n"] unfolding dot_basis[OF assms] by auto

text{* This gives a simple derivation of limit component bounds.                 *}

lemma Lim_component_le: fixes f :: "'a \<Rightarrow> real^'n"
  assumes "(f ---> l) net" "\<not> (trivial_limit net)"  "eventually (\<lambda>x. f(x)$i \<le> b) net"
  and i:"i\<in> {1 .. dimindex(UNIV::'n set)}"
  shows "l$i \<le> b"
proof-
  { fix x have "x \<in> {x::real^'n. basis i \<bullet> x \<le> b} \<longleftrightarrow> x$i \<le> b" unfolding dot_basis[OF i] by auto } note * = this
  show ?thesis using Lim_in_closed_set[of "{x. basis i \<bullet> x \<le> b}" f net l] unfolding *
    using closed_halfspace_le[of "(basis i)::real^'n" b] and assms(1,2,3) by auto
qed

lemma Lim_component_ge: fixes f :: "'a \<Rightarrow> real^'n"
  assumes "(f ---> l) net"  "\<not> (trivial_limit net)"  "eventually (\<lambda>x. b \<le> (f x)$i) net"
  and i:"i\<in> {1 .. dimindex(UNIV::'n set)}"
  shows "b \<le> l$i"
proof-
  { fix x have "x \<in> {x::real^'n. basis i \<bullet> x \<ge> b} \<longleftrightarrow> x$i \<ge> b" unfolding dot_basis[OF i] by auto } note * = this
  show ?thesis using Lim_in_closed_set[of "{x. basis i \<bullet> x \<ge> b}" f net l] unfolding *
    using closed_halfspace_ge[of b "(basis i)::real^'n"] and assms(1,2,3) by auto
qed

lemma Lim_component_eq: fixes f :: "'a \<Rightarrow> real^'n"
  assumes net:"(f ---> l) net" "~(trivial_limit net)" and ev:"eventually (\<lambda>x. f(x)$i = b) net"
  and i:"i\<in> {1 .. dimindex(UNIV::'n set)}"
  shows "l$i = b"
  using ev[unfolded order_eq_iff eventually_and] using Lim_component_ge[OF net, of b i] and Lim_component_le[OF net, of i b] using i by auto

lemma Lim_drop_le: fixes f :: "'a \<Rightarrow> real^1" shows
  "(f ---> l) net \<Longrightarrow> ~(trivial_limit net) \<Longrightarrow> eventually (\<lambda>x. dest_vec1 (f x) \<le> b) net ==> dest_vec1 l \<le> b"
  using Lim_component_le[of f l net 1 b] unfolding dest_vec1_def and dim1 by auto

lemma Lim_drop_ge: fixes f :: "'a \<Rightarrow> real^1" shows
 "(f ---> l) net \<Longrightarrow> ~(trivial_limit net) \<Longrightarrow> eventually (\<lambda>x. b \<le> dest_vec1 (f x)) net ==> b \<le> dest_vec1 l"
  using Lim_component_ge[of f l net b 1] unfolding dest_vec1_def and dim1 by auto

text{* Limits relative to a union.                                               *}

lemma Lim_within_union:
 "(f ---> l) (at x within (s \<union> t)) \<longleftrightarrow>
  (f ---> l) (at x within s) \<and> (f ---> l) (at x within t)"
  unfolding Lim_within apply auto apply blast apply blast
    apply(erule_tac x=e in allE)+ apply auto
    apply(rule_tac x="min d da" in exI) by auto

lemma continuous_on_union:
  assumes "closed s" "closed t" "continuous_on s f" "continuous_on t f"
  shows "continuous_on (s \<union> t) f"
  using assms unfolding continuous_on unfolding Lim_within_union
  unfolding Lim unfolding trivial_limit_within unfolding closed_limpt by auto

lemma continuous_on_cases: fixes g :: "real^'m \<Rightarrow> real ^'n"
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

lemma connected_ivt_hyperplane: fixes y :: "real^'n"
  assumes "connected s" "x \<in> s" "y \<in> s" "a \<bullet> x \<le> b" "b \<le> a \<bullet> y"
  shows "\<exists>z \<in> s. a \<bullet> z = b"
proof(rule ccontr)
  assume as:"\<not> (\<exists>z\<in>s. a \<bullet> z = b)"
  let ?A = "{x::real^'n. a \<bullet> x < b}"
  let ?B = "{x::real^'n. a \<bullet> x > b}"
  have "open ?A" "open ?B" using open_halfspace_lt and open_halfspace_gt by auto
  moreover have "?A \<inter> ?B = {}" by auto
  moreover have "s \<subseteq> ?A \<union> ?B" using as by auto
  ultimately show False using assms(1)[unfolded connected_def not_ex, THEN spec[where x="?A"], THEN spec[where x="?B"]] and assms(2-5) by auto
qed

lemma connected_ivt_component: fixes x::"real^'n" shows
 "connected s \<Longrightarrow> x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> k \<in> dimset x \<Longrightarrow> x$k \<le> a \<Longrightarrow> a \<le> y$k \<Longrightarrow> (\<exists>z\<in>s.  z$k = a)"
  using connected_ivt_hyperplane[of s x y "(basis k)::real^'n" a] by (auto simp add: dot_basis)

text{* Also more convenient formulations of monotone convergence.                *}

lemma bounded_increasing_convergent: fixes s::"nat \<Rightarrow> real^1"
  assumes "bounded {s n| n::nat. True}"  "\<forall>n. dest_vec1(s n) \<le> dest_vec1(s(Suc n))"
  shows "\<exists>l. (s ---> l) sequentially"
proof-
  obtain a where a:"\<forall>n. \<bar>dest_vec1 (s n)\<bar> \<le>  a" using assms(1)[unfolded bounded_def abs_dest_vec1] by auto
  { fix m::nat
    have "\<And> n. n\<ge>m \<longrightarrow> dest_vec1 (s m) \<le> dest_vec1 (s n)"
      apply(induct_tac n) apply simp using assms(2) apply(erule_tac x="na" in allE) by(auto simp add: not_less_eq_eq)  }
  hence "\<forall>m n. m \<le> n \<longrightarrow> dest_vec1 (s m) \<le> dest_vec1 (s n)" by auto
  then obtain l where "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<bar>dest_vec1 (s n) - l\<bar> < e" using convergent_bounded_monotone[OF a] by auto
  thus ?thesis unfolding Lim_sequentially apply(rule_tac x="vec1 l" in exI)
    unfolding dist_def unfolding abs_dest_vec1 and dest_vec1_sub by auto
qed

subsection{* Basic homeomorphism definitions.                                          *}

definition "homeomorphism s t f g \<equiv>
     (\<forall>x\<in>s. (g(f x) = x)) \<and> (f ` s = t) \<and> continuous_on s f \<and>
     (\<forall>y\<in>t. (f(g y) = y)) \<and> (g ` t = s) \<and> continuous_on t g"

definition homeomorphic :: "((real^'a) set) \<Rightarrow> ((real^'b) set) \<Rightarrow> bool" (infixr "homeomorphic" 60) where
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
  assumes "c \<noteq> 0"  shows "s homeomorphic ((\<lambda>x. c *s x) ` s)"
  unfolding homeomorphic_minimal
  apply(rule_tac x="\<lambda>x. c *s x" in exI)
  apply(rule_tac x="\<lambda>x. (1 / c) *s x" in exI)
  apply auto unfolding vector_smult_assoc using assms apply auto
  using continuous_on_cmul[OF continuous_on_id] by auto

lemma homeomorphic_translation:
 "s homeomorphic ((\<lambda>x. a + x) ` s)"
  unfolding homeomorphic_minimal
  apply(rule_tac x="\<lambda>x. a + x" in exI)
  apply(rule_tac x="\<lambda>x. -a + x" in exI)
  using continuous_on_add[OF continuous_on_const continuous_on_id] by auto

lemma homeomorphic_affinity:
  assumes "c \<noteq> 0"  shows "s homeomorphic ((\<lambda>x. a + c *s x) ` s)"
proof-
  have *:"op + a ` op *s c ` s = (\<lambda>x. a + c *s x) ` s" by auto
  show ?thesis
    using homeomorphic_trans
    using homeomorphic_scaling[OF assms, of s]
    using homeomorphic_translation[of "(\<lambda>x. c *s x) ` s" a] unfolding * by auto
qed

lemma homeomorphic_balls: fixes a b ::"real^'a"
  assumes "0 < d"  "0 < e"
  shows "(ball a d) homeomorphic  (ball b e)" (is ?th)
        "(cball a d) homeomorphic (cball b e)" (is ?cth)
proof-
  have *:"\<bar>e / d\<bar> > 0" "\<bar>d / e\<bar> >0" using assms using divide_pos_pos by auto
  show ?th unfolding homeomorphic_minimal
    apply(rule_tac x="\<lambda>x. b + (e/d) *s (x - a)" in exI)
    apply(rule_tac x="\<lambda>x. a + (d/e) *s (x - b)" in exI)
    apply (auto simp add: dist_sym) unfolding dist_def and vector_smult_assoc using assms apply auto
    unfolding norm_minus_cancel and norm_mul
    using continuous_on_add[OF continuous_on_const continuous_on_cmul[OF continuous_on_sub[OF continuous_on_id continuous_on_const]]]
    apply (auto simp add: dist_sym)
    using pos_less_divide_eq[OF *(1), THEN sym] unfolding real_mult_commute[of _ "\<bar>e / d\<bar>"]
    using pos_less_divide_eq[OF *(2), THEN sym] unfolding real_mult_commute[of _ "\<bar>d / e\<bar>"]
    by (auto simp add: dist_sym)
next
  have *:"\<bar>e / d\<bar> > 0" "\<bar>d / e\<bar> >0" using assms using divide_pos_pos by auto
  show ?cth unfolding homeomorphic_minimal
    apply(rule_tac x="\<lambda>x. b + (e/d) *s (x - a)" in exI)
    apply(rule_tac x="\<lambda>x. a + (d/e) *s (x - b)" in exI)
    apply (auto simp add: dist_sym) unfolding dist_def and vector_smult_assoc using assms apply auto
    unfolding norm_minus_cancel and norm_mul
    using continuous_on_add[OF continuous_on_const continuous_on_cmul[OF continuous_on_sub[OF continuous_on_id continuous_on_const]]]
    apply auto
    using pos_le_divide_eq[OF *(1), THEN sym] unfolding real_mult_commute[of _ "\<bar>e / d\<bar>"]
    using pos_le_divide_eq[OF *(2), THEN sym] unfolding real_mult_commute[of _ "\<bar>d / e\<bar>"]
    by auto
qed

text{* "Isometry" (up to constant bounds) of injective linear map etc.           *}

lemma cauchy_isometric:
  assumes e:"0 < e" and s:"subspace s" and f:"linear f" and normf:"\<forall>x\<in>s. norm(f x) \<ge> e * norm(x)" and xs:"\<forall>n::nat. x n \<in> s" and cf:"cauchy(f o x)"
  shows "cauchy x"
proof-
  { fix d::real assume "d>0"
    then obtain N where N:"\<forall>n\<ge>N. norm (f (x n) - f (x N)) < e * d"
      using cf[unfolded cauchy o_def dist_def, THEN spec[where x="e*d"]] and e and mult_pos_pos[of e d] by auto
    { fix n assume "n\<ge>N"
      hence "norm (f (x n - x N)) < e * d" using N[THEN spec[where x=n]] unfolding linear_sub[OF f, THEN sym] by auto
      moreover have "e * norm (x n - x N) \<le> norm (f (x n - x N))"
	using subspace_sub[OF s, of "x n" "x N"] using xs[THEN spec[where x=N]] and xs[THEN spec[where x=n]]
	using normf[THEN bspec[where x="x n - x N"]] by auto
      ultimately have "norm (x n - x N) < d" using `e>0`
	using mult_left_less_imp_less[of e "norm (x n - x N)" d] by auto   }
    hence "\<exists>N. \<forall>n\<ge>N. norm (x n - x N) < d" by auto }
  thus ?thesis unfolding cauchy and dist_def by auto
qed

lemma complete_isometric_image:
  assumes "0 < e" and s:"subspace s" and f:"linear f" and normf:"\<forall>x\<in>s. norm(f x) \<ge> e * norm(x)" and cs:"complete s"
  shows "complete(f ` s)"
proof-
  { fix g assume as:"\<forall>n::nat. g n \<in> f ` s" and cfg:"cauchy g"
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

lemma dist_0_norm:"dist 0 x = norm x" unfolding dist_def by(auto simp add: norm_minus_cancel)

lemma injective_imp_isometric: fixes f::"real^'m \<Rightarrow> real^'n"
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

  have "?S'' = frontier(cball 0 (norm a))" unfolding frontier_cball and dist_def by (auto simp add: norm_minus_cancel)
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
      have "\<forall>c. \<forall>x\<in>s. c *s x \<in> s" using s[unfolded subspace_def] by auto
      hence "(norm a / norm x) *s x \<in> {x \<in> s. norm x = norm a}" using `x\<in>s` and `x\<noteq>0` by auto
      thus "norm (f b) / norm b * norm x \<le> norm (f x)" using b[THEN bspec[where x="(norm a / norm x) *s x"]]
	unfolding linear_cmul[OF f(1)] and norm_mul and ba using `x\<noteq>0` `a\<noteq>0`
	by (auto simp add: real_mult_commute pos_le_divide_eq pos_divide_le_eq)
    qed }
  ultimately
  show ?thesis by auto
qed

lemma closed_injective_image_subspace:
  assumes "subspace s" "linear f" "\<forall>x\<in>s. f x = 0 --> x = 0" "closed s"
  shows "closed(f ` s)"
proof-
  obtain e where "e>0" and e:"\<forall>x\<in>s. e * norm x \<le> norm (f x)" using injective_imp_isometric[OF assms(4,1,2,3)] by auto
  show ?thesis using complete_isometric_image[OF `e>0` assms(1,2) e] and assms(4)
    unfolding complete_eq_closed[THEN sym] by auto
qed

subsection{* Some properties of a canonical subspace.                                  *}

lemma subspace_substandard:
 "subspace {x::real^'n. (\<forall>i \<in> dimset x. d < i \<longrightarrow> x$i = 0)}"
  unfolding subspace_def by(auto simp add: vector_add_component vector_smult_component elim!: ballE)

lemma closed_substandard:
 "closed {x::real^'n. \<forall>i \<in> dimset x. d < i --> x$i = 0}" (is "closed ?A")
proof-
  let ?D = "{Suc d..dimindex(UNIV::('n set))}"
  let ?Bs = "{{x::real^'n. basis i \<bullet> x = 0}| i. i \<in> ?D}"
  { fix x
    { assume "x\<in>?A"
      hence x:"\<forall>i\<in>?D. d < i \<longrightarrow> x $ i = 0" by auto
      hence "x\<in> \<Inter> ?Bs" by(auto simp add: dot_basis x) }
    moreover
    { assume x:"x\<in>\<Inter>?Bs"
      { fix i assume i:"i\<in>dimset x" and "d < i"
	hence "i \<in> ?D" by auto
	then obtain B where BB:"B \<in> ?Bs" and B:"B = {x::real^'n. basis i \<bullet> x = 0}" by auto
	hence "x $ i = 0" unfolding B unfolding dot_basis[OF i] using x by auto  }
      hence "x\<in>?A" by auto }
    ultimately have "x\<in>?A \<longleftrightarrow> x\<in> \<Inter>?Bs" by auto }
  hence "?A = \<Inter> ?Bs" by auto
  thus ?thesis by(auto simp add: closed_Inter closed_hyperplane)
qed

lemma dim_substandard:
  assumes "d \<le> dimindex(UNIV::'n set)"
  shows "dim {x::real^'n. \<forall>i \<in> dimset x. d < i --> x$i = 0} = d" (is "dim ?A = d")
proof-
  let ?D = "{1..dimindex (UNIV::'n set)}"
  let ?B = "(basis::nat\<Rightarrow>real^'n) ` {1..d}"

    let ?bas = "basis::nat \<Rightarrow> real^'n"

  have "?B \<subseteq> ?A" by (auto simp add: basis_component)

  moreover
  { fix x::"real^'n" assume "x\<in>?A"
    hence "x\<in> span ?B"
    proof(induct d arbitrary: x)
      case 0 hence "x=0" unfolding Cart_eq by auto
      thus ?case using subspace_0[OF subspace_span[of "{}"]] by auto
    next
      case (Suc n)
      hence *:"\<forall>i\<in>?D. Suc n < i \<longrightarrow> x $ i = 0" by auto
      have **:"{1..n} \<subseteq> {1..Suc n}" by auto
      def y \<equiv> "x - x$(Suc n) *s basis (Suc n)"
      have y:"x = y + (x$Suc n) *s basis (Suc n)" unfolding y_def by auto
      { fix i assume i:"i\<in>?D" and i':"n < i"
	hence "y $ i = 0" unfolding y_def unfolding vector_minus_component[OF i]
	  and vector_smult_component[OF i] and basis_component[OF i] using i'
	  using *[THEN bspec[where x=i]] by auto }
      hence "y \<in> span (basis ` {1..Suc n})" using Suc(1)[of y]
	using span_mono[of "?bas ` {1..n}" "?bas ` {1..Suc n}"]
	using image_mono[OF **, of basis] by auto
      moreover
      have "basis (Suc n) \<in> span (?bas ` {1..Suc n})" by(rule span_superset, auto)
      hence "x$(Suc n) *s basis (Suc n) \<in> span (?bas ` {1..Suc n})" using span_mul by auto
      ultimately
      have "y + x$(Suc n) *s basis (Suc n) \<in> span (?bas ` {1..Suc n})"
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
  have "{1..d} \<subseteq> ?D" unfolding subset_eq using assms by auto
  hence *:"inj_on (basis::nat\<Rightarrow>real^'n) {1..d}" using subset_inj_on[OF basis_inj, of "{1..d}"] using assms by auto
  have "?B hassize d" unfolding hassize_def and card_image[OF *] by auto

  ultimately show ?thesis using dim_unique[of "basis ` {1..d}" ?A] by auto
qed

text{* Hence closure and completeness of all subspaces.                          *}

lemma closed_subspace: fixes s::"(real^'n) set"
  assumes "subspace s" shows "closed s"
proof-
  let ?t = "{x::real^'n. \<forall>i\<in>{1..dimindex (UNIV :: 'n set)}. dim s<i \<longrightarrow> x$i = 0}"
  have "dim s \<le> dimindex (UNIV :: 'n set)" using dim_subset_univ by auto
  obtain f where f:"linear f"  "f ` ?t = s" "inj_on f ?t"
    using subspace_isomorphism[OF subspace_substandard[of "dim s"] assms]
    using dim_substandard[OF  dim_subset_univ[of s]] by auto
  have "\<forall>x\<in>?t. f x = 0 \<longrightarrow> x = 0" using linear_0[OF f(1)] using f(3)[unfolded inj_on_def]
    by(erule_tac x=0 in ballE) auto
  moreover have "closed ?t" using closed_substandard by auto
  moreover have "subspace ?t" using subspace_substandard by auto
  ultimately show ?thesis using closed_injective_image_subspace[of ?t f]
    unfolding f(2) using f(1) by auto
qed

lemma complete_subspace:
  "subspace s ==> complete s"
  using complete_eq_closed closed_subspace
  by auto

lemma dim_closure:
 "dim(closure s) = dim s" (is "?dc = ?d")
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
  shows "(\<lambda>x. m *s x + c) ` {a .. b} =
            (if {a .. b} = {} then {}
            else (if 0 \<le> m then {m *s a + c .. m *s b + c}
            else {m *s b + c .. m *s a + c}))"
proof(cases "m=0")
  { fix x assume "x \<le> c" "c \<le> x"
    hence "x=c" unfolding vector_less_eq_def and Cart_eq by(auto elim!: ballE)  }
  moreover case True
  moreover have "c \<in> {m *s a + c..m *s b + c}" unfolding True by(auto simp add: vector_less_eq_def)
  ultimately show ?thesis by auto
next
  case False
  { fix y assume "a \<le> y" "y \<le> b" "m > 0"
    hence "m *s a + c \<le> m *s y + c"  "m *s y + c \<le> m *s b + c"
      unfolding vector_less_eq_def by(auto simp add: vector_smult_component vector_add_component)
  } moreover
  { fix y assume "a \<le> y" "y \<le> b" "m < 0"
    hence "m *s b + c \<le> m *s y + c"  "m *s y + c \<le> m *s a + c"
      unfolding vector_less_eq_def by(auto simp add: vector_smult_component vector_add_component mult_left_mono_neg elim!:ballE)
  } moreover
  { fix y assume "m > 0"  "m *s a + c \<le> y"  "y \<le> m *s b + c"
    hence "y \<in> (\<lambda>x. m *s x + c) ` {a..b}"
      unfolding image_iff Bex_def mem_interval vector_less_eq_def
      apply(auto simp add: vector_smult_component vector_add_component vector_minus_component vector_smult_assoc pth_3[symmetric]
	intro!: exI[where x="(1 / m) *s (y - c)"])
      by(auto elim!: ballE simp add: pos_le_divide_eq pos_divide_le_eq real_mult_commute)
  } moreover
  { fix y assume "m *s b + c \<le> y" "y \<le> m *s a + c" "m < 0"
    hence "y \<in> (\<lambda>x. m *s x + c) ` {a..b}"
      unfolding image_iff Bex_def mem_interval vector_less_eq_def
      apply(auto simp add: vector_smult_component vector_add_component vector_minus_component vector_smult_assoc pth_3[symmetric]
	intro!: exI[where x="(1 / m) *s (y - c)"])
      by(auto elim!: ballE simp add: neg_le_divide_eq neg_divide_le_eq real_mult_commute)
  }
  ultimately show ?thesis using False by auto
qed

subsection{* Banach fixed point theorem (not really topological...)                    *}

lemma banach_fix:
  assumes s:"complete s" "s \<noteq> {}" and c:"0 \<le> c" "c < 1" and f:"(f ` s) \<subseteq> s" and
          lipschitz:"\<forall>x\<in>s. \<forall>y\<in>s. dist (f x) (f y) \<le> c * dist x y"
  shows "\<exists>! x\<in>s. (f x = x)"
proof-
  have "1 - c > 0" using c by auto

  from s(2) obtain z0 where "z0 \<in> s" by auto
  def z \<equiv> "\<lambda> n::nat. fun_pow n f z0"
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
	using c by (auto simp add: ring_simps dist_pos_le)
      finally show ?case by auto
    qed
  } note cf_z2 = this
  { fix e::real assume "e>0"
    hence "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (z m) (z n) < e"
    proof(cases "d = 0")
      case True
      hence "\<And>n. z n = z0" using cf_z2[of 0] and c unfolding z_def by (auto simp add: pos_prod_le[OF `1 - c > 0`] dist_le_0)
      thus ?thesis using `e>0` by auto
    next
      case False hence "d>0" unfolding d_def using dist_pos_le[of "z 0" "z 1"]
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
	  by (auto simp add: real_mult_commute dist_sym)
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
	  case False thus ?thesis using as and *[of n m] *[of m n] unfolding nat_neq_iff by (auto simp add: dist_sym)
	qed }
      thus ?thesis by auto
    qed
  }
  hence "cauchy z" unfolding cauchy_def by auto
  then obtain x where "x\<in>s" and x:"(z ---> x) sequentially" using s(1)[unfolded compact_def complete_def, THEN spec[where x=z]] and z_in_s by auto

  def e \<equiv> "dist (f x) x"
  have "e = 0" proof(rule ccontr)
    assume "e \<noteq> 0" hence "e>0" unfolding e_def using dist_pos_le[of "f x" x]
      by (metis dist_eq_0 dist_nz dist_sym e_def)
    then obtain N where N:"\<forall>n\<ge>N. dist (z n) x < e / 2"
      using x[unfolded Lim_sequentially, THEN spec[where x="e/2"]] by auto
    hence N':"dist (z N) x < e / 2" by auto

    have *:"c * dist (z N) x \<le> dist (z N) x" unfolding mult_le_cancel_right2
      using dist_pos_le[of "z N" x] and c
      by (metis dist_eq_0 dist_nz dist_sym order_less_asym real_less_def)
    have "dist (f (z N)) (f x) \<le> c * dist (z N) x" using lipschitz[THEN bspec[where x="z N"], THEN bspec[where x=x]]
      using z_in_s[of N] `x\<in>s` using c by auto
    also have "\<dots> < e / 2" using N' and c using * by auto
    finally show False unfolding fzn
      using N[THEN spec[where x="Suc N"]] and dist_triangle_half_r[of "z (Suc N)" "f x" e x]
      unfolding e_def by auto
  qed
  hence "f x = x" unfolding e_def and dist_eq_0 by auto
  moreover
  { fix y assume "f y = y" "y\<in>s"
    hence "dist x y \<le> c * dist x y" using lipschitz[THEN bspec[where x=x], THEN bspec[where x=y]]
      using `x\<in>s` and `f x = x` by auto
    hence "dist x y = 0" unfolding mult_le_cancel_right1
      using c and dist_pos_le[of x y] by auto
    hence "y = x" unfolding dist_eq_0 by auto
  }
  ultimately show ?thesis unfolding Bex1_def using `x\<in>s` by blast+
qed

subsection{* Edelstein fixed point theorem.                                            *}

lemma edelstein_fix:
  assumes s:"compact s" "s \<noteq> {}" and gs:"(g ` s) \<subseteq> s"
      and dist:"\<forall>x\<in>s. \<forall>y\<in>s. x \<noteq> y \<longrightarrow> dist (g x) (g y) < dist x y"
  shows "\<exists>! x::real^'a\<in>s. g x = x"
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
  def f \<equiv> "\<lambda> n. fun_pow n g"
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

  def h \<equiv> "\<lambda>n. pastecart (f n x) (f n y)"
  let ?s2 = "{pastecart x y |x y. x \<in> s \<and> y \<in> s}"
  obtain l r where "l\<in>?s2" and r:"\<forall>m n. m < n \<longrightarrow> r m < r n" and lr:"((h \<circ> r) ---> l) sequentially"
    using compact_pastecart[OF s(1) s(1), unfolded compact_def, THEN spec[where x=h]] unfolding  h_def
    using fs[OF `x\<in>s`] and fs[OF `y\<in>s`] by blast
  def a \<equiv> "fstcart l" def b \<equiv> "sndcart l"
  have lab:"l = pastecart a b" unfolding a_def b_def and pastecart_fst_snd by simp
  have [simp]:"a\<in>s" "b\<in>s" unfolding a_def b_def using `l\<in>?s2` by auto

  have "continuous_on UNIV fstcart" and "continuous_on UNIV sndcart"
    using linear_continuous_on using linear_fstcart and linear_sndcart by auto
  hence lima:"((fstcart \<circ> (h \<circ> r)) ---> a) sequentially" and limb:"((sndcart \<circ> (h \<circ> r)) ---> b) sequentially"
    unfolding atomize_conj unfolding continuous_on_sequentially
    apply(erule_tac x="h \<circ> r" in allE) apply(erule_tac x="h \<circ> r" in allE) using lr
    unfolding o_def and h_def a_def b_def  by auto

  { fix n::nat
    have *:"\<And>fx fy x y. dist fx fy \<le> dist x y \<Longrightarrow> \<not> (dist (fx - fy) (a - b) < dist a b - dist x y)" unfolding dist_def by norm
    { fix x y ::"real^'a"
      have "dist (-x) (-y) = dist x y" unfolding dist_def
	using norm_minus_cancel[of "x - y"] by (auto simp add: uminus_add_conv_diff) } note ** = this

    { assume as:"dist a b > dist (f n x) (f n y)"
      then obtain Na Nb where "\<forall>m\<ge>Na. dist (f (r m) x) a < (dist a b - dist (f n x) (f n y)) / 2"
	and "\<forall>m\<ge>Nb. dist (f (r m) y) b < (dist a b - dist (f n x) (f n y)) / 2"
	using lima limb unfolding h_def Lim_sequentially by (fastsimp simp del: Arith_Tools.less_divide_eq_number_of1)
      hence "dist (f (r (Na + Nb + n)) x - f (r (Na + Nb + n)) y) (a - b) < dist a b - dist (f n x) (f n y)"
	apply(erule_tac x="Na+Nb+n" in allE)
	apply(erule_tac x="Na+Nb+n" in allE) apply simp
	using dist_triangle_add_half[of a "f (r (Na + Nb + n)) x" "dist a b - dist (f n x) (f n y)"
          "-b"  "- f (r (Na + Nb + n)) y"]
	unfolding ** unfolding group_simps(12) by (auto simp add: dist_sym)
      moreover
      have "dist (f (r (Na + Nb + n)) x - f (r (Na + Nb + n)) y) (a - b) \<ge> dist a b - dist (f n x) (f n y)"
	using distf[of n "r (Na+Nb+n)", OF _ `x\<in>s` `y\<in>s`]
	using monotone_bigger[OF r, of "Na+Nb+n"]
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

  hence "((sndcart \<circ> h \<circ> r) ---> g a) sequentially" unfolding continuous_on_sequentially
    apply (rule allE[where x="\<lambda>n. (fstcart \<circ> h \<circ> r) n"]) apply (erule ballE[where x=a])
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
