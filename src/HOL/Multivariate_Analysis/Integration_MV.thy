
header {* Kurzweil-Henstock gauge integration in many dimensions. *}
(*  Author:                     John Harrison
    Translation from HOL light: Robert Himmelmann, TU Muenchen *)

theory Integration_MV
  imports Derivative SMT
begin

declare [[smt_certificates="~~/src/HOL/Multivariate_Analysis/Integration_MV.cert"]]
declare [[smt_record=true]]
declare [[z3_proofs=true]]

lemma conjunctD2: assumes "a \<and> b" shows a b using assms by auto
lemma conjunctD3: assumes "a \<and> b \<and> c" shows a b c using assms by auto
lemma conjunctD4: assumes "a \<and> b \<and> c \<and> d" shows a b c d using assms by auto
lemma conjunctD5: assumes "a \<and> b \<and> c \<and> d \<and> e" shows a b c d e using assms by auto

declare smult_conv_scaleR[simp]

subsection {* Some useful lemmas about intervals. *}

lemma empty_as_interval: "{} = {1..0::real^'n}"
  apply(rule set_ext,rule) defer unfolding vector_le_def mem_interval
  using UNIV_witness[where 'a='n] apply(erule_tac exE,rule_tac x=x in allE) by auto

lemma interior_subset_union_intervals: 
  assumes "i = {a..b::real^'n}" "j = {c..d}" "interior j \<noteq> {}" "i \<subseteq> j \<union> s" "interior(i) \<inter> interior(j) = {}"
  shows "interior i \<subseteq> interior s" proof-
  have "{a<..<b} \<inter> {c..d} = {}" using inter_interval_mixed_eq_empty[of c d a b] and assms(3,5)
    unfolding assms(1,2) interior_closed_interval by auto
  moreover have "{a<..<b} \<subseteq> {c..d} \<union> s" apply(rule order_trans,rule interval_open_subset_closed)
    using assms(4) unfolding assms(1,2) by auto
  ultimately show ?thesis apply-apply(rule interior_maximal) defer apply(rule open_interior)
    unfolding assms(1,2) interior_closed_interval by auto qed

lemma inter_interior_unions_intervals: fixes f::"(real^'n) set set"
  assumes "finite f" "open s" "\<forall>t\<in>f. \<exists>a b. t = {a..b}" "\<forall>t\<in>f. s \<inter> (interior t) = {}"
  shows "s \<inter> interior(\<Union>f) = {}" proof(rule ccontr,unfold ex_in_conv[THEN sym]) case goal1
  have lem1:"\<And>x e s U. ball x e \<subseteq> s \<inter> interior U \<longleftrightarrow> ball x e \<subseteq> s \<inter> U" apply rule  defer apply(rule_tac Int_greatest)
    unfolding open_subset_interior[OF open_ball]  using interior_subset by auto
  have lem2:"\<And>x s P. \<exists>x\<in>s. P x \<Longrightarrow> \<exists>x\<in>insert x s. P x" by auto
  have "\<And>f. finite f \<Longrightarrow> (\<forall>t\<in>f. \<exists>a b. t = {a..b}) \<Longrightarrow> (\<exists>x. x \<in> s \<inter> interior (\<Union>f)) \<Longrightarrow> (\<exists>t\<in>f. \<exists>x. \<exists>e>0. ball x e \<subseteq> s \<inter> t)" proof- case goal1
  thus ?case proof(induct rule:finite_induct) 
    case empty from this(2) guess x .. hence False unfolding Union_empty interior_empty by auto thus ?case by auto next
    case (insert i f) guess x using insert(5) .. note x = this
    then guess e unfolding open_contains_ball_eq[OF open_Int[OF assms(2) open_interior],rule_format] .. note e=this
    guess a using insert(4)[rule_format,OF insertI1] .. then guess b .. note ab = this
    show ?case proof(cases "x\<in>i") case False hence "x \<in> UNIV - {a..b}" unfolding ab by auto
      then guess d unfolding open_contains_ball_eq[OF open_Diff[OF open_UNIV closed_interval],rule_format] ..
      hence "0 < d" "ball x (min d e) \<subseteq> UNIV - i" using e unfolding ab by auto
      hence "ball x (min d e) \<subseteq> s \<inter> interior (\<Union>f)" using e unfolding lem1 by auto hence "x \<in> s \<inter> interior (\<Union>f)" using `d>0` e by auto
      hence "\<exists>t\<in>f. \<exists>x e. 0 < e \<and> ball x e \<subseteq> s \<inter> t" apply-apply(rule insert(3)) using insert(4) by auto thus ?thesis by auto next
    case True show ?thesis proof(cases "x\<in>{a<..<b}")
      case True then guess d unfolding open_contains_ball_eq[OF open_interval,rule_format] ..
      thus ?thesis apply(rule_tac x=i in bexI,rule_tac x=x in exI,rule_tac x="min d e" in exI)
	unfolding ab using interval_open_subset_closed[of a b] and e by fastsimp+ next
    case False then obtain k where "x$k \<le> a$k \<or> x$k \<ge> b$k" unfolding mem_interval by(auto simp add:not_less) 
    hence "x$k = a$k \<or> x$k = b$k" using True unfolding ab and mem_interval apply(erule_tac x=k in allE) by auto
    hence "\<exists>x. ball x (e/2) \<subseteq> s \<inter> (\<Union>f)" proof(erule_tac disjE)
      let ?z = "x - (e/2) *\<^sub>R basis k" assume as:"x$k = a$k" have "ball ?z (e / 2) \<inter> i = {}" apply(rule ccontr) unfolding ex_in_conv[THEN sym] proof(erule exE)
	fix y assume "y \<in> ball ?z (e / 2) \<inter> i" hence "dist ?z y < e/2" and yi:"y\<in>i" by auto
	hence "\<bar>(?z - y) $ k\<bar> < e/2" using component_le_norm[of "?z - y" k] unfolding vector_dist_norm by auto
	hence "y$k < a$k" unfolding vector_component_simps vector_scaleR_component as using e[THEN conjunct1] by(auto simp add:field_simps)
	hence "y \<notin> i" unfolding ab mem_interval not_all by(rule_tac x=k in exI,auto) thus False using yi by auto qed
      moreover have "ball ?z (e/2) \<subseteq> s \<inter> (\<Union>insert i f)" apply(rule order_trans[OF _ e[THEN conjunct2, unfolded lem1]]) proof
	fix y assume as:"y\<in> ball ?z (e/2)" have "norm (x - y) \<le> \<bar>e\<bar> / 2 + norm (x - y - (e / 2) *\<^sub>R basis k)"
	   apply-apply(rule order_trans,rule norm_triangle_sub[of "x - y" "(e/2) *\<^sub>R basis k"])
	  unfolding norm_scaleR norm_basis by auto
	also have "\<dots> < \<bar>e\<bar> / 2 + \<bar>e\<bar> / 2" apply(rule add_strict_left_mono) using as unfolding mem_ball vector_dist_norm using e by(auto simp add:field_simps)
	finally show "y\<in>ball x e" unfolding mem_ball vector_dist_norm using e by(auto simp add:field_simps) qed
      ultimately show ?thesis apply(rule_tac x="?z" in exI) unfolding Union_insert by auto
    next let ?z = "x + (e/2) *\<^sub>R basis k" assume as:"x$k = b$k" have "ball ?z (e / 2) \<inter> i = {}" apply(rule ccontr) unfolding ex_in_conv[THEN sym] proof(erule exE)
	fix y assume "y \<in> ball ?z (e / 2) \<inter> i" hence "dist ?z y < e/2" and yi:"y\<in>i" by auto
	hence "\<bar>(?z - y) $ k\<bar> < e/2" using component_le_norm[of "?z - y" k] unfolding vector_dist_norm by auto
	hence "y$k > b$k" unfolding vector_component_simps vector_scaleR_component as using e[THEN conjunct1] by(auto simp add:field_simps)
	hence "y \<notin> i" unfolding ab mem_interval not_all by(rule_tac x=k in exI,auto) thus False using yi by auto qed
      moreover have "ball ?z (e/2) \<subseteq> s \<inter> (\<Union>insert i f)" apply(rule order_trans[OF _ e[THEN conjunct2, unfolded lem1]]) proof
	fix y assume as:"y\<in> ball ?z (e/2)" have "norm (x - y) \<le> \<bar>e\<bar> / 2 + norm (x - y + (e / 2) *\<^sub>R basis k)"
	   apply-apply(rule order_trans,rule norm_triangle_sub[of "x - y" "- (e/2) *\<^sub>R basis k"])
	  unfolding norm_scaleR norm_basis by auto
	also have "\<dots> < \<bar>e\<bar> / 2 + \<bar>e\<bar> / 2" apply(rule add_strict_left_mono) using as unfolding mem_ball vector_dist_norm using e by(auto simp add:field_simps)
	finally show "y\<in>ball x e" unfolding mem_ball vector_dist_norm using e by(auto simp add:field_simps) qed
      ultimately show ?thesis apply(rule_tac x="?z" in exI) unfolding Union_insert by auto qed 
    then guess x .. hence "x \<in> s \<inter> interior (\<Union>f)" unfolding lem1[where U="\<Union>f",THEN sym] using centre_in_ball e[THEN conjunct1] by auto
    thus ?thesis apply-apply(rule lem2,rule insert(3)) using insert(4) by auto qed qed qed qed note * = this
  guess t using *[OF assms(1,3) goal1]  .. from this(2) guess x .. then guess e ..
  hence "x \<in> s" "x\<in>interior t" defer using open_subset_interior[OF open_ball, of x e t] by auto
  thus False using `t\<in>f` assms(4) by auto qed
subsection {* Bounds on intervals where they exist. *}

definition "interval_upperbound (s::(real^'n) set) = (\<chi> i. Sup {a. \<exists>x\<in>s. x$i = a})"

definition "interval_lowerbound (s::(real^'n) set) = (\<chi> i. Inf {a. \<exists>x\<in>s. x$i = a})"

lemma interval_upperbound[simp]: assumes "\<forall>i. a$i \<le> b$i" shows "interval_upperbound {a..b} = b"
  using assms unfolding interval_upperbound_def Cart_eq Cart_lambda_beta apply-apply(rule,erule_tac x=i in allE)
  apply(rule Sup_unique) unfolding setle_def apply rule unfolding mem_Collect_eq apply(erule bexE) unfolding mem_interval defer
  apply(rule,rule) apply(rule_tac x="b$i" in bexI) defer unfolding mem_Collect_eq apply(rule_tac x=b in bexI)
  unfolding mem_interval using assms by auto

lemma interval_lowerbound[simp]: assumes "\<forall>i. a$i \<le> b$i" shows "interval_lowerbound {a..b} = a"
  using assms unfolding interval_lowerbound_def Cart_eq Cart_lambda_beta apply-apply(rule,erule_tac x=i in allE)
  apply(rule Inf_unique) unfolding setge_def apply rule unfolding mem_Collect_eq apply(erule bexE) unfolding mem_interval defer
  apply(rule,rule) apply(rule_tac x="a$i" in bexI) defer unfolding mem_Collect_eq apply(rule_tac x=a in bexI)
  unfolding mem_interval using assms by auto

lemmas interval_bounds = interval_upperbound interval_lowerbound

lemma interval_bounds'[simp]: assumes "{a..b}\<noteq>{}" shows "interval_upperbound {a..b} = b" "interval_lowerbound {a..b} = a"
  using assms unfolding interval_ne_empty by auto

lemma interval_upperbound_1[simp]: "dest_vec1 a \<le> dest_vec1 b \<Longrightarrow> interval_upperbound {a..b} = (b::real^1)"
  apply(rule interval_upperbound) by auto

lemma interval_lowerbound_1[simp]: "dest_vec1 a \<le> dest_vec1 b \<Longrightarrow> interval_lowerbound {a..b} = (a::real^1)"
  apply(rule interval_lowerbound) by auto

lemmas interval_bound_1 = interval_upperbound_1 interval_lowerbound_1

subsection {* Content (length, area, volume...) of an interval. *}

definition "content (s::(real^'n) set) =
       (if s = {} then 0 else (\<Prod>i\<in>UNIV. (interval_upperbound s)$i - (interval_lowerbound s)$i))"

lemma interval_not_empty:"\<forall>i. a$i \<le> b$i \<Longrightarrow> {a..b::real^'n} \<noteq> {}"
  unfolding interval_eq_empty unfolding not_ex not_less by assumption

lemma content_closed_interval: assumes "\<forall>i. a$i \<le> b$i"
  shows "content {a..b} = (\<Prod>i\<in>UNIV. b$i - a$i)"
  using interval_not_empty[OF assms] unfolding content_def interval_upperbound[OF assms] interval_lowerbound[OF assms] by auto

lemma content_closed_interval': assumes "{a..b}\<noteq>{}" shows "content {a..b} = (\<Prod>i\<in>UNIV. b$i - a$i)"
  apply(rule content_closed_interval) using assms unfolding interval_ne_empty .

lemma content_1:"dest_vec1 a \<le> dest_vec1 b \<Longrightarrow> content {a..b} = dest_vec1 b - dest_vec1 a"
  using content_closed_interval[of a b] by auto

lemma content_1':"a \<le> b \<Longrightarrow> content {vec1 a..vec1 b} = b - a" using content_1[of "vec a" "vec b"] by auto

lemma content_unit[intro]: "content{0..1::real^'n} = 1" proof-
  have *:"\<forall>i. 0$i \<le> (1::real^'n::finite)$i" by auto
  have "0 \<in> {0..1::real^'n::finite}" unfolding mem_interval by auto
  thus ?thesis unfolding content_def interval_bounds[OF *] using setprod_1 by auto qed

lemma content_pos_le[intro]: "0 \<le> content {a..b}" proof(cases "{a..b}={}")
  case False hence *:"\<forall>i. a $ i \<le> b $ i" unfolding interval_ne_empty by assumption
  have "(\<Prod>i\<in>UNIV. interval_upperbound {a..b} $ i - interval_lowerbound {a..b} $ i) \<ge> 0"
    apply(rule setprod_nonneg) unfolding interval_bounds[OF *] using * apply(erule_tac x=x in allE) by auto
  thus ?thesis unfolding content_def by(auto simp del:interval_bounds') qed(unfold content_def, auto)

lemma content_pos_lt: assumes "\<forall>i. a$i < b$i" shows "0 < content {a..b}"
proof- have help_lemma1: "\<forall>i. a$i < b$i \<Longrightarrow> \<forall>i. a$i \<le> ((b$i)::real)" apply(rule,erule_tac x=i in allE) by auto
  show ?thesis unfolding content_closed_interval[OF help_lemma1[OF assms]] apply(rule setprod_pos)
    using assms apply(erule_tac x=x in allE) by auto qed

lemma content_pos_lt_1: "dest_vec1 a < dest_vec1 b \<Longrightarrow> 0 < content({a..b})"
  apply(rule content_pos_lt) by auto

lemma content_eq_0: "content({a..b::real^'n}) = 0 \<longleftrightarrow> (\<exists>i. b$i \<le> a$i)" proof(cases "{a..b} = {}")
  case True thus ?thesis unfolding content_def if_P[OF True] unfolding interval_eq_empty apply-
    apply(rule,erule exE) apply(rule_tac x=i in exI) by auto next
  guess a using UNIV_witness[where 'a='n] .. case False note as=this[unfolded interval_eq_empty not_ex not_less]
  show ?thesis unfolding content_def if_not_P[OF False] setprod_zero_iff[OF finite_UNIV]
    apply(rule) apply(erule_tac[!] exE bexE) unfolding interval_bounds[OF as] apply(rule_tac x=x in exI) defer
    apply(rule_tac x=i in bexI) using as apply(erule_tac x=i in allE) by auto qed

lemma cond_cases:"(P \<Longrightarrow> Q x) \<Longrightarrow> (\<not> P \<Longrightarrow> Q y) \<Longrightarrow> Q (if P then x else y)" by auto

lemma content_closed_interval_cases:
  "content {a..b} = (if \<forall>i. a$i \<le> b$i then setprod (\<lambda>i. b$i - a$i) UNIV else 0)" apply(rule cond_cases) 
  apply(rule content_closed_interval) unfolding content_eq_0 not_all not_le defer apply(erule exE,rule_tac x=x in exI) by auto

lemma content_eq_0_interior: "content {a..b} = 0 \<longleftrightarrow> interior({a..b}) = {}"
  unfolding content_eq_0 interior_closed_interval interval_eq_empty by auto

lemma content_eq_0_1: "content {a..b::real^1} = 0 \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a"
  unfolding content_eq_0 by auto

lemma content_pos_lt_eq: "0 < content {a..b} \<longleftrightarrow> (\<forall>i. a$i < b$i)"
  apply(rule) defer apply(rule content_pos_lt,assumption) proof- assume "0 < content {a..b}"
  hence "content {a..b} \<noteq> 0" by auto thus "\<forall>i. a$i < b$i" unfolding content_eq_0 not_ex not_le by auto qed

lemma content_empty[simp]: "content {} = 0" unfolding content_def by auto

lemma content_subset: assumes "{a..b} \<subseteq> {c..d}" shows "content {a..b::real^'n} \<le> content {c..d}" proof(cases "{a..b}={}")
  case True thus ?thesis using content_pos_le[of c d] by auto next
  case False hence ab_ne:"\<forall>i. a $ i \<le> b $ i" unfolding interval_ne_empty by auto
  hence ab_ab:"a\<in>{a..b}" "b\<in>{a..b}" unfolding mem_interval by auto
  have "{c..d} \<noteq> {}" using assms False by auto
  hence cd_ne:"\<forall>i. c $ i \<le> d $ i" using assms unfolding interval_ne_empty by auto
  show ?thesis unfolding content_def unfolding interval_bounds[OF ab_ne] interval_bounds[OF cd_ne]
    unfolding if_not_P[OF False] if_not_P[OF `{c..d} \<noteq> {}`] apply(rule setprod_mono,rule) proof fix i::'n
    show "0 \<le> b $ i - a $ i" using ab_ne[THEN spec[where x=i]] by auto
    show "b $ i - a $ i \<le> d $ i - c $ i"
      using assms[unfolded subset_eq mem_interval,rule_format,OF ab_ab(2),of i]
      using assms[unfolded subset_eq mem_interval,rule_format,OF ab_ab(1),of i] by auto qed qed

lemma content_lt_nz: "0 < content {a..b} \<longleftrightarrow> content {a..b} \<noteq> 0"
  unfolding content_pos_lt_eq content_eq_0 unfolding not_ex not_le by auto

subsection {* The notion of a gauge --- simply an open set containing the point. *}

definition gauge where "gauge d \<longleftrightarrow> (\<forall>x. x\<in>(d x) \<and> open(d x))"

lemma gaugeI:assumes "\<And>x. x\<in>g x" "\<And>x. open (g x)" shows "gauge g"
  using assms unfolding gauge_def by auto

lemma gaugeD[dest]: assumes "gauge d" shows "x\<in>d x" "open (d x)" using assms unfolding gauge_def by auto

lemma gauge_ball_dependent: "\<forall>x. 0 < e x \<Longrightarrow> gauge (\<lambda>x. ball x (e x))"
  unfolding gauge_def by auto 

lemma gauge_ball[intro?]: "0 < e \<Longrightarrow> gauge (\<lambda>x. ball x e)" unfolding gauge_def by auto 

lemma gauge_trivial[intro]: "gauge (\<lambda>x. ball x 1)" apply(rule gauge_ball) by auto

lemma gauge_inter: "gauge d1 \<Longrightarrow> gauge d2 \<Longrightarrow> gauge (\<lambda>x. (d1 x) \<inter> (d2 x))"
  unfolding gauge_def by auto 

lemma gauge_inters: assumes "finite s" "\<forall>d\<in>s. gauge (f d)" shows "gauge(\<lambda>x. \<Inter> {f d x | d. d \<in> s})" proof-
  have *:"\<And>x. {f d x |d. d \<in> s} = (\<lambda>d. f d x) ` s" by auto show ?thesis
  unfolding gauge_def unfolding * 
  using assms unfolding Ball_def Inter_iff mem_Collect_eq gauge_def by auto qed

lemma gauge_existence_lemma: "(\<forall>x. \<exists>d::real. p x \<longrightarrow> 0 < d \<and> q d x) \<longleftrightarrow> (\<forall>x. \<exists>d>0. p x \<longrightarrow> q d x)" by(meson zero_less_one)

subsection {* Divisions. *}

definition division_of (infixl "division'_of" 40) where
  "s division_of i \<equiv>
        finite s \<and>
        (\<forall>k\<in>s. k \<subseteq> i \<and> k \<noteq> {} \<and> (\<exists>a b. k = {a..b})) \<and>
        (\<forall>k1\<in>s. \<forall>k2\<in>s. k1 \<noteq> k2 \<longrightarrow> interior(k1) \<inter> interior(k2) = {}) \<and>
        (\<Union>s = i)"

lemma division_ofD[dest]: assumes  "s division_of i"
  shows"finite s" "\<And>k. k\<in>s \<Longrightarrow> k \<subseteq> i" "\<And>k. k\<in>s \<Longrightarrow>  k \<noteq> {}" "\<And>k. k\<in>s \<Longrightarrow> (\<exists>a b. k = {a..b})"
  "\<And>k1 k2. \<lbrakk>k1\<in>s; k2\<in>s; k1 \<noteq> k2\<rbrakk> \<Longrightarrow> interior(k1) \<inter> interior(k2) = {}" "\<Union>s = i" using assms unfolding division_of_def by auto

lemma division_ofI:
  assumes "finite s" "\<And>k. k\<in>s \<Longrightarrow> k \<subseteq> i" "\<And>k. k\<in>s \<Longrightarrow>  k \<noteq> {}" "\<And>k. k\<in>s \<Longrightarrow> (\<exists>a b. k = {a..b})"
  "\<And>k1 k2. \<lbrakk>k1\<in>s; k2\<in>s; k1 \<noteq> k2\<rbrakk> \<Longrightarrow> interior(k1) \<inter> interior(k2) = {}" "\<Union>s = i"
  shows "s division_of i" using assms unfolding division_of_def by auto

lemma division_of_finite: "s division_of i \<Longrightarrow> finite s"
  unfolding division_of_def by auto

lemma division_of_self[intro]: "{a..b} \<noteq> {} \<Longrightarrow> {{a..b}} division_of {a..b}"
  unfolding division_of_def by auto

lemma division_of_trivial[simp]: "s division_of {} \<longleftrightarrow> s = {}" unfolding division_of_def by auto 

lemma division_of_sing[simp]: "s division_of {a..a::real^'n} \<longleftrightarrow> s = {{a..a}}" (is "?l = ?r") proof
  assume ?r moreover { assume "s = {{a}}" moreover fix k assume "k\<in>s" 
    ultimately have"\<exists>x y. k = {x..y}" apply(rule_tac x=a in exI)+ unfolding interval_sing[THEN conjunct1] by auto }
  ultimately show ?l unfolding division_of_def interval_sing[THEN conjunct1] by auto next
  assume ?l note as=conjunctD4[OF this[unfolded division_of_def interval_sing[THEN conjunct1]]]
  { fix x assume x:"x\<in>s" have "x={a}" using as(2)[rule_format,OF x] by auto }
  moreover have "s \<noteq> {}" using as(4) by auto ultimately show ?r unfolding interval_sing[THEN conjunct1] by auto qed

lemma elementary_empty: obtains p where "p division_of {}"
  unfolding division_of_trivial by auto

lemma elementary_interval: obtains p where  "p division_of {a..b}"
  by(metis division_of_trivial division_of_self)

lemma division_contains: "s division_of i \<Longrightarrow> \<forall>x\<in>i. \<exists>k\<in>s. x \<in> k"
  unfolding division_of_def by auto

lemma forall_in_division:
 "d division_of i \<Longrightarrow> ((\<forall>x\<in>d. P x) \<longleftrightarrow> (\<forall>a b. {a..b} \<in> d \<longrightarrow> P {a..b}))"
  unfolding division_of_def by fastsimp

lemma division_of_subset: assumes "p division_of (\<Union>p)" "q \<subseteq> p" shows "q division_of (\<Union>q)"
  apply(rule division_ofI) proof- note as=division_ofD[OF assms(1)]
  show "finite q" apply(rule finite_subset) using as(1) assms(2) by auto
  { fix k assume "k \<in> q" hence kp:"k\<in>p" using assms(2) by auto show "k\<subseteq>\<Union>q" using `k \<in> q` by auto
  show "\<exists>a b. k = {a..b}" using as(4)[OF kp] by auto show "k \<noteq> {}" using as(3)[OF kp] by auto }
  fix k1 k2 assume "k1 \<in> q" "k2 \<in> q" "k1 \<noteq> k2" hence *:"k1\<in>p" "k2\<in>p" "k1\<noteq>k2" using assms(2) by auto
  show "interior k1 \<inter> interior k2 = {}" using as(5)[OF *] by auto qed auto

lemma division_of_union_self[intro]: "p division_of s \<Longrightarrow> p division_of (\<Union>p)" unfolding division_of_def by auto

lemma division_of_content_0: assumes "content {a..b} = 0" "d division_of {a..b}" shows "\<forall>k\<in>d. content k = 0"
  unfolding forall_in_division[OF assms(2)] apply(rule,rule,rule) apply(drule division_ofD(2)[OF assms(2)])
  apply(drule content_subset) unfolding assms(1) proof- case goal1 thus ?case using content_pos_le[of a b] by auto qed

lemma division_inter: assumes "p1 division_of s1" "p2 division_of (s2::(real^'a) set)"
  shows "{k1 \<inter> k2 | k1 k2 .k1 \<in> p1 \<and> k2 \<in> p2 \<and> k1 \<inter> k2 \<noteq> {}} division_of (s1 \<inter> s2)" (is "?A' division_of _") proof-
let ?A = "{s. s \<in>  (\<lambda>(k1,k2). k1 \<inter> k2) ` (p1 \<times> p2) \<and> s \<noteq> {}}" have *:"?A' = ?A" by auto
show ?thesis unfolding * proof(rule division_ofI) have "?A \<subseteq> (\<lambda>(x, y). x \<inter> y) ` (p1 \<times> p2)" by auto
  moreover have "finite (p1 \<times> p2)" using assms unfolding division_of_def by auto ultimately show "finite ?A" by auto
  have *:"\<And>s. \<Union>{x\<in>s. x \<noteq> {}} = \<Union>s" by auto show "\<Union>?A = s1 \<inter> s2" apply(rule set_ext) unfolding * and Union_image_eq UN_iff
    using division_ofD(6)[OF assms(1)] and division_ofD(6)[OF assms(2)] by auto
  { fix k assume "k\<in>?A" then obtain k1 k2 where k:"k = k1 \<inter> k2" "k1\<in>p1" "k2\<in>p2" "k\<noteq>{}" by auto thus "k \<noteq> {}" by auto
  show "k \<subseteq> s1 \<inter> s2" using division_ofD(2)[OF assms(1) k(2)] and division_ofD(2)[OF assms(2) k(3)] unfolding k by auto
  guess a1 using division_ofD(4)[OF assms(1) k(2)] .. then guess b1 .. note ab1=this
  guess a2 using division_ofD(4)[OF assms(2) k(3)] .. then guess b2 .. note ab2=this
  show "\<exists>a b. k = {a..b}" unfolding k ab1 ab2 unfolding inter_interval by auto } fix k1 k2
  assume "k1\<in>?A" then obtain x1 y1 where k1:"k1 = x1 \<inter> y1" "x1\<in>p1" "y1\<in>p2" "k1\<noteq>{}" by auto
  assume "k2\<in>?A" then obtain x2 y2 where k2:"k2 = x2 \<inter> y2" "x2\<in>p1" "y2\<in>p2" "k2\<noteq>{}" by auto
  assume "k1 \<noteq> k2" hence th:"x1\<noteq>x2 \<or> y1\<noteq>y2" unfolding k1 k2 by auto
  have *:"(interior x1 \<inter> interior x2 = {} \<or> interior y1 \<inter> interior y2 = {}) \<Longrightarrow>
      interior(x1 \<inter> y1) \<subseteq> interior(x1) \<Longrightarrow> interior(x1 \<inter> y1) \<subseteq> interior(y1) \<Longrightarrow>
      interior(x2 \<inter> y2) \<subseteq> interior(x2) \<Longrightarrow> interior(x2 \<inter> y2) \<subseteq> interior(y2)
      \<Longrightarrow> interior(x1 \<inter> y1) \<inter> interior(x2 \<inter> y2) = {}" by auto
  show "interior k1 \<inter> interior k2 = {}" unfolding k1 k2 apply(rule *) defer apply(rule_tac[1-4] subset_interior)
    using division_ofD(5)[OF assms(1) k1(2) k2(2)]
    using division_ofD(5)[OF assms(2) k1(3) k2(3)] using th by auto qed qed

lemma division_inter_1: assumes "d division_of i" "{a..b::real^'n} \<subseteq> i"
  shows "{ {a..b} \<inter> k |k. k \<in> d \<and> {a..b} \<inter> k \<noteq> {} } division_of {a..b}" proof(cases "{a..b} = {}")
  case True show ?thesis unfolding True and division_of_trivial by auto next
  have *:"{a..b} \<inter> i = {a..b}" using assms(2) by auto 
  case False show ?thesis using division_inter[OF division_of_self[OF False] assms(1)] unfolding * by auto qed

lemma elementary_inter: assumes "p1 division_of s" "p2 division_of (t::(real^'n) set)"
  shows "\<exists>p. p division_of (s \<inter> t)"
  by(rule,rule division_inter[OF assms])

lemma elementary_inters: assumes "finite f" "f\<noteq>{}" "\<forall>s\<in>f. \<exists>p. p division_of (s::(real^'n) set)"
  shows "\<exists>p. p division_of (\<Inter> f)" using assms apply-proof(induct f rule:finite_induct)
case (insert x f) show ?case proof(cases "f={}")
  case True thus ?thesis unfolding True using insert by auto next
  case False guess p using insert(3)[OF False insert(5)[unfolded ball_simps,THEN conjunct2]] ..
  moreover guess px using insert(5)[rule_format,OF insertI1] .. ultimately
  show ?thesis unfolding Inter_insert apply(rule_tac elementary_inter) by assumption+ qed qed auto

lemma division_disjoint_union:
  assumes "p1 division_of s1" "p2 division_of s2" "interior s1 \<inter> interior s2 = {}"
  shows "(p1 \<union> p2) division_of (s1 \<union> s2)" proof(rule division_ofI) 
  note d1 = division_ofD[OF assms(1)] and d2 = division_ofD[OF assms(2)]
  show "finite (p1 \<union> p2)" using d1(1) d2(1) by auto
  show "\<Union>(p1 \<union> p2) = s1 \<union> s2" using d1(6) d2(6) by auto
  { fix k1 k2 assume as:"k1 \<in> p1 \<union> p2" "k2 \<in> p1 \<union> p2" "k1 \<noteq> k2" moreover let ?g="interior k1 \<inter> interior k2 = {}"
  { assume as:"k1\<in>p1" "k2\<in>p2" have ?g using subset_interior[OF d1(2)[OF as(1)]] subset_interior[OF d2(2)[OF as(2)]]
      using assms(3) by blast } moreover
  { assume as:"k1\<in>p2" "k2\<in>p1" have ?g using subset_interior[OF d1(2)[OF as(2)]] subset_interior[OF d2(2)[OF as(1)]]
      using assms(3) by blast} ultimately
  show ?g using d1(5)[OF _ _ as(3)] and d2(5)[OF _ _ as(3)] by auto }
  fix k assume k:"k \<in> p1 \<union> p2"  show "k \<subseteq> s1 \<union> s2" using k d1(2) d2(2) by auto
  show "k \<noteq> {}" using k d1(3) d2(3) by auto show "\<exists>a b. k = {a..b}" using k d1(4) d2(4) by auto qed

lemma partial_division_extend_1:
  assumes "{c..d} \<subseteq> {a..b::real^'n}" "{c..d} \<noteq> {}"
  obtains p where "p division_of {a..b}" "{c..d} \<in> p"
proof- def n \<equiv> "CARD('n)" have n:"1 \<le> n" "0 < n" "n \<noteq> 0" unfolding n_def by auto
  guess \<pi> using ex_bij_betw_nat_finite_1[OF finite_UNIV[where 'a='n]] .. note \<pi>=this
  def \<pi>' \<equiv> "inv_into {1..n} \<pi>"
  have \<pi>':"bij_betw \<pi>' UNIV {1..n}" using bij_betw_inv_into[OF \<pi>] unfolding \<pi>'_def n_def by auto
  hence \<pi>'i:"\<And>i. \<pi>' i \<in> {1..n}" unfolding bij_betw_def by auto 
  have \<pi>\<pi>'[simp]:"\<And>i. \<pi> (\<pi>' i) = i" unfolding \<pi>'_def apply(rule f_inv_into_f) unfolding n_def using \<pi> unfolding bij_betw_def by auto
  have \<pi>'\<pi>[simp]:"\<And>i. i\<in>{1..n} \<Longrightarrow> \<pi>' (\<pi> i) = i" unfolding \<pi>'_def apply(rule inv_into_f_eq) using \<pi> unfolding n_def bij_betw_def by auto
  have "{c..d} \<noteq> {}" using assms by auto
  let ?p1 = "\<lambda>l. {(\<chi> i. if \<pi>' i < l then c$i else a$i) .. (\<chi> i. if \<pi>' i < l then d$i else if \<pi>' i = l then c$\<pi> l else b$i)}"
  let ?p2 = "\<lambda>l. {(\<chi> i. if \<pi>' i < l then c$i else if \<pi>' i = l then d$\<pi> l else a$i) .. (\<chi> i. if \<pi>' i < l then d$i else b$i)}"
  let ?p =  "{?p1 l |l. l \<in> {1..n+1}} \<union> {?p2 l |l. l \<in> {1..n+1}}"
  have abcd:"\<And>i. a $ i \<le> c $ i \<and> c$i \<le> d$i \<and> d $ i \<le> b $ i" using assms unfolding subset_interval interval_eq_empty by(auto simp add:not_le not_less)
  show ?thesis apply(rule that[of ?p]) apply(rule division_ofI)
  proof- have "\<And>i. \<pi>' i < Suc n"
    proof(rule ccontr,unfold not_less) fix i assume "Suc n \<le> \<pi>' i"
      hence "\<pi>' i \<notin> {1..n}" by auto thus False using \<pi>' unfolding bij_betw_def by auto
    qed hence "c = (\<chi> i. if \<pi>' i < Suc n then c $ i else a $ i)"
        "d = (\<chi> i. if \<pi>' i < Suc n then d $ i else if \<pi>' i = n + 1 then c $ \<pi> (n + 1) else b $ i)"
      unfolding Cart_eq Cart_lambda_beta using \<pi>' unfolding bij_betw_def by auto
    thus cdp:"{c..d} \<in> ?p" apply-apply(rule UnI1) unfolding mem_Collect_eq apply(rule_tac x="n + 1" in exI) by auto
    have "\<And>l. l\<in>{1..n+1} \<Longrightarrow> ?p1 l \<subseteq> {a..b}"  "\<And>l. l\<in>{1..n+1} \<Longrightarrow> ?p2 l \<subseteq> {a..b}"
      unfolding subset_eq apply(rule_tac[!] ballI,rule_tac[!] ccontr)
    proof- fix l assume l:"l\<in>{1..n+1}" fix x assume "x\<notin>{a..b}"
      then guess i unfolding mem_interval not_all .. note i=this
      show "x \<in> ?p1 l \<Longrightarrow> False" "x \<in> ?p2 l \<Longrightarrow> False" unfolding mem_interval apply(erule_tac[!] x=i in allE)
        apply(case_tac[!] "\<pi>' i < l", case_tac[!] "\<pi>' i = l") using abcd[of i] i by auto 
    qed moreover have "\<And>x. x \<in> {a..b} \<Longrightarrow> x \<in> \<Union>?p"
    proof- fix x assume x:"x\<in>{a..b}"
      { presume "x\<notin>{c..d} \<Longrightarrow> x \<in> \<Union>?p" thus "x \<in> \<Union>?p" using cdp by blast }
      let ?M = "{i. i\<in>{1..n+1} \<and> \<not> (c $ \<pi> i \<le> x $ \<pi> i \<and> x $ \<pi> i \<le> d $ \<pi> i)}"
      assume "x\<notin>{c..d}" then guess i0 unfolding mem_interval not_all ..
      hence "\<pi>' i0 \<in> ?M" using \<pi>' unfolding bij_betw_def by(auto intro!:le_SucI)
      hence M:"finite ?M" "?M \<noteq> {}" by auto
      def l \<equiv> "Min ?M" note l = Min_less_iff[OF M,unfolded l_def[symmetric]] Min_in[OF M,unfolded mem_Collect_eq l_def[symmetric]]
        Min_gr_iff[OF M,unfolded l_def[symmetric]]
      have "x\<in>?p1 l \<or> x\<in>?p2 l" using l(2)[THEN conjunct2] unfolding de_Morgan_conj not_le
        apply- apply(erule disjE) apply(rule disjI1) defer apply(rule disjI2)
      proof- assume as:"x $ \<pi> l < c $ \<pi> l"
        show "x \<in> ?p1 l" unfolding mem_interval Cart_lambda_beta
        proof case goal1 have "\<pi>' i \<in> {1..n}" using \<pi>' unfolding bij_betw_def not_le by auto
          thus ?case using as x[unfolded mem_interval,rule_format,of i]
            apply auto using l(3)[of "\<pi>' i"] by(auto elim!:ballE[where x="\<pi>' i"])
        qed
      next assume as:"x $ \<pi> l > d $ \<pi> l"
        show "x \<in> ?p2 l" unfolding mem_interval Cart_lambda_beta
        proof case goal1 have "\<pi>' i \<in> {1..n}" using \<pi>' unfolding bij_betw_def not_le by auto
          thus ?case using as x[unfolded mem_interval,rule_format,of i]
            apply auto using l(3)[of "\<pi>' i"] by(auto elim!:ballE[where x="\<pi>' i"])
        qed qed
      thus "x \<in> \<Union>?p" using l(2) by blast 
    qed ultimately show "\<Union>?p = {a..b}" apply-apply(rule) defer apply(rule) by(assumption,blast)
    
    show "finite ?p" by auto
    fix k assume k:"k\<in>?p" then obtain l where l:"k = ?p1 l \<or> k = ?p2 l" "l \<in> {1..n + 1}" by auto
    show "k\<subseteq>{a..b}" apply(rule,unfold mem_interval,rule,rule) 
    proof- fix i::'n and x assume "x \<in> k" moreover have "\<pi>' i < l \<or> \<pi>' i = l \<or> \<pi>' i > l" by auto
      ultimately show "a$i \<le> x$i" "x$i \<le> b$i" using abcd[of i] using l by(auto elim:disjE elim!:allE[where x=i] simp add:vector_le_def)
    qed have "\<And>l. ?p1 l \<noteq> {}" "\<And>l. ?p2 l \<noteq> {}" unfolding interval_eq_empty not_ex apply(rule_tac[!] allI)
    proof- case goal1 thus ?case using abcd[of x] by auto
    next   case goal2 thus ?case using abcd[of x] by auto
    qed thus "k \<noteq> {}" using k by auto
    show "\<exists>a b. k = {a..b}" using k by auto
    fix k' assume k':"k' \<in> ?p" "k \<noteq> k'" then obtain l' where l':"k' = ?p1 l' \<or> k' = ?p2 l'" "l' \<in> {1..n + 1}" by auto
    { fix k k' l l'
      assume k:"k\<in>?p" and l:"k = ?p1 l \<or> k = ?p2 l" "l \<in> {1..n + 1}" 
      assume k':"k' \<in> ?p" "k \<noteq> k'" and  l':"k' = ?p1 l' \<or> k' = ?p2 l'" "l' \<in> {1..n + 1}" 
      assume "l \<le> l'" fix x
      have "x \<notin> interior k \<inter> interior k'" 
      proof(rule,cases "l' = n+1") assume x:"x \<in> interior k \<inter> interior k'"
        case True hence "\<And>i. \<pi>' i < l'" using \<pi>'i by(auto simp add:less_Suc_eq_le)
        hence k':"k' = {c..d}" using l'(1) \<pi>'i by(auto simp add:Cart_nth_inverse)
        have ln:"l < n + 1" 
        proof(rule ccontr) case goal1 hence l2:"l = n+1" using l by auto
          hence "\<And>i. \<pi>' i < l" using \<pi>'i by(auto simp add:less_Suc_eq_le)
          hence "k = {c..d}" using l(1) \<pi>'i by(auto simp add:Cart_nth_inverse)
          thus False using `k\<noteq>k'` k' by auto
        qed have **:"\<pi>' (\<pi> l) = l" using \<pi>'\<pi>[of l] using l ln by auto
        have "x $ \<pi> l < c $ \<pi> l \<or> d $ \<pi> l < x $ \<pi> l" using l(1) apply-
        proof(erule disjE)
          assume as:"k = ?p1 l" note * = conjunct1[OF x[unfolded as Int_iff interior_closed_interval mem_interval],rule_format]
          show ?thesis using *[of "\<pi> l"] using ln unfolding Cart_lambda_beta ** by auto
        next assume as:"k = ?p2 l" note * = conjunct1[OF x[unfolded as Int_iff interior_closed_interval mem_interval],rule_format]
          show ?thesis using *[of "\<pi> l"] using ln unfolding Cart_lambda_beta ** by auto
        qed thus False using x unfolding k' unfolding Int_iff interior_closed_interval mem_interval
          by(auto elim!:allE[where x="\<pi> l"])
      next case False hence "l < n + 1" using l'(2) using `l\<le>l'` by auto
        hence ln:"l \<in> {1..n}" "l' \<in> {1..n}" using l l' False by auto
        note \<pi>l = \<pi>'\<pi>[OF ln(1)] \<pi>'\<pi>[OF ln(2)]
        assume x:"x \<in> interior k \<inter> interior k'"
        show False using l(1) l'(1) apply-
        proof(erule_tac[!] disjE)+
          assume as:"k = ?p1 l" "k' = ?p1 l'"
          note * = x[unfolded as Int_iff interior_closed_interval mem_interval]
          have "l \<noteq> l'" using k'(2)[unfolded as] by auto
          thus False using * by(smt Cart_lambda_beta \<pi>l)
        next assume as:"k = ?p2 l" "k' = ?p2 l'"
          note * = conjunctD2[OF x[unfolded as Int_iff interior_closed_interval mem_interval],rule_format]
          have "l \<noteq> l'" apply(rule) using k'(2)[unfolded as] by auto
          thus False using *[of "\<pi> l"] *[of "\<pi> l'"]
            unfolding Cart_lambda_beta \<pi>l using `l \<le> l'` by auto
        next assume as:"k = ?p1 l" "k' = ?p2 l'"
          note * = conjunctD2[OF x[unfolded as Int_iff interior_closed_interval mem_interval],rule_format]
          show False using *[of "\<pi> l"] *[of "\<pi> l'"]
            unfolding Cart_lambda_beta \<pi>l using `l \<le> l'` using abcd[of "\<pi> l'"] by smt 
        next assume as:"k = ?p2 l" "k' = ?p1 l'"
          note * = conjunctD2[OF x[unfolded as Int_iff interior_closed_interval mem_interval],rule_format]
          show False using *[of "\<pi> l"] *[of "\<pi> l'"]
            unfolding Cart_lambda_beta \<pi>l using `l \<le> l'` using abcd[of "\<pi> l'"] by smt
        qed qed } 
    from this[OF k l k' l'] this[OF k'(1) l' k _ l] have "\<And>x. x \<notin> interior k \<inter> interior k'"
      apply - apply(cases "l' \<le> l") using k'(2) by auto            
    thus "interior k \<inter> interior k' = {}" by auto        
qed qed

lemma partial_division_extend_interval: assumes "p division_of (\<Union>p)" "(\<Union>p) \<subseteq> {a..b}"
  obtains q where "p \<subseteq> q" "q division_of {a..b::real^'n}" proof(cases "p = {}")
  case True guess q apply(rule elementary_interval[of a b]) .
  thus ?thesis apply- apply(rule that[of q]) unfolding True by auto next
  case False note p = division_ofD[OF assms(1)]
  have *:"\<forall>k\<in>p. \<exists>q. q division_of {a..b} \<and> k\<in>q" proof case goal1
    guess c using p(4)[OF goal1] .. then guess d .. note cd_ = this
    have *:"{c..d} \<subseteq> {a..b}" "{c..d} \<noteq> {}" using p(2,3)[OF goal1, unfolded cd_] using assms(2) by auto
    guess q apply(rule partial_division_extend_1[OF *]) . thus ?case unfolding cd_ by auto qed
  guess q using bchoice[OF *] .. note q = conjunctD2[OF this[rule_format]]
  have "\<And>x. x\<in>p \<Longrightarrow> \<exists>d. d division_of \<Union>(q x - {x})" apply(rule,rule_tac p="q x" in division_of_subset) proof-
    fix x assume x:"x\<in>p" show "q x division_of \<Union>q x" apply-apply(rule division_ofI)
      using division_ofD[OF q(1)[OF x]] by auto show "q x - {x} \<subseteq> q x" by auto qed
  hence "\<exists>d. d division_of \<Inter> ((\<lambda>i. \<Union>(q i - {i})) ` p)" apply- apply(rule elementary_inters)
    apply(rule finite_imageI[OF p(1)]) unfolding image_is_empty apply(rule False) by auto
  then guess d .. note d = this
  show ?thesis apply(rule that[of "d \<union> p"]) proof-
    have *:"\<And>s f t. s \<noteq> {} \<Longrightarrow> (\<forall>i\<in>s. f i \<union> i = t) \<Longrightarrow> t = \<Inter> (f ` s) \<union> (\<Union>s)" by auto
    have *:"{a..b} = \<Inter> (\<lambda>i. \<Union>(q i - {i})) ` p \<union> \<Union>p" apply(rule *[OF False]) proof fix i assume i:"i\<in>p"
      show "\<Union>(q i - {i}) \<union> i = {a..b}" using division_ofD(6)[OF q(1)[OF i]] using q(2)[OF i] by auto qed
    show "d \<union> p division_of {a..b}" unfolding * apply(rule division_disjoint_union[OF d assms(1)])
      apply(rule inter_interior_unions_intervals) apply(rule p open_interior ballI)+ proof(assumption,rule)
      fix k assume k:"k\<in>p" have *:"\<And>u t s. u \<subseteq> s \<Longrightarrow> s \<inter> t = {} \<Longrightarrow> u \<inter> t = {}" by auto
      show "interior (\<Inter>(\<lambda>i. \<Union>(q i - {i})) ` p) \<inter> interior k = {}" apply(rule *[of _ "interior (\<Union>(q k - {k}))"])
	defer apply(subst Int_commute) apply(rule inter_interior_unions_intervals) proof- note qk=division_ofD[OF q(1)[OF k]]
	show "finite (q k - {k})" "open (interior k)"  "\<forall>t\<in>q k - {k}. \<exists>a b. t = {a..b}" using qk by auto
	show "\<forall>t\<in>q k - {k}. interior k \<inter> interior t = {}" using qk(5) using q(2)[OF k] by auto
	have *:"\<And>x s. x \<in> s \<Longrightarrow> \<Inter>s \<subseteq> x" by auto show "interior (\<Inter>(\<lambda>i. \<Union>(q i - {i})) ` p) \<subseteq> interior (\<Union>(q k - {k}))"
	  apply(rule subset_interior *)+ using k by auto qed qed qed auto qed

lemma elementary_bounded[dest]: "p division_of s \<Longrightarrow> bounded (s::(real^'n) set)"
  unfolding division_of_def by(metis bounded_Union bounded_interval) 

lemma elementary_subset_interval: "p division_of s \<Longrightarrow> \<exists>a b. s \<subseteq> {a..b::real^'n}"
  by(meson elementary_bounded bounded_subset_closed_interval)

lemma division_union_intervals_exists: assumes "{a..b::real^'n} \<noteq> {}"
  obtains p where "(insert {a..b} p) division_of ({a..b} \<union> {c..d})" proof(cases "{c..d} = {}")
  case True show ?thesis apply(rule that[of "{}"]) unfolding True using assms by auto next
  case False note false=this show ?thesis proof(cases "{a..b} \<inter> {c..d} = {}")
  have *:"\<And>a b. {a,b} = {a} \<union> {b}" by auto
  case True show ?thesis apply(rule that[of "{{c..d}}"]) unfolding * apply(rule division_disjoint_union)
    using false True assms using interior_subset by auto next
  case False obtain u v where uv:"{a..b} \<inter> {c..d} = {u..v}" unfolding inter_interval by auto
  have *:"{u..v} \<subseteq> {c..d}" using uv by auto
  guess p apply(rule partial_division_extend_1[OF * False[unfolded uv]]) . note p=this division_ofD[OF this(1)]
  have *:"{a..b} \<union> {c..d} = {a..b} \<union> \<Union>(p - {{u..v}})" "\<And>x s. insert x s = {x} \<union> s" using p(8) unfolding uv[THEN sym] by auto
  show thesis apply(rule that[of "p - {{u..v}}"]) unfolding *(1) apply(subst *(2)) apply(rule division_disjoint_union)
    apply(rule,rule assms) apply(rule division_of_subset[of p]) apply(rule division_of_union_self[OF p(1)]) defer
    unfolding interior_inter[THEN sym] proof-
    have *:"\<And>cd p uv ab. p \<subseteq> cd \<Longrightarrow> ab \<inter> cd = uv \<Longrightarrow> ab \<inter> p = uv \<inter> p" by auto
    have "interior ({a..b} \<inter> \<Union>(p - {{u..v}})) = interior({u..v} \<inter> \<Union>(p - {{u..v}}))" 
      apply(rule arg_cong[of _ _ interior]) apply(rule *[OF _ uv]) using p(8) by auto
    also have "\<dots> = {}" unfolding interior_inter apply(rule inter_interior_unions_intervals) using p(6) p(7)[OF p(2)] p(3) by auto
    finally show "interior ({a..b} \<inter> \<Union>(p - {{u..v}})) = {}" by assumption qed auto qed qed

lemma division_of_unions: assumes "finite f"  "\<And>p. p\<in>f \<Longrightarrow> p division_of (\<Union>p)"
  "\<And>k1 k2. \<lbrakk>k1 \<in> \<Union>f; k2 \<in> \<Union>f; k1 \<noteq> k2\<rbrakk> \<Longrightarrow> interior k1 \<inter> interior k2 = {}"
  shows "\<Union>f division_of \<Union>\<Union>f" apply(rule division_ofI) prefer 5 apply(rule assms(3)|assumption)+
  apply(rule finite_Union assms(1))+ prefer 3 apply(erule UnionE) apply(rule_tac s=X in division_ofD(3)[OF assms(2)])
  using division_ofD[OF assms(2)] by auto
  
lemma elementary_union_interval: assumes "p division_of \<Union>p"
  obtains q where "q division_of ({a..b::real^'n} \<union> \<Union>p)" proof-
  note assm=division_ofD[OF assms]
  have lem1:"\<And>f s. \<Union>\<Union> (f ` s) = \<Union>(\<lambda>x.\<Union>(f x)) ` s" by auto
  have lem2:"\<And>f s. f \<noteq> {} \<Longrightarrow> \<Union>{s \<union> t |t. t \<in> f} = s \<union> \<Union>f" by auto
{ presume "p={} \<Longrightarrow> thesis" "{a..b} = {} \<Longrightarrow> thesis" "{a..b} \<noteq> {} \<Longrightarrow> interior {a..b} = {} \<Longrightarrow> thesis"
    "p\<noteq>{} \<Longrightarrow> interior {a..b}\<noteq>{} \<Longrightarrow> {a..b} \<noteq> {} \<Longrightarrow> thesis"
  thus thesis by auto
next assume as:"p={}" guess p apply(rule elementary_interval[of a b]) .
  thus thesis apply(rule_tac that[of p]) unfolding as by auto 
next assume as:"{a..b}={}" show thesis apply(rule that) unfolding as using assms by auto
next assume as:"interior {a..b} = {}" "{a..b} \<noteq> {}"
  show thesis apply(rule that[of "insert {a..b} p"],rule division_ofI)
    unfolding finite_insert apply(rule assm(1)) unfolding Union_insert  
    using assm(2-4) as apply- by(fastsimp dest: assm(5))+
next assume as:"p \<noteq> {}" "interior {a..b} \<noteq> {}" "{a..b}\<noteq>{}"
  have "\<forall>k\<in>p. \<exists>q. (insert {a..b} q) division_of ({a..b} \<union> k)" proof case goal1
    from assm(4)[OF this] guess c .. then guess d ..
    thus ?case apply-apply(rule division_union_intervals_exists[OF as(3),of c d]) by auto
  qed from bchoice[OF this] guess q .. note q=division_ofD[OF this[rule_format]]
  let ?D = "\<Union>{insert {a..b} (q k) | k. k \<in> p}"
  show thesis apply(rule that[of "?D"]) proof(rule division_ofI)
    have *:"{insert {a..b} (q k) |k. k \<in> p} = (\<lambda>k. insert {a..b} (q k)) ` p" by auto
    show "finite ?D" apply(rule finite_Union) unfolding * apply(rule finite_imageI) using assm(1) q(1) by auto
    show "\<Union>?D = {a..b} \<union> \<Union>p" unfolding * lem1 unfolding lem2[OF as(1), of "{a..b}",THEN sym]
      using q(6) by auto
    fix k assume k:"k\<in>?D" thus " k \<subseteq> {a..b} \<union> \<Union>p" using q(2) by auto
    show "k \<noteq> {}" using q(3) k by auto show "\<exists>a b. k = {a..b}" using q(4) k by auto
    fix k' assume k':"k'\<in>?D" "k\<noteq>k'"
    obtain x  where x: "k \<in>insert {a..b} (q x)"  "x\<in>p"  using k  by auto
    obtain x' where x':"k'\<in>insert {a..b} (q x')" "x'\<in>p" using k' by auto
    show "interior k \<inter> interior k' = {}" proof(cases "x=x'")
      case True show ?thesis apply(rule q(5)) using x x' k' unfolding True by auto
    next case False 
      { presume "k = {a..b} \<Longrightarrow> ?thesis" "k' = {a..b} \<Longrightarrow> ?thesis" 
        "k \<noteq> {a..b} \<Longrightarrow> k' \<noteq> {a..b} \<Longrightarrow> ?thesis"
        thus ?thesis by auto }
      { assume as':"k  = {a..b}" show ?thesis apply(rule q(5)) using x' k'(2) unfolding as' by auto }
      { assume as':"k' = {a..b}" show ?thesis apply(rule q(5)) using x  k'(2) unfolding as' by auto }
      assume as':"k \<noteq> {a..b}" "k' \<noteq> {a..b}"
      guess c using q(4)[OF x(2,1)] .. then guess d .. note c_d=this
      have "interior k  \<inter> interior {a..b} = {}" apply(rule q(5)) using x  k'(2) using as' by auto
      hence "interior k \<subseteq> interior x" apply-
        apply(rule interior_subset_union_intervals[OF c_d _ as(2) q(2)[OF x(2,1)]]) by auto moreover
      guess c using q(4)[OF x'(2,1)] .. then guess d .. note c_d=this
      have "interior k' \<inter> interior {a..b} = {}" apply(rule q(5)) using x' k'(2) using as' by auto
      hence "interior k' \<subseteq> interior x'" apply-
        apply(rule interior_subset_union_intervals[OF c_d _ as(2) q(2)[OF x'(2,1)]]) by auto
      ultimately show ?thesis using assm(5)[OF x(2) x'(2) False] by auto
    qed qed } qed

lemma elementary_unions_intervals:
  assumes "finite f" "\<And>s. s \<in> f \<Longrightarrow> \<exists>a b. s = {a..b::real^'n}"
  obtains p where "p division_of (\<Union>f)" proof-
  have "\<exists>p. p division_of (\<Union>f)" proof(induct_tac f rule:finite_subset_induct) 
    show "\<exists>p. p division_of \<Union>{}" using elementary_empty by auto
    fix x F assume as:"finite F" "x \<notin> F" "\<exists>p. p division_of \<Union>F" "x\<in>f"
    from this(3) guess p .. note p=this
    from assms(2)[OF as(4)] guess a .. then guess b .. note ab=this
    have *:"\<Union>F = \<Union>p" using division_ofD[OF p] by auto
    show "\<exists>p. p division_of \<Union>insert x F" using elementary_union_interval[OF p[unfolded *], of a b]
      unfolding Union_insert ab * by auto
  qed(insert assms,auto) thus ?thesis apply-apply(erule exE,rule that) by auto qed

lemma elementary_union: assumes "ps division_of s" "pt division_of (t::(real^'n) set)"
  obtains p where "p division_of (s \<union> t)"
proof- have "s \<union> t = \<Union>ps \<union> \<Union>pt" using assms unfolding division_of_def by auto
  hence *:"\<Union>(ps \<union> pt) = s \<union> t" by auto
  show ?thesis apply-apply(rule elementary_unions_intervals[of "ps\<union>pt"])
    unfolding * prefer 3 apply(rule_tac p=p in that)
    using assms[unfolded division_of_def] by auto qed

lemma partial_division_extend: fixes t::"(real^'n) set"
  assumes "p division_of s" "q division_of t" "s \<subseteq> t"
  obtains r where "p \<subseteq> r" "r division_of t" proof-
  note divp = division_ofD[OF assms(1)] and divq = division_ofD[OF assms(2)]
  obtain a b where ab:"t\<subseteq>{a..b}" using elementary_subset_interval[OF assms(2)] by auto
  guess r1 apply(rule partial_division_extend_interval) apply(rule assms(1)[unfolded divp(6)[THEN sym]])
    apply(rule subset_trans) by(rule ab assms[unfolded divp(6)[THEN sym]])+  note r1 = this division_ofD[OF this(2)]
  guess p' apply(rule elementary_unions_intervals[of "r1 - p"]) using r1(3,6) by auto 
  then obtain r2 where r2:"r2 division_of (\<Union>(r1 - p)) \<inter> (\<Union>q)" 
    apply- apply(drule elementary_inter[OF _ assms(2)[unfolded divq(6)[THEN sym]]]) by auto
  { fix x assume x:"x\<in>t" "x\<notin>s"
    hence "x\<in>\<Union>r1" unfolding r1 using ab by auto
    then guess r unfolding Union_iff .. note r=this moreover
    have "r \<notin> p" proof assume "r\<in>p" hence "x\<in>s" using divp(2) r by auto
      thus False using x by auto qed
    ultimately have "x\<in>\<Union>(r1 - p)" by auto }
  hence *:"t = \<Union>p \<union> (\<Union>(r1 - p) \<inter> \<Union>q)" unfolding divp divq using assms(3) by auto
  show ?thesis apply(rule that[of "p \<union> r2"]) unfolding * defer apply(rule division_disjoint_union)
    unfolding divp(6) apply(rule assms r2)+
  proof- have "interior s \<inter> interior (\<Union>(r1-p)) = {}"
    proof(rule inter_interior_unions_intervals)
      show "finite (r1 - p)" "open (interior s)" "\<forall>t\<in>r1-p. \<exists>a b. t = {a..b}" using r1 by auto
      have *:"\<And>s. (\<And>x. x \<in> s \<Longrightarrow> False) \<Longrightarrow> s = {}" by auto
      show "\<forall>t\<in>r1-p. interior s \<inter> interior t = {}" proof(rule)
        fix m x assume as:"m\<in>r1-p"
        have "interior m \<inter> interior (\<Union>p) = {}" proof(rule inter_interior_unions_intervals)
          show "finite p" "open (interior m)" "\<forall>t\<in>p. \<exists>a b. t = {a..b}" using divp by auto
          show "\<forall>t\<in>p. interior m \<inter> interior t = {}" apply(rule, rule r1(7)) using as using r1 by auto
        qed thus "interior s \<inter> interior m = {}" unfolding divp by auto
      qed qed        
    thus "interior s \<inter> interior (\<Union>(r1-p) \<inter> (\<Union>q)) = {}" using interior_subset by auto
  qed auto qed

subsection {* Tagged (partial) divisions. *}

definition tagged_partial_division_of (infixr "tagged'_partial'_division'_of" 40) where
  "(s tagged_partial_division_of i) \<equiv>
        finite s \<and>
        (\<forall>x k. (x,k) \<in> s \<longrightarrow> x \<in> k \<and> k \<subseteq> i \<and> (\<exists>a b. k = {a..b})) \<and>
        (\<forall>x1 k1 x2 k2. (x1,k1) \<in> s \<and> (x2,k2) \<in> s \<and> ((x1,k1) \<noteq> (x2,k2))
                       \<longrightarrow> (interior(k1) \<inter> interior(k2) = {}))"

lemma tagged_partial_division_ofD[dest]: assumes "s tagged_partial_division_of i"
  shows "finite s" "\<And>x k. (x,k) \<in> s \<Longrightarrow> x \<in> k" "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> i"
  "\<And>x k. (x,k) \<in> s \<Longrightarrow> \<exists>a b. k = {a..b}"
  "\<And>x1 k1 x2 k2. (x1,k1) \<in> s \<Longrightarrow> (x2,k2) \<in> s \<Longrightarrow> (x1,k1) \<noteq> (x2,k2) \<Longrightarrow> interior(k1) \<inter> interior(k2) = {}"
  using assms unfolding tagged_partial_division_of_def  apply- by blast+ 

definition tagged_division_of (infixr "tagged'_division'_of" 40) where
  "(s tagged_division_of i) \<equiv>
        (s tagged_partial_division_of i) \<and> (\<Union>{k. \<exists>x. (x,k) \<in> s} = i)"

lemma tagged_division_of_finite[dest]: "s tagged_division_of i \<Longrightarrow> finite s"
  unfolding tagged_division_of_def tagged_partial_division_of_def by auto

lemma tagged_division_of:
 "(s tagged_division_of i) \<longleftrightarrow>
        finite s \<and>
        (\<forall>x k. (x,k) \<in> s
               \<longrightarrow> x \<in> k \<and> k \<subseteq> i \<and> (\<exists>a b. k = {a..b})) \<and>
        (\<forall>x1 k1 x2 k2. (x1,k1) \<in> s \<and> (x2,k2) \<in> s \<and> ~((x1,k1) = (x2,k2))
                       \<longrightarrow> (interior(k1) \<inter> interior(k2) = {})) \<and>
        (\<Union>{k. \<exists>x. (x,k) \<in> s} = i)"
  unfolding tagged_division_of_def tagged_partial_division_of_def by auto

lemma tagged_division_ofI: assumes
  "finite s" "\<And>x k. (x,k) \<in> s \<Longrightarrow> x \<in> k" "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> i"  "\<And>x k. (x,k) \<in> s \<Longrightarrow> \<exists>a b. k = {a..b}"
  "\<And>x1 k1 x2 k2. (x1,k1) \<in> s \<Longrightarrow> (x2,k2) \<in> s \<Longrightarrow> ~((x1,k1) = (x2,k2)) \<Longrightarrow> (interior(k1) \<inter> interior(k2) = {})"
  "(\<Union>{k. \<exists>x. (x,k) \<in> s} = i)"
  shows "s tagged_division_of i"
  unfolding tagged_division_of apply(rule) defer apply rule
  apply(rule allI impI conjI assms)+ apply assumption
  apply(rule, rule assms, assumption) apply(rule assms, assumption)
  using assms(1,5-) apply- by blast+

lemma tagged_division_ofD[dest]: assumes "s tagged_division_of i"
  shows "finite s" "\<And>x k. (x,k) \<in> s \<Longrightarrow> x \<in> k" "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> i"  "\<And>x k. (x,k) \<in> s \<Longrightarrow> \<exists>a b. k = {a..b}"
  "\<And>x1 k1 x2 k2. (x1,k1) \<in> s \<Longrightarrow> (x2,k2) \<in> s \<Longrightarrow> ~((x1,k1) = (x2,k2)) \<Longrightarrow> (interior(k1) \<inter> interior(k2) = {})"
  "(\<Union>{k. \<exists>x. (x,k) \<in> s} = i)" using assms unfolding tagged_division_of apply- by blast+

lemma division_of_tagged_division: assumes"s tagged_division_of i"  shows "(snd ` s) division_of i"
proof(rule division_ofI) note assm=tagged_division_ofD[OF assms]
  show "\<Union>snd ` s = i" "finite (snd ` s)" using assm by auto
  fix k assume k:"k \<in> snd ` s" then obtain xk where xk:"(xk, k) \<in> s" by auto
  thus  "k \<subseteq> i" "k \<noteq> {}" "\<exists>a b. k = {a..b}" using assm apply- by fastsimp+
  fix k' assume k':"k' \<in> snd ` s" "k \<noteq> k'" from this(1) obtain xk' where xk':"(xk', k') \<in> s" by auto
  thus "interior k \<inter> interior k' = {}" apply-apply(rule assm(5)) apply(rule xk xk')+ using k' by auto
qed

lemma partial_division_of_tagged_division: assumes "s tagged_partial_division_of i"
  shows "(snd ` s) division_of \<Union>(snd ` s)"
proof(rule division_ofI) note assm=tagged_partial_division_ofD[OF assms]
  show "finite (snd ` s)" "\<Union>snd ` s = \<Union>snd ` s" using assm by auto
  fix k assume k:"k \<in> snd ` s" then obtain xk where xk:"(xk, k) \<in> s" by auto
  thus "k\<noteq>{}" "\<exists>a b. k = {a..b}" "k \<subseteq> \<Union>snd ` s" using assm by auto
  fix k' assume k':"k' \<in> snd ` s" "k \<noteq> k'" from this(1) obtain xk' where xk':"(xk', k') \<in> s" by auto
  thus "interior k \<inter> interior k' = {}" apply-apply(rule assm(5)) apply(rule xk xk')+ using k' by auto
qed

lemma tagged_partial_division_subset: assumes "s tagged_partial_division_of i" "t \<subseteq> s"
  shows "t tagged_partial_division_of i"
  using assms unfolding tagged_partial_division_of_def using finite_subset[OF assms(2)] by blast

lemma setsum_over_tagged_division_lemma: fixes d::"(real^'m) set \<Rightarrow> 'a::real_normed_vector"
  assumes "p tagged_division_of i" "\<And>u v. {u..v} \<noteq> {} \<Longrightarrow> content {u..v} = 0 \<Longrightarrow> d {u..v} = 0"
  shows "setsum (\<lambda>(x,k). d k) p = setsum d (snd ` p)"
proof- note assm=tagged_division_ofD[OF assms(1)]
  have *:"(\<lambda>(x,k). d k) = d \<circ> snd" unfolding o_def apply(rule ext) by auto
  show ?thesis unfolding * apply(subst eq_commute) proof(rule setsum_reindex_nonzero)
    show "finite p" using assm by auto
    fix x y assume as:"x\<in>p" "y\<in>p" "x\<noteq>y" "snd x = snd y" 
    obtain a b where ab:"snd x = {a..b}" using assm(4)[of "fst x" "snd x"] as(1) by auto
    have "(fst x, snd y) \<in> p" "(fst x, snd y) \<noteq> y" unfolding as(4)[THEN sym] using as(1-3) by auto
    hence "interior (snd x) \<inter> interior (snd y) = {}" apply-apply(rule assm(5)[of "fst x" _ "fst y"]) using as by auto 
    hence "content {a..b} = 0" unfolding as(4)[THEN sym] ab content_eq_0_interior by auto
    hence "d {a..b} = 0" apply-apply(rule assms(2)) using assm(2)[of "fst x" "snd x"] as(1) unfolding ab[THEN sym] by auto
    thus "d (snd x) = 0" unfolding ab by auto qed qed

lemma tag_in_interval: "p tagged_division_of i \<Longrightarrow> (x,k) \<in> p \<Longrightarrow> x \<in> i" by auto

lemma tagged_division_of_empty: "{} tagged_division_of {}"
  unfolding tagged_division_of by auto

lemma tagged_partial_division_of_trivial[simp]:
 "p tagged_partial_division_of {} \<longleftrightarrow> p = {}"
  unfolding tagged_partial_division_of_def by auto

lemma tagged_division_of_trivial[simp]:
 "p tagged_division_of {} \<longleftrightarrow> p = {}"
  unfolding tagged_division_of by auto

lemma tagged_division_of_self:
 "x \<in> {a..b} \<Longrightarrow> {(x,{a..b})} tagged_division_of {a..b}"
  apply(rule tagged_division_ofI) by auto

lemma tagged_division_union:
  assumes "p1 tagged_division_of s1"  "p2 tagged_division_of s2" "interior s1 \<inter> interior s2 = {}"
  shows "(p1 \<union> p2) tagged_division_of (s1 \<union> s2)"
proof(rule tagged_division_ofI) note p1=tagged_division_ofD[OF assms(1)] and p2=tagged_division_ofD[OF assms(2)]
  show "finite (p1 \<union> p2)" using p1(1) p2(1) by auto
  show "\<Union>{k. \<exists>x. (x, k) \<in> p1 \<union> p2} = s1 \<union> s2" using p1(6) p2(6) by blast
  fix x k assume xk:"(x,k)\<in>p1\<union>p2" show "x\<in>k" "\<exists>a b. k = {a..b}" using xk p1(2,4) p2(2,4) by auto
  show "k\<subseteq>s1\<union>s2" using xk p1(3) p2(3) by blast
  fix x' k' assume xk':"(x',k')\<in>p1\<union>p2" "(x,k) \<noteq> (x',k')"
  have *:"\<And>a b. a\<subseteq> s1 \<Longrightarrow> b\<subseteq> s2 \<Longrightarrow> interior a \<inter> interior b = {}" using assms(3) subset_interior by blast
  show "interior k \<inter> interior k' = {}" apply(cases "(x,k)\<in>p1", case_tac[!] "(x',k')\<in>p1")
    apply(rule p1(5)) prefer 4 apply(rule *) prefer 6 apply(subst Int_commute,rule *) prefer 8 apply(rule p2(5))
    using p1(3) p2(3) using xk xk' by auto qed 

lemma tagged_division_unions:
  assumes "finite iset" "\<forall>i\<in>iset. (pfn(i) tagged_division_of i)"
  "\<forall>i1 \<in> iset. \<forall>i2 \<in> iset. ~(i1 = i2) \<longrightarrow> (interior(i1) \<inter> interior(i2) = {})"
  shows "\<Union>(pfn ` iset) tagged_division_of (\<Union>iset)"
proof(rule tagged_division_ofI)
  note assm = tagged_division_ofD[OF assms(2)[rule_format]]
  show "finite (\<Union>pfn ` iset)" apply(rule finite_Union) using assms by auto
  have "\<Union>{k. \<exists>x. (x, k) \<in> \<Union>pfn ` iset} = \<Union>(\<lambda>i. \<Union>{k. \<exists>x. (x, k) \<in> pfn i}) ` iset" by blast 
  also have "\<dots> = \<Union>iset" using assm(6) by auto
  finally show "\<Union>{k. \<exists>x. (x, k) \<in> \<Union>pfn ` iset} = \<Union>iset" . 
  fix x k assume xk:"(x,k)\<in>\<Union>pfn ` iset" then obtain i where i:"i \<in> iset" "(x, k) \<in> pfn i" by auto
  show "x\<in>k" "\<exists>a b. k = {a..b}" "k \<subseteq> \<Union>iset" using assm(2-4)[OF i] using i(1) by auto
  fix x' k' assume xk':"(x',k')\<in>\<Union>pfn ` iset" "(x, k) \<noteq> (x', k')" then obtain i' where i':"i' \<in> iset" "(x', k') \<in> pfn i'" by auto
  have *:"\<And>a b. i\<noteq>i' \<Longrightarrow> a\<subseteq> i \<Longrightarrow> b\<subseteq> i' \<Longrightarrow> interior a \<inter> interior b = {}" using i(1) i'(1)
    using assms(3)[rule_format] subset_interior by blast
  show "interior k \<inter> interior k' = {}" apply(cases "i=i'")
    using assm(5)[OF i _ xk'(2)]  i'(2) using assm(3)[OF i] assm(3)[OF i'] defer apply-apply(rule *) by auto
qed

lemma tagged_partial_division_of_union_self:
  assumes "p tagged_partial_division_of s" shows "p tagged_division_of (\<Union>(snd ` p))"
  apply(rule tagged_division_ofI) using tagged_partial_division_ofD[OF assms] by auto

lemma tagged_division_of_union_self: assumes "p tagged_division_of s"
  shows "p tagged_division_of (\<Union>(snd ` p))"
  apply(rule tagged_division_ofI) using tagged_division_ofD[OF assms] by auto

subsection {* Fine-ness of a partition w.r.t. a gauge. *}

definition fine (infixr "fine" 46) where
  "d fine s \<longleftrightarrow> (\<forall>(x,k) \<in> s. k \<subseteq> d(x))"

lemma fineI: assumes "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> d x"
  shows "d fine s" using assms unfolding fine_def by auto

lemma fineD[dest]: assumes "d fine s"
  shows "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> d x" using assms unfolding fine_def by auto

lemma fine_inter: "(\<lambda>x. d1 x \<inter> d2 x) fine p \<longleftrightarrow> d1 fine p \<and> d2 fine p"
  unfolding fine_def by auto

lemma fine_inters:
 "(\<lambda>x. \<Inter> {f d x | d.  d \<in> s}) fine p \<longleftrightarrow> (\<forall>d\<in>s. (f d) fine p)"
  unfolding fine_def by blast

lemma fine_union:
  "d fine p1 \<Longrightarrow> d fine p2 \<Longrightarrow> d fine (p1 \<union> p2)"
  unfolding fine_def by blast

lemma fine_unions:"(\<And>p. p \<in> ps \<Longrightarrow> d fine p) \<Longrightarrow> d fine (\<Union>ps)"
  unfolding fine_def by auto

lemma fine_subset:  "p \<subseteq> q \<Longrightarrow> d fine q \<Longrightarrow> d fine p"
  unfolding fine_def by blast

subsection {* Gauge integral. Define on compact intervals first, then use a limit. *}

definition has_integral_compact_interval (infixr "has'_integral'_compact'_interval" 46) where
  "(f has_integral_compact_interval y) i \<equiv>
        (\<forall>e>0. \<exists>d. gauge d \<and>
          (\<forall>p. p tagged_division_of i \<and> d fine p
                        \<longrightarrow> norm(setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - y) < e))"

definition has_integral (infixr "has'_integral" 46) where 
"((f::(real^'n \<Rightarrow> 'b::real_normed_vector)) has_integral y) i \<equiv>
        if (\<exists>a b. i = {a..b}) then (f has_integral_compact_interval y) i
        else (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> {a..b}
              \<longrightarrow> (\<exists>z. ((\<lambda>x. if x \<in> i then f x else 0) has_integral_compact_interval z) {a..b} \<and>
                                       norm(z - y) < e))"

lemma has_integral:
 "(f has_integral y) ({a..b}) \<longleftrightarrow>
        (\<forall>e>0. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a..b} \<and> d fine p
                        \<longrightarrow> norm(setsum (\<lambda>(x,k). content(k) *\<^sub>R f x) p - y) < e))"
  unfolding has_integral_def has_integral_compact_interval_def by auto

lemma has_integralD[dest]: assumes
 "(f has_integral y) ({a..b})" "e>0"
  obtains d where "gauge d" "\<And>p. p tagged_division_of {a..b} \<Longrightarrow> d fine p
                        \<Longrightarrow> norm(setsum (\<lambda>(x,k). content(k) *\<^sub>R f(x)) p - y) < e"
  using assms unfolding has_integral by auto

lemma has_integral_alt:
 "(f has_integral y) i \<longleftrightarrow>
      (if (\<exists>a b. i = {a..b}) then (f has_integral y) i
       else (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> {a..b}
                               \<longrightarrow> (\<exists>z. ((\<lambda>x. if x \<in> i then f(x) else 0)
                                        has_integral z) ({a..b}) \<and>
                                       norm(z - y) < e)))"
  unfolding has_integral unfolding has_integral_compact_interval_def has_integral_def by auto

lemma has_integral_altD:
  assumes "(f has_integral y) i" "\<not> (\<exists>a b. i = {a..b})" "e>0"
  obtains B where "B>0" "\<forall>a b. ball 0 B \<subseteq> {a..b}\<longrightarrow> (\<exists>z. ((\<lambda>x. if x \<in> i then f(x) else 0) has_integral z) ({a..b}) \<and> norm(z - y) < e)"
  using assms unfolding has_integral unfolding has_integral_compact_interval_def has_integral_def by auto

definition integrable_on (infixr "integrable'_on" 46) where
  "(f integrable_on i) \<equiv> \<exists>y. (f has_integral y) i"

definition "integral i f \<equiv> SOME y. (f has_integral y) i"

lemma integrable_integral[dest]:
 "f integrable_on i \<Longrightarrow> (f has_integral (integral i f)) i"
  unfolding integrable_on_def integral_def by(rule someI_ex)

lemma has_integral_integrable[intro]: "(f has_integral i) s \<Longrightarrow> f integrable_on s"
  unfolding integrable_on_def by auto

lemma has_integral_integral:"f integrable_on s \<longleftrightarrow> (f has_integral (integral s f)) s"
  by auto

lemma has_integral_vec1: assumes "(f has_integral k) {a..b}"
  shows "((\<lambda>x. vec1 (f x)) has_integral (vec1 k)) {a..b}"
proof- have *:"\<And>p. (\<Sum>(x, k)\<in>p. content k *\<^sub>R vec1 (f x)) - vec1 k = vec1 ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - k)"
    unfolding vec_sub Cart_eq by(auto simp add:vec1_dest_vec1_simps split_beta)
  show ?thesis using assms unfolding has_integral apply safe
    apply(erule_tac x=e in allE,safe) apply(rule_tac x=d in exI,safe)
    apply(erule_tac x=p in allE,safe) unfolding * norm_vector_1 by auto qed

lemma setsum_content_null:
  assumes "content({a..b}) = 0" "p tagged_division_of {a..b}"
  shows "setsum (\<lambda>(x,k). content k *\<^sub>R f x) p = (0::'a::real_normed_vector)"
proof(rule setsum_0',rule) fix y assume y:"y\<in>p"
  obtain x k where xk:"y = (x,k)" using surj_pair[of y] by blast
  note assm = tagged_division_ofD(3-4)[OF assms(2) y[unfolded xk]]
  from this(2) guess c .. then guess d .. note c_d=this
  have "(\<lambda>(x, k). content k *\<^sub>R f x) y = content k *\<^sub>R f x" unfolding xk by auto
  also have "\<dots> = 0" using content_subset[OF assm(1)[unfolded c_d]] content_pos_le[of c d]
    unfolding assms(1) c_d by auto
  finally show "(\<lambda>(x, k). content k *\<^sub>R f x) y = 0" .
qed

subsection {* Some basic combining lemmas. *}

lemma tagged_division_unions_exists:
  assumes "finite iset" "\<forall>i \<in> iset. \<exists>p. p tagged_division_of i \<and> d fine p"
  "\<forall>i1\<in>iset. \<forall>i2\<in>iset. ~(i1 = i2) \<longrightarrow> (interior(i1) \<inter> interior(i2) = {})" "(\<Union>iset = i)"
   obtains p where "p tagged_division_of i" "d fine p"
proof- guess pfn using bchoice[OF assms(2)] .. note pfn = conjunctD2[OF this[rule_format]]
  show thesis apply(rule_tac p="\<Union>(pfn ` iset)" in that) unfolding assms(4)[THEN sym]
    apply(rule tagged_division_unions[OF assms(1) _ assms(3)]) defer 
    apply(rule fine_unions) using pfn by auto
qed

subsection {* The set we're concerned with must be closed. *}

lemma division_of_closed: "s division_of i \<Longrightarrow> closed (i::(real^'n) set)"
  unfolding division_of_def by(fastsimp intro!: closed_Union closed_interval)

subsection {* General bisection principle for intervals; might be useful elsewhere. *}

lemma interval_bisection_step:
  assumes "P {}" "(\<forall>s t. P s \<and> P t \<and> interior(s) \<inter> interior(t) = {} \<longrightarrow> P(s \<union> t))" "~(P {a..b::real^'n})"
  obtains c d where "~(P{c..d})"
  "\<forall>i. a$i \<le> c$i \<and> c$i \<le> d$i \<and> d$i \<le> b$i \<and> 2 * (d$i - c$i) \<le> b$i - a$i"
proof- have "{a..b} \<noteq> {}" using assms(1,3) by auto
  note ab=this[unfolded interval_eq_empty not_ex not_less]
  { fix f have "finite f \<Longrightarrow>
        (\<forall>s\<in>f. P s) \<Longrightarrow>
        (\<forall>s\<in>f. \<exists>a b. s = {a..b}) \<Longrightarrow>
        (\<forall>s\<in>f.\<forall>t\<in>f. ~(s = t) \<longrightarrow> interior(s) \<inter> interior(t) = {}) \<Longrightarrow> P(\<Union>f)"
    proof(induct f rule:finite_induct)
      case empty show ?case using assms(1) by auto
    next case (insert x f) show ?case unfolding Union_insert apply(rule assms(2)[rule_format])
        apply rule defer apply rule defer apply(rule inter_interior_unions_intervals)
        using insert by auto
    qed } note * = this
  let ?A = "{{c..d} | c d. \<forall>i. (c$i = a$i) \<and> (d$i = (a$i + b$i) / 2) \<or> (c$i = (a$i + b$i) / 2) \<and> (d$i = b$i)}"
  let ?PP = "\<lambda>c d. \<forall>i. a$i \<le> c$i \<and> c$i \<le> d$i \<and> d$i \<le> b$i \<and> 2 * (d$i - c$i) \<le> b$i - a$i"
  { presume "\<forall>c d. ?PP c d \<longrightarrow> P {c..d} \<Longrightarrow> False"
    thus thesis unfolding atomize_not not_all apply-apply(erule exE)+ apply(rule_tac c=x and d=xa in that) by auto }
  assume as:"\<forall>c d. ?PP c d \<longrightarrow> P {c..d}"
  have "P (\<Union> ?A)" proof(rule *, rule_tac[2-] ballI, rule_tac[4] ballI, rule_tac[4] impI) 
    let ?B = "(\<lambda>s.{(\<chi> i. if i \<in> s then a$i else (a$i + b$i) / 2) ..
      (\<chi> i. if i \<in> s then (a$i + b$i) / 2 else b$i)}) ` {s. s \<subseteq> UNIV}"
    have "?A \<subseteq> ?B" proof case goal1
      then guess c unfolding mem_Collect_eq .. then guess d apply- by(erule exE,(erule conjE)+) note c_d=this[rule_format]
      have *:"\<And>a b c d. a = c \<Longrightarrow> b = d \<Longrightarrow> {a..b} = {c..d}" by auto
      show "x\<in>?B" unfolding image_iff apply(rule_tac x="{i. c$i = a$i}" in bexI)
        unfolding c_d apply(rule * ) unfolding Cart_eq cond_component Cart_lambda_beta
      proof(rule_tac[1-2] allI) fix i show "c $ i = (if i \<in> {i. c $ i = a $ i} then a $ i else (a $ i + b $ i) / 2)"
          "d $ i = (if i \<in> {i. c $ i = a $ i} then (a $ i + b $ i) / 2 else b $ i)"
          using c_d(2)[of i] ab[THEN spec[where x=i]] by(auto simp add:field_simps)
      qed auto qed
    thus "finite ?A" apply(rule finite_subset[of _ ?B]) by auto
    fix s assume "s\<in>?A" then guess c unfolding mem_Collect_eq .. then guess d apply- by(erule exE,(erule conjE)+)
    note c_d=this[rule_format]
    show "P s" unfolding c_d apply(rule as[rule_format]) proof- case goal1 show ?case 
        using c_d(2)[of i] using ab[THEN spec[where x=i]] by auto qed
    show "\<exists>a b. s = {a..b}" unfolding c_d by auto
    fix t assume "t\<in>?A" then guess e unfolding mem_Collect_eq .. then guess f apply- by(erule exE,(erule conjE)+)
    note e_f=this[rule_format]
    assume "s \<noteq> t" hence "\<not> (c = e \<and> d = f)" unfolding c_d e_f by auto
    then obtain i where "c$i \<noteq> e$i \<or> d$i \<noteq> f$i" unfolding de_Morgan_conj Cart_eq by auto
    hence i:"c$i \<noteq> e$i" "d$i \<noteq> f$i" apply- apply(erule_tac[!] disjE)
    proof- assume "c$i \<noteq> e$i" thus "d$i \<noteq> f$i" using c_d(2)[of i] e_f(2)[of i] by fastsimp
    next   assume "d$i \<noteq> f$i" thus "c$i \<noteq> e$i" using c_d(2)[of i] e_f(2)[of i] by fastsimp
    qed have *:"\<And>s t. (\<And>a. a\<in>s \<Longrightarrow> a\<in>t \<Longrightarrow> False) \<Longrightarrow> s \<inter> t = {}" by auto
    show "interior s \<inter> interior t = {}" unfolding e_f c_d interior_closed_interval proof(rule *)
      fix x assume "x\<in>{c<..<d}" "x\<in>{e<..<f}"
      hence x:"c$i < d$i" "e$i < f$i" "c$i < f$i" "e$i < d$i" unfolding mem_interval apply-apply(erule_tac[!] x=i in allE)+ by auto
      show False using c_d(2)[of i] apply- apply(erule_tac disjE)
      proof(erule_tac[!] conjE) assume as:"c $ i = a $ i" "d $ i = (a $ i + b $ i) / 2"
        show False using e_f(2)[of i] and i x unfolding as by(fastsimp simp add:field_simps)
      next assume as:"c $ i = (a $ i + b $ i) / 2" "d $ i = b $ i"
        show False using e_f(2)[of i] and i x unfolding as by(fastsimp simp add:field_simps)
      qed qed qed
  also have "\<Union> ?A = {a..b}" proof(rule set_ext,rule)
    fix x assume "x\<in>\<Union>?A" then guess Y unfolding Union_iff ..
    from this(1) guess c unfolding mem_Collect_eq .. then guess d ..
    note c_d = this[THEN conjunct2,rule_format] `x\<in>Y`[unfolded this[THEN conjunct1]]
    show "x\<in>{a..b}" unfolding mem_interval proof 
      fix i show "a $ i \<le> x $ i \<and> x $ i \<le> b $ i"
        using c_d(1)[of i] c_d(2)[unfolded mem_interval,THEN spec[where x=i]] by auto qed
  next fix x assume x:"x\<in>{a..b}"
    have "\<forall>i. \<exists>c d. (c = a$i \<and> d = (a$i + b$i) / 2 \<or> c = (a$i + b$i) / 2 \<and> d = b$i) \<and> c\<le>x$i \<and> x$i \<le> d"
      (is "\<forall>i. \<exists>c d. ?P i c d") unfolding mem_interval proof fix i
      have "?P i (a$i) ((a $ i + b $ i) / 2) \<or> ?P i ((a $ i + b $ i) / 2) (b$i)"
        using x[unfolded mem_interval,THEN spec[where x=i]] by auto thus "\<exists>c d. ?P i c d" by blast
    qed thus "x\<in>\<Union>?A" unfolding Union_iff lambda_skolem unfolding Bex_def mem_Collect_eq
      apply-apply(erule exE)+ apply(rule_tac x="{xa..xaa}" in exI) unfolding mem_interval by auto
  qed finally show False using assms by auto qed

lemma interval_bisection:
  assumes "P {}" "(\<forall>s t. P s \<and> P t \<and> interior(s) \<inter> interior(t) = {} \<longrightarrow> P(s \<union> t))" "\<not> P {a..b::real^'n}"
  obtains x where "x \<in> {a..b}" "\<forall>e>0. \<exists>c d. x \<in> {c..d} \<and> {c..d} \<subseteq> ball x e \<and> {c..d} \<subseteq> {a..b} \<and> ~P({c..d})"
proof-
  have "\<forall>x. \<exists>y. \<not> P {fst x..snd x} \<longrightarrow> (\<not> P {fst y..snd y} \<and> (\<forall>i. fst x$i \<le> fst y$i \<and> fst y$i \<le> snd y$i \<and> snd y$i \<le> snd x$i \<and>
                           2 * (snd y$i - fst y$i) \<le> snd x$i - fst x$i))" proof case goal1 thus ?case proof-
      presume "\<not> P {fst x..snd x} \<Longrightarrow> ?thesis"
      thus ?thesis apply(cases "P {fst x..snd x}") by auto
    next assume as:"\<not> P {fst x..snd x}" from interval_bisection_step[of P, OF assms(1-2) as] guess c d . 
      thus ?thesis apply- apply(rule_tac x="(c,d)" in exI) by auto
    qed qed then guess f apply-apply(drule choice) by(erule exE) note f=this
  def AB \<equiv> "\<lambda>n. (f ^^ n) (a,b)" def A \<equiv> "\<lambda>n. fst(AB n)" and B \<equiv> "\<lambda>n. snd(AB n)" note ab_def = this AB_def
  have "A 0 = a" "B 0 = b" "\<And>n. \<not> P {A(Suc n)..B(Suc n)} \<and>
    (\<forall>i. A(n)$i \<le> A(Suc n)$i \<and> A(Suc n)$i \<le> B(Suc n)$i \<and> B(Suc n)$i \<le> B(n)$i \<and> 
    2 * (B(Suc n)$i - A(Suc n)$i) \<le> B(n)$i - A(n)$i)" (is "\<And>n. ?P n")
  proof- show "A 0 = a" "B 0 = b" unfolding ab_def by auto
    case goal3 note S = ab_def funpow.simps o_def id_apply show ?case
    proof(induct n) case 0 thus ?case unfolding S apply(rule f[rule_format]) using assms(3) by auto
    next case (Suc n) show ?case unfolding S apply(rule f[rule_format]) using Suc unfolding S by auto
    qed qed note AB = this(1-2) conjunctD2[OF this(3),rule_format]

  have interv:"\<And>e. 0 < e \<Longrightarrow> \<exists>n. \<forall>x\<in>{A n..B n}. \<forall>y\<in>{A n..B n}. dist x y < e"
  proof- case goal1 guess n using real_arch_pow2[of "(setsum (\<lambda>i. b$i - a$i) UNIV) / e"] .. note n=this
    show ?case apply(rule_tac x=n in exI) proof(rule,rule)
      fix x y assume xy:"x\<in>{A n..B n}" "y\<in>{A n..B n}"
      have "dist x y \<le> setsum (\<lambda>i. abs((x - y)$i)) UNIV" unfolding vector_dist_norm by(rule norm_le_l1)
      also have "\<dots> \<le> setsum (\<lambda>i. B n$i - A n$i) UNIV"
      proof(rule setsum_mono) fix i show "\<bar>(x - y) $ i\<bar> \<le> B n $ i - A n $ i"
          using xy[unfolded mem_interval,THEN spec[where x=i]]
          unfolding vector_minus_component by auto qed
      also have "\<dots> \<le> setsum (\<lambda>i. b$i - a$i) UNIV / 2^n" unfolding setsum_divide_distrib
      proof(rule setsum_mono) case goal1 thus ?case
        proof(induct n) case 0 thus ?case unfolding AB by auto
        next case (Suc n) have "B (Suc n) $ i - A (Suc n) $ i \<le> (B n $ i - A n $ i) / 2" using AB(4)[of n i] by auto
          also have "\<dots> \<le> (b $ i - a $ i) / 2 ^ Suc n" using Suc by(auto simp add:field_simps) finally show ?case .
        qed qed
      also have "\<dots> < e" using n using goal1 by(auto simp add:field_simps) finally show "dist x y < e" .
    qed qed
  { fix n m ::nat assume "m \<le> n" then guess d unfolding le_Suc_ex_iff .. note d=this
    have "{A n..B n} \<subseteq> {A m..B m}" unfolding d 
    proof(induct d) case 0 thus ?case by auto
    next case (Suc d) show ?case apply(rule subset_trans[OF _ Suc])
        apply(rule) unfolding mem_interval apply(rule,erule_tac x=i in allE)
      proof- case goal1 thus ?case using AB(4)[of "m + d" i] by(auto simp add:field_simps)
      qed qed } note ABsubset = this 
  have "\<exists>a. \<forall>n. a\<in>{A n..B n}" apply(rule decreasing_closed_nest[rule_format,OF closed_interval _ ABsubset interv])
  proof- fix n show "{A n..B n} \<noteq> {}" apply(cases "0<n") using AB(3)[of "n - 1"] assms(1,3) AB(1-2) by auto qed auto
  then guess x0 .. note x0=this[rule_format]
  show thesis proof(rule that[rule_format,of x0])
    show "x0\<in>{a..b}" using x0[of 0] unfolding AB .
    fix e assume "0 < (e::real)" from interv[OF this] guess n .. note n=this
    show "\<exists>c d. x0 \<in> {c..d} \<and> {c..d} \<subseteq> ball x0 e \<and> {c..d} \<subseteq> {a..b} \<and> \<not> P {c..d}"
      apply(rule_tac x="A n" in exI,rule_tac x="B n" in exI) apply(rule,rule x0) apply rule defer 
    proof show "\<not> P {A n..B n}" apply(cases "0<n") using AB(3)[of "n - 1"] assms(3) AB(1-2) by auto
      show "{A n..B n} \<subseteq> ball x0 e" using n using x0[of n] by auto
      show "{A n..B n} \<subseteq> {a..b}" unfolding AB(1-2)[symmetric] apply(rule ABsubset) by auto
    qed qed qed 

subsection {* Cousin's lemma. *}

lemma fine_division_exists: assumes "gauge g" 
  obtains p where "p tagged_division_of {a..b::real^'n}" "g fine p"
proof- presume "\<not> (\<exists>p. p tagged_division_of {a..b} \<and> g fine p) \<Longrightarrow> False"
  then guess p unfolding atomize_not not_not .. thus thesis apply-apply(rule that[of p]) by auto
next assume as:"\<not> (\<exists>p. p tagged_division_of {a..b} \<and> g fine p)"
  guess x apply(rule interval_bisection[of "\<lambda>s. \<exists>p. p tagged_division_of s \<and> g fine p",rule_format,OF _ _ as])
    apply(rule_tac x="{}" in exI) defer apply(erule conjE exE)+
  proof- show "{} tagged_division_of {} \<and> g fine {}" unfolding fine_def by auto
    fix s t p p' assume "p tagged_division_of s" "g fine p" "p' tagged_division_of t" "g fine p'" "interior s \<inter> interior t = {}"
    thus "\<exists>p. p tagged_division_of s \<union> t \<and> g fine p" apply-apply(rule_tac x="p \<union> p'" in exI) apply rule
      apply(rule tagged_division_union) prefer 4 apply(rule fine_union) by auto
  qed note x=this
  obtain e where e:"e>0" "ball x e \<subseteq> g x" using gaugeD[OF assms, of x] unfolding open_contains_ball by auto
  from x(2)[OF e(1)] guess c d apply-apply(erule exE conjE)+ . note c_d = this
  have "g fine {(x, {c..d})}" unfolding fine_def using e using c_d(2) by auto
  thus False using tagged_division_of_self[OF c_d(1)] using c_d by auto qed

subsection {* Basic theorems about integrals. *}

lemma has_integral_unique: fixes f::"real^'n \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral k1) i" "(f has_integral k2) i" shows "k1 = k2"
proof(rule ccontr) let ?e = "norm(k1 - k2) / 2" assume as:"k1 \<noteq> k2" hence e:"?e > 0" by auto
  have lem:"\<And>f::real^'n \<Rightarrow> 'a.  \<And> a b k1 k2.
    (f has_integral k1) ({a..b}) \<Longrightarrow> (f has_integral k2) ({a..b}) \<Longrightarrow> k1 \<noteq> k2 \<Longrightarrow> False"
  proof- case goal1 let ?e = "norm(k1 - k2) / 2" from goal1(3) have e:"?e > 0" by auto
    guess d1 by(rule has_integralD[OF goal1(1) e]) note d1=this
    guess d2 by(rule has_integralD[OF goal1(2) e]) note d2=this
    guess p by(rule fine_division_exists[OF gauge_inter[OF d1(1) d2(1)],of a b]) note p=this
    let ?c = "(\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)" have "norm (k1 - k2) \<le> norm (?c - k2) + norm (?c - k1)"
      using norm_triangle_ineq4[of "k1 - ?c" "k2 - ?c"] by(auto simp add:group_simps norm_minus_commute)
    also have "\<dots> < norm (k1 - k2) / 2 + norm (k1 - k2) / 2"
      apply(rule add_strict_mono) apply(rule_tac[!] d2(2) d1(2)) using p unfolding fine_def by auto
    finally show False by auto
  qed { presume "\<not> (\<exists>a b. i = {a..b}) \<Longrightarrow> False"
    thus False apply-apply(cases "\<exists>a b. i = {a..b}")
      using assms by(auto simp add:has_integral intro:lem[OF _ _ as]) }
  assume as:"\<not> (\<exists>a b. i = {a..b})"
  guess B1 by(rule has_integral_altD[OF assms(1) as,OF e]) note B1=this[rule_format]
  guess B2 by(rule has_integral_altD[OF assms(2) as,OF e]) note B2=this[rule_format]
  have "\<exists>a b::real^'n. ball 0 B1 \<union> ball 0 B2 \<subseteq> {a..b}" apply(rule bounded_subset_closed_interval)
    using bounded_Un bounded_ball by auto then guess a b apply-by(erule exE)+
  note ab=conjunctD2[OF this[unfolded Un_subset_iff]]
  guess w using B1(2)[OF ab(1)] .. note w=conjunctD2[OF this]
  guess z using B2(2)[OF ab(2)] .. note z=conjunctD2[OF this]
  have "z = w" using lem[OF w(1) z(1)] by auto
  hence "norm (k1 - k2) \<le> norm (z - k2) + norm (w - k1)"
    using norm_triangle_ineq4[of "k1 - w" "k2 - z"] by(auto simp add: norm_minus_commute) 
  also have "\<dots> < norm (k1 - k2) / 2 + norm (k1 - k2) / 2" apply(rule add_strict_mono) by(rule_tac[!] z(2) w(2))
  finally show False by auto qed

lemma integral_unique[intro]:
  "(f has_integral y) k \<Longrightarrow> integral k f = y"
  unfolding integral_def apply(rule some_equality) by(auto intro: has_integral_unique) 

lemma has_integral_is_0: fixes f::"real^'n \<Rightarrow> 'a::real_normed_vector" 
  assumes "\<forall>x\<in>s. f x = 0" shows "(f has_integral 0) s"
proof- have lem:"\<And>a b. \<And>f::real^'n \<Rightarrow> 'a.
    (\<forall>x\<in>{a..b}. f(x) = 0) \<Longrightarrow> (f has_integral 0) ({a..b})" unfolding has_integral
  proof(rule,rule) fix a b e and f::"real^'n \<Rightarrow> 'a"
    assume as:"\<forall>x\<in>{a..b}. f x = 0" "0 < (e::real)"
    show "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a..b} \<and> d fine p \<longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) < e)"
      apply(rule_tac x="\<lambda>x. ball x 1" in exI)  apply(rule,rule gaugeI) unfolding centre_in_ball defer apply(rule open_ball)
    proof(rule,rule,erule conjE) case goal1
      have "(\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) = 0" proof(rule setsum_0',rule)
        fix x assume x:"x\<in>p" have "f (fst x) = 0" using tagged_division_ofD(2-3)[OF goal1(1), of "fst x" "snd x"] using as x by auto
        thus "(\<lambda>(x, k). content k *\<^sub>R f x) x = 0" apply(subst surjective_pairing[of x]) unfolding split_conv by auto
      qed thus ?case using as by auto
    qed auto qed  { presume "\<not> (\<exists>a b. s = {a..b}) \<Longrightarrow> ?thesis"
    thus ?thesis apply-apply(cases "\<exists>a b. s = {a..b}")
      using assms by(auto simp add:has_integral intro:lem) }
  have *:"(\<lambda>x. if x \<in> s then f x else 0) = (\<lambda>x. 0)" apply(rule ext) using assms by auto
  assume "\<not> (\<exists>a b. s = {a..b})" thus ?thesis apply(subst has_integral_alt) unfolding if_not_P *
  apply(rule,rule,rule_tac x=1 in exI,rule) defer apply(rule,rule,rule)
  proof- fix e::real and a b assume "e>0"
    thus "\<exists>z. ((\<lambda>x::real^'n. 0::'a) has_integral z) {a..b} \<and> norm (z - 0) < e"
      apply(rule_tac x=0 in exI) apply(rule,rule lem) by auto
  qed auto qed

lemma has_integral_0[simp]: "((\<lambda>x::real^'n. 0) has_integral 0) s"
  apply(rule has_integral_is_0) by auto 

lemma has_integral_0_eq[simp]: "((\<lambda>x. 0) has_integral i) s \<longleftrightarrow> i = 0"
  using has_integral_unique[OF has_integral_0] by auto

lemma has_integral_linear: fixes f::"real^'n \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral y) s" "bounded_linear h" shows "((h o f) has_integral ((h y))) s"
proof- interpret bounded_linear h using assms(2) . from pos_bounded guess B .. note B=conjunctD2[OF this,rule_format]
  have lem:"\<And>f::real^'n \<Rightarrow> 'a. \<And> y a b.
    (f has_integral y) ({a..b}) \<Longrightarrow> ((h o f) has_integral h(y)) ({a..b})"
  proof(subst has_integral,rule,rule) case goal1
    from pos_bounded guess B .. note B=conjunctD2[OF this,rule_format]
    have *:"e / B > 0" apply(rule divide_pos_pos) using goal1(2) B by auto
    guess g using has_integralD[OF goal1(1) *] . note g=this
    show ?case apply(rule_tac x=g in exI) apply(rule,rule g(1))
    proof(rule,rule,erule conjE) fix p assume as:"p tagged_division_of {a..b}" "g fine p" 
      have *:"\<And>x k. h ((\<lambda>(x, k). content k *\<^sub>R f x) x) = (\<lambda>(x, k). h (content k *\<^sub>R f x)) x" by auto
      have "(\<Sum>(x, k)\<in>p. content k *\<^sub>R (h \<circ> f) x) = setsum (h \<circ> (\<lambda>(x, k). content k *\<^sub>R f x)) p"
        unfolding o_def unfolding scaleR[THEN sym] * by simp
      also have "\<dots> = h (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)" using setsum[of "\<lambda>(x,k). content k *\<^sub>R f x" p] using as by auto
      finally have *:"(\<Sum>(x, k)\<in>p. content k *\<^sub>R (h \<circ> f) x) = h (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)" .
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R (h \<circ> f) x) - h y) < e" unfolding * diff[THEN sym]
        apply(rule le_less_trans[OF B(2)]) using g(2)[OF as] B(1) by(auto simp add:field_simps)
    qed qed { presume "\<not> (\<exists>a b. s = {a..b}) \<Longrightarrow> ?thesis"
    thus ?thesis apply-apply(cases "\<exists>a b. s = {a..b}") using assms by(auto simp add:has_integral intro!:lem) }
  assume as:"\<not> (\<exists>a b. s = {a..b})" thus ?thesis apply(subst has_integral_alt) unfolding if_not_P
  proof(rule,rule) fix e::real  assume e:"0<e"
    have *:"0 < e/B" by(rule divide_pos_pos,rule e,rule B(1))
    guess M using has_integral_altD[OF assms(1) as *,rule_format] . note M=this
    show "\<exists>B>0. \<forall>a b. ball 0 B \<subseteq> {a..b} \<longrightarrow> (\<exists>z. ((\<lambda>x. if x \<in> s then (h \<circ> f) x else 0) has_integral z) {a..b} \<and> norm (z - h y) < e)"
      apply(rule_tac x=M in exI) apply(rule,rule M(1))
    proof(rule,rule,rule) case goal1 guess z using M(2)[OF goal1(1)] .. note z=conjunctD2[OF this]
      have *:"(\<lambda>x. if x \<in> s then (h \<circ> f) x else 0) = h \<circ> (\<lambda>x. if x \<in> s then f x else 0)"
        unfolding o_def apply(rule ext) using zero by auto
      show ?case apply(rule_tac x="h z" in exI,rule) unfolding * apply(rule lem[OF z(1)]) unfolding diff[THEN sym]
        apply(rule le_less_trans[OF B(2)]) using B(1) z(2) by(auto simp add:field_simps)
    qed qed qed

lemma has_integral_cmul:
  shows "(f has_integral k) s \<Longrightarrow> ((\<lambda>x. c *\<^sub>R f x) has_integral (c *\<^sub>R k)) s"
  unfolding o_def[THEN sym] apply(rule has_integral_linear,assumption)
  by(rule scaleR.bounded_linear_right)

lemma has_integral_neg:
  shows "(f has_integral k) s \<Longrightarrow> ((\<lambda>x. -(f x)) has_integral (-k)) s"
  apply(drule_tac c="-1" in has_integral_cmul) by auto

lemma has_integral_add: fixes f::"real^'n \<Rightarrow> 'a::real_normed_vector" 
  assumes "(f has_integral k) s" "(g has_integral l) s"
  shows "((\<lambda>x. f x + g x) has_integral (k + l)) s"
proof- have lem:"\<And>f g::real^'n \<Rightarrow> 'a. \<And>a b k l.
    (f has_integral k) ({a..b}) \<Longrightarrow> (g has_integral l) ({a..b}) \<Longrightarrow>
     ((\<lambda>x. f(x) + g(x)) has_integral (k + l)) ({a..b})" proof- case goal1
    show ?case unfolding has_integral proof(rule,rule) fix e::real assume e:"e>0" hence *:"e/2>0" by auto
      guess d1 using has_integralD[OF goal1(1) *] . note d1=this
      guess d2 using has_integralD[OF goal1(2) *] . note d2=this
      show "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a..b} \<and> d fine p \<longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R (f x + g x)) - (k + l)) < e)"
        apply(rule_tac x="\<lambda>x. (d1 x) \<inter> (d2 x)" in exI) apply(rule,rule gauge_inter[OF d1(1) d2(1)])
      proof(rule,rule,erule conjE) fix p assume as:"p tagged_division_of {a..b}" "(\<lambda>x. d1 x \<inter> d2 x) fine p"
        have *:"(\<Sum>(x, k)\<in>p. content k *\<^sub>R (f x + g x)) = (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>p. content k *\<^sub>R g x)"
          unfolding scaleR_right_distrib setsum_addf[of "\<lambda>(x,k). content k *\<^sub>R f x" "\<lambda>(x,k). content k *\<^sub>R g x" p,THEN sym]
          by(rule setsum_cong2,auto)
        have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R (f x + g x)) - (k + l)) = norm (((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - k) + ((\<Sum>(x, k)\<in>p. content k *\<^sub>R g x) - l))"
          unfolding * by(auto simp add:group_simps) also let ?res = "\<dots>"
        from as have *:"d1 fine p" "d2 fine p" unfolding fine_inter by auto
        have "?res < e/2 + e/2" apply(rule le_less_trans[OF norm_triangle_ineq])
          apply(rule add_strict_mono) using d1(2)[OF as(1) *(1)] and d2(2)[OF as(1) *(2)] by auto
        finally show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R (f x + g x)) - (k + l)) < e" by auto
      qed qed qed { presume "\<not> (\<exists>a b. s = {a..b}) \<Longrightarrow> ?thesis"
    thus ?thesis apply-apply(cases "\<exists>a b. s = {a..b}") using assms by(auto simp add:has_integral intro!:lem) }
  assume as:"\<not> (\<exists>a b. s = {a..b})" thus ?thesis apply(subst has_integral_alt) unfolding if_not_P
  proof(rule,rule) case goal1 hence *:"e/2 > 0" by auto
    from has_integral_altD[OF assms(1) as *] guess B1 . note B1=this[rule_format]
    from has_integral_altD[OF assms(2) as *] guess B2 . note B2=this[rule_format]
    show ?case apply(rule_tac x="max B1 B2" in exI) apply(rule,rule min_max.less_supI1,rule B1)
    proof(rule,rule,rule) fix a b assume "ball 0 (max B1 B2) \<subseteq> {a..b::real^'n}"
      hence *:"ball 0 B1 \<subseteq> {a..b::real^'n}" "ball 0 B2 \<subseteq> {a..b::real^'n}" by auto
      guess w using B1(2)[OF *(1)] .. note w=conjunctD2[OF this]
      guess z using B2(2)[OF *(2)] .. note z=conjunctD2[OF this]
      have *:"\<And>x. (if x \<in> s then f x + g x else 0) = (if x \<in> s then f x else 0) + (if x \<in> s then g x else 0)" by auto
      show "\<exists>z. ((\<lambda>x. if x \<in> s then f x + g x else 0) has_integral z) {a..b} \<and> norm (z - (k + l)) < e"
        apply(rule_tac x="w + z" in exI) apply(rule,rule lem[OF w(1) z(1), unfolded *[THEN sym]])
        using norm_triangle_ineq[of "w - k" "z - l"] w(2) z(2) by(auto simp add:field_simps)
    qed qed qed

lemma has_integral_sub:
  shows "(f has_integral k) s \<Longrightarrow> (g has_integral l) s \<Longrightarrow> ((\<lambda>x. f(x) - g(x)) has_integral (k - l)) s"
  using has_integral_add[OF _ has_integral_neg,of f k s g l] unfolding group_simps by auto

lemma integral_0: "integral s (\<lambda>x::real^'n. 0::real^'m) = 0"
  by(rule integral_unique has_integral_0)+

lemma integral_add:
  shows "f integrable_on s \<Longrightarrow> g integrable_on s \<Longrightarrow>
   integral s (\<lambda>x. f x + g x) = integral s f + integral s g"
  apply(rule integral_unique) apply(drule integrable_integral)+
  apply(rule has_integral_add) by assumption+

lemma integral_cmul:
  shows "f integrable_on s \<Longrightarrow> integral s (\<lambda>x. c *\<^sub>R f x) = c *\<^sub>R integral s f"
  apply(rule integral_unique) apply(drule integrable_integral)+
  apply(rule has_integral_cmul) by assumption+

lemma integral_neg:
  shows "f integrable_on s \<Longrightarrow> integral s (\<lambda>x. - f x) = - integral s f"
  apply(rule integral_unique) apply(drule integrable_integral)+
  apply(rule has_integral_neg) by assumption+

lemma integral_sub:
  shows "f integrable_on s \<Longrightarrow> g integrable_on s \<Longrightarrow> integral s (\<lambda>x. f x - g x) = integral s f - integral s g"
  apply(rule integral_unique) apply(drule integrable_integral)+
  apply(rule has_integral_sub) by assumption+

lemma integrable_0: "(\<lambda>x. 0) integrable_on s"
  unfolding integrable_on_def using has_integral_0 by auto

lemma integrable_add:
  shows "f integrable_on s \<Longrightarrow> g integrable_on s \<Longrightarrow> (\<lambda>x. f x + g x) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_add)

lemma integrable_cmul:
  shows "f integrable_on s \<Longrightarrow> (\<lambda>x. c *\<^sub>R f(x)) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_cmul)

lemma integrable_neg:
  shows "f integrable_on s \<Longrightarrow> (\<lambda>x. -f(x)) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_neg)

lemma integrable_sub:
  shows "f integrable_on s \<Longrightarrow> g integrable_on s \<Longrightarrow> (\<lambda>x. f x - g x) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_sub)

lemma integrable_linear:
  shows "f integrable_on s \<Longrightarrow> bounded_linear h \<Longrightarrow> (h o f) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_linear)

lemma integral_linear:
  shows "f integrable_on s \<Longrightarrow> bounded_linear h \<Longrightarrow> integral s (h o f) = h(integral s f)"
  apply(rule has_integral_unique) defer unfolding has_integral_integral 
  apply(drule has_integral_linear,assumption,assumption) unfolding has_integral_integral[THEN sym]
  apply(rule integrable_linear) by assumption+

lemma has_integral_setsum:
  assumes "finite t" "\<forall>a\<in>t. ((f a) has_integral (i a)) s"
  shows "((\<lambda>x. setsum (\<lambda>a. f a x) t) has_integral (setsum i t)) s"
proof(insert assms(1) subset_refl[of t],induct rule:finite_subset_induct)
  case (insert x F) show ?case unfolding setsum_insert[OF insert(1,3)]
    apply(rule has_integral_add) using insert assms by auto
qed auto

lemma integral_setsum:
  shows "finite t \<Longrightarrow> \<forall>a\<in>t. (f a) integrable_on s \<Longrightarrow>
  integral s (\<lambda>x. setsum (\<lambda>a. f a x) t) = setsum (\<lambda>a. integral s (f a)) t"
  apply(rule integral_unique) apply(rule has_integral_setsum)
  using integrable_integral by auto

lemma integrable_setsum:
  shows "finite t \<Longrightarrow> \<forall>a \<in> t.(f a) integrable_on s \<Longrightarrow> (\<lambda>x. setsum (\<lambda>a. f a x) t) integrable_on s"
  unfolding integrable_on_def apply(drule bchoice) using has_integral_setsum[of t] by auto

lemma has_integral_eq:
  assumes "\<forall>x\<in>s. f x = g x" "(f has_integral k) s" shows "(g has_integral k) s"
  using has_integral_sub[OF assms(2), of "\<lambda>x. f x - g x" 0]
  using has_integral_is_0[of s "\<lambda>x. f x - g x"] using assms(1) by auto

lemma integrable_eq:
  shows "\<forall>x\<in>s. f x = g x \<Longrightarrow> f integrable_on s \<Longrightarrow> g integrable_on s"
  unfolding integrable_on_def using has_integral_eq[of s f g] by auto

lemma has_integral_eq_eq:
  shows "\<forall>x\<in>s. f x = g x \<Longrightarrow> ((f has_integral k) s \<longleftrightarrow> (g has_integral k) s)"
  using has_integral_eq[of s f g] has_integral_eq[of s g f] by auto 

lemma has_integral_null[dest]:
  assumes "content({a..b}) = 0" shows  "(f has_integral 0) ({a..b})"
  unfolding has_integral apply(rule,rule,rule_tac x="\<lambda>x. ball x 1" in exI,rule) defer
proof(rule,rule,erule conjE) fix e::real assume e:"e>0" thus "gauge (\<lambda>x. ball x 1)" by auto
  fix p assume p:"p tagged_division_of {a..b}" (*"(\<lambda>x. ball x 1) fine p"*)
  have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) = 0" unfolding norm_eq_zero diff_0_right
    using setsum_content_null[OF assms(1) p, of f] . 
  thus "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) < e" using e by auto qed

lemma has_integral_null_eq[simp]:
  shows "content({a..b}) = 0 \<Longrightarrow> ((f has_integral i) ({a..b}) \<longleftrightarrow> i = 0)"
  apply rule apply(rule has_integral_unique,assumption) 
  apply(drule has_integral_null,assumption)
  apply(drule has_integral_null) by auto

lemma integral_null[dest]: shows "content({a..b}) = 0 \<Longrightarrow> integral({a..b}) f = 0"
  by(rule integral_unique,drule has_integral_null)

lemma integrable_on_null[dest]: shows "content({a..b}) = 0 \<Longrightarrow> f integrable_on {a..b}"
  unfolding integrable_on_def apply(drule has_integral_null) by auto

lemma has_integral_empty[intro]: shows "(f has_integral 0) {}"
  unfolding empty_as_interval apply(rule has_integral_null) 
  using content_empty unfolding empty_as_interval .

lemma has_integral_empty_eq[simp]: shows "(f has_integral i) {} \<longleftrightarrow> i = 0"
  apply(rule,rule has_integral_unique,assumption) by auto

lemma integrable_on_empty[intro]: shows "f integrable_on {}" unfolding integrable_on_def by auto

lemma integral_empty[simp]: shows "integral {} f = 0"
  apply(rule integral_unique) using has_integral_empty .

lemma has_integral_refl[intro]: shows "(f has_integral 0) {a..a}"
  apply(rule has_integral_null) unfolding content_eq_0_interior
  unfolding interior_closed_interval using interval_sing by auto

lemma integrable_on_refl[intro]: shows "f integrable_on {a..a}" unfolding integrable_on_def by auto

lemma integral_refl: shows "integral {a..a} f = 0" apply(rule integral_unique) by auto

subsection {* Cauchy-type criterion for integrability. *}

lemma integrable_cauchy: fixes f::"real^'n \<Rightarrow> 'a::{real_normed_vector,complete_space}" 
  shows "f integrable_on {a..b} \<longleftrightarrow>
  (\<forall>e>0.\<exists>d. gauge d \<and> (\<forall>p1 p2. p1 tagged_division_of {a..b} \<and> d fine p1 \<and>
                            p2 tagged_division_of {a..b} \<and> d fine p2
                            \<longrightarrow> norm(setsum (\<lambda>(x,k). content k *\<^sub>R f x) p1 -
                                     setsum (\<lambda>(x,k). content k *\<^sub>R f x) p2) < e))" (is "?l = (\<forall>e>0. \<exists>d. ?P e d)")
proof assume ?l
  then guess y unfolding integrable_on_def has_integral .. note y=this
  show "\<forall>e>0. \<exists>d. ?P e d" proof(rule,rule) case goal1 hence "e/2 > 0" by auto
    then guess d apply- apply(drule y[rule_format]) by(erule exE,erule conjE) note d=this[rule_format]
    show ?case apply(rule_tac x=d in exI,rule,rule d) apply(rule,rule,rule,(erule conjE)+)
    proof- fix p1 p2 assume as:"p1 tagged_division_of {a..b}" "d fine p1" "p2 tagged_division_of {a..b}" "d fine p2"
      show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e"
        apply(rule dist_triangle_half_l[where y=y,unfolded vector_dist_norm])
        using d(2)[OF conjI[OF as(1-2)]] d(2)[OF conjI[OF as(3-4)]] .
    qed qed
next assume "\<forall>e>0. \<exists>d. ?P e d" hence "\<forall>n::nat. \<exists>d. ?P (inverse(real (n + 1))) d" by auto
  from choice[OF this] guess d .. note d=conjunctD2[OF this[rule_format],rule_format]
  have "\<And>n. gauge (\<lambda>x. \<Inter>{d i x |i. i \<in> {0..n}})" apply(rule gauge_inters) using d(1) by auto
  hence "\<forall>n. \<exists>p. p tagged_division_of {a..b} \<and> (\<lambda>x. \<Inter>{d i x |i. i \<in> {0..n}}) fine p" apply-
  proof case goal1 from this[of n] show ?case apply(drule_tac fine_division_exists) by auto qed
  from choice[OF this] guess p .. note p = conjunctD2[OF this[rule_format]]
  have dp:"\<And>i n. i\<le>n \<Longrightarrow> d i fine p n" using p(2) unfolding fine_inters by auto
  have "Cauchy (\<lambda>n. setsum (\<lambda>(x,k). content k *\<^sub>R (f x)) (p n))"
  proof(rule CauchyI) case goal1 then guess N unfolding real_arch_inv[of e] .. note N=this
    show ?case apply(rule_tac x=N in exI)
    proof(rule,rule,rule,rule) fix m n assume mn:"N \<le> m" "N \<le> n" have *:"N = (N - 1) + 1" using N by auto
      show "norm ((\<Sum>(x, k)\<in>p m. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p n. content k *\<^sub>R f x)) < e"
        apply(rule less_trans[OF _ N[THEN conjunct2,THEN conjunct2]]) apply(subst *) apply(rule d(2))
        using dp p(1) using mn by auto 
    qed qed
  then guess y unfolding convergent_eq_cauchy[THEN sym] .. note y=this[unfolded Lim_sequentially,rule_format]
  show ?l unfolding integrable_on_def has_integral apply(rule_tac x=y in exI)
  proof(rule,rule) fix e::real assume "e>0" hence *:"e/2 > 0" by auto
    then guess N1 unfolding real_arch_inv[of "e/2"] .. note N1=this hence N1':"N1 = N1 - 1 + 1" by auto
    guess N2 using y[OF *] .. note N2=this
    show "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a..b} \<and> d fine p \<longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - y) < e)"
      apply(rule_tac x="d (N1 + N2)" in exI) apply rule defer 
    proof(rule,rule,erule conjE) show "gauge (d (N1 + N2))" using d by auto
      fix q assume as:"q tagged_division_of {a..b}" "d (N1 + N2) fine q"
      have *:"inverse (real (N1 + N2 + 1)) < e / 2" apply(rule less_trans) using N1 by auto
      show "norm ((\<Sum>(x, k)\<in>q. content k *\<^sub>R f x) - y) < e" apply(rule norm_triangle_half_r)
        apply(rule less_trans[OF _ *]) apply(subst N1', rule d(2)[of "p (N1+N2)"]) defer
        using N2[rule_format,unfolded vector_dist_norm,of "N1+N2"]
        using as dp[of "N1 - 1 + 1 + N2" "N1 + N2"] using p(1)[of "N1 + N2"] using N1 by auto qed qed qed

subsection {* Additivity of integral on abutting intervals. *}

lemma interval_split:
  "{a..b::real^'n} \<inter> {x. x$k \<le> c} = {a .. (\<chi> i. if i = k then min (b$k) c else b$i)}"
  "{a..b} \<inter> {x. x$k \<ge> c} = {(\<chi> i. if i = k then max (a$k) c else a$i) .. b}"
  apply(rule_tac[!] set_ext) unfolding Int_iff mem_interval mem_Collect_eq
  unfolding Cart_lambda_beta by auto

lemma content_split:
  "content {a..b::real^'n} = content({a..b} \<inter> {x. x$k \<le> c}) + content({a..b} \<inter> {x. x$k >= c})"
proof- note simps = interval_split content_closed_interval_cases Cart_lambda_beta vector_le_def
  { presume "a\<le>b \<Longrightarrow> ?thesis" thus ?thesis apply(cases "a\<le>b") unfolding simps by auto }
  have *:"UNIV = insert k (UNIV - {k})" "\<And>x. finite (UNIV-{x::'n})" "\<And>x. x\<notin>UNIV-{x}" by auto
  have *:"\<And>X Y Z. (\<Prod>i\<in>UNIV. Z i (if i = k then X else Y i)) = Z k X * (\<Prod>i\<in>UNIV-{k}. Z i (Y i))"
    "(\<Prod>i\<in>UNIV. b$i - a$i) = (\<Prod>i\<in>UNIV-{k}. b$i - a$i) * (b$k - a$k)" 
    apply(subst *(1)) defer apply(subst *(1)) unfolding setprod_insert[OF *(2-)] by auto
  assume as:"a\<le>b" moreover have "\<And>x. min (b $ k) c = max (a $ k) c
    \<Longrightarrow> x* (b$k - a$k) = x*(max (a $ k) c - a $ k) + x*(b $ k - max (a $ k) c)"
    by  (auto simp add:field_simps)
  moreover have "\<not> a $ k \<le> c \<Longrightarrow> \<not> c \<le> b $ k \<Longrightarrow> False"
    unfolding not_le using as[unfolded vector_le_def,rule_format,of k] by auto
  ultimately show ?thesis 
    unfolding simps unfolding *(1)[of "\<lambda>i x. b$i - x"] *(1)[of "\<lambda>i x. x - a$i"] *(2) by(auto)
qed

lemma division_split_left_inj:
  assumes "d division_of i" "k1 \<in> d" "k2 \<in> d"  "k1 \<noteq> k2"
  "k1 \<inter> {x::real^'n. x$k \<le> c} = k2 \<inter> {x. x$k \<le> c}"
  shows "content(k1 \<inter> {x. x$k \<le> c}) = 0"
proof- note d=division_ofD[OF assms(1)]
  have *:"\<And>a b::real^'n. \<And> c k. (content({a..b} \<inter> {x. x$k \<le> c}) = 0 \<longleftrightarrow> interior({a..b} \<inter> {x. x$k \<le> c}) = {})"
    unfolding interval_split content_eq_0_interior by auto
  guess u1 v1 using d(4)[OF assms(2)] apply-by(erule exE)+ note uv1=this
  guess u2 v2 using d(4)[OF assms(3)] apply-by(erule exE)+ note uv2=this
  have **:"\<And>s t u. s \<inter> t = {} \<Longrightarrow> u \<subseteq> s \<Longrightarrow> u \<subseteq> t \<Longrightarrow> u = {}" by auto
  show ?thesis unfolding uv1 uv2 * apply(rule **[OF d(5)[OF assms(2-4)]])
    defer apply(subst assms(5)[unfolded uv1 uv2]) unfolding uv1 uv2 by auto qed

lemma division_split_right_inj:
  assumes "d division_of i" "k1 \<in> d" "k2 \<in> d"  "k1 \<noteq> k2"
  "k1 \<inter> {x::real^'n. x$k \<ge> c} = k2 \<inter> {x. x$k \<ge> c}"
  shows "content(k1 \<inter> {x. x$k \<ge> c}) = 0"
proof- note d=division_ofD[OF assms(1)]
  have *:"\<And>a b::real^'n. \<And> c k. (content({a..b} \<inter> {x. x$k >= c}) = 0 \<longleftrightarrow> interior({a..b} \<inter> {x. x$k >= c}) = {})"
    unfolding interval_split content_eq_0_interior by auto
  guess u1 v1 using d(4)[OF assms(2)] apply-by(erule exE)+ note uv1=this
  guess u2 v2 using d(4)[OF assms(3)] apply-by(erule exE)+ note uv2=this
  have **:"\<And>s t u. s \<inter> t = {} \<Longrightarrow> u \<subseteq> s \<Longrightarrow> u \<subseteq> t \<Longrightarrow> u = {}" by auto
  show ?thesis unfolding uv1 uv2 * apply(rule **[OF d(5)[OF assms(2-4)]])
    defer apply(subst assms(5)[unfolded uv1 uv2]) unfolding uv1 uv2 by auto qed

lemma tagged_division_split_left_inj:
  assumes "d tagged_division_of i" "(x1,k1) \<in> d" "(x2,k2) \<in> d" "k1 \<noteq> k2"  "k1 \<inter> {x. x$k \<le> c} = k2 \<inter> {x. x$k \<le> c}" 
  shows "content(k1 \<inter> {x. x$k \<le> c}) = 0"
proof- have *:"\<And>a b c. (a,b) \<in> c \<Longrightarrow> b \<in> snd ` c" unfolding image_iff apply(rule_tac x="(a,b)" in bexI) by auto
  show ?thesis apply(rule division_split_left_inj[OF division_of_tagged_division[OF assms(1)]])
    apply(rule_tac[1-2] *) using assms(2-) by auto qed

lemma tagged_division_split_right_inj:
  assumes "d tagged_division_of i" "(x1,k1) \<in> d" "(x2,k2) \<in> d" "k1 \<noteq> k2"  "k1 \<inter> {x. x$k \<ge> c} = k2 \<inter> {x. x$k \<ge> c}" 
  shows "content(k1 \<inter> {x. x$k \<ge> c}) = 0"
proof- have *:"\<And>a b c. (a,b) \<in> c \<Longrightarrow> b \<in> snd ` c" unfolding image_iff apply(rule_tac x="(a,b)" in bexI) by auto
  show ?thesis apply(rule division_split_right_inj[OF division_of_tagged_division[OF assms(1)]])
    apply(rule_tac[1-2] *) using assms(2-) by auto qed

lemma division_split:
  assumes "p division_of {a..b::real^'n}"
  shows "{l \<inter> {x. x$k \<le> c} | l. l \<in> p \<and> ~(l \<inter> {x. x$k \<le> c} = {})} division_of ({a..b} \<inter> {x. x$k \<le> c})" (is "?p1 division_of ?I1") and 
        "{l \<inter> {x. x$k \<ge> c} | l. l \<in> p \<and> ~(l \<inter> {x. x$k \<ge> c} = {})} division_of ({a..b} \<inter> {x. x$k \<ge> c})" (is "?p2 division_of ?I2")
proof(rule_tac[!] division_ofI) note p=division_ofD[OF assms]
  show "finite ?p1" "finite ?p2" using p(1) by auto show "\<Union>?p1 = ?I1" "\<Union>?p2 = ?I2" unfolding p(6)[THEN sym] by auto
  { fix k assume "k\<in>?p1" then guess l unfolding mem_Collect_eq apply-by(erule exE,(erule conjE)+) note l=this
    guess u v using p(4)[OF l(2)] apply-by(erule exE)+ note uv=this
    show "k\<subseteq>?I1" "k \<noteq> {}" "\<exists>a b. k = {a..b}" unfolding l
      using p(2-3)[OF l(2)] l(3) unfolding uv apply- prefer 3 apply(subst interval_split) by auto
    fix k' assume "k'\<in>?p1" then guess l' unfolding mem_Collect_eq apply-by(erule exE,(erule conjE)+) note l'=this
    assume "k\<noteq>k'" thus "interior k \<inter> interior k' = {}" unfolding l l' using p(5)[OF l(2) l'(2)] by auto }
  { fix k assume "k\<in>?p2" then guess l unfolding mem_Collect_eq apply-by(erule exE,(erule conjE)+) note l=this
    guess u v using p(4)[OF l(2)] apply-by(erule exE)+ note uv=this
    show "k\<subseteq>?I2" "k \<noteq> {}" "\<exists>a b. k = {a..b}" unfolding l
      using p(2-3)[OF l(2)] l(3) unfolding uv apply- prefer 3 apply(subst interval_split) by auto
    fix k' assume "k'\<in>?p2" then guess l' unfolding mem_Collect_eq apply-by(erule exE,(erule conjE)+) note l'=this
    assume "k\<noteq>k'" thus "interior k \<inter> interior k' = {}" unfolding l l' using p(5)[OF l(2) l'(2)] by auto }
qed

lemma has_integral_split: fixes f::"real^'n \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral i) ({a..b} \<inter> {x. x$k \<le> c})"  "(f has_integral j) ({a..b} \<inter> {x. x$k \<ge> c})"
  shows "(f has_integral (i + j)) ({a..b})"
proof(unfold has_integral,rule,rule) case goal1 hence e:"e/2>0" by auto
  guess d1 using has_integralD[OF assms(1)[unfolded interval_split] e] . note d1=this[unfolded interval_split[THEN sym]]
  guess d2 using has_integralD[OF assms(2)[unfolded interval_split] e] . note d2=this[unfolded interval_split[THEN sym]]
  let ?d = "\<lambda>x. if x$k = c then (d1 x \<inter> d2 x) else ball x (abs(x$k - c)) \<inter> d1 x \<inter> d2 x"
  show ?case apply(rule_tac x="?d" in exI,rule) defer apply(rule,rule,(erule conjE)+)
  proof- show "gauge ?d" using d1(1) d2(1) unfolding gauge_def by auto
    fix p assume "p tagged_division_of {a..b}" "?d fine p" note p = this tagged_division_ofD[OF this(1)]
    have lem0:"\<And>x kk. (x,kk) \<in> p \<Longrightarrow> ~(kk \<inter> {x. x$k \<le> c} = {}) \<Longrightarrow> x$k \<le> c"
         "\<And>x kk. (x,kk) \<in> p \<Longrightarrow> ~(kk \<inter> {x. x$k \<ge> c} = {}) \<Longrightarrow> x$k \<ge> c"
    proof- fix x kk assume as:"(x,kk)\<in>p"
      show "~(kk \<inter> {x. x$k \<le> c} = {}) \<Longrightarrow> x$k \<le> c"
      proof(rule ccontr) case goal1
        from this(2)[unfolded not_le] have "kk \<subseteq> ball x \<bar>x $ k - c\<bar>"
          using p(2)[unfolded fine_def,rule_format,OF as,unfolded split_conv] by auto
        hence "\<exists>y. y \<in> ball x \<bar>x $ k - c\<bar> \<inter> {x. x $ k \<le> c}" using goal1(1) by blast 
        then guess y .. hence "\<bar>x $ k - y $ k\<bar> < \<bar>x $ k - c\<bar>" "y$k \<le> c" apply-apply(rule le_less_trans)
          using component_le_norm[of "x - y" k,unfolded vector_minus_component] by(auto simp add:vector_dist_norm)
        thus False using goal1(2)[unfolded not_le] by(auto simp add:field_simps)
      qed
      show "~(kk \<inter> {x. x$k \<ge> c} = {}) \<Longrightarrow> x$k \<ge> c"
      proof(rule ccontr) case goal1
        from this(2)[unfolded not_le] have "kk \<subseteq> ball x \<bar>x $ k - c\<bar>"
          using p(2)[unfolded fine_def,rule_format,OF as,unfolded split_conv] by auto
        hence "\<exists>y. y \<in> ball x \<bar>x $ k - c\<bar> \<inter> {x. x $ k \<ge> c}" using goal1(1) by blast 
        then guess y .. hence "\<bar>x $ k - y $ k\<bar> < \<bar>x $ k - c\<bar>" "y$k \<ge> c" apply-apply(rule le_less_trans)
          using component_le_norm[of "x - y" k,unfolded vector_minus_component] by(auto simp add:vector_dist_norm)
        thus False using goal1(2)[unfolded not_le] by(auto simp add:field_simps)
      qed
    qed

    have lem1: "\<And>f P Q. (\<forall>x k. (x,k) \<in> {(x,f k) | x k. P x k} \<longrightarrow> Q x k) \<longleftrightarrow> (\<forall>x k. P x k \<longrightarrow> Q x (f k))" by auto
    have lem2: "\<And>f s P f. finite s \<Longrightarrow> finite {(x,f k) | x k. (x,k) \<in> s \<and> P x k}"
    proof- case goal1 thus ?case apply-apply(rule finite_subset[of _ "(\<lambda>(x,k). (x,f k)) ` s"]) by auto qed
    have lem3: "\<And>g::(real ^ 'n \<Rightarrow> bool) \<Rightarrow> real ^ 'n \<Rightarrow> bool. finite p \<Longrightarrow>
      setsum (\<lambda>(x,k). content k *\<^sub>R f x) {(x,g k) |x k. (x,k) \<in> p \<and> ~(g k = {})}
               = setsum (\<lambda>(x,k). content k *\<^sub>R f x) ((\<lambda>(x,k). (x,g k)) ` p)"
      apply(rule setsum_mono_zero_left) prefer 3
    proof fix g::"(real ^ 'n \<Rightarrow> bool) \<Rightarrow> real ^ 'n \<Rightarrow> bool" and i::"(real^'n) \<times> ((real^'n) set)"
      assume "i \<in> (\<lambda>(x, k). (x, g k)) ` p - {(x, g k) |x k. (x, k) \<in> p \<and> g k \<noteq> {}}"
      then obtain x k where xk:"i=(x,g k)" "(x,k)\<in>p" "(x,g k) \<notin> {(x, g k) |x k. (x, k) \<in> p \<and> g k \<noteq> {}}" by auto
      have "content (g k) = 0" using xk using content_empty by auto
      thus "(\<lambda>(x, k). content k *\<^sub>R f x) i = 0" unfolding xk split_conv by auto
    qed auto
    have lem4:"\<And>g. (\<lambda>(x,l). content (g l) *\<^sub>R f x) = (\<lambda>(x,l). content l *\<^sub>R f x) o (\<lambda>(x,l). (x,g l))" apply(rule ext) by auto

    let ?M1 = "{(x,kk \<inter> {x. x$k \<le> c}) |x kk. (x,kk) \<in> p \<and> kk \<inter> {x. x$k \<le> c} \<noteq> {}}"
    have "norm ((\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) - i) < e/2" apply(rule d1(2),rule tagged_division_ofI)
      apply(rule lem2 p(3))+ prefer 6 apply(rule fineI)
    proof- show "\<Union>{k. \<exists>x. (x, k) \<in> ?M1} = {a..b} \<inter> {x. x$k \<le> c}" unfolding p(8)[THEN sym] by auto
      fix x l assume xl:"(x,l)\<in>?M1"
      then guess x' l' unfolding mem_Collect_eq apply- unfolding Pair_eq apply((erule exE)+,(erule conjE)+) .  note xl'=this
      have "l' \<subseteq> d1 x'" apply(rule order_trans[OF fineD[OF p(2) xl'(3)]]) by auto
      thus "l \<subseteq> d1 x" unfolding xl' by auto
      show "x\<in>l" "l \<subseteq> {a..b} \<inter> {x. x $ k \<le> c}" unfolding xl' using p(4-6)[OF xl'(3)] using xl'(4)
        using lem0(1)[OF xl'(3-4)] by auto
      show  "\<exists>a b. l = {a..b}" unfolding xl' using p(6)[OF xl'(3)] by(fastsimp simp add: interval_split[where c=c and k=k])
      fix y r let ?goal = "interior l \<inter> interior r = {}" assume yr:"(y,r)\<in>?M1"
      then guess y' r' unfolding mem_Collect_eq apply- unfolding Pair_eq apply((erule exE)+,(erule conjE)+) .  note yr'=this
      assume as:"(x,l) \<noteq> (y,r)" show "interior l \<inter> interior r = {}"
      proof(cases "l' = r' \<longrightarrow> x' = y'")
        case False thus ?thesis using p(7)[OF xl'(3) yr'(3)] using as unfolding xl' yr' by auto
      next case True hence "l' \<noteq> r'" using as unfolding xl' yr' by auto
        thus ?thesis using p(7)[OF xl'(3) yr'(3)] using as unfolding xl' yr' by auto
      qed qed moreover

    let ?M2 = "{(x,kk \<inter> {x. x$k \<ge> c}) |x kk. (x,kk) \<in> p \<and> kk \<inter> {x. x$k \<ge> c} \<noteq> {}}" 
    have "norm ((\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - j) < e/2" apply(rule d2(2),rule tagged_division_ofI)
      apply(rule lem2 p(3))+ prefer 6 apply(rule fineI)
    proof- show "\<Union>{k. \<exists>x. (x, k) \<in> ?M2} = {a..b} \<inter> {x. x$k \<ge> c}" unfolding p(8)[THEN sym] by auto
      fix x l assume xl:"(x,l)\<in>?M2"
      then guess x' l' unfolding mem_Collect_eq apply- unfolding Pair_eq apply((erule exE)+,(erule conjE)+) .  note xl'=this
      have "l' \<subseteq> d2 x'" apply(rule order_trans[OF fineD[OF p(2) xl'(3)]]) by auto
      thus "l \<subseteq> d2 x" unfolding xl' by auto
      show "x\<in>l" "l \<subseteq> {a..b} \<inter> {x. x $ k \<ge> c}" unfolding xl' using p(4-6)[OF xl'(3)] using xl'(4)
        using lem0(2)[OF xl'(3-4)] by auto
      show  "\<exists>a b. l = {a..b}" unfolding xl' using p(6)[OF xl'(3)] by(fastsimp simp add: interval_split[where c=c and k=k])
      fix y r let ?goal = "interior l \<inter> interior r = {}" assume yr:"(y,r)\<in>?M2"
      then guess y' r' unfolding mem_Collect_eq apply- unfolding Pair_eq apply((erule exE)+,(erule conjE)+) .  note yr'=this
      assume as:"(x,l) \<noteq> (y,r)" show "interior l \<inter> interior r = {}"
      proof(cases "l' = r' \<longrightarrow> x' = y'")
        case False thus ?thesis using p(7)[OF xl'(3) yr'(3)] using as unfolding xl' yr' by auto
      next case True hence "l' \<noteq> r'" using as unfolding xl' yr' by auto
        thus ?thesis using p(7)[OF xl'(3) yr'(3)] using as unfolding xl' yr' by auto
      qed qed ultimately

    have "norm (((\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) - i) + ((\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - j)) < e/2 + e/2"
      apply- apply(rule norm_triangle_lt) by auto
    also { have *:"\<And>x y. x = (0::real) \<Longrightarrow> x *\<^sub>R (y::'a) = 0" using scaleR_zero_left by auto
      have "((\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) - i) + ((\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - j)
       = (\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - (i + j)" by auto
      also have "\<dots> = (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. x $ k \<le> c}) *\<^sub>R f x) + (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. c \<le> x $ k}) *\<^sub>R f x) - (i + j)"
        unfolding lem3[OF p(3)] apply(subst setsum_reindex_nonzero[OF p(3)]) defer apply(subst setsum_reindex_nonzero[OF p(3)])
        defer unfolding lem4[THEN sym] apply(rule refl) unfolding split_paired_all split_conv apply(rule_tac[!] *)
      proof- case goal1 thus ?case apply- apply(rule tagged_division_split_left_inj [OF p(1), of a b aa ba]) by auto
      next case   goal2 thus ?case apply- apply(rule tagged_division_split_right_inj[OF p(1), of a b aa ba]) by auto
      qed also note setsum_addf[THEN sym]
      also have *:"\<And>x. x\<in>p \<Longrightarrow> (\<lambda>(x, ka). content (ka \<inter> {x. x $ k \<le> c}) *\<^sub>R f x) x + (\<lambda>(x, ka). content (ka \<inter> {x. c \<le> x $ k}) *\<^sub>R f x) x
        = (\<lambda>(x,ka). content ka *\<^sub>R f x) x" unfolding split_paired_all split_conv
      proof- fix a b assume "(a,b) \<in> p" from p(6)[OF this] guess u v apply-by(erule exE)+ note uv=this
        thus "content (b \<inter> {x. x $ k \<le> c}) *\<^sub>R f a + content (b \<inter> {x. c \<le> x $ k}) *\<^sub>R f a = content b *\<^sub>R f a"
          unfolding scaleR_left_distrib[THEN sym] unfolding uv content_split[of u v k c] by auto
      qed note setsum_cong2[OF this]
      finally have "(\<Sum>(x, k)\<in>{(x, kk \<inter> {x. x $ k \<le> c}) |x kk. (x, kk) \<in> p \<and> kk \<inter> {x. x $ k \<le> c} \<noteq> {}}. content k *\<^sub>R f x) - i +
        ((\<Sum>(x, k)\<in>{(x, kk \<inter> {x. c \<le> x $ k}) |x kk. (x, kk) \<in> p \<and> kk \<inter> {x. c \<le> x $ k} \<noteq> {}}. content k *\<^sub>R f x) - j) =
        (\<Sum>(x, ka)\<in>p. content ka *\<^sub>R f x) - (i + j)" by auto }
    finally show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - (i + j)) < e" by auto qed qed

subsection {* A sort of converse, integrability on subintervals. *}

lemma tagged_division_union_interval:
  assumes "p1 tagged_division_of ({a..b} \<inter> {x::real^'n. x$k \<le> (c::real)})"  "p2 tagged_division_of ({a..b} \<inter> {x. x$k \<ge> c})"
  shows "(p1 \<union> p2) tagged_division_of ({a..b})"
proof- have *:"{a..b} = ({a..b} \<inter> {x. x$k \<le> c}) \<union> ({a..b} \<inter> {x. x$k \<ge> c})" by auto
  show ?thesis apply(subst *) apply(rule tagged_division_union[OF assms])
    unfolding interval_split interior_closed_interval
    by(auto simp add: vector_less_def Cart_lambda_beta elim!:allE[where x=k]) qed

lemma has_integral_separate_sides: fixes f::"real^'m \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral i) ({a..b})" "e>0"
  obtains d where "gauge d" "(\<forall>p1 p2. p1 tagged_division_of ({a..b} \<inter> {x. x$k \<le> c}) \<and> d fine p1 \<and>
                                p2 tagged_division_of ({a..b} \<inter> {x. x$k \<ge> c}) \<and> d fine p2
                                \<longrightarrow> norm((setsum (\<lambda>(x,k). content k *\<^sub>R f x) p1 +
                                          setsum (\<lambda>(x,k). content k *\<^sub>R f x) p2) - i) < e)"
proof- guess d using has_integralD[OF assms] . note d=this
  show ?thesis apply(rule that[of d]) apply(rule d) apply(rule,rule,rule,(erule conjE)+)
  proof- fix p1 p2 assume "p1 tagged_division_of {a..b} \<inter> {x. x $ k \<le> c}" "d fine p1" note p1=tagged_division_ofD[OF this(1)] this
                   assume "p2 tagged_division_of {a..b} \<inter> {x. c \<le> x $ k}" "d fine p2" note p2=tagged_division_ofD[OF this(1)] this
    note tagged_division_union_interval[OF p1(7) p2(7)] note p12 = tagged_division_ofD[OF this] this
    have "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x) - i) = norm ((\<Sum>(x, k)\<in>p1 \<union> p2. content k *\<^sub>R f x) - i)"
      apply(subst setsum_Un_zero) apply(rule p1 p2)+ apply(rule) unfolding split_paired_all split_conv
    proof- fix a b assume ab:"(a,b) \<in> p1 \<inter> p2"
      have "(a,b) \<in> p1" using ab by auto from p1(4)[OF this] guess u v apply-by(erule exE)+ note uv =this
      have "b \<subseteq> {x. x$k = c}" using ab p1(3)[of a b] p2(3)[of a b] by fastsimp
      moreover have "interior {x. x $ k = c} = {}" 
      proof(rule ccontr) case goal1 then obtain x where x:"x\<in>interior {x. x$k = c}" by auto
        then guess e unfolding mem_interior .. note e=this
        have x:"x$k = c" using x interior_subset by fastsimp
        have *:"\<And>i. \<bar>(x - (x + (\<chi> i. if i = k then e / 2 else 0))) $ i\<bar> = (if i = k then e/2 else 0)" using e by auto
        have "x + (\<chi> i. if i = k then e/2 else 0) \<in> ball x e" unfolding mem_ball vector_dist_norm 
          apply(rule le_less_trans[OF norm_le_l1]) unfolding * 
          unfolding setsum_delta[OF finite_UNIV] using e by auto 
        hence "x + (\<chi> i. if i = k then e/2 else 0) \<in> {x. x$k = c}" using e by auto
        thus False unfolding mem_Collect_eq using e x by auto
      qed ultimately have "content b = 0" unfolding uv content_eq_0_interior apply-apply(drule subset_interior) by auto
      thus "content b *\<^sub>R f a = 0" by auto
    qed auto
    also have "\<dots> < e" by(rule d(2) p12 fine_union p1 p2)+
    finally show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x) - i) < e" . qed qed

lemma integrable_split[intro]: fixes f::"real^'n \<Rightarrow> 'a::{real_normed_vector,complete_space}" assumes "f integrable_on {a..b}"
  shows "f integrable_on ({a..b} \<inter> {x. x$k \<le> c})" (is ?t1) and "f integrable_on ({a..b} \<inter> {x. x$k \<ge> c})" (is ?t2) 
proof- guess y using assms unfolding integrable_on_def .. note y=this
  def b' \<equiv> "(\<chi> i. if i = k then min (b$k) c else b$i)::real^'n"
  and a' \<equiv> "(\<chi> i. if i = k then max (a$k) c else a$i)::real^'n"
  show ?t1 ?t2 unfolding interval_split integrable_cauchy unfolding interval_split[THEN sym]
  proof(rule_tac[!] allI impI)+ fix e::real assume "e>0" hence "e/2>0" by auto
    from has_integral_separate_sides[OF y this,of k c] guess d . note d=this[rule_format]
    let ?P = "\<lambda>A. \<exists>d. gauge d \<and> (\<forall>p1 p2. p1 tagged_division_of {a..b} \<inter> A \<and> d fine p1 \<and> p2 tagged_division_of {a..b} \<inter> A \<and> d fine p2 \<longrightarrow>
                              norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e)"
    show "?P {x. x $ k \<le> c}" apply(rule_tac x=d in exI) apply(rule,rule d) apply(rule,rule,rule)
    proof- fix p1 p2 assume as:"p1 tagged_division_of {a..b} \<inter> {x. x $ k \<le> c} \<and> d fine p1 \<and> p2 tagged_division_of {a..b} \<inter> {x. x $ k \<le> c} \<and> d fine p2"
      show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e"
      proof- guess p using fine_division_exists[OF d(1), of a' b] . note p=this
        show ?thesis using norm_triangle_half_l[OF d(2)[of p1 p] d(2)[of p2 p]]
          using as unfolding interval_split b'_def[symmetric] a'_def[symmetric]
          using p using assms by(auto simp add:group_simps)
      qed qed  
    show "?P {x. x $ k \<ge> c}" apply(rule_tac x=d in exI) apply(rule,rule d) apply(rule,rule,rule)
    proof- fix p1 p2 assume as:"p1 tagged_division_of {a..b} \<inter> {x. x $ k \<ge> c} \<and> d fine p1 \<and> p2 tagged_division_of {a..b} \<inter> {x. x $ k \<ge> c} \<and> d fine p2"
      show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e"
      proof- guess p using fine_division_exists[OF d(1), of a b'] . note p=this
        show ?thesis using norm_triangle_half_l[OF d(2)[of p p1] d(2)[of p p2]]
          using as unfolding interval_split b'_def[symmetric] a'_def[symmetric]
          using p using assms by(auto simp add:group_simps) qed qed qed qed

subsection {* Generalized notion of additivity. *}

definition "neutral opp = (SOME x. \<forall>y. opp x y = y \<and> opp y x = y)"

definition operative :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ((real^'n) set \<Rightarrow> 'a) \<Rightarrow> bool" where
  "operative opp f \<equiv> 
    (\<forall>a b. content {a..b} = 0 \<longrightarrow> f {a..b} = neutral(opp)) \<and>
    (\<forall>a b c k. f({a..b}) =
                   opp (f({a..b} \<inter> {x. x$k \<le> c}))
                       (f({a..b} \<inter> {x. x$k \<ge> c})))"

lemma operativeD[dest]: assumes "operative opp f"
  shows "\<And>a b. content {a..b} = 0 \<Longrightarrow> f {a..b} = neutral(opp)"
  "\<And>a b c k. f({a..b}) = opp (f({a..b} \<inter> {x. x$k \<le> c})) (f({a..b} \<inter> {x. x$k \<ge> c}))"
  using assms unfolding operative_def by auto

lemma operative_trivial:
 "operative opp f \<Longrightarrow> content({a..b}) = 0 \<Longrightarrow> f({a..b}) = neutral opp"
  unfolding operative_def by auto

lemma property_empty_interval:
 "(\<forall>a b. content({a..b}) = 0 \<longrightarrow> P({a..b})) \<Longrightarrow> P {}" 
  using content_empty unfolding empty_as_interval by auto

lemma operative_empty: "operative opp f \<Longrightarrow> f {} = neutral opp"
  unfolding operative_def apply(rule property_empty_interval) by auto

subsection {* Using additivity of lifted function to encode definedness. *}

lemma forall_option: "(\<forall>x. P x) \<longleftrightarrow> P None \<and> (\<forall>x. P(Some x))"
  by (metis map_of.simps option.nchotomy)

lemma exists_option:
 "(\<exists>x. P x) \<longleftrightarrow> P None \<or> (\<exists>x. P(Some x))" 
  by (metis map_of.simps option.nchotomy)

fun lifted where 
  "lifted (opp::'a\<Rightarrow>'a\<Rightarrow>'b) (Some x) (Some y) = Some(opp x y)" |
  "lifted opp None _ = (None::'b option)" |
  "lifted opp _ None = None"

lemma lifted_simp_1[simp]: "lifted opp v None = None"
  apply(induct v) by auto

definition "monoidal opp \<equiv>  (\<forall>x y. opp x y = opp y x) \<and>
                   (\<forall>x y z. opp x (opp y z) = opp (opp x y) z) \<and>
                   (\<forall>x. opp (neutral opp) x = x)"

lemma monoidalI: assumes "\<And>x y. opp x y = opp y x"
  "\<And>x y z. opp x (opp y z) = opp (opp x y) z"
  "\<And>x. opp (neutral opp) x = x" shows "monoidal opp"
  unfolding monoidal_def using assms by fastsimp

lemma monoidal_ac: assumes "monoidal opp"
  shows "opp (neutral opp) a = a" "opp a (neutral opp) = a" "opp a b = opp b a"
  "opp (opp a b) c = opp a (opp b c)"  "opp a (opp b c) = opp b (opp a c)"
  using assms unfolding monoidal_def apply- by metis+

lemma monoidal_simps[simp]: assumes "monoidal opp"
  shows "opp (neutral opp) a = a" "opp a (neutral opp) = a"
  using monoidal_ac[OF assms] by auto

lemma neutral_lifted[cong]: assumes "monoidal opp"
  shows "neutral (lifted opp) = Some(neutral opp)"
  apply(subst neutral_def) apply(rule some_equality) apply(rule,induct_tac y) prefer 3
proof- fix x assume "\<forall>y. lifted opp x y = y \<and> lifted opp y x = y"
  thus "x = Some (neutral opp)" apply(induct x) defer
    apply rule apply(subst neutral_def) apply(subst eq_commute,rule some_equality)
    apply(rule,erule_tac x="Some y" in allE) defer apply(erule_tac x="Some x" in allE) by auto
qed(auto simp add:monoidal_ac[OF assms])

lemma monoidal_lifted[intro]: assumes "monoidal opp" shows "monoidal(lifted opp)"
  unfolding monoidal_def forall_option neutral_lifted[OF assms] using monoidal_ac[OF assms] by auto

definition "support opp f s = {x. x\<in>s \<and> f x \<noteq> neutral opp}"
definition "fold' opp e s \<equiv> (if finite s then fold opp e s else e)"
definition "iterate opp s f \<equiv> fold' (\<lambda>x a. opp (f x) a) (neutral opp) (support opp f s)"

lemma support_subset[intro]:"support opp f s \<subseteq> s" unfolding support_def by auto
lemma support_empty[simp]:"support opp f {} = {}" using support_subset[of opp f "{}"] by auto

lemma fun_left_comm_monoidal[intro]: assumes "monoidal opp" shows "fun_left_comm opp"
  unfolding fun_left_comm_def using monoidal_ac[OF assms] by auto

lemma support_clauses:
  "\<And>f g s. support opp f {} = {}"
  "\<And>f g s. support opp f (insert x s) = (if f(x) = neutral opp then support opp f s else insert x (support opp f s))"
  "\<And>f g s. support opp f (s - {x}) = (support opp f s) - {x}"
  "\<And>f g s. support opp f (s \<union> t) = (support opp f s) \<union> (support opp f t)"
  "\<And>f g s. support opp f (s \<inter> t) = (support opp f s) \<inter> (support opp f t)"
  "\<And>f g s. support opp f (s - t) = (support opp f s) - (support opp f t)"
  "\<And>f g s. support opp g (f ` s) = f ` (support opp (g o f) s)"
unfolding support_def by auto

lemma finite_support[intro]:"finite s \<Longrightarrow> finite (support opp f s)"
  unfolding support_def by auto

lemma iterate_empty[simp]:"iterate opp {} f = neutral opp"
  unfolding iterate_def fold'_def by auto 

lemma iterate_insert[simp]: assumes "monoidal opp" "finite s"
  shows "iterate opp (insert x s) f = (if x \<in> s then iterate opp s f else opp (f x) (iterate opp s f))" 
proof(cases "x\<in>s") case True hence *:"insert x s = s" by auto
  show ?thesis unfolding iterate_def if_P[OF True] * by auto
next case False note x=this
  note * = fun_left_comm.fun_left_comm_apply[OF fun_left_comm_monoidal[OF assms(1)]]
  show ?thesis proof(cases "f x = neutral opp")
    case True show ?thesis unfolding iterate_def if_not_P[OF x] support_clauses if_P[OF True]
      unfolding True monoidal_simps[OF assms(1)] by auto
  next case False show ?thesis unfolding iterate_def fold'_def  if_not_P[OF x] support_clauses if_not_P[OF False]
      apply(subst fun_left_comm.fold_insert[OF * finite_support])
      using `finite s` unfolding support_def using False x by auto qed qed 

lemma iterate_some:
  assumes "monoidal opp"  "finite s"
  shows "iterate (lifted opp) s (\<lambda>x. Some(f x)) = Some (iterate opp s f)" using assms(2)
proof(induct s) case empty thus ?case using assms by auto
next case (insert x F) show ?case apply(subst iterate_insert) prefer 3 apply(subst if_not_P)
    defer unfolding insert(3) lifted.simps apply rule using assms insert by auto qed

subsection {* Two key instances of additivity. *}

lemma neutral_add[simp]:
  "neutral op + = (0::_::comm_monoid_add)" unfolding neutral_def 
  apply(rule some_equality) defer apply(erule_tac x=0 in allE) by auto

lemma operative_content[intro]: "operative (op +) content"
  unfolding operative_def content_split[THEN sym] neutral_add by auto

lemma neutral_monoid[simp]: "neutral ((op +)::('a::comm_monoid_add) \<Rightarrow> 'a \<Rightarrow> 'a) = 0"
  unfolding neutral_def apply(rule some_equality) defer
  apply(erule_tac x=0 in allE) by auto

lemma monoidal_monoid[intro]:
  shows "monoidal ((op +)::('a::comm_monoid_add) \<Rightarrow> 'a \<Rightarrow> 'a)"
  unfolding monoidal_def neutral_monoid by(auto simp add: group_simps) 

lemma operative_integral: fixes f::"real^'n \<Rightarrow> 'a::banach"
  shows "operative (lifted(op +)) (\<lambda>i. if f integrable_on i then Some(integral i f) else None)"
  unfolding operative_def unfolding neutral_lifted[OF monoidal_monoid] neutral_add
  apply(rule,rule,rule,rule) defer apply(rule allI)+
proof- fix a b c k show "(if f integrable_on {a..b} then Some (integral {a..b} f) else None) =
              lifted op + (if f integrable_on {a..b} \<inter> {x. x $ k \<le> c} then Some (integral ({a..b} \<inter> {x. x $ k \<le> c}) f) else None)
               (if f integrable_on {a..b} \<inter> {x. c \<le> x $ k} then Some (integral ({a..b} \<inter> {x. c \<le> x $ k}) f) else None)"
  proof(cases "f integrable_on {a..b}") 
    case True show ?thesis unfolding if_P[OF True]
      unfolding if_P[OF integrable_split(1)[OF True]] if_P[OF integrable_split(2)[OF True]]
      unfolding lifted.simps option.inject apply(rule integral_unique) apply(rule has_integral_split) 
      apply(rule_tac[!] integrable_integral integrable_split)+ using True by assumption+
  next case False have "(\<not> (f integrable_on {a..b} \<inter> {x. x $ k \<le> c})) \<or> (\<not> ( f integrable_on {a..b} \<inter> {x. c \<le> x $ k}))"
    proof(rule ccontr) case goal1 hence "f integrable_on {a..b}" apply- unfolding integrable_on_def
        apply(rule_tac x="integral ({a..b} \<inter> {x. x $ k \<le> c}) f + integral ({a..b} \<inter> {x. x $ k \<ge> c}) f" in exI)
        apply(rule has_integral_split) apply(rule_tac[!] integrable_integral) by auto
      thus False using False by auto
    qed thus ?thesis using False by auto 
  qed next 
  fix a b assume as:"content {a..b::real^'n} = 0"
  thus "(if f integrable_on {a..b} then Some (integral {a..b} f) else None) = Some 0"
    unfolding if_P[OF integrable_on_null[OF as]] using has_integral_null_eq[OF as] by auto qed

subsection {* Points of division of a partition. *}

definition "division_points (k::(real^'n) set) d = 
    {(j,x). (interval_lowerbound k)$j < x \<and> x < (interval_upperbound k)$j \<and>
           (\<exists>i\<in>d. (interval_lowerbound i)$j = x \<or> (interval_upperbound i)$j = x)}"

lemma division_points_finite: assumes "d division_of i"
  shows "finite (division_points i d)"
proof- note assm = division_ofD[OF assms]
  let ?M = "\<lambda>j. {(j,x)|x. (interval_lowerbound i)$j < x \<and> x < (interval_upperbound i)$j \<and>
           (\<exists>i\<in>d. (interval_lowerbound i)$j = x \<or> (interval_upperbound i)$j = x)}"
  have *:"division_points i d = \<Union>(?M ` UNIV)"
    unfolding division_points_def by auto
  show ?thesis unfolding * using assm by auto qed

lemma division_points_subset:
  assumes "d division_of {a..b}" "\<forall>i. a$i < b$i"  "a$k < c" "c < b$k"
  shows "division_points ({a..b} \<inter> {x. x$k \<le> c}) {l \<inter> {x. x$k \<le> c} | l . l \<in> d \<and> ~(l \<inter> {x. x$k \<le> c} = {})}
                  \<subseteq> division_points ({a..b}) d" (is ?t1) and
        "division_points ({a..b} \<inter> {x. x$k \<ge> c}) {l \<inter> {x. x$k \<ge> c} | l . l \<in> d \<and> ~(l \<inter> {x. x$k \<ge> c} = {})}
                  \<subseteq> division_points ({a..b}) d" (is ?t2)
proof- note assm = division_ofD[OF assms(1)]
  have *:"\<forall>i. a$i \<le> b$i"   "\<forall>i. a$i \<le> (\<chi> i. if i = k then min (b $ k) c else b $ i) $ i"
    "\<forall>i. (\<chi> i. if i = k then max (a $ k) c else a $ i) $ i \<le> b$i"  "min (b $ k) c = c" "max (a $ k) c = c"
    using assms using less_imp_le by auto
  show ?t1 unfolding division_points_def interval_split[of a b]
    unfolding interval_bounds[OF *(1)] interval_bounds[OF *(2)] interval_bounds[OF *(3)] Cart_lambda_beta unfolding *
    unfolding subset_eq apply(rule) unfolding mem_Collect_eq split_beta apply(erule bexE conjE)+ unfolding mem_Collect_eq apply(erule exE conjE)+
  proof- fix i l x assume as:"a $ fst x < snd x" "snd x < (if fst x = k then c else b $ fst x)"
      "interval_lowerbound i $ fst x = snd x \<or> interval_upperbound i $ fst x = snd x"  "i = l \<inter> {x. x $ k \<le> c}" "l \<in> d" "l \<inter> {x. x $ k \<le> c} \<noteq> {}"
    from assm(4)[OF this(5)] guess u v apply-by(erule exE)+ note l=this
    have *:"\<forall>i. u $ i \<le> (\<chi> i. if i = k then min (v $ k) c else v $ i) $ i" using as(6) unfolding l interval_split interval_ne_empty as .
    have **:"\<forall>i. u$i \<le> v$i" using l using as(6) unfolding interval_ne_empty[THEN sym] by auto
    show "a $ fst x < snd x \<and> snd x < b $ fst x \<and> (\<exists>i\<in>d. interval_lowerbound i $ fst x = snd x \<or> interval_upperbound i $ fst x = snd x)"
      using as(1-3,5) unfolding l interval_split interval_ne_empty as interval_bounds[OF *] Cart_lambda_beta apply-
      apply(rule,assumption,rule) defer apply(rule_tac x="{u..v}" in bexI) unfolding interval_bounds[OF **]
      apply(case_tac[!] "fst x = k") using assms by auto
  qed
  show ?t2 unfolding division_points_def interval_split[of a b]
    unfolding interval_bounds[OF *(1)] interval_bounds[OF *(2)] interval_bounds[OF *(3)] Cart_lambda_beta unfolding *
    unfolding subset_eq apply(rule) unfolding mem_Collect_eq split_beta apply(erule bexE conjE)+ unfolding mem_Collect_eq apply(erule exE conjE)+
  proof- fix i l x assume as:"(if fst x = k then c else a $ fst x) < snd x" "snd x < b $ fst x" "interval_lowerbound i $ fst x = snd x \<or> interval_upperbound i $ fst x = snd x"
      "i = l \<inter> {x. c \<le> x $ k}" "l \<in> d" "l \<inter> {x. c \<le> x $ k} \<noteq> {}"
    from assm(4)[OF this(5)] guess u v apply-by(erule exE)+ note l=this
    have *:"\<forall>i. (\<chi> i. if i = k then max (u $ k) c else u $ i) $ i \<le> v $ i" using as(6) unfolding l interval_split interval_ne_empty as .
    have **:"\<forall>i. u$i \<le> v$i" using l using as(6) unfolding interval_ne_empty[THEN sym] by auto
    show "a $ fst x < snd x \<and> snd x < b $ fst x \<and> (\<exists>i\<in>d. interval_lowerbound i $ fst x = snd x \<or> interval_upperbound i $ fst x = snd x)"
      using as(1-3,5) unfolding l interval_split interval_ne_empty as interval_bounds[OF *] Cart_lambda_beta apply-
      apply rule defer apply(rule,assumption) apply(rule_tac x="{u..v}" in bexI) unfolding interval_bounds[OF **]
      apply(case_tac[!] "fst x = k") using assms by auto qed qed

lemma division_points_psubset:
  assumes "d division_of {a..b}"  "\<forall>i. a$i < b$i"  "a$k < c" "c < b$k"
  "l \<in> d" "interval_lowerbound l$k = c \<or> interval_upperbound l$k = c"
  shows "division_points ({a..b} \<inter> {x. x$k \<le> c}) {l \<inter> {x. x$k \<le> c} | l. l\<in>d \<and> l \<inter> {x. x$k \<le> c} \<noteq> {}} \<subset> division_points ({a..b}) d" (is "?D1 \<subset> ?D") 
        "division_points ({a..b} \<inter> {x. x$k \<ge> c}) {l \<inter> {x. x$k \<ge> c} | l. l\<in>d \<and> l \<inter> {x. x$k \<ge> c} \<noteq> {}} \<subset> division_points ({a..b}) d" (is "?D2 \<subset> ?D") 
proof- have ab:"\<forall>i. a$i \<le> b$i" using assms(2) by(auto intro!:less_imp_le)
  guess u v using division_ofD(4)[OF assms(1,5)] apply-by(erule exE)+ note l=this
  have uv:"\<forall>i. u$i \<le> v$i" "\<forall>i. a$i \<le> u$i \<and> v$i \<le> b$i" using division_ofD(2,2,3)[OF assms(1,5)] unfolding l interval_ne_empty
    unfolding subset_eq apply- defer apply(erule_tac x=u in ballE, erule_tac x=v in ballE) unfolding mem_interval by auto
  have *:"interval_upperbound ({a..b} \<inter> {x. x $ k \<le> interval_upperbound l $ k}) $ k = interval_upperbound l $ k"
         "interval_upperbound ({a..b} \<inter> {x. x $ k \<le> interval_lowerbound l $ k}) $ k = interval_lowerbound l $ k"
    unfolding interval_split apply(subst interval_bounds) prefer 3 apply(subst interval_bounds)
    unfolding l interval_bounds[OF uv(1)] using uv[rule_format,of k] ab by auto
  have "\<exists>x. x \<in> ?D - ?D1" using assms(2-) apply-apply(erule disjE)
    apply(rule_tac x="(k,(interval_lowerbound l)$k)" in exI) defer
    apply(rule_tac x="(k,(interval_upperbound l)$k)" in exI)
    unfolding division_points_def unfolding interval_bounds[OF ab]
    apply (auto simp add:interval_bounds) unfolding * by auto
  thus "?D1 \<subset> ?D" apply-apply(rule,rule division_points_subset[OF assms(1-4)]) by auto

  have *:"interval_lowerbound ({a..b} \<inter> {x. x $ k \<ge> interval_lowerbound l $ k}) $ k = interval_lowerbound l $ k"
         "interval_lowerbound ({a..b} \<inter> {x. x $ k \<ge> interval_upperbound l $ k}) $ k = interval_upperbound l $ k"
    unfolding interval_split apply(subst interval_bounds) prefer 3 apply(subst interval_bounds)
    unfolding l interval_bounds[OF uv(1)] using uv[rule_format,of k] ab by auto
  have "\<exists>x. x \<in> ?D - ?D2" using assms(2-) apply-apply(erule disjE)
    apply(rule_tac x="(k,(interval_lowerbound l)$k)" in exI) defer
    apply(rule_tac x="(k,(interval_upperbound l)$k)" in exI)
    unfolding division_points_def unfolding interval_bounds[OF ab]
    apply (auto simp add:interval_bounds) unfolding * by auto
  thus "?D2 \<subset> ?D" apply-apply(rule,rule division_points_subset[OF assms(1-4)]) by auto qed

subsection {* Preservation by divisions and tagged divisions. *}

lemma support_support[simp]:"support opp f (support opp f s) = support opp f s"
  unfolding support_def by auto

lemma iterate_support[simp]: "iterate opp (support opp f s) f = iterate opp s f"
  unfolding iterate_def support_support by auto

lemma iterate_expand_cases:
  "iterate opp s f = (if finite(support opp f s) then iterate opp (support opp f s) f else neutral opp)"
  apply(cases) apply(subst if_P,assumption) unfolding iterate_def support_support fold'_def by auto 

lemma iterate_image: assumes "monoidal opp"  "inj_on f s"
  shows "iterate opp (f ` s) g = iterate opp s (g \<circ> f)"
proof- have *:"\<And>s. finite s \<Longrightarrow>  \<forall>x\<in>s. \<forall>y\<in>s. f x = f y \<longrightarrow> x = y \<Longrightarrow>
     iterate opp (f ` s) g = iterate opp s (g \<circ> f)"
  proof- case goal1 show ?case using goal1
    proof(induct s) case empty thus ?case using assms(1) by auto
    next case (insert x s) show ?case unfolding iterate_insert[OF assms(1) insert(1)]
        unfolding if_not_P[OF insert(2)] apply(subst insert(3)[THEN sym])
        unfolding image_insert defer apply(subst iterate_insert[OF assms(1)])
        apply(rule finite_imageI insert)+ apply(subst if_not_P)
        unfolding image_iff o_def using insert(2,4) by auto
    qed qed
  show ?thesis 
    apply(cases "finite (support opp g (f ` s))")
    apply(subst (1) iterate_support[THEN sym],subst (2) iterate_support[THEN sym])
    unfolding support_clauses apply(rule *)apply(rule finite_imageD,assumption) unfolding inj_on_def[symmetric]
    apply(rule subset_inj_on[OF assms(2) support_subset])+
    apply(subst iterate_expand_cases) unfolding support_clauses apply(simp only: if_False)
    apply(subst iterate_expand_cases) apply(subst if_not_P) by auto qed


(* This lemma about iterations comes up in a few places.                     *)
lemma iterate_nonzero_image_lemma:
  assumes "monoidal opp" "finite s" "g(a) = neutral opp"
  "\<forall>x\<in>s. \<forall>y\<in>s. f x = f y \<and> x \<noteq> y \<longrightarrow> g(f x) = neutral opp"
  shows "iterate opp {f x | x. x \<in> s \<and> f x \<noteq> a} g = iterate opp s (g \<circ> f)"
proof- have *:"{f x |x. x \<in> s \<and> ~(f x = a)} = f ` {x. x \<in> s \<and> ~(f x = a)}" by auto
  have **:"support opp (g \<circ> f) {x \<in> s. f x \<noteq> a} = support opp (g \<circ> f) s"
    unfolding support_def using assms(3) by auto
  show ?thesis unfolding *
    apply(subst iterate_support[THEN sym]) unfolding support_clauses
    apply(subst iterate_image[OF assms(1)]) defer
    apply(subst(2) iterate_support[THEN sym]) apply(subst **)
    unfolding inj_on_def using assms(3,4) unfolding support_def by auto qed

lemma iterate_eq_neutral:
  assumes "monoidal opp"  "\<forall>x \<in> s. (f(x) = neutral opp)"
  shows "(iterate opp s f = neutral opp)"
proof- have *:"support opp f s = {}" unfolding support_def using assms(2) by auto
  show ?thesis apply(subst iterate_support[THEN sym]) 
    unfolding * using assms(1) by auto qed

lemma iterate_op: assumes "monoidal opp" "finite s"
  shows "iterate opp s (\<lambda>x. opp (f x) (g x)) = opp (iterate opp s f) (iterate opp s g)" using assms(2)
proof(induct s) case empty thus ?case unfolding iterate_insert[OF assms(1)] using assms(1) by auto
next case (insert x F) show ?case unfolding iterate_insert[OF assms(1) insert(1)] if_not_P[OF insert(2)] insert(3)
    unfolding monoidal_ac[OF assms(1)] by(rule refl) qed

lemma iterate_eq: assumes "monoidal opp" "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "iterate opp s f = iterate opp s g"
proof- have *:"support opp g s = support opp f s"
    unfolding support_def using assms(2) by auto
  show ?thesis
  proof(cases "finite (support opp f s)")
    case False thus ?thesis apply(subst iterate_expand_cases,subst(2) iterate_expand_cases)
      unfolding * by auto
  next def su \<equiv> "support opp f s"
    case True note support_subset[of opp f s] 
    thus ?thesis apply- apply(subst iterate_support[THEN sym],subst(2) iterate_support[THEN sym]) unfolding * using True
      unfolding su_def[symmetric]
    proof(induct su) case empty show ?case by auto
    next case (insert x s) show ?case unfolding iterate_insert[OF assms(1) insert(1)] 
        unfolding if_not_P[OF insert(2)] apply(subst insert(3))
        defer apply(subst assms(2)[of x]) using insert by auto qed qed qed

lemma nonempty_witness: assumes "s \<noteq> {}" obtains x where "x \<in> s" using assms by auto

lemma operative_division: fixes f::"(real^'n) set \<Rightarrow> 'a"
  assumes "monoidal opp" "operative opp f" "d division_of {a..b}"
  shows "iterate opp d f = f {a..b}"
proof- def C \<equiv> "card (division_points {a..b} d)" thus ?thesis using assms
  proof(induct C arbitrary:a b d rule:full_nat_induct)
    case goal1
    { presume *:"content {a..b} \<noteq> 0 \<Longrightarrow> ?case"
      thus ?case apply-apply(cases) defer apply assumption
      proof- assume as:"content {a..b} = 0"
        show ?case unfolding operativeD(1)[OF assms(2) as] apply(rule iterate_eq_neutral[OF goal1(2)])
        proof fix x assume x:"x\<in>d"
          then guess u v apply(drule_tac division_ofD(4)[OF goal1(4)]) by(erule exE)+
          thus "f x = neutral opp" using division_of_content_0[OF as goal1(4)] 
            using operativeD(1)[OF assms(2)] x by auto
        qed qed }
    assume "content {a..b} \<noteq> 0" note ab = this[unfolded content_lt_nz[THEN sym] content_pos_lt_eq]
    hence ab':"\<forall>i. a$i \<le> b$i" by (auto intro!: less_imp_le) show ?case 
    proof(cases "division_points {a..b} d = {}")
      case True have d':"\<forall>i\<in>d. \<exists>u v. i = {u..v} \<and>
        (\<forall>j. u$j = a$j \<and> v$j = a$j \<or> u$j = b$j \<and> v$j = b$j \<or> u$j = a$j \<and> v$j = b$j)"
        unfolding forall_in_division[OF goal1(4)] apply(rule,rule,rule)
        apply(rule_tac x=a in exI,rule_tac x=b in exI) apply(rule,rule refl) apply(rule)
      proof- fix u v j assume as:"{u..v} \<in> d" note division_ofD(3)[OF goal1(4) this]
        hence uv:"\<forall>i. u$i \<le> v$i" "u$j \<le> v$j" unfolding interval_ne_empty by auto
        have *:"\<And>p r Q. p \<or> r \<or> (\<forall>x\<in>d. Q x) \<Longrightarrow> p \<or> r \<or> (Q {u..v})" using as by auto
        have "(j, u$j) \<notin> division_points {a..b} d"
          "(j, v$j) \<notin> division_points {a..b} d" using True by auto
        note this[unfolded de_Morgan_conj division_points_def mem_Collect_eq split_conv interval_bounds[OF ab'] bex_simps]
        note *[OF this(1)] *[OF this(2)] note this[unfolded interval_bounds[OF uv(1)]]
        moreover have "a$j \<le> u$j" "v$j \<le> b$j" using division_ofD(2,2,3)[OF goal1(4) as] 
          unfolding subset_eq apply- apply(erule_tac x=u in ballE,erule_tac[3] x=v in ballE)
          unfolding interval_ne_empty mem_interval by auto
        ultimately show "u$j = a$j \<and> v$j = a$j \<or> u$j = b$j \<and> v$j = b$j \<or> u$j = a$j \<and> v$j = b$j"
          unfolding not_less de_Morgan_disj using ab[rule_format,of j] uv(2) by auto
      qed have "(1/2) *\<^sub>R (a+b) \<in> {a..b}" unfolding mem_interval using ab by(auto intro!:less_imp_le)
      note this[unfolded division_ofD(6)[OF goal1(4),THEN sym] Union_iff]
      then guess i .. note i=this guess u v using d'[rule_format,OF i(1)] apply-by(erule exE conjE)+ note uv=this
      have "{a..b} \<in> d"
      proof- { presume "i = {a..b}" thus ?thesis using i by auto }
        { presume "u = a" "v = b" thus "i = {a..b}" using uv by auto }
        show "u = a" "v = b" unfolding Cart_eq
        proof(rule_tac[!] allI) fix j note i(2)[unfolded uv mem_interval,rule_format,of j]
          thus "u $ j = a $ j" "v $ j = b $ j" using uv(2)[rule_format,of j] by auto
        qed qed
      hence *:"d = insert {a..b} (d - {{a..b}})" by auto
      have "iterate opp (d - {{a..b}}) f = neutral opp" apply(rule iterate_eq_neutral[OF goal1(2)])
      proof fix x assume x:"x \<in> d - {{a..b}}" hence "x\<in>d" by auto note d'[rule_format,OF this]
        then guess u v apply-by(erule exE conjE)+ note uv=this
        have "u\<noteq>a \<or> v\<noteq>b" using x[unfolded uv] by auto  
        then obtain j where "u$j \<noteq> a$j \<or> v$j \<noteq> b$j" unfolding Cart_eq by auto
        hence "u$j = v$j" using uv(2)[rule_format,of j] by auto
        hence "content {u..v} = 0"  unfolding content_eq_0 apply(rule_tac x=j in exI) by auto
        thus "f x = neutral opp" unfolding uv(1) by(rule operativeD(1)[OF goal1(3)])
      qed thus "iterate opp d f = f {a..b}" apply-apply(subst *) 
        apply(subst iterate_insert[OF goal1(2)]) using goal1(2,4) by auto
    next case False hence "\<exists>x. x\<in>division_points {a..b} d" by auto
      then guess k c unfolding split_paired_Ex apply- unfolding division_points_def mem_Collect_eq split_conv
        by(erule exE conjE)+ note kc=this[unfolded interval_bounds[OF ab']]
      from this(3) guess j .. note j=this
      def d1 \<equiv> "{l \<inter> {x. x$k \<le> c} | l. l \<in> d \<and> l \<inter> {x. x$k \<le> c} \<noteq> {}}"
      def d2 \<equiv> "{l \<inter> {x. x$k \<ge> c} | l. l \<in> d \<and> l \<inter> {x. x$k \<ge> c} \<noteq> {}}"
      def cb \<equiv> "(\<chi> i. if i = k then c else b$i)" and ca \<equiv> "(\<chi> i. if i = k then c else a$i)"
      note division_points_psubset[OF goal1(4) ab kc(1-2) j]
      note psubset_card_mono[OF _ this(1)] psubset_card_mono[OF _ this(2)]
      hence *:"(iterate opp d1 f) = f ({a..b} \<inter> {x. x$k \<le> c})" "(iterate opp d2 f) = f ({a..b} \<inter> {x. x$k \<ge> c})"
        apply- unfolding interval_split apply(rule_tac[!] goal1(1)[rule_format])
        using division_split[OF goal1(4), where k=k and c=c]
        unfolding interval_split d1_def[symmetric] d2_def[symmetric] unfolding goal1(2) Suc_le_mono
        using goal1(2-3) using division_points_finite[OF goal1(4)] by auto
      have "f {a..b} = opp (iterate opp d1 f) (iterate opp d2 f)" (is "_ = ?prev")
        unfolding * apply(rule operativeD(2)) using goal1(3) .
      also have "iterate opp d1 f = iterate opp d (\<lambda>l. f(l \<inter> {x. x$k \<le> c}))"
        unfolding d1_def apply(rule iterate_nonzero_image_lemma[unfolded o_def])
        unfolding empty_as_interval apply(rule goal1 division_of_finite operativeD[OF goal1(3)])+
        unfolding empty_as_interval[THEN sym] apply(rule content_empty)
      proof(rule,rule,rule,erule conjE) fix l y assume as:"l \<in> d" "y \<in> d" "l \<inter> {x. x $ k \<le> c} = y \<inter> {x. x $ k \<le> c}" "l \<noteq> y" 
        from division_ofD(4)[OF goal1(4) this(1)] guess u v apply-by(erule exE)+ note l=this
        show "f (l \<inter> {x. x $ k \<le> c}) = neutral opp" unfolding l interval_split
          apply(rule operativeD(1) goal1)+ unfolding interval_split[THEN sym] apply(rule division_split_left_inj)
          apply(rule goal1) unfolding l[THEN sym] apply(rule as(1),rule as(2)) by(rule as)+
      qed also have "iterate opp d2 f = iterate opp d (\<lambda>l. f(l \<inter> {x. x$k \<ge> c}))"
        unfolding d2_def apply(rule iterate_nonzero_image_lemma[unfolded o_def])
        unfolding empty_as_interval apply(rule goal1 division_of_finite operativeD[OF goal1(3)])+
        unfolding empty_as_interval[THEN sym] apply(rule content_empty)
      proof(rule,rule,rule,erule conjE) fix l y assume as:"l \<in> d" "y \<in> d" "l \<inter> {x. c \<le> x $ k} = y \<inter> {x. c \<le> x $ k}" "l \<noteq> y" 
        from division_ofD(4)[OF goal1(4) this(1)] guess u v apply-by(erule exE)+ note l=this
        show "f (l \<inter> {x. x $ k \<ge> c}) = neutral opp" unfolding l interval_split
          apply(rule operativeD(1) goal1)+ unfolding interval_split[THEN sym] apply(rule division_split_right_inj)
          apply(rule goal1) unfolding l[THEN sym] apply(rule as(1),rule as(2)) by(rule as)+
      qed also have *:"\<forall>x\<in>d. f x = opp (f (x \<inter> {x. x $ k \<le> c})) (f (x \<inter> {x. c \<le> x $ k}))"
        unfolding forall_in_division[OF goal1(4)] apply(rule,rule,rule,rule operativeD(2)) using goal1(3) .
      have "opp (iterate opp d (\<lambda>l. f (l \<inter> {x. x $ k \<le> c}))) (iterate opp d (\<lambda>l. f (l \<inter> {x. c \<le> x $ k})))
        = iterate opp d f" apply(subst(3) iterate_eq[OF _ *[rule_format]]) prefer 3
        apply(rule iterate_op[THEN sym]) using goal1 by auto
      finally show ?thesis by auto
    qed qed qed 

lemma iterate_image_nonzero: assumes "monoidal opp"
  "finite s" "\<forall>x\<in>s. \<forall>y\<in>s. ~(x = y) \<and> f x = f y \<longrightarrow> g(f x) = neutral opp"
  shows "iterate opp (f ` s) g = iterate opp s (g \<circ> f)" using assms
proof(induct rule:finite_subset_induct[OF assms(2) subset_refl])
  case goal1 show ?case using assms(1) by auto
next case goal2 have *:"\<And>x y. y = neutral opp \<Longrightarrow> x = opp y x" using assms(1) by auto
  show ?case unfolding image_insert apply(subst iterate_insert[OF assms(1)])
    apply(rule finite_imageI goal2)+
    apply(cases "f a \<in> f ` F") unfolding if_P if_not_P apply(subst goal2(4)[OF assms(1) goal2(1)]) defer
    apply(subst iterate_insert[OF assms(1) goal2(1)]) defer
    apply(subst iterate_insert[OF assms(1) goal2(1)])
    unfolding if_not_P[OF goal2(3)] defer unfolding image_iff defer apply(erule bexE)
    apply(rule *) unfolding o_def apply(rule_tac y=x in goal2(7)[rule_format])
    using goal2 unfolding o_def by auto qed 

lemma operative_tagged_division: assumes "monoidal opp" "operative opp f" "d tagged_division_of {a..b}"
  shows "iterate(opp) d (\<lambda>(x,l). f l) = f {a..b}"
proof- have *:"(\<lambda>(x,l). f l) = (f o snd)" unfolding o_def by(rule,auto) note assm = tagged_division_ofD[OF assms(3)]
  have "iterate(opp) d (\<lambda>(x,l). f l) = iterate opp (snd ` d) f" unfolding *
    apply(rule iterate_image_nonzero[THEN sym,OF assms(1)]) apply(rule tagged_division_of_finite assms)+ 
    unfolding Ball_def split_paired_All snd_conv apply(rule,rule,rule,rule,rule,rule,rule,erule conjE)
  proof- fix a b aa ba assume as:"(a, b) \<in> d" "(aa, ba) \<in> d" "(a, b) \<noteq> (aa, ba)" "b = ba"
    guess u v using assm(4)[OF as(1)] apply-by(erule exE)+ note uv=this
    show "f b = neutral opp" unfolding uv apply(rule operativeD(1)[OF assms(2)])
      unfolding content_eq_0_interior using tagged_division_ofD(5)[OF assms(3) as(1-3)]
      unfolding as(4)[THEN sym] uv by auto
  qed also have "\<dots> = f {a..b}" 
    using operative_division[OF assms(1-2) division_of_tagged_division[OF assms(3)]] .
  finally show ?thesis . qed

subsection {* Additivity of content. *}

lemma setsum_iterate:assumes "finite s" shows "setsum f s = iterate op + s f"
proof- have *:"setsum f s = setsum f (support op + f s)"
    apply(rule setsum_mono_zero_right)
    unfolding support_def neutral_monoid using assms by auto
  thus ?thesis unfolding * setsum_def iterate_def fold_image_def fold'_def
    unfolding neutral_monoid . qed

lemma additive_content_division: assumes "d division_of {a..b}"
  shows "setsum content d = content({a..b})"
  unfolding operative_division[OF monoidal_monoid operative_content assms,THEN sym]
  apply(subst setsum_iterate) using assms by auto

lemma additive_content_tagged_division:
  assumes "d tagged_division_of {a..b}"
  shows "setsum (\<lambda>(x,l). content l) d = content({a..b})"
  unfolding operative_tagged_division[OF monoidal_monoid operative_content assms,THEN sym]
  apply(subst setsum_iterate) using assms by auto

subsection {* Finally, the integral of a constant\<forall> *}

lemma has_integral_const[intro]:
  "((\<lambda>x. c) has_integral (content({a..b::real^'n}) *\<^sub>R c)) ({a..b})"
  unfolding has_integral apply(rule,rule,rule_tac x="\<lambda>x. ball x 1" in exI)
  apply(rule,rule gauge_trivial)apply(rule,rule,erule conjE)
  unfolding split_def apply(subst scaleR_left.setsum[THEN sym, unfolded o_def])
  defer apply(subst additive_content_tagged_division[unfolded split_def]) apply assumption by auto

subsection {* Bounds on the norm of Riemann sums and the integral itself. *}

lemma dsum_bound: assumes "p division_of {a..b}" "norm(c) \<le> e"
  shows "norm(setsum (\<lambda>l. content l *\<^sub>R c) p) \<le> e * content({a..b})" (is "?l \<le> ?r")
  apply(rule order_trans,rule setsum_norm) defer unfolding norm_scaleR setsum_left_distrib[THEN sym]
  apply(rule order_trans[OF mult_left_mono],rule assms,rule setsum_abs_ge_zero)
  apply(subst real_mult_commute) apply(rule mult_left_mono)
  apply(rule order_trans[of _ "setsum content p"]) apply(rule eq_refl,rule setsum_cong2)
  apply(subst abs_of_nonneg) unfolding additive_content_division[OF assms(1)]
proof- from order_trans[OF norm_ge_zero[of c] assms(2)] show "0 \<le> e" .
  fix x assume "x\<in>p" from division_ofD(4)[OF assms(1) this] guess u v apply-by(erule exE)+
  thus "0 \<le> content x" using content_pos_le by auto
qed(insert assms,auto)

lemma rsum_bound: assumes "p tagged_division_of {a..b}" "\<forall>x\<in>{a..b}. norm(f x) \<le> e"
  shows "norm(setsum (\<lambda>(x,k). content k *\<^sub>R f x) p) \<le> e * content({a..b})"
proof(cases "{a..b} = {}") case True
  show ?thesis using assms(1) unfolding True tagged_division_of_trivial by auto
next case False show ?thesis
    apply(rule order_trans,rule setsum_norm) defer unfolding split_def norm_scaleR
    apply(rule order_trans[OF setsum_mono]) apply(rule mult_left_mono[OF _ abs_ge_zero, of _ e]) defer
    unfolding setsum_left_distrib[THEN sym] apply(subst real_mult_commute) apply(rule mult_left_mono)
    apply(rule order_trans[of _ "setsum (content \<circ> snd) p"]) apply(rule eq_refl,rule setsum_cong2)
    apply(subst o_def, rule abs_of_nonneg)
  proof- show "setsum (content \<circ> snd) p \<le> content {a..b}" apply(rule eq_refl)
      unfolding additive_content_tagged_division[OF assms(1),THEN sym] split_def by auto
    guess w using nonempty_witness[OF False] .
    thus "e\<ge>0" apply-apply(rule order_trans) defer apply(rule assms(2)[rule_format],assumption) by auto
    fix xk assume *:"xk\<in>p" guess x k  using surj_pair[of xk] apply-by(erule exE)+ note xk = this *[unfolded this]
    from tagged_division_ofD(4)[OF assms(1) xk(2)] guess u v apply-by(erule exE)+ note uv=this
    show "0\<le> content (snd xk)" unfolding xk snd_conv uv by(rule content_pos_le)
    show "norm (f (fst xk)) \<le> e" unfolding xk fst_conv using tagged_division_ofD(2,3)[OF assms(1) xk(2)] assms(2) by auto
  qed(insert assms,auto) qed

lemma rsum_diff_bound:
  assumes "p tagged_division_of {a..b}"  "\<forall>x\<in>{a..b}. norm(f x - g x) \<le> e"
  shows "norm(setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - setsum (\<lambda>(x,k). content k *\<^sub>R g x) p) \<le> e * content({a..b})"
  apply(rule order_trans[OF _ rsum_bound[OF assms]]) apply(rule eq_refl) apply(rule arg_cong[where f=norm])
  unfolding setsum_subtractf[THEN sym] apply(rule setsum_cong2) unfolding scaleR.diff_right by auto

lemma has_integral_bound: fixes f::"real^'n \<Rightarrow> 'a::real_normed_vector"
  assumes "0 \<le> B" "(f has_integral i) ({a..b})" "\<forall>x\<in>{a..b}. norm(f x) \<le> B"
  shows "norm i \<le> B * content {a..b}"
proof- let ?P = "content {a..b} > 0" { presume "?P \<Longrightarrow> ?thesis"
    thus ?thesis proof(cases ?P) case False
      hence *:"content {a..b} = 0" using content_lt_nz by auto
      hence **:"i = 0" using assms(2) apply(subst has_integral_null_eq[THEN sym]) by auto
      show ?thesis unfolding * ** using assms(1) by auto
    qed auto } assume ab:?P
  { presume "\<not> ?thesis \<Longrightarrow> False" thus ?thesis by auto }
  assume "\<not> ?thesis" hence *:"norm i - B * content {a..b} > 0" by auto
  from assms(2)[unfolded has_integral,rule_format,OF *] guess d apply-by(erule exE conjE)+ note d=this[rule_format]
  from fine_division_exists[OF this(1), of a b] guess p . note p=this
  have *:"\<And>s B. norm s \<le> B \<Longrightarrow> \<not> (norm (s - i) < norm i - B)"
  proof- case goal1 thus ?case unfolding not_less
    using norm_triangle_sub[of i s] unfolding norm_minus_commute by auto
  qed show False using d(2)[OF conjI[OF p]] *[OF rsum_bound[OF p(1) assms(3)]] by auto qed

subsection {* Similar theorems about relationship among components. *}

lemma rsum_component_le: fixes f::"real^'n \<Rightarrow> real^'m"
  assumes "p tagged_division_of {a..b}"  "\<forall>x\<in>{a..b}. (f x)$i \<le> (g x)$i"
  shows "(setsum (\<lambda>(x,k). content k *\<^sub>R f x) p)$i \<le> (setsum (\<lambda>(x,k). content k *\<^sub>R g x) p)$i"
  unfolding setsum_component apply(rule setsum_mono)
  apply(rule mp) defer apply assumption apply(induct_tac x,rule) unfolding split_conv
proof- fix a b assume ab:"(a,b) \<in> p" note assm = tagged_division_ofD(2-4)[OF assms(1) ab]
  from this(3) guess u v apply-by(erule exE)+ note b=this
  show "(content b *\<^sub>R f a) $ i \<le> (content b *\<^sub>R g a) $ i" unfolding b
    unfolding Cart_nth.scaleR real_scaleR_def apply(rule mult_left_mono)
    defer apply(rule content_pos_le,rule assms(2)[rule_format]) using assm by auto qed

lemma has_integral_component_le: fixes f::"real^'n \<Rightarrow> real^'m"
  assumes "(f has_integral i) s" "(g has_integral j) s"  "\<forall>x\<in>s. (f x)$k \<le> (g x)$k"
  shows "i$k \<le> j$k"
proof- have lem:"\<And>a b g i j. \<And>f::real^'n \<Rightarrow> real^'m. (f has_integral i) ({a..b}) \<Longrightarrow> 
    (g has_integral j) ({a..b}) \<Longrightarrow> \<forall>x\<in>{a..b}. (f x)$k \<le> (g x)$k \<Longrightarrow> i$k \<le> j$k"
  proof(rule ccontr) case goal1 hence *:"0 < (i$k - j$k) / 3" by auto
    guess d1 using goal1(1)[unfolded has_integral,rule_format,OF *] apply-by(erule exE conjE)+ note d1=this[rule_format]
    guess d2 using goal1(2)[unfolded has_integral,rule_format,OF *] apply-by(erule exE conjE)+ note d2=this[rule_format]
    guess p using fine_division_exists[OF gauge_inter[OF d1(1) d2(1)], of a b] unfolding fine_inter .
    note p = this(1) conjunctD2[OF this(2)]  note le_less_trans[OF component_le_norm, of _ _ k]
    note this[OF d1(2)[OF conjI[OF p(1,2)]]] this[OF d2(2)[OF conjI[OF p(1,3)]]]
    thus False unfolding Cart_nth.diff using rsum_component_le[OF p(1) goal1(3)] by smt
  qed let ?P = "\<exists>a b. s = {a..b}"
  { presume "\<not> ?P \<Longrightarrow> ?thesis" thus ?thesis proof(cases ?P)
      case True then guess a b apply-by(erule exE)+ note s=this
      show ?thesis apply(rule lem) using assms[unfolded s] by auto
    qed auto } assume as:"\<not> ?P"
  { presume "\<not> ?thesis \<Longrightarrow> False" thus ?thesis by auto }
  assume "\<not> i$k \<le> j$k" hence ij:"(i$k - j$k) / 3 > 0" by auto
  note has_integral_altD[OF _ as this] from this[OF assms(1)] this[OF assms(2)] guess B1 B2 . note B=this[rule_format]
  have "bounded (ball 0 B1 \<union> ball (0::real^'n) B2)" unfolding bounded_Un by(rule conjI bounded_ball)+
  from bounded_subset_closed_interval[OF this] guess a b apply- by(erule exE)+
  note ab = conjunctD2[OF this[unfolded Un_subset_iff]]
  guess w1 using B(2)[OF ab(1)] .. note w1=conjunctD2[OF this]
  guess w2 using B(4)[OF ab(2)] .. note w2=conjunctD2[OF this]
  have *:"\<And>w1 w2 j i::real .\<bar>w1 - i\<bar> < (i - j) / 3 \<Longrightarrow> \<bar>w2 - j\<bar> < (i - j) / 3 \<Longrightarrow> w1 \<le> w2 \<Longrightarrow> False" by smt(*SMTSMT*)
  note le_less_trans[OF component_le_norm[of _ k]] note this[OF w1(2)] this[OF w2(2)] moreover
  have "w1$k \<le> w2$k" apply(rule lem[OF w1(1) w2(1)]) using assms by auto ultimately
  show False unfolding Cart_nth.diff by(rule *) qed

lemma integral_component_le: fixes f::"real^'n \<Rightarrow> real^'m"
  assumes "f integrable_on s" "g integrable_on s"  "\<forall>x\<in>s. (f x)$k \<le> (g x)$k"
  shows "(integral s f)$k \<le> (integral s g)$k"
  apply(rule has_integral_component_le) using integrable_integral assms by auto

lemma has_integral_dest_vec1_le: fixes f::"real^'n \<Rightarrow> real^1"
  assumes "(f has_integral i) s"  "(g has_integral j) s" "\<forall>x\<in>s. f x \<le> g x"
  shows "dest_vec1 i \<le> dest_vec1 j" apply(rule has_integral_component_le[OF assms(1-2)])
  using assms(3) unfolding vector_le_def by auto

lemma integral_dest_vec1_le: fixes f::"real^'n \<Rightarrow> real^1"
  assumes "f integrable_on s" "g integrable_on s" "\<forall>x\<in>s. f x \<le> g x"
  shows "dest_vec1(integral s f) \<le> dest_vec1(integral s g)"
  apply(rule has_integral_dest_vec1_le) apply(rule_tac[1-2] integrable_integral) using assms by auto

lemma has_integral_component_pos: fixes f::"real^'n \<Rightarrow> real^'m"
  assumes "(f has_integral i) s" "\<forall>x\<in>s. 0 \<le> (f x)$k" shows "0 \<le> i$k"
  using has_integral_component_le[OF has_integral_0 assms(1)] using assms(2) by auto

lemma integral_component_pos: fixes f::"real^'n \<Rightarrow> real^'m"
  assumes "f integrable_on s" "\<forall>x\<in>s. 0 \<le> (f x)$k" shows "0 \<le> (integral s f)$k"
  apply(rule has_integral_component_pos) using assms by auto

lemma has_integral_dest_vec1_pos: fixes f::"real^'n \<Rightarrow> real^1"
  assumes "(f has_integral i) s" "\<forall>x\<in>s. 0 \<le> f x" shows "0 \<le> i"
  using has_integral_component_pos[OF assms(1), of 1]
  using assms(2) unfolding vector_le_def by auto

lemma integral_dest_vec1_pos: fixes f::"real^'n \<Rightarrow> real^1"
  assumes "f integrable_on s" "\<forall>x\<in>s. 0 \<le> f x" shows "0 \<le> integral s f"
  apply(rule has_integral_dest_vec1_pos) using assms by auto

lemma has_integral_component_neg: fixes f::"real^'n \<Rightarrow> real^'m"
  assumes "(f has_integral i) s" "\<forall>x\<in>s. (f x)$k \<le> 0" shows "i$k \<le> 0"
  using has_integral_component_le[OF assms(1) has_integral_0] assms(2) by auto

lemma has_integral_dest_vec1_neg: fixes f::"real^'n \<Rightarrow> real^1"
  assumes "(f has_integral i) s" "\<forall>x\<in>s. f x \<le> 0" shows "i \<le> 0"
  using has_integral_component_neg[OF assms(1),of 1] using assms(2) by auto

lemma has_integral_component_lbound:
  assumes "(f has_integral i) {a..b}"  "\<forall>x\<in>{a..b}. B \<le> f(x)$k" shows "B * content {a..b} \<le> i$k"
  using has_integral_component_le[OF has_integral_const assms(1),of "(\<chi> i. B)" k] assms(2)
  unfolding Cart_lambda_beta vector_scaleR_component by(auto simp add:field_simps)

lemma has_integral_component_ubound: 
  assumes "(f has_integral i) {a..b}" "\<forall>x\<in>{a..b}. f x$k \<le> B"
  shows "i$k \<le> B * content({a..b})"
  using has_integral_component_le[OF assms(1) has_integral_const, of k "vec B"]
  unfolding vec_component Cart_nth.scaleR using assms(2) by(auto simp add:field_simps)

lemma integral_component_lbound:
  assumes "f integrable_on {a..b}" "\<forall>x\<in>{a..b}. B \<le> f(x)$k"
  shows "B * content({a..b}) \<le> (integral({a..b}) f)$k"
  apply(rule has_integral_component_lbound) using assms unfolding has_integral_integral by auto

lemma integral_component_ubound:
  assumes "f integrable_on {a..b}" "\<forall>x\<in>{a..b}. f(x)$k \<le> B"
  shows "(integral({a..b}) f)$k \<le> B * content({a..b})"
  apply(rule has_integral_component_ubound) using assms unfolding has_integral_integral by auto

subsection {* Uniform limit of integrable functions is integrable. *}

lemma real_arch_invD:
  "0 < (e::real) \<Longrightarrow> (\<exists>n::nat. n \<noteq> 0 \<and> 0 < inverse (real n) \<and> inverse (real n) < e)"
  by(subst(asm) real_arch_inv)

lemma integrable_uniform_limit: fixes f::"real^'n \<Rightarrow> 'a::banach"
  assumes "\<forall>e>0. \<exists>g. (\<forall>x\<in>{a..b}. norm(f x - g x) \<le> e) \<and> g integrable_on {a..b}"
  shows "f integrable_on {a..b}"
proof- { presume *:"content {a..b} > 0 \<Longrightarrow> ?thesis"
    show ?thesis apply cases apply(rule *,assumption)
      unfolding content_lt_nz integrable_on_def using has_integral_null by auto }
  assume as:"content {a..b} > 0"
  have *:"\<And>P. \<forall>e>(0::real). P e \<Longrightarrow> \<forall>n::nat. P (inverse (real n+1))" by auto
  from choice[OF *[OF assms]] guess g .. note g=conjunctD2[OF this[rule_format],rule_format]
  from choice[OF allI[OF g(2)[unfolded integrable_on_def], of "\<lambda>x. x"]] guess i .. note i=this[rule_format]
  
  have "Cauchy i" unfolding Cauchy_def
  proof(rule,rule) fix e::real assume "e>0"
    hence "e / 4 / content {a..b} > 0" using as by(auto simp add:field_simps)
    then guess M apply-apply(subst(asm) real_arch_inv) by(erule exE conjE)+ note M=this
    show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (i m) (i n) < e" apply(rule_tac x=M in exI,rule,rule,rule,rule)
    proof- case goal1 have "e/4>0" using `e>0` by auto note * = i[unfolded has_integral,rule_format,OF this]
      from *[of m] guess gm apply-by(erule conjE exE)+ note gm=this[rule_format]
      from *[of n] guess gn apply-by(erule conjE exE)+ note gn=this[rule_format]
      from fine_division_exists[OF gauge_inter[OF gm(1) gn(1)], of a b] guess p . note p=this
      have lem2:"\<And>s1 s2 i1 i2. norm(s2 - s1) \<le> e/2 \<Longrightarrow> norm(s1 - i1) < e / 4 \<Longrightarrow> norm(s2 - i2) < e / 4 \<Longrightarrow>norm(i1 - i2) < e"
      proof- case goal1 have "norm (i1 - i2) \<le> norm (i1 - s1) + norm (s1 - s2) + norm (s2 - i2)"
          using norm_triangle_ineq[of "i1 - s1" "s1 - i2"]
          using norm_triangle_ineq[of "s1 - s2" "s2 - i2"] by(auto simp add:group_simps)
        also have "\<dots> < e" using goal1 unfolding norm_minus_commute by(auto simp add:group_simps)
        finally show ?case .
      qed
      show ?case unfolding vector_dist_norm apply(rule lem2) defer
        apply(rule gm(2)[OF conjI[OF p(1)]],rule_tac[2] gn(2)[OF conjI[OF p(1)]])
        using conjunctD2[OF p(2)[unfolded fine_inter]] apply- apply assumption+ apply(rule order_trans)
        apply(rule rsum_diff_bound[OF p(1), where e="2 / real M"])
      proof show "2 / real M * content {a..b} \<le> e / 2" unfolding divide_inverse 
          using M as by(auto simp add:field_simps)
        fix x assume x:"x \<in> {a..b}"
        have "norm (f x - g n x) + norm (f x - g m x) \<le> inverse (real n + 1) + inverse (real m + 1)" 
            using g(1)[OF x, of n] g(1)[OF x, of m] by auto
        also have "\<dots> \<le> inverse (real M) + inverse (real M)" apply(rule add_mono)
          apply(rule_tac[!] le_imp_inverse_le) using goal1 M by auto
        also have "\<dots> = 2 / real M" unfolding real_divide_def by auto
        finally show "norm (g n x - g m x) \<le> 2 / real M"
          using norm_triangle_le[of "g n x - f x" "f x - g m x" "2 / real M"]
          by(auto simp add:group_simps simp add:norm_minus_commute)
      qed qed qed
  from this[unfolded convergent_eq_cauchy[THEN sym]] guess s .. note s=this

  show ?thesis unfolding integrable_on_def apply(rule_tac x=s in exI) unfolding has_integral
  proof(rule,rule)  
    case goal1 hence *:"e/3 > 0" by auto
    from s[unfolded Lim_sequentially,rule_format,OF this] guess N1 .. note N1=this
    from goal1 as have "e / 3 / content {a..b} > 0" by(auto simp add:field_simps)
    from real_arch_invD[OF this] guess N2 apply-by(erule exE conjE)+ note N2=this
    from i[of "N1 + N2",unfolded has_integral,rule_format,OF *] guess g' .. note g'=conjunctD2[OF this,rule_format]
    have lem:"\<And>sf sg i. norm(sf - sg) \<le> e / 3 \<Longrightarrow> norm(i - s) < e / 3 \<Longrightarrow> norm(sg - i) < e / 3 \<Longrightarrow> norm(sf - s) < e"
    proof- case goal1 have "norm (sf - s) \<le> norm (sf - sg) + norm (sg - i) + norm (i - s)"
        using norm_triangle_ineq[of "sf - sg" "sg - s"]
        using norm_triangle_ineq[of "sg -  i" " i - s"] by(auto simp add:group_simps)
      also have "\<dots> < e" using goal1 unfolding norm_minus_commute by(auto simp add:group_simps)
      finally show ?case .
    qed
    show ?case apply(rule_tac x=g' in exI) apply(rule,rule g')
    proof(rule,rule) fix p assume p:"p tagged_division_of {a..b} \<and> g' fine p" note * = g'(2)[OF this]
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - s) < e" apply-apply(rule lem[OF _ _ *])
        apply(rule order_trans,rule rsum_diff_bound[OF p[THEN conjunct1]]) apply(rule,rule g,assumption)
      proof- have "content {a..b} < e / 3 * (real N2)"
          using N2 unfolding inverse_eq_divide using as by(auto simp add:field_simps)
        hence "content {a..b} < e / 3 * (real (N1 + N2) + 1)"
          apply-apply(rule less_le_trans,assumption) using `e>0` by auto 
        thus "inverse (real (N1 + N2) + 1) * content {a..b} \<le> e / 3"
          unfolding inverse_eq_divide by(auto simp add:field_simps)
        show "norm (i (N1 + N2) - s) < e / 3" by(rule N1[rule_format,unfolded vector_dist_norm],auto)
      qed qed qed qed

subsection {* Negligible sets. *}

definition "indicator s \<equiv> (\<lambda>x. if x \<in> s then 1 else (0::real))"

lemma dest_vec1_indicator:
 "indicator s x = (if x \<in> s then 1 else 0)" unfolding indicator_def by auto

lemma indicator_pos_le[intro]: "0 \<le> (indicator s x)" unfolding indicator_def by auto

lemma indicator_le_1[intro]: "(indicator s x) \<le> 1" unfolding indicator_def by auto

lemma dest_vec1_indicator_abs_le_1: "abs(indicator s x) \<le> 1"
  unfolding indicator_def by auto

definition "negligible (s::(real^'n) set) \<equiv> (\<forall>a b. ((indicator s) has_integral 0) {a..b})"

lemma indicator_simps[simp]:"x\<in>s \<Longrightarrow> indicator s x = 1" "x\<notin>s \<Longrightarrow> indicator s x = 0"
  unfolding indicator_def by auto

subsection {* Negligibility of hyperplane. *}

lemma vsum_nonzero_image_lemma: 
  assumes "finite s" "g(a) = 0"
  "\<forall>x\<in>s. \<forall>y\<in>s. f x = f y \<and> x \<noteq> y \<longrightarrow> g(f x) = 0"
  shows "setsum g {f x |x. x \<in> s \<and> f x \<noteq> a} = setsum (g o f) s"
  unfolding setsum_iterate[OF assms(1)] apply(subst setsum_iterate) defer
  apply(rule iterate_nonzero_image_lemma) apply(rule assms monoidal_monoid)+
  unfolding assms using neutral_add unfolding neutral_add using assms by auto 

lemma interval_doublesplit: shows "{a..b} \<inter> {x . abs(x$k - c) \<le> (e::real)} =
  {(\<chi> i. if i = k then max (a$k) (c - e) else a$i) .. (\<chi> i. if i = k then min (b$k) (c + e) else b$i)}"
proof- have *:"\<And>x c e::real. abs(x - c) \<le> e \<longleftrightarrow> x \<ge> c - e \<and> x \<le> c + e" by auto
  have **:"\<And>s P Q. s \<inter> {x. P x \<and> Q x} = (s \<inter> {x. Q x}) \<inter> {x. P x}" by blast
  show ?thesis unfolding * ** interval_split by(rule refl) qed

lemma division_doublesplit: assumes "p division_of {a..b::real^'n}" 
  shows "{l \<inter> {x. abs(x$k - c) \<le> e} |l. l \<in> p \<and> l \<inter> {x. abs(x$k - c) \<le> e} \<noteq> {}} division_of ({a..b} \<inter> {x. abs(x$k - c) \<le> e})"
proof- have *:"\<And>x c. abs(x - c) \<le> e \<longleftrightarrow> x \<ge> c - e \<and> x \<le> c + e" by auto
  have **:"\<And>p q p' q'. p division_of q \<Longrightarrow> p = p' \<Longrightarrow> q = q' \<Longrightarrow> p' division_of q'" by auto
  note division_split(1)[OF assms, where c="c+e" and k=k,unfolded interval_split]
  note division_split(2)[OF this, where c="c-e" and k=k] 
  thus ?thesis apply(rule **) unfolding interval_doublesplit unfolding * unfolding interval_split interval_doublesplit
    apply(rule set_ext) unfolding mem_Collect_eq apply rule apply(erule conjE exE)+ apply(rule_tac x=la in exI) defer
    apply(erule conjE exE)+ apply(rule_tac x="l \<inter> {x. c + e \<ge> x $ k}" in exI) apply rule defer apply rule
    apply(rule_tac x=l in exI) by blast+ qed

lemma content_doublesplit: assumes "0 < e"
  obtains d where "0 < d" "content({a..b} \<inter> {x. abs(x$k - c) \<le> d}) < e"
proof(cases "content {a..b} = 0")
  case True show ?thesis apply(rule that[of 1]) defer unfolding interval_doublesplit
    apply(rule le_less_trans[OF content_subset]) defer apply(subst True)
    unfolding interval_doublesplit[THEN sym] using assms by auto 
next case False def d \<equiv> "e / 3 / setprod (\<lambda>i. b$i - a$i) (UNIV - {k})"
  note False[unfolded content_eq_0 not_ex not_le, rule_format]
  hence prod0:"0 < setprod (\<lambda>i. b$i - a$i) (UNIV - {k})" apply-apply(rule setprod_pos) by smt
  hence "d > 0" unfolding d_def using assms by(auto simp add:field_simps) thus ?thesis
  proof(rule that[of d]) have *:"UNIV = insert k (UNIV - {k})" by auto
    have **:"{a..b} \<inter> {x. \<bar>x $ k - c\<bar> \<le> d} \<noteq> {} \<Longrightarrow> 
      (\<Prod>i\<in>UNIV - {k}. interval_upperbound ({a..b} \<inter> {x. \<bar>x $ k - c\<bar> \<le> d}) $ i - interval_lowerbound ({a..b} \<inter> {x. \<bar>x $ k - c\<bar> \<le> d}) $ i)
      = (\<Prod>i\<in>UNIV - {k}. b$i - a$i)" apply(rule setprod_cong,rule refl)
      unfolding interval_doublesplit interval_eq_empty not_ex not_less unfolding interval_bounds by auto
    show "content ({a..b} \<inter> {x. \<bar>x $ k - c\<bar> \<le> d}) < e" apply(cases) unfolding content_def apply(subst if_P,assumption,rule assms)
      unfolding if_not_P apply(subst *) apply(subst setprod_insert) unfolding **
      unfolding interval_doublesplit interval_eq_empty not_ex not_less unfolding interval_bounds unfolding Cart_lambda_beta if_P[OF refl]
    proof- have "(min (b $ k) (c + d) - max (a $ k) (c - d)) \<le> 2 * d" by auto
      also have "... < e / (\<Prod>i\<in>UNIV - {k}. b $ i - a $ i)" unfolding d_def using assms prod0 by(auto simp add:field_simps)
      finally show "(min (b $ k) (c + d) - max (a $ k) (c - d)) * (\<Prod>i\<in>UNIV - {k}. b $ i - a $ i) < e"
        unfolding pos_less_divide_eq[OF prod0] . qed auto qed qed

lemma negligible_standard_hyperplane[intro]: "negligible {x. x$k = (c::real)}" 
  unfolding negligible_def has_integral apply(rule,rule,rule,rule)
proof- case goal1 from content_doublesplit[OF this,of a b k c] guess d . note d=this let ?i = "indicator {x. x$k = c}"
  show ?case apply(rule_tac x="\<lambda>x. ball x d" in exI) apply(rule,rule gauge_ball,rule d)
  proof(rule,rule) fix p assume p:"p tagged_division_of {a..b} \<and> (\<lambda>x. ball x d) fine p"
    have *:"(\<Sum>(x, ka)\<in>p. content ka *\<^sub>R ?i x) = (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. abs(x$k - c) \<le> d}) *\<^sub>R ?i x)"
      apply(rule setsum_cong2) unfolding split_paired_all real_scaleR_def mult_cancel_right split_conv
      apply(cases,rule disjI1,assumption,rule disjI2)
    proof- fix x l assume as:"(x,l)\<in>p" "?i x \<noteq> 0" hence xk:"x$k = c" unfolding indicator_def apply-by(rule ccontr,auto)
      show "content l = content (l \<inter> {x. \<bar>x $ k - c\<bar> \<le> d})" apply(rule arg_cong[where f=content])
        apply(rule set_ext,rule,rule) unfolding mem_Collect_eq
      proof- fix y assume y:"y\<in>l" note p[THEN conjunct2,unfolded fine_def,rule_format,OF as(1),unfolded split_conv]
        note this[unfolded subset_eq mem_ball vector_dist_norm,rule_format,OF y] note le_less_trans[OF component_le_norm[of _ k] this]
        thus "\<bar>y $ k - c\<bar> \<le> d" unfolding Cart_nth.diff xk by auto
      qed auto qed
    note p'= tagged_division_ofD[OF p[THEN conjunct1]] and p''=division_of_tagged_division[OF p[THEN conjunct1]]
    show "norm ((\<Sum>(x, ka)\<in>p. content ka *\<^sub>R ?i x) - 0) < e" unfolding diff_0_right * unfolding real_scaleR_def real_norm_def
      apply(subst abs_of_nonneg) apply(rule setsum_nonneg,rule) unfolding split_paired_all split_conv
      apply(rule mult_nonneg_nonneg) apply(drule p'(4)) apply(erule exE)+ apply(rule_tac b=b in back_subst)
      prefer 2 apply(subst(asm) eq_commute) apply assumption
      apply(subst interval_doublesplit) apply(rule content_pos_le) apply(rule indicator_pos_le)
    proof- have "(\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. \<bar>x $ k - c\<bar> \<le> d}) * ?i x) \<le> (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. \<bar>x $ k - c\<bar> \<le> d}))"
        apply(rule setsum_mono) unfolding split_paired_all split_conv 
        apply(rule mult_right_le_one_le) apply(drule p'(4)) by(auto simp add:interval_doublesplit intro!:content_pos_le)
      also have "... < e" apply(subst setsum_over_tagged_division_lemma[OF p[THEN conjunct1]])
      proof- case goal1 have "content ({u..v} \<inter> {x. \<bar>x $ k - c\<bar> \<le> d}) \<le> content {u..v}"
          unfolding interval_doublesplit apply(rule content_subset) unfolding interval_doublesplit[THEN sym] by auto
        thus ?case unfolding goal1 unfolding interval_doublesplit using content_pos_le by smt
      next have *:"setsum content {l \<inter> {x. \<bar>x $ k - c\<bar> \<le> d} |l. l \<in> snd ` p \<and> l \<inter> {x. \<bar>x $ k - c\<bar> \<le> d} \<noteq> {}} \<ge> 0"
          apply(rule setsum_nonneg,rule) unfolding mem_Collect_eq image_iff apply(erule exE bexE conjE)+ unfolding split_paired_all 
        proof- fix x l a b assume as:"x = l \<inter> {x. \<bar>x $ k - c\<bar> \<le> d}" "(a, b) \<in> p" "l = snd (a, b)"
          guess u v using p'(4)[OF as(2)] apply-by(erule exE)+ note * = this
          show "content x \<ge> 0" unfolding as snd_conv * interval_doublesplit by(rule content_pos_le)
        qed have **:"norm (1::real) \<le> 1" by auto note division_doublesplit[OF p'',unfolded interval_doublesplit]
        note dsum_bound[OF this **,unfolded interval_doublesplit[THEN sym]]
        note this[unfolded real_scaleR_def real_norm_def class_semiring.semiring_rules, of k c d] note le_less_trans[OF this d(2)]
        from this[unfolded abs_of_nonneg[OF *]] show "(\<Sum>ka\<in>snd ` p. content (ka \<inter> {x. \<bar>x $ k - c\<bar> \<le> d})) < e"
          apply(subst vsum_nonzero_image_lemma[of "snd ` p" content "{}", unfolded o_def,THEN sym])
          apply(rule finite_imageI p' content_empty)+ unfolding forall_in_division[OF p'']
        proof(rule,rule,rule,rule,rule,rule,rule,erule conjE) fix m n u v
          assume as:"{m..n} \<in> snd ` p" "{u..v} \<in> snd ` p" "{m..n} \<noteq> {u..v}"  "{m..n} \<inter> {x. \<bar>x $ k - c\<bar> \<le> d} = {u..v} \<inter> {x. \<bar>x $ k - c\<bar> \<le> d}"
          have "({m..n} \<inter> {x. \<bar>x $ k - c\<bar> \<le> d}) \<inter> ({u..v} \<inter> {x. \<bar>x $ k - c\<bar> \<le> d}) \<subseteq> {m..n} \<inter> {u..v}" by blast
          note subset_interior[OF this, unfolded division_ofD(5)[OF p'' as(1-3)] interior_inter[of "{m..n}"]]
          hence "interior ({m..n} \<inter> {x. \<bar>x $ k - c\<bar> \<le> d}) = {}" unfolding as Int_absorb by auto
          thus "content ({m..n} \<inter> {x. \<bar>x $ k - c\<bar> \<le> d}) = 0" unfolding interval_doublesplit content_eq_0_interior[THEN sym] .
        qed qed
      finally show "(\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. \<bar>x $ k - c\<bar> \<le> d}) * ?i x) < e" .
    qed qed qed

subsection {* A technical lemma about "refinement" of division. *}

lemma tagged_division_finer: fixes p::"((real^'n) \<times> ((real^'n) set)) set"
  assumes "p tagged_division_of {a..b}" "gauge d"
  obtains q where "q tagged_division_of {a..b}" "d fine q" "\<forall>(x,k) \<in> p. k \<subseteq> d(x) \<longrightarrow> (x,k) \<in> q"
proof-
  let ?P = "\<lambda>p. p tagged_partial_division_of {a..b} \<longrightarrow> gauge d \<longrightarrow>
    (\<exists>q. q tagged_division_of (\<Union>{k. \<exists>x. (x,k) \<in> p}) \<and> d fine q \<and>
                   (\<forall>(x,k) \<in> p. k \<subseteq> d(x) \<longrightarrow> (x,k) \<in> q))"
  { have *:"finite p" "p tagged_partial_division_of {a..b}" using assms(1) unfolding tagged_division_of_def by auto
    presume "\<And>p. finite p \<Longrightarrow> ?P p" from this[rule_format,OF * assms(2)] guess q .. note q=this
    thus ?thesis apply-apply(rule that[of q]) unfolding tagged_division_ofD[OF assms(1)] by auto
  } fix p::"((real^'n) \<times> ((real^'n) set)) set" assume as:"finite p"
  show "?P p" apply(rule,rule) using as proof(induct p) 
    case empty show ?case apply(rule_tac x="{}" in exI) unfolding fine_def by auto
  next case (insert xk p) guess x k using surj_pair[of xk] apply- by(erule exE)+ note xk=this
    note tagged_partial_division_subset[OF insert(4) subset_insertI]
    from insert(3)[OF this insert(5)] guess q1 .. note q1 = conjunctD3[OF this]
    have *:"\<Union>{l. \<exists>y. (y,l) \<in> insert xk p} = k \<union> \<Union>{l. \<exists>y. (y,l) \<in> p}" unfolding xk by auto
    note p = tagged_partial_division_ofD[OF insert(4)]
    from p(4)[unfolded xk, OF insertI1] guess u v apply-by(erule exE)+ note uv=this

    have "finite {k. \<exists>x. (x, k) \<in> p}" 
      apply(rule finite_subset[of _ "snd ` p"],rule) unfolding subset_eq image_iff mem_Collect_eq
      apply(erule exE,rule_tac x="(xa,x)" in bexI) using p by auto
    hence int:"interior {u..v} \<inter> interior (\<Union>{k. \<exists>x. (x, k) \<in> p}) = {}"
      apply(rule inter_interior_unions_intervals) apply(rule open_interior) apply(rule_tac[!] ballI)
      unfolding mem_Collect_eq apply(erule_tac[!] exE) apply(drule p(4)[OF insertI2],assumption)      
      apply(rule p(5))  unfolding uv xk apply(rule insertI1,rule insertI2) apply assumption
      using insert(2) unfolding uv xk by auto

    show ?case proof(cases "{u..v} \<subseteq> d x")
      case True thus ?thesis apply(rule_tac x="{(x,{u..v})} \<union> q1" in exI) apply rule
        unfolding * uv apply(rule tagged_division_union,rule tagged_division_of_self)
        apply(rule p[unfolded xk uv] insertI1)+  apply(rule q1,rule int) 
        apply(rule,rule fine_union,subst fine_def) defer apply(rule q1)
        unfolding Ball_def split_paired_All split_conv apply(rule,rule,rule,rule)
        apply(erule insertE) defer apply(rule UnI2) apply(drule q1(3)[rule_format]) unfolding xk uv by auto
    next case False from fine_division_exists[OF assms(2), of u v] guess q2 . note q2=this
      show ?thesis apply(rule_tac x="q2 \<union> q1" in exI)
        apply rule unfolding * uv apply(rule tagged_division_union q2 q1 int fine_union)+
        unfolding Ball_def split_paired_All split_conv apply rule apply(rule fine_union)
        apply(rule q1 q2)+ apply(rule,rule,rule,rule) apply(erule insertE)
        apply(rule UnI2) defer apply(drule q1(3)[rule_format])using False unfolding xk uv by auto
    qed qed qed

subsection {* Hence the main theorem about negligible sets. *}

lemma finite_product_dependent: assumes "finite s" "\<And>x. x\<in>s\<Longrightarrow> finite (t x)"
  shows "finite {(i, j) |i j. i \<in> s \<and> j \<in> t i}" using assms
proof(induct) case (insert x s) 
  have *:"{(i, j) |i j. i \<in> insert x s \<and> j \<in> t i} = (\<lambda>y. (x,y)) ` (t x) \<union> {(i, j) |i j. i \<in> s \<and> j \<in> t i}" by auto
  show ?case unfolding * apply(rule finite_UnI) using insert by auto qed auto

lemma sum_sum_product: assumes "finite s" "\<forall>i\<in>s. finite (t i)"
  shows "setsum (\<lambda>i. setsum (x i) (t i)::real) s = setsum (\<lambda>(i,j). x i j) {(i,j) | i j. i \<in> s \<and> j \<in> t i}" using assms
proof(induct) case (insert a s)
  have *:"{(i, j) |i j. i \<in> insert a s \<and> j \<in> t i} = (\<lambda>y. (a,y)) ` (t a) \<union> {(i, j) |i j. i \<in> s \<and> j \<in> t i}" by auto
  show ?case unfolding * apply(subst setsum_Un_disjoint) unfolding setsum_insert[OF insert(1-2)]
    prefer 4 apply(subst insert(3)) unfolding add_right_cancel
  proof- show "setsum (x a) (t a) = (\<Sum>(xa, y)\<in>Pair a ` t a. x xa y)" apply(subst setsum_reindex) unfolding inj_on_def by auto
    show "finite {(i, j) |i j. i \<in> s \<and> j \<in> t i}" apply(rule finite_product_dependent) using insert by auto
  qed(insert insert, auto) qed auto

lemma has_integral_negligible: fixes f::"real^'n \<Rightarrow> 'a::real_normed_vector"
  assumes "negligible s" "\<forall>x\<in>(t - s). f x = 0"
  shows "(f has_integral 0) t"
proof- presume P:"\<And>f::real^'n \<Rightarrow> 'a. \<And>a b. (\<forall>x. ~(x \<in> s) \<longrightarrow> f x = 0) \<Longrightarrow> (f has_integral 0) ({a..b})"
  let ?f = "(\<lambda>x. if x \<in> t then f x else 0)"
  show ?thesis apply(rule_tac f="?f" in has_integral_eq) apply(rule) unfolding if_P apply(rule refl)
    apply(subst has_integral_alt) apply(cases,subst if_P,assumption) unfolding if_not_P
  proof- assume "\<exists>a b. t = {a..b}" then guess a b apply-by(erule exE)+ note t = this
    show "(?f has_integral 0) t" unfolding t apply(rule P) using assms(2) unfolding t by auto
  next show "\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> {a..b} \<longrightarrow> (\<exists>z. ((\<lambda>x. if x \<in> t then ?f x else 0) has_integral z) {a..b} \<and> norm (z - 0) < e)"
      apply(safe,rule_tac x=1 in exI,rule) apply(rule zero_less_one,safe) apply(rule_tac x=0 in exI)
      apply(rule,rule P) using assms(2) by auto
  qed
next fix f::"real^'n \<Rightarrow> 'a" and a b::"real^'n" assume assm:"\<forall>x. x \<notin> s \<longrightarrow> f x = 0" 
  show "(f has_integral 0) {a..b}" unfolding has_integral
  proof(safe) case goal1
    hence "\<And>n. e / 2 / ((real n+1) * (2 ^ n)) > 0" 
      apply-apply(rule divide_pos_pos) defer apply(rule mult_pos_pos) by(auto simp add:field_simps)
    note assms(1)[unfolded negligible_def has_integral,rule_format,OF this,of a b] note allI[OF this,of "\<lambda>x. x"] 
    from choice[OF this] guess d .. note d=conjunctD2[OF this[rule_format]]
    show ?case apply(rule_tac x="\<lambda>x. d (nat \<lfloor>norm (f x)\<rfloor>) x" in exI) 
    proof safe show "gauge (\<lambda>x. d (nat \<lfloor>norm (f x)\<rfloor>) x)" using d(1) unfolding gauge_def by auto
      fix p assume as:"p tagged_division_of {a..b}" "(\<lambda>x. d (nat \<lfloor>norm (f x)\<rfloor>) x) fine p" 
      let ?goal = "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) < e"
      { presume "p\<noteq>{} \<Longrightarrow> ?goal" thus ?goal apply(cases "p={}") using goal1 by auto  }
      assume as':"p \<noteq> {}" from real_arch_simple[of "Sup((\<lambda>(x,k). norm(f x)) ` p)"] guess N ..
      hence N:"\<forall>x\<in>(\<lambda>(x, k). norm (f x)) ` p. x \<le> real N" apply(subst(asm) Sup_finite_le_iff) using as as' by auto
      have "\<forall>i. \<exists>q. q tagged_division_of {a..b} \<and> (d i) fine q \<and> (\<forall>(x, k)\<in>p. k \<subseteq> (d i) x \<longrightarrow> (x, k) \<in> q)"
        apply(rule,rule tagged_division_finer[OF as(1) d(1)]) by auto
      from choice[OF this] guess q .. note q=conjunctD3[OF this[rule_format]]
      have *:"\<And>i. (\<Sum>(x, k)\<in>q i. content k *\<^sub>R indicator s x) \<ge> 0" apply(rule setsum_nonneg,safe) 
        unfolding real_scaleR_def apply(rule mult_nonneg_nonneg) apply(drule tagged_division_ofD(4)[OF q(1)]) by auto
      have **:"\<And>f g s t. finite s \<Longrightarrow> finite t \<Longrightarrow> (\<forall>(x,y) \<in> t. (0::real) \<le> g(x,y)) \<Longrightarrow> (\<forall>y\<in>s. \<exists>x. (x,y) \<in> t \<and> f(y) \<le> g(x,y)) \<Longrightarrow> setsum f s \<le> setsum g t"
      proof- case goal1 thus ?case apply-apply(rule setsum_le_included[of s t g snd f]) prefer 4
          apply safe apply(erule_tac x=x in ballE) apply(erule exE) apply(rule_tac x="(xa,x)" in bexI) by auto qed
      have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) \<le> setsum (\<lambda>i. (real i + 1) *
                     norm(setsum (\<lambda>(x,k). content k *\<^sub>R indicator s x) (q i))) {0..N+1}"
        unfolding real_norm_def setsum_right_distrib abs_of_nonneg[OF *] diff_0_right
        apply(rule order_trans,rule setsum_norm) defer apply(subst sum_sum_product) prefer 3 
      proof(rule **,safe) show "finite {(i, j) |i j. i \<in> {0..N + 1} \<and> j \<in> q i}" apply(rule finite_product_dependent) using q by auto
        fix i a b assume as'':"(a,b) \<in> q i" show "0 \<le> (real i + 1) * (content b *\<^sub>R indicator s a)"
          unfolding real_scaleR_def apply(rule mult_nonneg_nonneg) defer apply(rule mult_nonneg_nonneg)
          using tagged_division_ofD(4)[OF q(1) as''] by auto
      next fix i::nat show "finite (q i)" using q by auto
      next fix x k assume xk:"(x,k) \<in> p" def n \<equiv> "nat \<lfloor>norm (f x)\<rfloor>"
        have *:"norm (f x) \<in> (\<lambda>(x, k). norm (f x)) ` p" using xk by auto
        have nfx:"real n \<le> norm(f x)" "norm(f x) \<le> real n + 1" unfolding n_def by auto
        hence "n \<in> {0..N + 1}" using N[rule_format,OF *] by auto
        moreover  note as(2)[unfolded fine_def,rule_format,OF xk,unfolded split_conv]
        note q(3)[rule_format,OF xk,unfolded split_conv,rule_format,OF this] note this[unfolded n_def[symmetric]]
        moreover have "norm (content k *\<^sub>R f x) \<le> (real n + 1) * (content k * indicator s x)"
        proof(cases "x\<in>s") case False thus ?thesis using assm by auto
        next case True have *:"content k \<ge> 0" using tagged_division_ofD(4)[OF as(1) xk] by auto
          moreover have "content k * norm (f x) \<le> content k * (real n + 1)" apply(rule mult_mono) using nfx * by auto
          ultimately show ?thesis unfolding abs_mult using nfx True by(auto simp add:field_simps)
        qed ultimately show "\<exists>y. (y, x, k) \<in> {(i, j) |i j. i \<in> {0..N + 1} \<and> j \<in> q i} \<and> norm (content k *\<^sub>R f x) \<le> (real y + 1) * (content k *\<^sub>R indicator s x)"
          apply(rule_tac x=n in exI,safe) apply(rule_tac x=n in exI,rule_tac x="(x,k)" in exI,safe) by auto
      qed(insert as, auto)
      also have "... \<le> setsum (\<lambda>i. e / 2 / 2 ^ i) {0..N+1}" apply(rule setsum_mono) 
      proof- case goal1 thus ?case apply(subst mult_commute, subst pos_le_divide_eq[THEN sym])
          using d(2)[rule_format,of "q i" i] using q[rule_format] by(auto simp add:field_simps)
      qed also have "... < e * inverse 2 * 2" unfolding real_divide_def setsum_right_distrib[THEN sym]
        apply(rule mult_strict_left_mono) unfolding power_inverse atLeastLessThanSuc_atLeastAtMost[THEN sym]
        apply(subst sumr_geometric) using goal1 by auto
      finally show "?goal" by auto qed qed qed

lemma has_integral_spike: fixes f::"real^'n \<Rightarrow> 'a::real_normed_vector"
  assumes "negligible s" "(\<forall>x\<in>(t - s). g x = f x)" "(f has_integral y) t"
  shows "(g has_integral y) t"
proof- { fix a b::"real^'n" and f g ::"real^'n \<Rightarrow> 'a" and y::'a
    assume as:"\<forall>x \<in> {a..b} - s. g x = f x" "(f has_integral y) {a..b}"
    have "((\<lambda>x. f x + (g x - f x)) has_integral (y + 0)) {a..b}" apply(rule has_integral_add[OF as(2)])
      apply(rule has_integral_negligible[OF assms(1)]) using as by auto
    hence "(g has_integral y) {a..b}" by auto } note * = this
  show ?thesis apply(subst has_integral_alt) using assms(2-) apply-apply(rule cond_cases,safe)
    apply(rule *, assumption+) apply(subst(asm) has_integral_alt) unfolding if_not_P
    apply(erule_tac x=e in allE,safe,rule_tac x=B in exI,safe) apply(erule_tac x=a in allE,erule_tac x=b in allE,safe)
    apply(rule_tac x=z in exI,safe) apply(rule *[where fa2="\<lambda>x. if x\<in>t then f x else 0"]) by auto qed

lemma has_integral_spike_eq:
  assumes "negligible s" "\<forall>x\<in>(t - s). g x = f x"
  shows "((f has_integral y) t \<longleftrightarrow> (g has_integral y) t)"
  apply rule apply(rule_tac[!] has_integral_spike[OF assms(1)]) using assms(2) by auto

lemma integrable_spike: assumes "negligible s" "\<forall>x\<in>(t - s). g x = f x" "f integrable_on t"
  shows "g integrable_on  t"
  using assms unfolding integrable_on_def apply-apply(erule exE)
  apply(rule,rule has_integral_spike) by fastsimp+

lemma integral_spike: assumes "negligible s" "\<forall>x\<in>(t - s). g x = f x"
  shows "integral t f = integral t g"
  unfolding integral_def using has_integral_spike_eq[OF assms] by auto

subsection {* Some other trivialities about negligible sets. *}

lemma negligible_subset[intro]: assumes "negligible s" "t \<subseteq> s" shows "negligible t" unfolding negligible_def 
proof(safe) case goal1 show ?case using assms(1)[unfolded negligible_def,rule_format,of a b]
    apply-apply(rule has_integral_spike[OF assms(1)]) defer apply assumption
    using assms(2) unfolding indicator_def by auto qed

lemma negligible_diff[intro?]: assumes "negligible s" shows "negligible(s - t)" using assms by auto

lemma negligible_inter: assumes "negligible s \<or> negligible t" shows "negligible(s \<inter> t)" using assms by auto

lemma negligible_union: assumes "negligible s" "negligible t" shows "negligible (s \<union> t)" unfolding negligible_def 
proof safe case goal1 note assm = assms[unfolded negligible_def,rule_format,of a b]
  thus ?case apply(subst has_integral_spike_eq[OF assms(2)])
    defer apply assumption unfolding indicator_def by auto qed

lemma negligible_union_eq[simp]: "negligible (s \<union> t) \<longleftrightarrow> (negligible s \<and> negligible t)"
  using negligible_union by auto

lemma negligible_sing[intro]: "negligible {a::real^'n}" 
proof- guess x using UNIV_witness[where 'a='n] ..
  show ?thesis using negligible_standard_hyperplane[of x "a$x"] by auto qed

lemma negligible_insert[simp]: "negligible(insert a s) \<longleftrightarrow> negligible s"
  apply(subst insert_is_Un) unfolding negligible_union_eq by auto

lemma negligible_empty[intro]: "negligible {}" by auto

lemma negligible_finite[intro]: assumes "finite s" shows "negligible s"
  using assms apply(induct s) by auto

lemma negligible_unions[intro]: assumes "finite s" "\<forall>t\<in>s. negligible t" shows "negligible(\<Union>s)"
  using assms by(induct,auto) 

lemma negligible:  "negligible s \<longleftrightarrow> (\<forall>t::(real^'n) set. (indicator s has_integral 0) t)"
  apply safe defer apply(subst negligible_def)
proof- fix t::"(real^'n) set" assume as:"negligible s"
  have *:"(\<lambda>x. if x \<in> s \<inter> t then 1 else 0) = (\<lambda>x. if x\<in>t then if x\<in>s then 1 else 0 else 0)" by(rule ext,auto)  
  show "(indicator s has_integral 0) t" apply(subst has_integral_alt)
    apply(cases,subst if_P,assumption) unfolding if_not_P apply(safe,rule as[unfolded negligible_def,rule_format])
    apply(rule_tac x=1 in exI) apply(safe,rule zero_less_one) apply(rule_tac x=0 in exI)
    using negligible_subset[OF as,of "s \<inter> t"] unfolding negligible_def indicator_def unfolding * by auto qed auto

subsection {* Finite case of the spike theorem is quite commonly needed. *}

lemma has_integral_spike_finite: assumes "finite s" "\<forall>x\<in>t-s. g x = f x" 
  "(f has_integral y) t" shows "(g has_integral y) t"
  apply(rule has_integral_spike) using assms by auto

lemma has_integral_spike_finite_eq: assumes "finite s" "\<forall>x\<in>t-s. g x = f x"
  shows "((f has_integral y) t \<longleftrightarrow> (g has_integral y) t)"
  apply rule apply(rule_tac[!] has_integral_spike_finite) using assms by auto

lemma integrable_spike_finite:
  assumes "finite s" "\<forall>x\<in>t-s. g x = f x" "f integrable_on t" shows "g integrable_on  t"
  using assms unfolding integrable_on_def apply safe apply(rule_tac x=y in exI)
  apply(rule has_integral_spike_finite) by auto

subsection {* In particular, the boundary of an interval is negligible. *}

lemma negligible_frontier_interval: "negligible({a..b} - {a<..<b})"
proof- let ?A = "\<Union>((\<lambda>k. {x. x$k = a$k} \<union> {x. x$k = b$k}) ` UNIV)"
  have "{a..b} - {a<..<b} \<subseteq> ?A" apply rule unfolding Diff_iff mem_interval not_all
    apply(erule conjE exE)+ apply(rule_tac X="{x. x $ xa = a $ xa} \<union> {x. x $ xa = b $ xa}" in UnionI)
    apply(erule_tac[!] x=xa in allE) by auto
  thus ?thesis apply-apply(rule negligible_subset[of ?A]) apply(rule negligible_unions[OF finite_imageI]) by auto qed

lemma has_integral_spike_interior:
  assumes "\<forall>x\<in>{a<..<b}. g x = f x" "(f has_integral y) ({a..b})" shows "(g has_integral y) ({a..b})"
  apply(rule has_integral_spike[OF negligible_frontier_interval _ assms(2)]) using assms(1) by auto

lemma has_integral_spike_interior_eq:
  assumes "\<forall>x\<in>{a<..<b}. g x = f x" shows "((f has_integral y) ({a..b}) \<longleftrightarrow> (g has_integral y) ({a..b}))"
  apply rule apply(rule_tac[!] has_integral_spike_interior) using assms by auto

lemma integrable_spike_interior: assumes "\<forall>x\<in>{a<..<b}. g x = f x" "f integrable_on {a..b}" shows "g integrable_on {a..b}"
  using  assms unfolding integrable_on_def using has_integral_spike_interior[OF assms(1)] by auto

subsection {* Integrability of continuous functions. *}

lemma neutral_and[simp]: "neutral op \<and> = True"
  unfolding neutral_def apply(rule some_equality) by auto

lemma monoidal_and[intro]: "monoidal op \<and>" unfolding monoidal_def by auto

lemma iterate_and[simp]: assumes "finite s" shows "(iterate op \<and>) s p \<longleftrightarrow> (\<forall>x\<in>s. p x)" using assms
apply induct unfolding iterate_insert[OF monoidal_and] by auto

lemma operative_division_and: assumes "operative op \<and> P" "d division_of {a..b}"
  shows "(\<forall>i\<in>d. P i) \<longleftrightarrow> P {a..b}"
  using operative_division[OF monoidal_and assms] division_of_finite[OF assms(2)] by auto

lemma operative_approximable: assumes "0 \<le> e" fixes f::"real^'n \<Rightarrow> 'a::banach"
  shows "operative op \<and> (\<lambda>i. \<exists>g. (\<forall>x\<in>i. norm (f x - g (x::real^'n)) \<le> e) \<and> g integrable_on i)" unfolding operative_def neutral_and
proof safe fix a b::"real^'n" { assume "content {a..b} = 0"
    thus "\<exists>g. (\<forall>x\<in>{a..b}. norm (f x - g x) \<le> e) \<and> g integrable_on {a..b}" 
      apply(rule_tac x=f in exI) using assms by(auto intro!:integrable_on_null) }
  { fix c k g assume as:"\<forall>x\<in>{a..b}. norm (f x - g x) \<le> e" "g integrable_on {a..b}"
    show "\<exists>g. (\<forall>x\<in>{a..b} \<inter> {x. x $ k \<le> c}. norm (f x - g x) \<le> e) \<and> g integrable_on {a..b} \<inter> {x. x $ k \<le> c}"
      "\<exists>g. (\<forall>x\<in>{a..b} \<inter> {x. c \<le> x $ k}. norm (f x - g x) \<le> e) \<and> g integrable_on {a..b} \<inter> {x. c \<le> x $ k}"
      apply(rule_tac[!] x=g in exI) using as(1) integrable_split[OF as(2)] by auto }
  fix c k g1 g2 assume as:"\<forall>x\<in>{a..b} \<inter> {x. x $ k \<le> c}. norm (f x - g1 x) \<le> e" "g1 integrable_on {a..b} \<inter> {x. x $ k \<le> c}"
                          "\<forall>x\<in>{a..b} \<inter> {x. c \<le> x $ k}. norm (f x - g2 x) \<le> e" "g2 integrable_on {a..b} \<inter> {x. c \<le> x $ k}"
  let ?g = "\<lambda>x. if x$k = c then f x else if x$k \<le> c then g1 x else g2 x"
  show "\<exists>g. (\<forall>x\<in>{a..b}. norm (f x - g x) \<le> e) \<and> g integrable_on {a..b}" apply(rule_tac x="?g" in exI)
  proof safe case goal1 thus ?case apply- apply(cases "x$k=c", case_tac "x$k < c") using as assms by auto
  next case goal2 presume "?g integrable_on {a..b} \<inter> {x. x $ k \<le> c}" "?g integrable_on {a..b} \<inter> {x. x $ k \<ge> c}"
    then guess h1 h2 unfolding integrable_on_def by auto from has_integral_split[OF this]
    show ?case unfolding integrable_on_def by auto
  next show "?g integrable_on {a..b} \<inter> {x. x $ k \<le> c}" "?g integrable_on {a..b} \<inter> {x. x $ k \<ge> c}"
      apply(rule_tac[!] integrable_spike[OF negligible_standard_hyperplane[of k c]]) using as(2,4) by auto qed qed

lemma approximable_on_division: fixes f::"real^'n \<Rightarrow> 'a::banach"
  assumes "0 \<le> e" "d division_of {a..b}" "\<forall>i\<in>d. \<exists>g. (\<forall>x\<in>i. norm (f x - g x) \<le> e) \<and> g integrable_on i"
  obtains g where "\<forall>x\<in>{a..b}. norm (f x - g x) \<le> e" "g integrable_on {a..b}"
proof- note * = operative_division[OF monoidal_and operative_approximable[OF assms(1)] assms(2)]
  note this[unfolded iterate_and[OF division_of_finite[OF assms(2)]]] from assms(3)[unfolded this[of f]]
  guess g .. thus thesis apply-apply(rule that[of g]) by auto qed

lemma integrable_continuous: fixes f::"real^'n \<Rightarrow> 'a::banach"
  assumes "continuous_on {a..b} f" shows "f integrable_on {a..b}"
proof(rule integrable_uniform_limit,safe) fix e::real assume e:"0 < e"
  from compact_uniformly_continuous[OF assms compact_interval,unfolded uniformly_continuous_on_def,rule_format,OF e] guess d ..
  note d=conjunctD2[OF this,rule_format]
  from fine_division_exists[OF gauge_ball[OF d(1)], of a b] guess p . note p=this
  note p' = tagged_division_ofD[OF p(1)]
  have *:"\<forall>i\<in>snd ` p. \<exists>g. (\<forall>x\<in>i. norm (f x - g x) \<le> e) \<and> g integrable_on i"
  proof(safe,unfold snd_conv) fix x l assume as:"(x,l) \<in> p" 
    from p'(4)[OF this] guess a b apply-by(erule exE)+ note l=this
    show "\<exists>g. (\<forall>x\<in>l. norm (f x - g x) \<le> e) \<and> g integrable_on l" apply(rule_tac x="\<lambda>y. f x" in exI)
    proof safe show "(\<lambda>y. f x) integrable_on l" unfolding integrable_on_def l by(rule,rule has_integral_const)
      fix y assume y:"y\<in>l" note fineD[OF p(2) as,unfolded subset_eq,rule_format,OF this]
      note d(2)[OF _ _ this[unfolded mem_ball]]
      thus "norm (f y - f x) \<le> e" using y p'(2-3)[OF as] unfolding vector_dist_norm l norm_minus_commute by fastsimp qed qed
  from e have "0 \<le> e" by auto from approximable_on_division[OF this division_of_tagged_division[OF p(1)] *] guess g .
  thus "\<exists>g. (\<forall>x\<in>{a..b}. norm (f x - g x) \<le> e) \<and> g integrable_on {a..b}" by auto qed 

subsection {* Specialization of additivity to one dimension. *}

lemma operative_1_lt: assumes "monoidal opp"
  shows "operative opp f \<longleftrightarrow> ((\<forall>a b. b \<le> a \<longrightarrow> f {a..b::real^1} = neutral opp) \<and>
                (\<forall>a b c. a < c \<and> c < b \<longrightarrow> opp (f{a..c})(f{c..b}) = f {a..b}))"
  unfolding operative_def content_eq_0_1 forall_1 vector_le_def vector_less_def
proof safe fix a b c::"real^1" assume as:"\<forall>a b c. f {a..b} = opp (f ({a..b} \<inter> {x. x $ 1 \<le> c})) (f ({a..b} \<inter> {x. c \<le> x $ 1}))" "a $ 1 < c $ 1" "c $ 1 < b $ 1"
    from this(2-) have "{a..b} \<inter> {x. x $ 1 \<le> c $ 1} = {a..c}" "{a..b} \<inter> {x. x $ 1 \<ge> c $ 1} = {c..b}" by auto
    thus "opp (f {a..c}) (f {c..b}) = f {a..b}" unfolding as(1)[rule_format,of a b "c$1"] by auto
next fix a b::"real^1" and c::real
  assume as:"\<forall>a b. b $ 1 \<le> a $ 1 \<longrightarrow> f {a..b} = neutral opp" "\<forall>a b c. a $ 1 < c $ 1 \<and> c $ 1 < b $ 1 \<longrightarrow> opp (f {a..c}) (f {c..b}) = f {a..b}"
  show "f {a..b} = opp (f ({a..b} \<inter> {x. x $ 1 \<le> c})) (f ({a..b} \<inter> {x. c \<le> x $ 1}))"
  proof(cases "c \<in> {a$1 .. b$1}")
    case False hence "c<a$1 \<or> c>b$1" by auto
    thus ?thesis apply-apply(erule disjE)
    proof- assume "c<a$1" hence *:"{a..b} \<inter> {x. x $ 1 \<le> c} = {1..0}"  "{a..b} \<inter> {x. c \<le> x $ 1} = {a..b}" by auto
      show ?thesis unfolding * apply(subst as(1)[rule_format,of 0 1]) using assms by auto
    next   assume "b$1<c" hence *:"{a..b} \<inter> {x. x $ 1 \<le> c} = {a..b}"  "{a..b} \<inter> {x. c \<le> x $ 1} = {1..0}" by auto
      show ?thesis unfolding * apply(subst as(1)[rule_format,of 0 1]) using assms by auto
    qed
  next case True hence *:"min (b $ 1) c = c" "max (a $ 1) c = c" by auto
    show ?thesis unfolding interval_split num1_eq_iff if_True * vec_def[THEN sym]
    proof(cases "c = a$1 \<or> c = b$1")
      case False thus "f {a..b} = opp (f {a..vec1 c}) (f {vec1 c..b})"
        apply-apply(subst as(2)[rule_format]) using True by auto
    next case True thus "f {a..b} = opp (f {a..vec1 c}) (f {vec1 c..b})" apply-
      proof(erule disjE) assume "c=a$1" hence *:"a = vec1 c" unfolding Cart_eq by auto 
        hence "f {a..vec1 c} = neutral opp" apply-apply(rule as(1)[rule_format]) by auto
        thus ?thesis using assms unfolding * by auto
      next assume "c=b$1" hence *:"b = vec1 c" unfolding Cart_eq by auto 
        hence "f {vec1 c..b} = neutral opp" apply-apply(rule as(1)[rule_format]) by auto
        thus ?thesis using assms unfolding * by auto qed qed qed qed

lemma operative_1_le: assumes "monoidal opp"
  shows "operative opp f \<longleftrightarrow> ((\<forall>a b. b \<le> a \<longrightarrow> f {a..b::real^1} = neutral opp) \<and>
                (\<forall>a b c. a \<le> c \<and> c \<le> b \<longrightarrow> opp (f{a..c})(f{c..b}) = f {a..b}))"
unfolding operative_1_lt[OF assms]
proof safe fix a b c::"real^1" assume as:"\<forall>a b c. a \<le> c \<and> c \<le> b \<longrightarrow> opp (f {a..c}) (f {c..b}) = f {a..b}" "a < c" "c < b"
  show "opp (f {a..c}) (f {c..b}) = f {a..b}" apply(rule as(1)[rule_format]) using as(2-) unfolding vector_le_def vector_less_def by auto
next fix a b c ::"real^1"
  assume "\<forall>a b. b \<le> a \<longrightarrow> f {a..b} = neutral opp" "\<forall>a b c. a < c \<and> c < b \<longrightarrow> opp (f {a..c}) (f {c..b}) = f {a..b}" "a \<le> c" "c \<le> b"
  note as = this[rule_format]
  show "opp (f {a..c}) (f {c..b}) = f {a..b}"
  proof(cases "c = a \<or> c = b")
    case False thus ?thesis apply-apply(subst as(2)) using as(3-) unfolding vector_le_def vector_less_def Cart_eq by(auto simp del:dest_vec1_eq)
    next case True thus ?thesis apply-
      proof(erule disjE) assume *:"c=a" hence "f {a..c} = neutral opp" apply-apply(rule as(1)[rule_format]) by auto
        thus ?thesis using assms unfolding * by auto
      next               assume *:"c=b" hence "f {c..b} = neutral opp" apply-apply(rule as(1)[rule_format]) by auto
        thus ?thesis using assms unfolding * by auto qed qed qed 

subsection {* Special case of additivity we need for the FCT. *}

lemma additive_tagged_division_1: fixes f::"real^1 \<Rightarrow> 'a::real_normed_vector"
  assumes "dest_vec1 a \<le> dest_vec1 b" "p tagged_division_of {a..b}"
  shows "setsum (\<lambda>(x,k). f(interval_upperbound k) - f(interval_lowerbound k)) p = f b - f a"
proof- let ?f = "(\<lambda>k::(real^1) set. if k = {} then 0 else f(interval_upperbound k) - f(interval_lowerbound k))"
  have *:"operative op + ?f" unfolding operative_1_lt[OF monoidal_monoid] interval_eq_empty_1
    by(auto simp add:not_less interval_bound_1 vector_less_def)
  have **:"{a..b} \<noteq> {}" using assms(1) by auto note operative_tagged_division[OF monoidal_monoid * assms(2)]
  note * = this[unfolded if_not_P[OF **] interval_bound_1[OF assms(1)],THEN sym ]
  show ?thesis unfolding * apply(subst setsum_iterate[THEN sym]) defer
    apply(rule setsum_cong2) unfolding split_paired_all split_conv using assms(2) by auto qed

subsection {* A useful lemma allowing us to factor out the content size. *}

lemma has_integral_factor_content:
  "(f has_integral i) {a..b} \<longleftrightarrow> (\<forall>e>0. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a..b} \<and> d fine p
    \<longrightarrow> norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - i) \<le> e * content {a..b}))"
proof(cases "content {a..b} = 0")
  case True show ?thesis unfolding has_integral_null_eq[OF True] apply safe
    apply(rule,rule,rule gauge_trivial,safe) unfolding setsum_content_null[OF True] True defer 
    apply(erule_tac x=1 in allE,safe) defer apply(rule fine_division_exists[of _ a b],assumption)
    apply(erule_tac x=p in allE) unfolding setsum_content_null[OF True] by auto
next case False note F = this[unfolded content_lt_nz[THEN sym]]
  let ?P = "\<lambda>e opp. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a..b} \<and> d fine p \<longrightarrow> opp (norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - i)) e)"
  show ?thesis apply(subst has_integral)
  proof safe fix e::real assume e:"e>0"
    { assume "\<forall>e>0. ?P e op <" thus "?P (e * content {a..b}) op \<le>" apply(erule_tac x="e * content {a..b}" in allE)
        apply(erule impE) defer apply(erule exE,rule_tac x=d in exI)
        using F e by(auto simp add:field_simps intro:mult_pos_pos) }
    {  assume "\<forall>e>0. ?P (e * content {a..b}) op \<le>" thus "?P e op <" apply(erule_tac x="e / 2 / content {a..b}" in allE)
        apply(erule impE) defer apply(erule exE,rule_tac x=d in exI)
        using F e by(auto simp add:field_simps intro:mult_pos_pos) } qed qed

subsection {* Fundamental theorem of calculus. *}

lemma fundamental_theorem_of_calculus: fixes f::"real^1 \<Rightarrow> 'a::banach"
  assumes "a \<le> b"  "\<forall>x\<in>{a..b}. ((f o vec1) has_vector_derivative f'(vec1 x)) (at x within {a..b})"
  shows "(f' has_integral (f(vec1 b) - f(vec1 a))) ({vec1 a..vec1 b})"
unfolding has_integral_factor_content
proof safe fix e::real assume e:"e>0" have ab:"dest_vec1 (vec1 a) \<le> dest_vec1 (vec1 b)" using assms(1) by auto
  note assm = assms(2)[unfolded has_vector_derivative_def has_derivative_within_alt]
  have *:"\<And>P Q. \<forall>x\<in>{a..b}. P x \<and> (\<forall>e>0. \<exists>d>0. Q x e d) \<Longrightarrow> \<forall>x. \<exists>(d::real)>0. x\<in>{a..b} \<longrightarrow> Q x e d" using e by blast
  note this[OF assm,unfolded gauge_existence_lemma] from choice[OF this,unfolded Ball_def[symmetric]]
  guess d .. note d=conjunctD2[OF this[rule_format],rule_format]
  show "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {vec1 a..vec1 b} \<and> d fine p \<longrightarrow>
                 norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f' x) - (f (vec1 b) - f (vec1 a))) \<le> e * content {vec1 a..vec1 b})"
    apply(rule_tac x="\<lambda>x. ball x (d (dest_vec1 x))" in exI,safe)
    apply(rule gauge_ball_dependent,rule,rule d(1))
  proof- fix p assume as:"p tagged_division_of {vec1 a..vec1 b}" "(\<lambda>x. ball x (d (dest_vec1 x))) fine p"
    show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f' x) - (f (vec1 b) - f (vec1 a))) \<le> e * content {vec1 a..vec1 b}" 
      unfolding content_1[OF ab] additive_tagged_division_1[OF ab as(1),of f,THEN sym]
      unfolding vector_minus_component[THEN sym] additive_tagged_division_1[OF ab as(1),of "\<lambda>x. x",THEN sym]
      apply(subst dest_vec1_setsum) unfolding setsum_right_distrib defer unfolding setsum_subtractf[THEN sym] 
    proof(rule setsum_norm_le,safe) fix x k assume "(x,k)\<in>p"
      note xk = tagged_division_ofD(2-4)[OF as(1) this] from this(3) guess u v apply-by(erule exE)+ note k=this
      have *:"dest_vec1 u \<le> dest_vec1 v" using xk unfolding k by auto
      have ball:"\<forall>xa\<in>k. xa \<in> ball x (d (dest_vec1 x))" using as(2)[unfolded fine_def,rule_format,OF `(x,k)\<in>p`,unfolded split_conv subset_eq] .
      have "norm ((v$1 - u$1) *\<^sub>R f' x - (f v - f u)) \<le> norm (f u - f x - (u$1 - x$1) *\<^sub>R f' x) + norm (f v - f x - (v$1 - x$1) *\<^sub>R f' x)"
        apply(rule order_trans[OF _ norm_triangle_ineq4]) apply(rule eq_refl) apply(rule arg_cong[where f=norm])
        unfolding scaleR.diff_left by(auto simp add:group_simps)
      also have "... \<le> e * norm (dest_vec1 u - dest_vec1 x) + e * norm (dest_vec1 v - dest_vec1 x)"
        apply(rule add_mono) apply(rule d(2)[of "x$1" "u$1",unfolded o_def vec1_dest_vec1]) prefer 4
        apply(rule d(2)[of "x$1" "v$1",unfolded o_def vec1_dest_vec1])
        using ball[rule_format,of u] ball[rule_format,of v] 
        using xk(1-2) unfolding k subset_eq by(auto simp add:vector_dist_norm norm_real)
      also have "... \<le> e * dest_vec1 (interval_upperbound k - interval_lowerbound k)"
        unfolding k interval_bound_1[OF *] using xk(1) unfolding k by(auto simp add:vector_dist_norm norm_real field_simps)
      finally show "norm (content k *\<^sub>R f' x - (f (interval_upperbound k) - f (interval_lowerbound k))) \<le>
        e * dest_vec1 (interval_upperbound k - interval_lowerbound k)" unfolding k interval_bound_1[OF *] content_1[OF *] .
    qed(insert as, auto) qed qed

subsection {* Attempt a systematic general set of "offset" results for components. *}

lemma gauge_modify:
  assumes "(\<forall>s. open s \<longrightarrow> open {x. f(x) \<in> s})" "gauge d"
  shows "gauge (\<lambda>x y. d (f x) (f y))"
  using assms unfolding gauge_def apply safe defer apply(erule_tac x="f x" in allE)
  apply(erule_tac x="d (f x)" in allE) unfolding mem_def Collect_def by auto

subsection {* Only need trivial subintervals if the interval itself is trivial. *}

lemma division_of_nontrivial: fixes s::"(real^'n) set set"
  assumes "s division_of {a..b}" "content({a..b}) \<noteq> 0"
  shows "{k. k \<in> s \<and> content k \<noteq> 0} division_of {a..b}" using assms(1) apply-
proof(induct "card s" arbitrary:s rule:nat_less_induct)
  fix s::"(real^'n) set set" assume assm:"s division_of {a..b}"
    "\<forall>m<card s. \<forall>x. m = card x \<longrightarrow> x division_of {a..b} \<longrightarrow> {k \<in> x. content k \<noteq> 0} division_of {a..b}" 
  note s = division_ofD[OF assm(1)] let ?thesis = "{k \<in> s. content k \<noteq> 0} division_of {a..b}"
  { presume *:"{k \<in> s. content k \<noteq> 0} \<noteq> s \<Longrightarrow> ?thesis"
    show ?thesis apply cases defer apply(rule *,assumption) using assm(1) by auto }
  assume noteq:"{k \<in> s. content k \<noteq> 0} \<noteq> s"
  then obtain k where k:"k\<in>s" "content k = 0" by auto
  from s(4)[OF k(1)] guess c d apply-by(erule exE)+ note k=k this
  from k have "card s > 0" unfolding card_gt_0_iff using assm(1) by auto
  hence card:"card (s - {k}) < card s" using assm(1) k(1) apply(subst card_Diff_singleton_if) by auto
  have *:"closed (\<Union>(s - {k}))" apply(rule closed_Union) defer apply rule apply(drule DiffD1,drule s(4))
    apply safe apply(rule closed_interval) using assm(1) by auto
  have "k \<subseteq> \<Union>(s - {k})" apply safe apply(rule *[unfolded closed_limpt,rule_format]) unfolding islimpt_approachable
  proof safe fix x and e::real assume as:"x\<in>k" "e>0"
    from k(2)[unfolded k content_eq_0] guess i .. 
    hence i:"c$i = d$i" using s(3)[OF k(1),unfolded k] unfolding interval_ne_empty by smt
    hence xi:"x$i = d$i" using as unfolding k mem_interval by smt
    def y \<equiv> "(\<chi> j. if j = i then if c$i \<le> (a$i + b$i) / 2 then c$i + min e (b$i - c$i) / 2 else c$i - min e (c$i - a$i) / 2 else x$j)"
    show "\<exists>x'\<in>\<Union>(s - {k}). x' \<noteq> x \<and> dist x' x < e" apply(rule_tac x=y in bexI) 
    proof have "d \<in> {c..d}" using s(3)[OF k(1)] unfolding k interval_eq_empty mem_interval by(fastsimp simp add: not_less)
      hence "d \<in> {a..b}" using s(2)[OF k(1)] unfolding k by auto note di = this[unfolded mem_interval,THEN spec[where x=i]]
      hence xyi:"y$i \<noteq> x$i" unfolding y_def unfolding i xi Cart_lambda_beta if_P[OF refl]
        apply(cases) apply(subst if_P,assumption) unfolding if_not_P not_le using as(2) using assms(2)[unfolded content_eq_0] by smt+ 
      thus "y \<noteq> x" unfolding Cart_eq by auto
      have *:"UNIV = insert i (UNIV - {i})" by auto
      have "norm (y - x) < e + setsum (\<lambda>i. 0) (UNIV::'n set)" apply(rule le_less_trans[OF norm_le_l1])
        apply(subst *,subst setsum_insert) prefer 3 apply(rule add_less_le_mono)
      proof- show "\<bar>(y - x) $ i\<bar> < e" unfolding y_def Cart_lambda_beta vector_minus_component if_P[OF refl]
          apply(cases) apply(subst if_P,assumption) unfolding if_not_P unfolding i xi using di as(2) by auto
        show "(\<Sum>i\<in>UNIV - {i}. \<bar>(y - x) $ i\<bar>) \<le> (\<Sum>i\<in>UNIV. 0)" unfolding y_def by auto 
      qed auto thus "dist y x < e" unfolding vector_dist_norm by auto
      have "y\<notin>k" unfolding k mem_interval apply rule apply(erule_tac x=i in allE) using xyi unfolding k i xi by auto
      moreover have "y \<in> \<Union>s" unfolding s mem_interval
      proof note simps = y_def Cart_lambda_beta if_not_P
        fix j::'n show "a $ j \<le> y $ j \<and> y $ j \<le> b $ j" 
        proof(cases "j = i") case False have "x \<in> {a..b}" using s(2)[OF k(1)] as(1) by auto
          thus ?thesis unfolding simps if_not_P[OF False] unfolding mem_interval by auto
        next case True note T = this show ?thesis
          proof(cases "c $ i \<le> (a $ i + b $ i) / 2")
            case True show ?thesis unfolding simps if_P[OF T] if_P[OF True] unfolding i
              using True as(2) di apply-apply rule unfolding T by (auto simp add:field_simps) 
          next case False thus ?thesis unfolding simps if_P[OF T] if_not_P[OF False] unfolding i
              using True as(2) di apply-apply rule unfolding T by (auto simp add:field_simps)
          qed qed qed
      ultimately show "y \<in> \<Union>(s - {k})" by auto
    qed qed hence "\<Union>(s - {k}) = {a..b}" unfolding s(6)[THEN sym] by auto
  hence  "{ka \<in> s - {k}. content ka \<noteq> 0} division_of {a..b}" apply-apply(rule assm(2)[rule_format,OF card refl])
    apply(rule division_ofI) defer apply(rule_tac[1-4] s) using assm(1) by auto
  moreover have "{ka \<in> s - {k}. content ka \<noteq> 0} = {k \<in> s. content k \<noteq> 0}" using k by auto ultimately show ?thesis by auto qed

subsection {* Integrabibility on subintervals. *}

lemma operative_integrable: fixes f::"real^'n \<Rightarrow> 'a::banach" shows
  "operative op \<and> (\<lambda>i. f integrable_on i)"
  unfolding operative_def neutral_and apply safe apply(subst integrable_on_def)
  unfolding has_integral_null_eq apply(rule,rule refl) apply(rule,assumption)+
  unfolding integrable_on_def by(auto intro: has_integral_split)

lemma integrable_subinterval: fixes f::"real^'n \<Rightarrow> 'a::banach" 
  assumes "f integrable_on {a..b}" "{c..d} \<subseteq> {a..b}" shows "f integrable_on {c..d}" 
  apply(cases "{c..d} = {}") defer apply(rule partial_division_extend_1[OF assms(2)],assumption)
  using operative_division_and[OF operative_integrable,THEN sym,of _ _ _ f] assms(1) by auto

subsection {* Combining adjacent intervals in 1 dimension. *}

lemma has_integral_combine: assumes "(a::real^1) \<le> c" "c \<le> b"
  "(f has_integral i) {a..c}" "(f has_integral (j::'a::banach)) {c..b}"
  shows "(f has_integral (i + j)) {a..b}"
proof- note operative_integral[of f, unfolded operative_1_le[OF monoidal_lifted[OF monoidal_monoid]]]
  note conjunctD2[OF this,rule_format] note * = this(2)[OF conjI[OF assms(1-2)],unfolded if_P[OF assms(3)]]
  hence "f integrable_on {a..b}" apply- apply(rule ccontr) apply(subst(asm) if_P) defer
    apply(subst(asm) if_P) using assms(3-) by auto
  with * show ?thesis apply-apply(subst(asm) if_P) defer apply(subst(asm) if_P) defer apply(subst(asm) if_P)
    unfolding lifted.simps using assms(3-) by(auto simp add: integrable_on_def integral_unique) qed

lemma integral_combine: fixes f::"real^1 \<Rightarrow> 'a::banach"
  assumes "a \<le> c" "c \<le> b" "f integrable_on ({a..b})"
  shows "integral {a..c} f + integral {c..b} f = integral({a..b}) f"
  apply(rule integral_unique[THEN sym]) apply(rule has_integral_combine[OF assms(1-2)])
  apply(rule_tac[!] integrable_integral integrable_subinterval[OF assms(3)])+ using assms(1-2) by auto

lemma integrable_combine: fixes f::"real^1 \<Rightarrow> 'a::banach"
  assumes "a \<le> c" "c \<le> b" "f integrable_on {a..c}" "f integrable_on {c..b}"
  shows "f integrable_on {a..b}" using assms unfolding integrable_on_def by(fastsimp intro!:has_integral_combine)

subsection {* Reduce integrability to "local" integrability. *}

lemma integrable_on_little_subintervals: fixes f::"real^'n \<Rightarrow> 'a::banach"
  assumes "\<forall>x\<in>{a..b}. \<exists>d>0. \<forall>u v. x \<in> {u..v} \<and> {u..v} \<subseteq> ball x d \<and> {u..v} \<subseteq> {a..b} \<longrightarrow> f integrable_on {u..v}"
  shows "f integrable_on {a..b}"
proof- have "\<forall>x. \<exists>d. x\<in>{a..b} \<longrightarrow> d>0 \<and> (\<forall>u v. x \<in> {u..v} \<and> {u..v} \<subseteq> ball x d \<and> {u..v} \<subseteq> {a..b} \<longrightarrow> f integrable_on {u..v})"
    using assms by auto note this[unfolded gauge_existence_lemma] from choice[OF this] guess d .. note d=this[rule_format]
  guess p apply(rule fine_division_exists[OF gauge_ball_dependent,of d a b]) using d by auto note p=this(1-2)
  note division_of_tagged_division[OF this(1)] note * = operative_division_and[OF operative_integrable,OF this,THEN sym,of f]
  show ?thesis unfolding * apply safe unfolding snd_conv
  proof- fix x k assume "(x,k) \<in> p" note tagged_division_ofD(2-4)[OF p(1) this] fineD[OF p(2) this]
    thus "f integrable_on k" apply safe apply(rule d[THEN conjunct2,rule_format,of x]) by auto qed qed

subsection {* Second FCT or existence of antiderivative. *}

lemma integrable_const[intro]:"(\<lambda>x. c) integrable_on {a..b}"
  unfolding integrable_on_def by(rule,rule has_integral_const)

lemma integral_has_vector_derivative: fixes f::"real \<Rightarrow> 'a::banach"
  assumes "continuous_on {a..b} f" "x \<in> {a..b}"
  shows "((\<lambda>u. integral {vec a..vec u} (f o dest_vec1)) has_vector_derivative f(x)) (at x within {a..b})"
  unfolding has_vector_derivative_def has_derivative_within_alt
apply safe apply(rule scaleR.bounded_linear_left)
proof- fix e::real assume e:"e>0"
  note compact_uniformly_continuous[OF assms(1) compact_real_interval,unfolded uniformly_continuous_on_def]
  from this[rule_format,OF e] guess d apply-by(erule conjE exE)+ note d=this[rule_format]
  let ?I = "\<lambda>a b. integral {vec1 a..vec1 b} (f \<circ> dest_vec1)"
  show "\<exists>d>0. \<forall>y\<in>{a..b}. norm (y - x) < d \<longrightarrow> norm (?I a y - ?I a x - (y - x) *\<^sub>R f x) \<le> e * norm (y - x)"
  proof(rule,rule,rule d,safe) case goal1 show ?case proof(cases "y < x")
      case False have "f \<circ> dest_vec1 integrable_on {vec1 a..vec1 y}" apply(rule integrable_subinterval,rule integrable_continuous)
        apply(rule continuous_on_o_dest_vec1 assms)+  unfolding not_less using assms(2) goal1 by auto
      hence *:"?I a y - ?I a x = ?I x y" unfolding group_simps apply(subst eq_commute) apply(rule integral_combine)
        using False unfolding not_less using assms(2) goal1 by auto
      have **:"norm (y - x) = content {vec1 x..vec1 y}" apply(subst content_1) using False unfolding not_less by auto
      show ?thesis unfolding ** apply(rule has_integral_bound[where f="(\<lambda>u. f u - f x) o dest_vec1"]) unfolding * unfolding o_def
        defer apply(rule has_integral_sub) apply(rule integrable_integral)
        apply(rule integrable_subinterval,rule integrable_continuous) apply(rule continuous_on_o_dest_vec1[unfolded o_def] assms)+
      proof- show "{vec1 x..vec1 y} \<subseteq> {vec1 a..vec1 b}" using goal1 assms(2) by auto
        have *:"y - x = norm(y - x)" using False by auto
        show "((\<lambda>xa. f x) has_integral (y - x) *\<^sub>R f x) {vec1 x..vec1 y}" apply(subst *) unfolding ** by auto
        show "\<forall>xa\<in>{vec1 x..vec1 y}. norm (f (dest_vec1 xa) - f x) \<le> e" apply safe apply(rule less_imp_le)
          apply(rule d(2)[unfolded vector_dist_norm]) using assms(2) using goal1 by auto
      qed(insert e,auto)
    next case True have "f \<circ> dest_vec1 integrable_on {vec1 a..vec1 x}" apply(rule integrable_subinterval,rule integrable_continuous)
        apply(rule continuous_on_o_dest_vec1 assms)+  unfolding not_less using assms(2) goal1 by auto
      hence *:"?I a x - ?I a y = ?I y x" unfolding group_simps apply(subst eq_commute) apply(rule integral_combine)
        using True using assms(2) goal1 by auto
      have **:"norm (y - x) = content {vec1 y..vec1 x}" apply(subst content_1) using True unfolding not_less by auto
      have ***:"\<And>fy fx c::'a. fx - fy - (y - x) *\<^sub>R c = -(fy - fx - (x - y) *\<^sub>R c)" unfolding scaleR_left.diff by auto 
      show ?thesis apply(subst ***) unfolding norm_minus_cancel **
        apply(rule has_integral_bound[where f="(\<lambda>u. f u - f x) o dest_vec1"]) unfolding * unfolding o_def
        defer apply(rule has_integral_sub) apply(subst minus_minus[THEN sym]) unfolding minus_minus
        apply(rule integrable_integral) apply(rule integrable_subinterval,rule integrable_continuous)
        apply(rule continuous_on_o_dest_vec1[unfolded o_def] assms)+
      proof- show "{vec1 y..vec1 x} \<subseteq> {vec1 a..vec1 b}" using goal1 assms(2) by auto
        have *:"x - y = norm(y - x)" using True by auto
        show "((\<lambda>xa. f x) has_integral (x - y) *\<^sub>R f x) {vec1 y..vec1 x}" apply(subst *) unfolding ** by auto
        show "\<forall>xa\<in>{vec1 y..vec1 x}. norm (f (dest_vec1 xa) - f x) \<le> e" apply safe apply(rule less_imp_le)
          apply(rule d(2)[unfolded vector_dist_norm]) using assms(2) using goal1 by auto
      qed(insert e,auto) qed qed qed

lemma integral_has_vector_derivative': fixes f::"real^1 \<Rightarrow> 'a::banach"
  assumes "continuous_on {a..b} f" "x \<in> {a..b}"
  shows "((\<lambda>u. (integral {a..vec u} f)) has_vector_derivative f x) (at (x$1) within {a$1..b$1})"
  using integral_has_vector_derivative[OF continuous_on_o_vec1[OF assms(1)], of "x$1"]
  unfolding o_def vec1_dest_vec1 using assms(2) by auto

lemma antiderivative_continuous: assumes "continuous_on {a..b::real} f"
  obtains g where "\<forall>x\<in> {a..b}. (g has_vector_derivative (f(x)::_::banach)) (at x within {a..b})"
  apply(rule that,rule) using integral_has_vector_derivative[OF assms] by auto

subsection {* Combined fundamental theorem of calculus. *}

lemma antiderivative_integral_continuous: fixes f::"real \<Rightarrow> 'a::banach" assumes "continuous_on {a..b} f"
  obtains g where "\<forall>u\<in>{a..b}. \<forall>v \<in> {a..b}. u \<le> v \<longrightarrow> ((f o dest_vec1) has_integral (g v - g u)) {vec u..vec v}"
proof- from antiderivative_continuous[OF assms] guess g . note g=this
  show ?thesis apply(rule that[of g])
  proof safe case goal1 have "\<forall>x\<in>{u..v}. (g has_vector_derivative f x) (at x within {u..v})"
      apply(rule,rule has_vector_derivative_within_subset) apply(rule g[rule_format]) using goal1(1-2) by auto
    thus ?case using fundamental_theorem_of_calculus[OF goal1(3),of "g o dest_vec1" "f o dest_vec1"]
      unfolding o_def vec1_dest_vec1 by auto qed qed

subsection {* General "twiddling" for interval-to-interval function image. *}

lemma has_integral_twiddle:
  assumes "0 < r" "\<forall>x. h(g x) = x" "\<forall>x. g(h x) = x" "\<forall>x. continuous (at x) g"
  "\<forall>u v. \<exists>w z. g ` {u..v} = {w..z}"
  "\<forall>u v. \<exists>w z. h ` {u..v} = {w..z}"
  "\<forall>u v. content(g ` {u..v}) = r * content {u..v}"
  "(f has_integral i) {a..b}"
  shows "((\<lambda>x. f(g x)) has_integral (1 / r) *\<^sub>R i) (h ` {a..b})"
proof- { presume *:"{a..b} \<noteq> {} \<Longrightarrow> ?thesis"
    show ?thesis apply cases defer apply(rule *,assumption)
    proof- case goal1 thus ?thesis unfolding goal1 assms(8)[unfolded goal1 has_integral_empty_eq] by auto qed }
  assume "{a..b} \<noteq> {}" from assms(6)[rule_format,of a b] guess w z apply-by(erule exE)+ note wz=this
  have inj:"inj g" "inj h" unfolding inj_on_def apply safe apply(rule_tac[!] ccontr)
    using assms(2) apply(erule_tac x=x in allE) using assms(2) apply(erule_tac x=y in allE) defer
    using assms(3) apply(erule_tac x=x in allE) using assms(3) apply(erule_tac x=y in allE) by auto
  show ?thesis unfolding has_integral_def has_integral_compact_interval_def apply(subst if_P) apply(rule,rule,rule wz)
  proof safe fix e::real assume e:"e>0" hence "e * r > 0" using assms(1) by(rule mult_pos_pos)
    from assms(8)[unfolded has_integral,rule_format,OF this] guess d apply-by(erule exE conjE)+ note d=this[rule_format]
    def d' \<equiv> "\<lambda>x y. d (g x) (g y)" have d':"\<And>x. d' x = {y. g y \<in> (d (g x))}" unfolding d'_def by(auto simp add:mem_def)
    show "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of h ` {a..b} \<and> d fine p \<longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - (1 / r) *\<^sub>R i) < e)"
    proof(rule_tac x=d' in exI,safe) show "gauge d'" using d(1) unfolding gauge_def d' using continuous_open_preimage_univ[OF assms(4)] by auto
      fix p assume as:"p tagged_division_of h ` {a..b}" "d' fine p" note p = tagged_division_ofD[OF as(1)] 
      have "(\<lambda>(x, k). (g x, g ` k)) ` p tagged_division_of {a..b} \<and> d fine (\<lambda>(x, k). (g x, g ` k)) ` p" unfolding tagged_division_of 
      proof safe show "finite ((\<lambda>(x, k). (g x, g ` k)) ` p)" using as by auto
        show "d fine (\<lambda>(x, k). (g x, g ` k)) ` p" using as(2) unfolding fine_def d' by auto
        fix x k assume xk[intro]:"(x,k) \<in> p" show "g x \<in> g ` k" using p(2)[OF xk] by auto
        show "\<exists>u v. g ` k = {u..v}" using p(4)[OF xk] using assms(5-6) by auto
        { fix y assume "y \<in> k" thus "g y \<in> {a..b}" "g y \<in> {a..b}" using p(3)[OF xk,unfolded subset_eq,rule_format,of "h (g y)"]
            using assms(2)[rule_format,of y] unfolding inj_image_mem_iff[OF inj(2)] by auto }
        fix x' k' assume xk':"(x',k') \<in> p" fix z assume "z \<in> interior (g ` k)" "z \<in> interior (g ` k')"
        hence *:"interior (g ` k) \<inter> interior (g ` k') \<noteq> {}" by auto
        have same:"(x, k) = (x', k')" apply-apply(rule ccontr,drule p(5)[OF xk xk'])
        proof- assume as:"interior k \<inter> interior k' = {}" from nonempty_witness[OF *] guess z .
          hence "z \<in> g ` (interior k \<inter> interior k')" using interior_image_subset[OF assms(4) inj(1)]
            unfolding image_Int[OF inj(1)] by auto thus False using as by blast
        qed thus "g x = g x'" by auto
        { fix z assume "z \<in> k"  thus  "g z \<in> g ` k'" using same by auto }
        { fix z assume "z \<in> k'" thus  "g z \<in> g ` k"  using same by auto }
      next fix x assume "x \<in> {a..b}" hence "h x \<in>  \<Union>{k. \<exists>x. (x, k) \<in> p}" using p(6) by auto
        then guess X unfolding Union_iff .. note X=this from this(1) guess y unfolding mem_Collect_eq ..
        thus "x \<in> \<Union>{k. \<exists>x. (x, k) \<in> (\<lambda>(x, k). (g x, g ` k)) ` p}" apply-
          apply(rule_tac X="g ` X" in UnionI) defer apply(rule_tac x="h x" in image_eqI)
          using X(2) assms(3)[rule_format,of x] by auto
      qed note ** = d(2)[OF this] have *:"inj_on (\<lambda>(x, k). (g x, g ` k)) p" using inj(1) unfolding inj_on_def by fastsimp
       have "(\<Sum>(x, k)\<in>(\<lambda>(x, k). (g x, g ` k)) ` p. content k *\<^sub>R f x) - i = r *\<^sub>R (\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - i" (is "?l = _") unfolding group_simps add_left_cancel
        unfolding setsum_reindex[OF *] apply(subst scaleR_right.setsum) defer apply(rule setsum_cong2) unfolding o_def split_paired_all split_conv
        apply(drule p(4)) apply safe unfolding assms(7)[rule_format] using p by auto
      also have "... = r *\<^sub>R ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - (1 / r) *\<^sub>R i)" (is "_ = ?r") unfolding scaleR.diff_right scaleR.scaleR_left[THEN sym]
        unfolding real_scaleR_def using assms(1) by auto finally have *:"?l = ?r" .
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - (1 / r) *\<^sub>R i) < e" using ** unfolding * unfolding norm_scaleR
        using assms(1) by(auto simp add:field_simps) qed qed qed

subsection {* Special case of a basic affine transformation. *}

lemma interval_image_affinity_interval: shows "\<exists>u v. (\<lambda>x. m *\<^sub>R (x::real^'n) + c) ` {a..b} = {u..v}"
  unfolding image_affinity_interval by auto

lemmas Cart_simps = Cart_nth.add Cart_nth.minus Cart_nth.zero Cart_nth.diff Cart_nth.scaleR real_scaleR_def Cart_lambda_beta
   Cart_eq vector_le_def vector_less_def

lemma setprod_cong2: assumes "\<And>x. x \<in> A \<Longrightarrow> f x = g x" shows "setprod f A = setprod g A"
  apply(rule setprod_cong) using assms by auto

lemma content_image_affinity_interval: 
 "content((\<lambda>x::real^'n. m *\<^sub>R x + c) ` {a..b}) = (abs m) ^ CARD('n) * content {a..b}" (is "?l = ?r")
proof- { presume *:"{a..b}\<noteq>{} \<Longrightarrow> ?thesis" show ?thesis apply(cases,rule *,assumption)
      unfolding not_not using content_empty by auto }
  assume as:"{a..b}\<noteq>{}" show ?thesis proof(cases "m \<ge> 0")
    case True show ?thesis unfolding image_affinity_interval if_not_P[OF as] if_P[OF True]
      unfolding content_closed_interval'[OF as] apply(subst content_closed_interval') 
      defer apply(subst setprod_constant[THEN sym]) apply(rule finite_UNIV) unfolding setprod_timesf[THEN sym]
      apply(rule setprod_cong2) using True as unfolding interval_ne_empty Cart_simps not_le  
      by(auto simp add:field_simps intro:mult_left_mono)
  next case False show ?thesis unfolding image_affinity_interval if_not_P[OF as] if_not_P[OF False]
      unfolding content_closed_interval'[OF as] apply(subst content_closed_interval') 
      defer apply(subst setprod_constant[THEN sym]) apply(rule finite_UNIV) unfolding setprod_timesf[THEN sym]
      apply(rule setprod_cong2) using False as unfolding interval_ne_empty Cart_simps not_le 
      by(auto simp add:field_simps mult_le_cancel_left_neg) qed qed

lemma has_integral_affinity: assumes "(f has_integral i) {a..b::real^'n}" "m \<noteq> 0"
  shows "((\<lambda>x. f(m *\<^sub>R x + c)) has_integral ((1 / (abs(m) ^ CARD('n::finite))) *\<^sub>R i)) ((\<lambda>x. (1 / m) *\<^sub>R x + -((1 / m) *\<^sub>R c)) ` {a..b})"
  apply(rule has_integral_twiddle,safe) unfolding Cart_eq Cart_simps apply(rule zero_less_power)
  defer apply(insert assms(2), simp add:field_simps) apply(insert assms(2), simp add:field_simps)
  apply(rule continuous_intros)+ apply(rule interval_image_affinity_interval)+ apply(rule content_image_affinity_interval) using assms by auto

lemma integrable_affinity: assumes "f integrable_on {a..b}" "m \<noteq> 0"
  shows "(\<lambda>x. f(m *\<^sub>R x + c)) integrable_on ((\<lambda>x. (1 / m) *\<^sub>R x + -((1/m) *\<^sub>R c)) ` {a..b})"
  using assms unfolding integrable_on_def apply safe apply(drule has_integral_affinity) by auto

subsection {* Special case of stretching coordinate axes separately. *}

lemma image_stretch_interval:
  "(\<lambda>x. \<chi> k. m k * x$k) ` {a..b::real^'n} =
  (if {a..b} = {} then {} else {(\<chi> k. min (m(k) * a$k) (m(k) * b$k)) ..  (\<chi> k. max (m(k) * a$k) (m(k) * b$k))})" (is "?l = ?r")
proof(cases "{a..b}={}") case True thus ?thesis unfolding True by auto
next have *:"\<And>P Q. (\<forall>i. P i) \<and> (\<forall>i. Q i) \<longleftrightarrow> (\<forall>i. P i \<and> Q i)" by auto
  case False note ab = this[unfolded interval_ne_empty]
  show ?thesis apply-apply(rule set_ext)
  proof- fix x::"real^'n" have **:"\<And>P Q. (\<forall>i. P i = Q i) \<Longrightarrow> (\<forall>i. P i) = (\<forall>i. Q i)" by auto
    show "x \<in> ?l \<longleftrightarrow> x \<in> ?r" unfolding if_not_P[OF False] 
      unfolding image_iff mem_interval Bex_def Cart_simps Cart_eq *
      unfolding lambda_skolem[THEN sym,of "\<lambda> i xa. (a $ i \<le> xa \<and> xa \<le> b $ i) \<and> x $ i = m i * xa"]
    proof(rule **,rule) fix i::'n show "(\<exists>xa. (a $ i \<le> xa \<and> xa \<le> b $ i) \<and> x $ i = m i * xa) =
        (min (m i * a $ i) (m i * b $ i) \<le> x $ i \<and> x $ i \<le> max (m i * a $ i) (m i * b $ i))"
      proof(cases "m i = 0") case True thus ?thesis using ab by auto
      next case False hence "0 < m i \<or> 0 > m i" by auto thus ?thesis apply-
        proof(erule disjE) assume as:"0 < m i" hence *:"min (m i * a $ i) (m i * b $ i) = m i * a $ i"
            "max (m i * a $ i) (m i * b $ i) = m i * b $ i" using ab unfolding min_def max_def by auto
          show ?thesis unfolding * apply rule defer apply(rule_tac x="1 / m i * x$i" in exI)
            using as by(auto simp add:field_simps)
        next assume as:"0 > m i" hence *:"max (m i * a $ i) (m i * b $ i) = m i * a $ i"
            "min (m i * a $ i) (m i * b $ i) = m i * b $ i" using ab as unfolding min_def max_def 
            by(auto simp add:field_simps mult_le_cancel_left_neg intro:real_le_antisym)
          show ?thesis unfolding * apply rule defer apply(rule_tac x="1 / m i * x$i" in exI)
            using as by(auto simp add:field_simps) qed qed qed qed qed 

lemma interval_image_stretch_interval: "\<exists>u v. (\<lambda>x. \<chi> k. m k * x$k) ` {a..b::real^'n} = {u..v}"
  unfolding image_stretch_interval by auto 

lemma content_image_stretch_interval:
  "content((\<lambda>x::real^'n. \<chi> k. m k * x$k) ` {a..b}) = abs(setprod m UNIV) * content({a..b})"
proof(cases "{a..b} = {}") case True thus ?thesis
    unfolding content_def image_is_empty image_stretch_interval if_P[OF True] by auto
next case False hence "(\<lambda>x. \<chi> k. m k * x $ k) ` {a..b} \<noteq> {}" by auto
  thus ?thesis using False unfolding content_def image_stretch_interval apply- unfolding interval_bounds' if_not_P
    unfolding abs_setprod setprod_timesf[THEN sym] apply(rule setprod_cong2) unfolding Cart_lambda_beta
  proof- fix i::'n have "(m i < 0 \<or> m i > 0) \<or> m i = 0" by auto
    thus "max (m i * a $ i) (m i * b $ i) - min (m i * a $ i) (m i * b $ i) = \<bar>m i\<bar> * (b $ i - a $ i)"
      apply-apply(erule disjE)+ unfolding min_def max_def using False[unfolded interval_ne_empty,rule_format,of i] 
      by(auto simp add:field_simps not_le mult_le_cancel_left_neg mult_le_cancel_left_pos) qed qed

lemma has_integral_stretch: assumes "(f has_integral i) {a..b}" "\<forall>k. ~(m k = 0)"
  shows "((\<lambda>x. f(\<chi> k. m k * x$k)) has_integral
             ((1/(abs(setprod m UNIV))) *\<^sub>R i)) ((\<lambda>x. \<chi> k. 1/(m k) * x$k) ` {a..b})"
  apply(rule has_integral_twiddle) unfolding zero_less_abs_iff content_image_stretch_interval
  unfolding image_stretch_interval empty_as_interval Cart_eq using assms
proof- show "\<forall>x. continuous (at x) (\<lambda>x. \<chi> k. m k * x $ k)"
   apply(rule,rule linear_continuous_at) unfolding linear_linear
   unfolding linear_def Cart_simps Cart_eq by(auto simp add:field_simps) qed auto

lemma integrable_stretch: 
  assumes "f integrable_on {a..b}" "\<forall>k. ~(m k = 0)"
  shows "(\<lambda>x. f(\<chi> k. m k * x$k)) integrable_on ((\<lambda>x. \<chi> k. 1/(m k) * x$k) ` {a..b})"
  using assms unfolding integrable_on_def apply-apply(erule exE) apply(drule has_integral_stretch) by auto

subsection {* even more special cases. *}

lemma uminus_interval_vector[simp]:"uminus ` {a..b} = {-b .. -a::real^'n}"
  apply(rule set_ext,rule) defer unfolding image_iff
  apply(rule_tac x="-x" in bexI) by(auto simp add:vector_le_def minus_le_iff le_minus_iff)

lemma has_integral_reflect_lemma[intro]: assumes "(f has_integral i) {a..b}"
  shows "((\<lambda>x. f(-x)) has_integral i) {-b .. -a}"
  using has_integral_affinity[OF assms, of "-1" 0] by auto

lemma has_integral_reflect[simp]: "((\<lambda>x. f(-x)) has_integral i) {-b..-a} \<longleftrightarrow> (f has_integral i) ({a..b})"
  apply rule apply(drule_tac[!] has_integral_reflect_lemma) by auto

lemma integrable_reflect[simp]: "(\<lambda>x. f(-x)) integrable_on {-b..-a} \<longleftrightarrow> f integrable_on {a..b}"
  unfolding integrable_on_def by auto

lemma integral_reflect[simp]: "integral {-b..-a} (\<lambda>x. f(-x)) = integral ({a..b}) f"
  unfolding integral_def by auto

subsection {* Stronger form of FCT; quite a tedious proof. *}

(** move this **)
declare norm_triangle_ineq4[intro] 

lemma bgauge_existence_lemma: "(\<forall>x\<in>s. \<exists>d::real. 0 < d \<and> q d x) \<longleftrightarrow> (\<forall>x. \<exists>d>0. x\<in>s \<longrightarrow> q d x)" by(meson zero_less_one)

lemma additive_tagged_division_1': fixes f::"real \<Rightarrow> 'a::real_normed_vector"
  assumes "a \<le> b" "p tagged_division_of {vec1 a..vec1 b}"
  shows "setsum (\<lambda>(x,k). f (dest_vec1 (interval_upperbound k)) - f(dest_vec1 (interval_lowerbound k))) p = f b - f a"
  using additive_tagged_division_1[OF _ assms(2), of "f o dest_vec1"]
  unfolding o_def vec1_dest_vec1 using assms(1) by auto

lemma split_minus[simp]:"(\<lambda>(x, k). ?f x k) x - (\<lambda>(x, k). ?g x k) x = (\<lambda>(x, k). ?f x k - ?g x k) x"
  unfolding split_def by(rule refl)

lemma norm_triangle_le_sub: "norm x + norm y \<le> e \<Longrightarrow> norm (x - y) \<le> e"
  apply(subst(asm)(2) norm_minus_cancel[THEN sym])
  apply(drule norm_triangle_le) by(auto simp add:group_simps)

lemma fundamental_theorem_of_calculus_interior:
  assumes"a \<le> b" "continuous_on {a..b} f" "\<forall>x\<in>{a<..<b}. (f has_vector_derivative f'(x)) (at x)"
  shows "((f' o dest_vec1) has_integral (f b - f a)) {vec a..vec b}"
proof- { presume *:"a < b \<Longrightarrow> ?thesis" 
    show ?thesis proof(cases,rule *,assumption)
      assume "\<not> a < b" hence "a = b" using assms(1) by auto
      hence *:"{vec a .. vec b} = {vec b}" "f b - f a = 0" apply(auto simp add: Cart_simps) by smt
      show ?thesis unfolding *(2) apply(rule has_integral_null) unfolding content_eq_0_1 using * `a=b` by auto
    qed } assume ab:"a < b"
  let ?P = "\<lambda>e. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {vec1 a..vec1 b} \<and> d fine p \<longrightarrow>
                   norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R (f' \<circ> dest_vec1) x) - (f b - f a)) \<le> e * content {vec1 a..vec1 b})"
  { presume "\<And>e. e>0 \<Longrightarrow> ?P e" thus ?thesis unfolding has_integral_factor_content by auto }
  fix e::real assume e:"e>0"
  note assms(3)[unfolded has_vector_derivative_def has_derivative_at_alt ball_conj_distrib]
  note conjunctD2[OF this] note bounded=this(1) and this(2)
  from this(2) have "\<forall>x\<in>{a<..<b}. \<exists>d>0. \<forall>y. norm (y - x) < d \<longrightarrow> norm (f y - f x - (y - x) *\<^sub>R f' x) \<le> e/2 * norm (y - x)"
    apply-apply safe apply(erule_tac x=x in ballE,erule_tac x="e/2" in allE) using e by auto note this[unfolded bgauge_existence_lemma]
  from choice[OF this] guess d .. note conjunctD2[OF this[rule_format]] note d = this[rule_format]
  have "bounded (f ` {a..b})" apply(rule compact_imp_bounded compact_continuous_image)+ using compact_real_interval assms by auto
  from this[unfolded bounded_pos] guess B .. note B = this[rule_format]

  have "\<exists>da. 0 < da \<and> (\<forall>c. a \<le> c \<and> {a..c} \<subseteq> {a..b} \<and> {a..c} \<subseteq> ball a da
    \<longrightarrow> norm(content {vec1 a..vec1 c} *\<^sub>R f' a - (f c - f a)) \<le> (e * (b - a)) / 4)"
  proof- have "a\<in>{a..b}" using ab by auto
    note assms(2)[unfolded continuous_on_eq_continuous_within,rule_format,OF this]
    note * = this[unfolded continuous_within Lim_within,rule_format] have "(e * (b - a)) / 8 > 0" using e ab by(auto simp add:field_simps)
    from *[OF this] guess k .. note k = conjunctD2[OF this,rule_format]
    have "\<exists>l. 0 < l \<and> norm(l *\<^sub>R f' a) \<le> (e * (b - a)) / 8"
    proof(cases "f' a = 0") case True
      thus ?thesis apply(rule_tac x=1 in exI) using ab e by(auto intro!:mult_nonneg_nonneg) 
    next case False thus ?thesis 
        apply(rule_tac x="(e * (b - a)) / 8 / norm (f' a)" in exI)
        using ab e by(auto simp add:field_simps)
    qed then guess l .. note l = conjunctD2[OF this]
    show ?thesis apply(rule_tac x="min k l" in exI) apply safe unfolding min_less_iff_conj apply(rule,(rule l k)+)
    proof- fix c assume as:"a \<le> c" "{a..c} \<subseteq> {a..b}" "{a..c} \<subseteq> ball a (min k l)" 
      note as' = this[unfolded subset_eq Ball_def mem_ball dist_real_def mem_interval]
      have "norm ((c - a) *\<^sub>R f' a - (f c - f a)) \<le> norm ((c - a) *\<^sub>R f' a) + norm (f c - f a)" by(rule norm_triangle_ineq4)
      also have "... \<le> e * (b - a) / 8 + e * (b - a) / 8" 
      proof(rule add_mono) case goal1 have "\<bar>c - a\<bar> \<le> \<bar>l\<bar>" using as' by auto
        thus ?case apply-apply(rule order_trans[OF _ l(2)]) unfolding norm_scaleR apply(rule mult_right_mono) by auto
      next case goal2 show ?case apply(rule less_imp_le) apply(cases "a = c") defer
          apply(rule k(2)[unfolded vector_dist_norm]) using as' e ab by(auto simp add:field_simps)
      qed finally show "norm (content {vec1 a..vec1 c} *\<^sub>R f' a - (f c - f a)) \<le> e * (b - a) / 4" unfolding content_1'[OF as(1)] by auto
    qed qed then guess da .. note da=conjunctD2[OF this,rule_format]

  have "\<exists>db>0. \<forall>c\<le>b. {c..b} \<subseteq> {a..b} \<and> {c..b} \<subseteq> ball b db \<longrightarrow> norm(content {vec1 c..vec1 b} *\<^sub>R f' b - (f b - f c)) \<le> (e * (b - a)) / 4"
  proof- have "b\<in>{a..b}" using ab by auto
    note assms(2)[unfolded continuous_on_eq_continuous_within,rule_format,OF this]
    note * = this[unfolded continuous_within Lim_within,rule_format] have "(e * (b - a)) / 8 > 0" using e ab by(auto simp add:field_simps)
    from *[OF this] guess k .. note k = conjunctD2[OF this,rule_format]
    have "\<exists>l. 0 < l \<and> norm(l *\<^sub>R f' b) \<le> (e * (b - a)) / 8"
    proof(cases "f' b = 0") case True
      thus ?thesis apply(rule_tac x=1 in exI) using ab e by(auto intro!:mult_nonneg_nonneg) 
    next case False thus ?thesis 
        apply(rule_tac x="(e * (b - a)) / 8 / norm (f' b)" in exI)
        using ab e by(auto simp add:field_simps)
    qed then guess l .. note l = conjunctD2[OF this]
    show ?thesis apply(rule_tac x="min k l" in exI) apply safe unfolding min_less_iff_conj apply(rule,(rule l k)+)
    proof- fix c assume as:"c \<le> b" "{c..b} \<subseteq> {a..b}" "{c..b} \<subseteq> ball b (min k l)" 
      note as' = this[unfolded subset_eq Ball_def mem_ball dist_real_def mem_interval]
      have "norm ((b - c) *\<^sub>R f' b - (f b - f c)) \<le> norm ((b - c) *\<^sub>R f' b) + norm (f b - f c)" by(rule norm_triangle_ineq4)
      also have "... \<le> e * (b - a) / 8 + e * (b - a) / 8" 
      proof(rule add_mono) case goal1 have "\<bar>c - b\<bar> \<le> \<bar>l\<bar>" using as' by auto
        thus ?case apply-apply(rule order_trans[OF _ l(2)]) unfolding norm_scaleR apply(rule mult_right_mono) by auto
      next case goal2 show ?case apply(rule less_imp_le) apply(cases "b = c") defer apply(subst norm_minus_commute)
          apply(rule k(2)[unfolded vector_dist_norm]) using as' e ab by(auto simp add:field_simps)
      qed finally show "norm (content {vec1 c..vec1 b} *\<^sub>R f' b - (f b - f c)) \<le> e * (b - a) / 4" unfolding content_1'[OF as(1)] by auto
    qed qed then guess db .. note db=conjunctD2[OF this,rule_format]

  let ?d = "(\<lambda>x. ball x (if x=vec1 a then da else if x=vec b then db else d (dest_vec1 x)))"
  show "?P e" apply(rule_tac x="?d" in exI)
  proof safe case goal1 show ?case apply(rule gauge_ball_dependent) using ab db(1) da(1) d(1) by auto
  next case goal2 note as=this let ?A = "{t. fst t \<in> {vec1 a, vec1 b}}" note p = tagged_division_ofD[OF goal2(1)]
    have pA:"p = (p \<inter> ?A) \<union> (p - ?A)" "finite (p \<inter> ?A)" "finite (p - ?A)" "(p \<inter> ?A) \<inter> (p - ?A) = {}"  using goal2 by auto
    note * = additive_tagged_division_1'[OF assms(1) goal2(1), THEN sym]
    have **:"\<And>n1 s1 n2 s2::real. n2 \<le> s2 / 2 \<Longrightarrow> n1 - s1 \<le> s2 / 2 \<Longrightarrow> n1 + n2 \<le> s1 + s2" by arith
    show ?case unfolding content_1'[OF assms(1)] and *[of "\<lambda>x. x"] *[of f] setsum_subtractf[THEN sym] split_minus
      unfolding setsum_right_distrib apply(subst(2) pA,subst pA) unfolding setsum_Un_disjoint[OF pA(2-)]
    proof(rule norm_triangle_le,rule **) 
      case goal1 show ?case apply(rule order_trans,rule setsum_norm_le) apply(rule pA) defer apply(subst divide.setsum)
      proof(rule order_refl,safe,unfold not_le o_def split_conv fst_conv,rule ccontr) fix x k assume as:"(x,k) \<in> p"
          "e * (dest_vec1 (interval_upperbound k) - dest_vec1 (interval_lowerbound k)) / 2
          < norm (content k *\<^sub>R f' (dest_vec1 x) - (f (dest_vec1 (interval_upperbound k)) - f (dest_vec1 (interval_lowerbound k))))"
        from p(4)[OF this(1)] guess u v apply-by(erule exE)+ note k=this
        hence "\<forall>i. u$i \<le> v$i" and uv:"{u,v}\<subseteq>{u..v}" using p(2)[OF as(1)] by auto note this(1) this(1)[unfolded forall_1]
        note result = as(2)[unfolded k interval_bounds[OF this(1)] content_1[OF this(2)]]

        assume as':"x \<noteq> vec1 a" "x \<noteq> vec1 b" hence "x$1 \<in> {a<..<b}" using p(2-3)[OF as(1)] by(auto simp add:Cart_simps) note  * = d(2)[OF this] 
        have "norm ((v$1 - u$1) *\<^sub>R f' (x$1) - (f (v$1) - f (u$1))) =
          norm ((f (u$1) - f (x$1) - (u$1 - x$1) *\<^sub>R f' (x$1)) - (f (v$1) - f (x$1) - (v$1 - x$1) *\<^sub>R f' (x$1)))" 
          apply(rule arg_cong[of _ _ norm]) unfolding scaleR_left.diff by auto 
        also have "... \<le> e / 2 * norm (u$1 - x$1) + e / 2 * norm (v$1 - x$1)" apply(rule norm_triangle_le_sub)
          apply(rule add_mono) apply(rule_tac[!] *) using fineD[OF goal2(2) as(1)] as' unfolding k subset_eq
          apply- apply(erule_tac x=u in ballE,erule_tac[3] x=v in ballE) using uv by(auto simp add:dist_real)
        also have "... \<le> e / 2 * norm (v$1 - u$1)" using p(2)[OF as(1)] unfolding k by(auto simp add:field_simps)
        finally have "e * (dest_vec1 v - dest_vec1 u) / 2 < e * (dest_vec1 v - dest_vec1 u) / 2"
          apply- apply(rule less_le_trans[OF result]) using uv by auto thus False by auto qed

    next have *:"\<And>x s1 s2::real. 0 \<le> s1 \<Longrightarrow> x \<le> (s1 + s2) / 2 \<Longrightarrow> x - s1 \<le> s2 / 2" by auto
      case goal2 show ?case apply(rule *) apply(rule setsum_nonneg) apply(rule,unfold split_paired_all split_conv)
        defer unfolding setsum_Un_disjoint[OF pA(2-),THEN sym] pA(1)[THEN sym] unfolding setsum_right_distrib[THEN sym] 
        apply(subst additive_tagged_division_1[OF _ as(1)]) unfolding vec1_dest_vec1 apply(rule assms)
      proof- fix x k assume "(x,k) \<in> p \<inter> {t. fst t \<in> {vec1 a, vec1 b}}" note xk=IntD1[OF this]
        from p(4)[OF this] guess u v apply-by(erule exE)+ note uv=this
        with p(2)[OF xk] have "{u..v} \<noteq> {}" by auto
        thus "0 \<le> e * ((interval_upperbound k)$1 - (interval_lowerbound k)$1)"
          unfolding uv using e by(auto simp add:field_simps)
      next have *:"\<And>s f t e. setsum f s = setsum f t \<Longrightarrow> norm(setsum f t) \<le> e \<Longrightarrow> norm(setsum f s) \<le> e" by auto
        show "norm (\<Sum>(x, k)\<in>p \<inter> ?A. content k *\<^sub>R (f' \<circ> dest_vec1) x -
          (f ((interval_upperbound k)$1) - f ((interval_lowerbound k)$1))) \<le> e * (b - a) / 2" 
          apply(rule *[where t="p \<inter> {t. fst t \<in> {vec1 a, vec1 b} \<and> content(snd t) \<noteq> 0}"])
          apply(rule setsum_mono_zero_right[OF pA(2)]) defer apply(rule) unfolding split_paired_all split_conv o_def
        proof- fix x k assume "(x,k) \<in> p \<inter> {t. fst t \<in> {vec1 a, vec1 b}} - p \<inter> {t. fst t \<in> {vec1 a, vec1 b} \<and> content (snd t) \<noteq> 0}"
          hence xk:"(x,k)\<in>p" "content k = 0" by auto from p(4)[OF xk(1)] guess u v apply-by(erule exE)+ note uv=this
          have "k\<noteq>{}" using p(2)[OF xk(1)] by auto hence *:"u = v" using xk unfolding uv content_eq_0_1 interval_eq_empty by auto
          thus "content k *\<^sub>R (f' (x$1)) - (f ((interval_upperbound k)$1) - f ((interval_lowerbound k)$1)) = 0" using xk unfolding uv by auto
        next have *:"p \<inter> {t. fst t \<in> {vec1 a, vec1 b} \<and> content(snd t) \<noteq> 0} = 
            {t. t\<in>p \<and> fst t = vec1 a \<and> content(snd t) \<noteq> 0} \<union> {t. t\<in>p \<and> fst t = vec1 b \<and> content(snd t) \<noteq> 0}" by blast
          have **:"\<And>s f. \<And>e::real. (\<forall>x y. x \<in> s \<and> y \<in> s \<longrightarrow> x = y) \<Longrightarrow> (\<forall>x. x \<in> s \<longrightarrow> norm(f x) \<le> e) \<Longrightarrow> e>0 \<Longrightarrow> norm(setsum f s) \<le> e"
          proof(case_tac "s={}") case goal2 then obtain x where "x\<in>s" by auto hence *:"s = {x}" using goal2(1) by auto
            thus ?case using `x\<in>s` goal2(2) by auto
          qed auto
          case goal2 show ?case apply(subst *, subst setsum_Un_disjoint) prefer 4 apply(rule order_trans[of _ "e * (b - a)/4 + e * (b - a)/4"]) 
            apply(rule norm_triangle_le,rule add_mono) apply(rule_tac[1-2] **)
          proof- let ?B = "\<lambda>x. {t \<in> p. fst t = vec1 x \<and> content (snd t) \<noteq> 0}"
            have pa:"\<And>k. (vec1 a, k) \<in> p \<Longrightarrow> \<exists>v. k = {vec1 a .. v} \<and> vec1 a \<le> v" 
            proof- case goal1 guess u v using p(4)[OF goal1] apply-by(erule exE)+ note uv=this
              have *:"u \<le> v" using p(2)[OF goal1] unfolding uv by auto
              have u:"u = vec1 a" proof(rule ccontr)  have "u \<in> {u..v}" using p(2-3)[OF goal1(1)] unfolding uv by auto 
                have "u \<ge> vec1 a" using p(2-3)[OF goal1(1)] unfolding uv subset_eq by auto moreover assume "u\<noteq>vec1 a" ultimately
                have "u > vec1 a" unfolding Cart_simps by auto
                thus False using p(2)[OF goal1(1)] unfolding uv by(auto simp add:Cart_simps)
              qed thus ?case apply(rule_tac x=v in exI) unfolding uv using * by auto
            qed
            have pb:"\<And>k. (vec1 b, k) \<in> p \<Longrightarrow> \<exists>v. k = {v .. vec1 b} \<and> vec1 b \<ge> v" 
            proof- case goal1 guess u v using p(4)[OF goal1] apply-by(erule exE)+ note uv=this
              have *:"u \<le> v" using p(2)[OF goal1] unfolding uv by auto
              have u:"v = vec1 b" proof(rule ccontr)  have "u \<in> {u..v}" using p(2-3)[OF goal1(1)] unfolding uv by auto 
                have "v \<le> vec1 b" using p(2-3)[OF goal1(1)] unfolding uv subset_eq by auto moreover assume "v\<noteq>vec1 b" ultimately
                have "v < vec1 b" unfolding Cart_simps by auto
                thus False using p(2)[OF goal1(1)] unfolding uv by(auto simp add:Cart_simps)
              qed thus ?case apply(rule_tac x=u in exI) unfolding uv using * by auto
            qed

            show "\<forall>x y. x \<in> ?B a \<and> y \<in> ?B a \<longrightarrow> x = y" apply(rule,rule,rule,unfold split_paired_all)
              unfolding mem_Collect_eq fst_conv snd_conv apply safe
            proof- fix x k k' assume k:"(vec1 a, k) \<in> p" "(vec1 a, k') \<in> p" "content k \<noteq> 0" "content k' \<noteq> 0"
              guess v using pa[OF k(1)] .. note v = conjunctD2[OF this]
              guess v' using pa[OF k(2)] .. note v' = conjunctD2[OF this] let ?v = "vec1 (min (v$1) (v'$1))"
              have "{vec1 a <..< ?v} \<subseteq> k \<inter> k'" unfolding v v' by(auto simp add:Cart_simps) note subset_interior[OF this,unfolded interior_inter]
              moreover have "vec1 ((a + ?v$1)/2) \<in> {vec1 a <..< ?v}" using k(3-) unfolding v v' content_eq_0_1 not_le by(auto simp add:Cart_simps)
              ultimately have "vec1 ((a + ?v$1)/2) \<in> interior k \<inter> interior k'" unfolding interior_open[OF open_interval] by auto
              hence *:"k = k'" apply- apply(rule ccontr) using p(5)[OF k(1-2)] by auto
              { assume "x\<in>k" thus "x\<in>k'" unfolding * . } { assume "x\<in>k'" thus "x\<in>k" unfolding * . }
            qed 
            show "\<forall>x y. x \<in> ?B b \<and> y \<in> ?B b \<longrightarrow> x = y" apply(rule,rule,rule,unfold split_paired_all)
              unfolding mem_Collect_eq fst_conv snd_conv apply safe
            proof- fix x k k' assume k:"(vec1 b, k) \<in> p" "(vec1 b, k') \<in> p" "content k \<noteq> 0" "content k' \<noteq> 0"
              guess v using pb[OF k(1)] .. note v = conjunctD2[OF this]
              guess v' using pb[OF k(2)] .. note v' = conjunctD2[OF this] let ?v = "vec1 (max (v$1) (v'$1))"
              have "{?v <..< vec1 b} \<subseteq> k \<inter> k'" unfolding v v' by(auto simp add:Cart_simps) note subset_interior[OF this,unfolded interior_inter]
              moreover have "vec1 ((b + ?v$1)/2) \<in> {?v <..< vec1 b}" using k(3-) unfolding v v' content_eq_0_1 not_le by(auto simp add:Cart_simps)
              ultimately have "vec1 ((b + ?v$1)/2) \<in> interior k \<inter> interior k'" unfolding interior_open[OF open_interval] by auto
              hence *:"k = k'" apply- apply(rule ccontr) using p(5)[OF k(1-2)] by auto
              { assume "x\<in>k" thus "x\<in>k'" unfolding * . } { assume "x\<in>k'" thus "x\<in>k" unfolding * . }
            qed

            let ?a = a and ?b = b (* a is something else while proofing the next theorem. *)
            show "\<forall>x. x \<in> ?B a \<longrightarrow> norm ((\<lambda>(x, k). content k *\<^sub>R f' (x$1) - (f ((interval_upperbound k)$1) - f ((interval_lowerbound k)$1))) x)
              \<le> e * (b - a) / 4" apply safe unfolding fst_conv snd_conv apply safe unfolding vec1_dest_vec1
            proof- case goal1 guess v using pa[OF goal1(1)] .. note v = conjunctD2[OF this]
              have "vec1 ?a\<in>{vec1 ?a..v}" using v(2) by auto hence "dest_vec1 v \<le> ?b" using p(3)[OF goal1(1)] unfolding subset_eq v by auto
              moreover have "{?a..dest_vec1 v} \<subseteq> ball ?a da" using fineD[OF as(2) goal1(1)]
                apply-apply(subst(asm) if_P,rule refl) unfolding subset_eq apply safe apply(erule_tac x="vec1 x" in ballE)
                by(auto simp add:Cart_simps subset_eq dist_real v dist_real_def) ultimately
              show ?case unfolding v unfolding interval_bounds[OF v(2)[unfolded v vector_le_def]] vec1_dest_vec1 apply-
                apply(rule da(2)[of "v$1",unfolded vec1_dest_vec1])
                using goal1 fineD[OF as(2) goal1(1)] unfolding v content_eq_0_1 by auto
            qed
            show "\<forall>x. x \<in> ?B b \<longrightarrow> norm ((\<lambda>(x, k). content k *\<^sub>R f' (x$1) - (f ((interval_upperbound k)$1) - f ((interval_lowerbound k)$1))) x)
              \<le> e * (b - a) / 4" apply safe unfolding fst_conv snd_conv apply safe unfolding vec1_dest_vec1
            proof- case goal1 guess v using pb[OF goal1(1)] .. note v = conjunctD2[OF this]
              have "vec1 ?b\<in>{v..vec1 ?b}" using v(2) by auto hence "dest_vec1 v \<ge> ?a" using p(3)[OF goal1(1)] unfolding subset_eq v by auto
              moreover have "{dest_vec1 v..?b} \<subseteq> ball ?b db" using fineD[OF as(2) goal1(1)]
                apply-apply(subst(asm) if_P,rule refl) unfolding subset_eq apply safe apply(erule_tac x="vec1 x" in ballE) using ab
                by(auto simp add:Cart_simps subset_eq dist_real v dist_real_def) ultimately
              show ?case unfolding v unfolding interval_bounds[OF v(2)[unfolded v vector_le_def]] vec1_dest_vec1 apply-
                apply(rule db(2)[of "v$1",unfolded vec1_dest_vec1])
                using goal1 fineD[OF as(2) goal1(1)] unfolding v content_eq_0_1 by auto
            qed
          qed(insert p(1) ab e, auto simp add:field_simps) qed auto qed qed qed qed

subsection {* Stronger form with finite number of exceptional points. *}

lemma fundamental_theorem_of_calculus_interior_strong: fixes f::"real \<Rightarrow> 'a::banach"
  assumes"finite s" "a \<le> b" "continuous_on {a..b} f"
  "\<forall>x\<in>{a<..<b} - s. (f has_vector_derivative f'(x)) (at x)"
  shows "((f' o dest_vec1) has_integral (f b - f a)) {vec a..vec b}" using assms apply- 
proof(induct "card s" arbitrary:s a b)
  case 0 show ?case apply(rule fundamental_theorem_of_calculus_interior) using 0 by auto
next case (Suc n) from this(2) guess c s' apply-apply(subst(asm) eq_commute) unfolding card_Suc_eq
    apply(subst(asm)(2) eq_commute) by(erule exE conjE)+ note cs = this[rule_format]
  show ?case proof(cases "c\<in>{a<..<b}")
    case False thus ?thesis apply- apply(rule Suc(1)[OF cs(3) _ Suc(4,5)]) apply safe defer
      apply(rule Suc(6)[rule_format]) using Suc(3) unfolding cs by auto
  next have *:"f b - f a = (f c - f a) + (f b - f c)" by auto
    case True hence "vec1 a \<le> vec1 c" "vec1 c \<le> vec1 b" by auto
    thus ?thesis apply(subst *) apply(rule has_integral_combine) apply assumption+
      apply(rule_tac[!] Suc(1)[OF cs(3)]) using Suc(3) unfolding cs
    proof- show "continuous_on {a..c} f" "continuous_on {c..b} f"
        apply(rule_tac[!] continuous_on_subset[OF Suc(5)]) using True by auto
      let ?P = "\<lambda>i j. \<forall>x\<in>{i<..<j} - s'. (f has_vector_derivative f' x) (at x)"
      show "?P a c" "?P c b" apply safe apply(rule_tac[!] Suc(6)[rule_format]) using True unfolding cs by auto
    qed auto qed qed

lemma fundamental_theorem_of_calculus_strong: fixes f::"real \<Rightarrow> 'a::banach"
  assumes "finite s" "a \<le> b" "continuous_on {a..b} f"
  "\<forall>x\<in>{a..b} - s. (f has_vector_derivative f'(x)) (at x)"
  shows "((f' o dest_vec1) has_integral (f(b) - f(a))) {vec1 a..vec1 b}"
  apply(rule fundamental_theorem_of_calculus_interior_strong[OF assms(1-3), of f'])
  using assms(4) by auto

end
