header {* Kurzweil-Henstock Gauge Integration in many dimensions. *}
(*  Author:                     John Harrison
    Translation from HOL light: Robert Himmelmann, TU Muenchen *)

theory Integration
imports
  Derivative
  "~~/src/HOL/Library/Indicator_Function"
begin

declare [[smt_certificates = "Integration.certs"]]
declare [[smt_read_only_certificates = true]]
declare [[smt_oracle = false]]

(*declare not_less[simp] not_le[simp]*)

lemmas scaleR_simps = scaleR_zero_left scaleR_minus_left scaleR_left_diff_distrib
  scaleR_zero_right scaleR_minus_right scaleR_right_diff_distrib scaleR_eq_0_iff
  scaleR_cancel_left scaleR_cancel_right scaleR_add_right scaleR_add_left real_vector_class.scaleR_one

lemma real_arch_invD:
  "0 < (e::real) \<Longrightarrow> (\<exists>n::nat. n \<noteq> 0 \<and> 0 < inverse (real n) \<and> inverse (real n) < e)"
  by(subst(asm) real_arch_inv)
subsection {* Sundries *}

lemma conjunctD2: assumes "a \<and> b" shows a b using assms by auto
lemma conjunctD3: assumes "a \<and> b \<and> c" shows a b c using assms by auto
lemma conjunctD4: assumes "a \<and> b \<and> c \<and> d" shows a b c d using assms by auto
lemma conjunctD5: assumes "a \<and> b \<and> c \<and> d \<and> e" shows a b c d e using assms by auto

declare norm_triangle_ineq4[intro] 

lemma simple_image: "{f x |x . x \<in> s} = f ` s" by blast

lemma linear_simps:  assumes "bounded_linear f"
  shows "f (a + b) = f a + f b" "f (a - b) = f a - f b" "f 0 = 0" "f (- a) = - f a" "f (s *\<^sub>R v) = s *\<^sub>R (f v)"
  apply(rule_tac[!] additive.add additive.minus additive.diff additive.zero bounded_linear.scaleR)
  using assms unfolding bounded_linear_def additive_def by auto

lemma bounded_linearI:assumes "\<And>x y. f (x + y) = f x + f y"
  "\<And>r x. f (r *\<^sub>R x) = r *\<^sub>R f x" "\<And>x. norm (f x) \<le> norm x * K"
  shows "bounded_linear f"
  unfolding bounded_linear_def additive_def bounded_linear_axioms_def using assms by auto
 
lemma real_le_inf_subset:
  assumes "t \<noteq> {}" "t \<subseteq> s" "\<exists>b. b <=* s" shows "Inf s <= Inf (t::real set)"
  apply(rule isGlb_le_isLb) apply(rule Inf[OF assms(1)])
  using assms apply-apply(erule exE) apply(rule_tac x=b in exI)
  unfolding isLb_def setge_def by auto

lemma real_ge_sup_subset:
  assumes "t \<noteq> {}" "t \<subseteq> s" "\<exists>b. s *<= b" shows "Sup s >= Sup (t::real set)"
  apply(rule isLub_le_isUb) apply(rule Sup[OF assms(1)])
  using assms apply-apply(erule exE) apply(rule_tac x=b in exI)
  unfolding isUb_def setle_def by auto

lemma bounded_linear_component[intro]: "bounded_linear (\<lambda>x::'a::euclidean_space. x $$ k)"
  apply(rule bounded_linearI[where K=1]) 
  using component_le_norm[of _ k] unfolding real_norm_def by auto

lemma transitive_stepwise_lt_eq:
  assumes "(\<And>x y z::nat. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z)"
  shows "((\<forall>m. \<forall>n>m. R m n) \<longleftrightarrow> (\<forall>n. R n (Suc n)))" (is "?l = ?r")
proof(safe) assume ?r fix n m::nat assume "m < n" thus "R m n" apply-
  proof(induct n arbitrary: m) case (Suc n) show ?case 
    proof(cases "m < n") case True
      show ?thesis apply(rule assms[OF Suc(1)[OF True]]) using `?r` by auto
    next case False hence "m = n" using Suc(2) by auto
      thus ?thesis using `?r` by auto
    qed qed auto qed auto

lemma transitive_stepwise_gt:
  assumes "\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z" "\<And>n. R n (Suc n) "
  shows "\<forall>n>m. R m n"
proof- have "\<forall>m. \<forall>n>m. R m n" apply(subst transitive_stepwise_lt_eq)
    apply(rule assms) apply(assumption,assumption) using assms(2) by auto
  thus ?thesis by auto qed

lemma transitive_stepwise_le_eq:
  assumes "\<And>x. R x x" "\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  shows "(\<forall>m. \<forall>n\<ge>m. R m n) \<longleftrightarrow> (\<forall>n. R n (Suc n))" (is "?l = ?r")
proof safe assume ?r fix m n::nat assume "m\<le>n" thus "R m n" apply-
  proof(induct n arbitrary: m) case (Suc n) show ?case 
    proof(cases "m \<le> n") case True show ?thesis apply(rule assms(2))
        apply(rule Suc(1)[OF True]) using `?r` by auto
    next case False hence "m = Suc n" using Suc(2) by auto
      thus ?thesis using assms(1) by auto
    qed qed(insert assms(1), auto) qed auto

lemma transitive_stepwise_le:
  assumes "\<And>x. R x x" "\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z" "\<And>n. R n (Suc n) "
  shows "\<forall>n\<ge>m. R m n"
proof- have "\<forall>m. \<forall>n\<ge>m. R m n" apply(subst transitive_stepwise_le_eq)
    apply(rule assms) apply(rule assms,assumption,assumption) using assms(3) by auto
  thus ?thesis by auto qed

subsection {* Some useful lemmas about intervals. *}

abbreviation One  where "One \<equiv> ((\<chi>\<chi> i. 1)::_::ordered_euclidean_space)"

lemma empty_as_interval: "{} = {One..0}"
  apply(rule set_eqI,rule) defer unfolding mem_interval
  using UNIV_witness[where 'a='n] apply(erule_tac exE,rule_tac x=x in allE) by auto

lemma interior_subset_union_intervals: 
  assumes "i = {a..b::'a::ordered_euclidean_space}" "j = {c..d}" "interior j \<noteq> {}" "i \<subseteq> j \<union> s" "interior(i) \<inter> interior(j) = {}"
  shows "interior i \<subseteq> interior s" proof-
  have "{a<..<b} \<inter> {c..d} = {}" using inter_interval_mixed_eq_empty[of c d a b] and assms(3,5)
    unfolding assms(1,2) interior_closed_interval by auto
  moreover have "{a<..<b} \<subseteq> {c..d} \<union> s" apply(rule order_trans,rule interval_open_subset_closed)
    using assms(4) unfolding assms(1,2) by auto
  ultimately show ?thesis apply-apply(rule interior_maximal) defer apply(rule open_interior)
    unfolding assms(1,2) interior_closed_interval by auto qed

lemma inter_interior_unions_intervals: fixes f::"('a::ordered_euclidean_space) set set"
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
      hence "0 < d" "ball x (min d e) \<subseteq> UNIV - i" unfolding ab ball_min_Int by auto
      hence "ball x (min d e) \<subseteq> s \<inter> interior (\<Union>f)" using e unfolding lem1 unfolding  ball_min_Int by auto
      hence "x \<in> s \<inter> interior (\<Union>f)" using `d>0` e by auto
      hence "\<exists>t\<in>f. \<exists>x e. 0 < e \<and> ball x e \<subseteq> s \<inter> t" apply-apply(rule insert(3)) using insert(4) by auto thus ?thesis by auto next
    case True show ?thesis proof(cases "x\<in>{a<..<b}")
      case True then guess d unfolding open_contains_ball_eq[OF open_interval,rule_format] ..
      thus ?thesis apply(rule_tac x=i in bexI,rule_tac x=x in exI,rule_tac x="min d e" in exI)
        unfolding ab using interval_open_subset_closed[of a b] and e by fastforce+ next
    case False then obtain k where "x$$k \<le> a$$k \<or> x$$k \<ge> b$$k" and k:"k<DIM('a)" unfolding mem_interval by(auto simp add:not_less) 
    hence "x$$k = a$$k \<or> x$$k = b$$k" using True unfolding ab and mem_interval apply(erule_tac x=k in allE) by auto
    hence "\<exists>x. ball x (e/2) \<subseteq> s \<inter> (\<Union>f)" proof(erule_tac disjE)
      let ?z = "x - (e/2) *\<^sub>R basis k" assume as:"x$$k = a$$k" have "ball ?z (e / 2) \<inter> i = {}" apply(rule ccontr) unfolding ex_in_conv[THEN sym] proof(erule exE)
        fix y assume "y \<in> ball ?z (e / 2) \<inter> i" hence "dist ?z y < e/2" and yi:"y\<in>i" by auto
        hence "\<bar>(?z - y) $$ k\<bar> < e/2" using component_le_norm[of "?z - y" k] unfolding dist_norm by auto
        hence "y$$k < a$$k" using e[THEN conjunct1] k by(auto simp add:field_simps as)
        hence "y \<notin> i" unfolding ab mem_interval not_all apply(rule_tac x=k in exI) using k by auto thus False using yi by auto qed
      moreover have "ball ?z (e/2) \<subseteq> s \<inter> (\<Union>insert i f)" apply(rule order_trans[OF _ e[THEN conjunct2, unfolded lem1]]) proof
        fix y assume as:"y\<in> ball ?z (e/2)" have "norm (x - y) \<le> \<bar>e\<bar> / 2 + norm (x - y - (e / 2) *\<^sub>R basis k)"
           apply-apply(rule order_trans,rule norm_triangle_sub[of "x - y" "(e/2) *\<^sub>R basis k"])
          unfolding norm_scaleR norm_basis by auto
        also have "\<dots> < \<bar>e\<bar> / 2 + \<bar>e\<bar> / 2" apply(rule add_strict_left_mono) using as unfolding mem_ball dist_norm using e by(auto simp add:field_simps)
        finally show "y\<in>ball x e" unfolding mem_ball dist_norm using e by(auto simp add:field_simps) qed
      ultimately show ?thesis apply(rule_tac x="?z" in exI) unfolding Union_insert by auto
    next let ?z = "x + (e/2) *\<^sub>R basis k" assume as:"x$$k = b$$k" have "ball ?z (e / 2) \<inter> i = {}" apply(rule ccontr) unfolding ex_in_conv[THEN sym] proof(erule exE)
        fix y assume "y \<in> ball ?z (e / 2) \<inter> i" hence "dist ?z y < e/2" and yi:"y\<in>i" by auto
        hence "\<bar>(?z - y) $$ k\<bar> < e/2" using component_le_norm[of "?z - y" k] unfolding dist_norm by auto
        hence "y$$k > b$$k" using e[THEN conjunct1] k by(auto simp add:field_simps as)
        hence "y \<notin> i" unfolding ab mem_interval not_all using k by(rule_tac x=k in exI,auto) thus False using yi by auto qed
      moreover have "ball ?z (e/2) \<subseteq> s \<inter> (\<Union>insert i f)" apply(rule order_trans[OF _ e[THEN conjunct2, unfolded lem1]]) proof
        fix y assume as:"y\<in> ball ?z (e/2)" have "norm (x - y) \<le> \<bar>e\<bar> / 2 + norm (x - y + (e / 2) *\<^sub>R basis k)"
           apply-apply(rule order_trans,rule norm_triangle_sub[of "x - y" "- (e/2) *\<^sub>R basis k"])
          unfolding norm_scaleR by auto
        also have "\<dots> < \<bar>e\<bar> / 2 + \<bar>e\<bar> / 2" apply(rule add_strict_left_mono) using as unfolding mem_ball dist_norm using e by(auto simp add:field_simps)
        finally show "y\<in>ball x e" unfolding mem_ball dist_norm using e by(auto simp add:field_simps) qed
      ultimately show ?thesis apply(rule_tac x="?z" in exI) unfolding Union_insert by auto qed 
    then guess x .. hence "x \<in> s \<inter> interior (\<Union>f)" unfolding lem1[where U="\<Union>f",THEN sym] using centre_in_ball e[THEN conjunct1] by auto
    thus ?thesis apply-apply(rule lem2,rule insert(3)) using insert(4) by auto qed qed qed qed note * = this
  guess t using *[OF assms(1,3) goal1]  .. from this(2) guess x .. then guess e ..
  hence "x \<in> s" "x\<in>interior t" defer using open_subset_interior[OF open_ball, of x e t] by auto
  thus False using `t\<in>f` assms(4) by auto qed

subsection {* Bounds on intervals where they exist. *}

definition "interval_upperbound (s::('a::ordered_euclidean_space) set) = ((\<chi>\<chi> i. Sup {a. \<exists>x\<in>s. x$$i = a})::'a)"

definition "interval_lowerbound (s::('a::ordered_euclidean_space) set) = ((\<chi>\<chi> i. Inf {a. \<exists>x\<in>s. x$$i = a})::'a)"

lemma interval_upperbound[simp]: assumes "\<forall>i<DIM('a::ordered_euclidean_space). a$$i \<le> (b::'a)$$i" shows "interval_upperbound {a..b} = b"
  using assms unfolding interval_upperbound_def apply(subst euclidean_eq[where 'a='a]) apply safe
  unfolding euclidean_lambda_beta' apply(erule_tac x=i in allE)
  apply(rule Sup_unique) unfolding setle_def apply rule unfolding mem_Collect_eq apply(erule bexE) unfolding mem_interval defer
  apply(rule,rule) apply(rule_tac x="b$$i" in bexI) defer unfolding mem_Collect_eq apply(rule_tac x=b in bexI)
  unfolding mem_interval using assms by auto

lemma interval_lowerbound[simp]: assumes "\<forall>i<DIM('a::ordered_euclidean_space). a$$i \<le> (b::'a)$$i" shows "interval_lowerbound {a..b} = a"
  using assms unfolding interval_lowerbound_def apply(subst euclidean_eq[where 'a='a]) apply safe
  unfolding euclidean_lambda_beta' apply(erule_tac x=i in allE)
  apply(rule Inf_unique) unfolding setge_def apply rule unfolding mem_Collect_eq apply(erule bexE) unfolding mem_interval defer
  apply(rule,rule) apply(rule_tac x="a$$i" in bexI) defer unfolding mem_Collect_eq apply(rule_tac x=a in bexI)
  unfolding mem_interval using assms by auto 

lemmas interval_bounds = interval_upperbound interval_lowerbound

lemma interval_bounds'[simp]: assumes "{a..b}\<noteq>{}" shows "interval_upperbound {a..b} = b" "interval_lowerbound {a..b} = a"
  using assms unfolding interval_ne_empty by auto

subsection {* Content (length, area, volume...) of an interval. *}

definition "content (s::('a::ordered_euclidean_space) set) =
       (if s = {} then 0 else (\<Prod>i<DIM('a). (interval_upperbound s)$$i - (interval_lowerbound s)$$i))"

lemma interval_not_empty:"\<forall>i<DIM('a). a$$i \<le> b$$i \<Longrightarrow> {a..b::'a::ordered_euclidean_space} \<noteq> {}"
  unfolding interval_eq_empty unfolding not_ex not_less by auto

lemma content_closed_interval: fixes a::"'a::ordered_euclidean_space" assumes "\<forall>i<DIM('a). a$$i \<le> b$$i"
  shows "content {a..b} = (\<Prod>i<DIM('a). b$$i - a$$i)"
  using interval_not_empty[OF assms] unfolding content_def interval_upperbound[OF assms] interval_lowerbound[OF assms] by auto

lemma content_closed_interval': fixes a::"'a::ordered_euclidean_space" assumes "{a..b}\<noteq>{}" shows "content {a..b} = (\<Prod>i<DIM('a). b$$i - a$$i)"
  apply(rule content_closed_interval) using assms unfolding interval_ne_empty .

lemma content_real:assumes "a\<le>b" shows "content {a..b} = b-a"
proof- have *:"{..<Suc 0} = {0}" by auto
  show ?thesis unfolding content_def using assms by(auto simp: *)
qed

lemma content_unit[intro]: "content{0..One::'a::ordered_euclidean_space} = 1" proof-
  have *:"\<forall>i<DIM('a). (0::'a)$$i \<le> (One::'a)$$i" by auto
  have "0 \<in> {0..One::'a}" unfolding mem_interval by auto
  thus ?thesis unfolding content_def interval_bounds[OF *] using setprod_1 by auto qed

lemma content_pos_le[intro]: fixes a::"'a::ordered_euclidean_space" shows "0 \<le> content {a..b}" proof(cases "{a..b}={}")
  case False hence *:"\<forall>i<DIM('a). a $$ i \<le> b $$ i" unfolding interval_ne_empty by assumption
  have "(\<Prod>i<DIM('a). interval_upperbound {a..b} $$ i - interval_lowerbound {a..b} $$ i) \<ge> 0"
    apply(rule setprod_nonneg) unfolding interval_bounds[OF *] using * apply(erule_tac x=x in allE) by auto
  thus ?thesis unfolding content_def by(auto simp del:interval_bounds') qed(unfold content_def, auto)

lemma content_pos_lt: fixes a::"'a::ordered_euclidean_space" assumes "\<forall>i<DIM('a). a$$i < b$$i" shows "0 < content {a..b}"
proof- have help_lemma1: "\<forall>i<DIM('a). a$$i < b$$i \<Longrightarrow> \<forall>i<DIM('a). a$$i \<le> ((b$$i)::real)" apply(rule,erule_tac x=i in allE) by auto
  show ?thesis unfolding content_closed_interval[OF help_lemma1[OF assms]] apply(rule setprod_pos)
    using assms apply(erule_tac x=x in allE) by auto qed

lemma content_eq_0: "content{a..b::'a::ordered_euclidean_space} = 0 \<longleftrightarrow> (\<exists>i<DIM('a). b$$i \<le> a$$i)" proof(cases "{a..b} = {}")
  case True thus ?thesis unfolding content_def if_P[OF True] unfolding interval_eq_empty apply-
    apply(rule,erule exE) apply(rule_tac x=i in exI) by auto next
  case False note this[unfolded interval_eq_empty not_ex not_less]
  hence as:"\<forall>i<DIM('a). b $$ i \<ge> a $$ i" by fastforce
  show ?thesis unfolding content_def if_not_P[OF False] setprod_zero_iff[OF finite_lessThan]
    apply(rule) apply(erule_tac[!] exE bexE) unfolding interval_bounds[OF as] apply(rule_tac x=x in exI) defer
    apply(rule_tac x=i in bexI) using as apply(erule_tac x=i in allE) by auto qed

lemma cond_cases:"(P \<Longrightarrow> Q x) \<Longrightarrow> (\<not> P \<Longrightarrow> Q y) \<Longrightarrow> Q (if P then x else y)" by auto

lemma content_closed_interval_cases:
  "content {a..b::'a::ordered_euclidean_space} = (if \<forall>i<DIM('a). a$$i \<le> b$$i then setprod (\<lambda>i. b$$i - a$$i) {..<DIM('a)} else 0)" apply(rule cond_cases) 
  apply(rule content_closed_interval) unfolding content_eq_0 not_all not_le defer apply(erule exE,rule_tac x=x in exI) by auto

lemma content_eq_0_interior: "content {a..b} = 0 \<longleftrightarrow> interior({a..b}) = {}"
  unfolding content_eq_0 interior_closed_interval interval_eq_empty by auto

(*lemma content_eq_0_1: "content {a..b::real^1} = 0 \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a"
  unfolding content_eq_0 by auto*)

lemma content_pos_lt_eq: "0 < content {a..b::'a::ordered_euclidean_space} \<longleftrightarrow> (\<forall>i<DIM('a). a$$i < b$$i)"
  apply(rule) defer apply(rule content_pos_lt,assumption) proof- assume "0 < content {a..b}"
  hence "content {a..b} \<noteq> 0" by auto thus "\<forall>i<DIM('a). a$$i < b$$i" unfolding content_eq_0 not_ex not_le by fastforce qed

lemma content_empty[simp]: "content {} = 0" unfolding content_def by auto

lemma content_subset: assumes "{a..b} \<subseteq> {c..d}" shows "content {a..b::'a::ordered_euclidean_space} \<le> content {c..d}" proof(cases "{a..b}={}")
  case True thus ?thesis using content_pos_le[of c d] by auto next
  case False hence ab_ne:"\<forall>i<DIM('a). a $$ i \<le> b $$ i" unfolding interval_ne_empty by auto
  hence ab_ab:"a\<in>{a..b}" "b\<in>{a..b}" unfolding mem_interval by auto
  have "{c..d} \<noteq> {}" using assms False by auto
  hence cd_ne:"\<forall>i<DIM('a). c $$ i \<le> d $$ i" using assms unfolding interval_ne_empty by auto
  show ?thesis unfolding content_def unfolding interval_bounds[OF ab_ne] interval_bounds[OF cd_ne]
    unfolding if_not_P[OF False] if_not_P[OF `{c..d} \<noteq> {}`] apply(rule setprod_mono,rule) proof
    fix i assume i:"i\<in>{..<DIM('a)}"
    show "0 \<le> b $$ i - a $$ i" using ab_ne[THEN spec[where x=i]] i by auto
    show "b $$ i - a $$ i \<le> d $$ i - c $$ i"
      using assms[unfolded subset_eq mem_interval,rule_format,OF ab_ab(2),of i]
      using assms[unfolded subset_eq mem_interval,rule_format,OF ab_ab(1),of i] using i by auto qed qed

lemma content_lt_nz: "0 < content {a..b} \<longleftrightarrow> content {a..b} \<noteq> 0"
  unfolding content_pos_lt_eq content_eq_0 unfolding not_ex not_le by fastforce

subsection {* The notion of a gauge --- simply an open set containing the point. *}

definition gauge where "gauge d \<longleftrightarrow> (\<forall>x. x\<in>(d x) \<and> open(d x))"

lemma gaugeI:assumes "\<And>x. x\<in>g x" "\<And>x. open (g x)" shows "gauge g"
  using assms unfolding gauge_def by auto

lemma gaugeD[dest]: assumes "gauge d" shows "x\<in>d x" "open (d x)" using assms unfolding gauge_def by auto

lemma gauge_ball_dependent: "\<forall>x. 0 < e x \<Longrightarrow> gauge (\<lambda>x. ball x (e x))"
  unfolding gauge_def by auto 

lemma gauge_ball[intro]: "0 < e \<Longrightarrow> gauge (\<lambda>x. ball x e)" unfolding gauge_def by auto 

lemma gauge_trivial[intro]: "gauge (\<lambda>x. ball x 1)" apply(rule gauge_ball) by auto

lemma gauge_inter[intro]: "gauge d1 \<Longrightarrow> gauge d2 \<Longrightarrow> gauge (\<lambda>x. (d1 x) \<inter> (d2 x))"
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

lemma division_of_sing[simp]: "s division_of {a..a::'a::ordered_euclidean_space} \<longleftrightarrow> s = {{a..a}}" (is "?l = ?r") proof
  assume ?r moreover { assume "s = {{a}}" moreover fix k assume "k\<in>s" 
    ultimately have"\<exists>x y. k = {x..y}" apply(rule_tac x=a in exI)+ unfolding interval_sing by auto }
  ultimately show ?l unfolding division_of_def interval_sing by auto next
  assume ?l note as=conjunctD4[OF this[unfolded division_of_def interval_sing]]
  { fix x assume x:"x\<in>s" have "x={a}" using as(2)[rule_format,OF x] by auto }
  moreover have "s \<noteq> {}" using as(4) by auto ultimately show ?r unfolding interval_sing by auto qed

lemma elementary_empty: obtains p where "p division_of {}"
  unfolding division_of_trivial by auto

lemma elementary_interval: obtains p where  "p division_of {a..b}"
  by(metis division_of_trivial division_of_self)

lemma division_contains: "s division_of i \<Longrightarrow> \<forall>x\<in>i. \<exists>k\<in>s. x \<in> k"
  unfolding division_of_def by auto

lemma forall_in_division:
 "d division_of i \<Longrightarrow> ((\<forall>x\<in>d. P x) \<longleftrightarrow> (\<forall>a b. {a..b} \<in> d \<longrightarrow> P {a..b}))"
  unfolding division_of_def by fastforce

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

lemma division_inter: assumes "p1 division_of s1" "p2 division_of (s2::('a::ordered_euclidean_space) set)"
  shows "{k1 \<inter> k2 | k1 k2 .k1 \<in> p1 \<and> k2 \<in> p2 \<and> k1 \<inter> k2 \<noteq> {}} division_of (s1 \<inter> s2)" (is "?A' division_of _") proof-
let ?A = "{s. s \<in>  (\<lambda>(k1,k2). k1 \<inter> k2) ` (p1 \<times> p2) \<and> s \<noteq> {}}" have *:"?A' = ?A" by auto
show ?thesis unfolding * proof(rule division_ofI) have "?A \<subseteq> (\<lambda>(x, y). x \<inter> y) ` (p1 \<times> p2)" by auto
  moreover have "finite (p1 \<times> p2)" using assms unfolding division_of_def by auto ultimately show "finite ?A" by auto
  have *:"\<And>s. \<Union>{x\<in>s. x \<noteq> {}} = \<Union>s" by auto show "\<Union>?A = s1 \<inter> s2" apply(rule set_eqI) unfolding * and Union_image_eq UN_iff
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
  show "interior k1 \<inter> interior k2 = {}" unfolding k1 k2 apply(rule *) defer apply(rule_tac[1-4] interior_mono)
    using division_ofD(5)[OF assms(1) k1(2) k2(2)]
    using division_ofD(5)[OF assms(2) k1(3) k2(3)] using th by auto qed qed

lemma division_inter_1: assumes "d division_of i" "{a..b::'a::ordered_euclidean_space} \<subseteq> i"
  shows "{ {a..b} \<inter> k |k. k \<in> d \<and> {a..b} \<inter> k \<noteq> {} } division_of {a..b}" proof(cases "{a..b} = {}")
  case True show ?thesis unfolding True and division_of_trivial by auto next
  have *:"{a..b} \<inter> i = {a..b}" using assms(2) by auto 
  case False show ?thesis using division_inter[OF division_of_self[OF False] assms(1)] unfolding * by auto qed

lemma elementary_inter: assumes "p1 division_of s" "p2 division_of (t::('a::ordered_euclidean_space) set)"
  shows "\<exists>p. p division_of (s \<inter> t)"
  by(rule,rule division_inter[OF assms])

lemma elementary_inters: assumes "finite f" "f\<noteq>{}" "\<forall>s\<in>f. \<exists>p. p division_of (s::('a::ordered_euclidean_space) set)"
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
  { assume as:"k1\<in>p1" "k2\<in>p2" have ?g using interior_mono[OF d1(2)[OF as(1)]] interior_mono[OF d2(2)[OF as(2)]]
      using assms(3) by blast } moreover
  { assume as:"k1\<in>p2" "k2\<in>p1" have ?g using interior_mono[OF d1(2)[OF as(2)]] interior_mono[OF d2(2)[OF as(1)]]
      using assms(3) by blast} ultimately
  show ?g using d1(5)[OF _ _ as(3)] and d2(5)[OF _ _ as(3)] by auto }
  fix k assume k:"k \<in> p1 \<union> p2"  show "k \<subseteq> s1 \<union> s2" using k d1(2) d2(2) by auto
  show "k \<noteq> {}" using k d1(3) d2(3) by auto show "\<exists>a b. k = {a..b}" using k d1(4) d2(4) by auto qed

lemma partial_division_extend_1:
  assumes "{c..d} \<subseteq> {a..b::'a::ordered_euclidean_space}" "{c..d} \<noteq> {}"
  obtains p where "p division_of {a..b}" "{c..d} \<in> p"
proof- def n \<equiv> "DIM('a)" have n:"1 \<le> n" "0 < n" "n \<noteq> 0" unfolding n_def using DIM_positive[where 'a='a] by auto
  guess \<pi> using ex_bij_betw_nat_finite_1[OF finite_lessThan[of "DIM('a)"]] .. note \<pi>=this
  def \<pi>' \<equiv> "inv_into {1..n} \<pi>"
  have \<pi>':"bij_betw \<pi>' {..<DIM('a)} {1..n}" using bij_betw_inv_into[OF \<pi>] unfolding \<pi>'_def n_def by auto
  hence \<pi>'i:"\<And>i. i<DIM('a) \<Longrightarrow> \<pi>' i \<in> {1..n}" unfolding bij_betw_def by auto 
  have \<pi>i:"\<And>i. i\<in>{1..n} \<Longrightarrow> \<pi> i <DIM('a)" using \<pi> unfolding bij_betw_def n_def by auto 
  have \<pi>\<pi>'[simp]:"\<And>i. i<DIM('a) \<Longrightarrow> \<pi> (\<pi>' i) = i" unfolding \<pi>'_def
    apply(rule f_inv_into_f) unfolding n_def using \<pi> unfolding bij_betw_def by auto
  have \<pi>'\<pi>[simp]:"\<And>i. i\<in>{1..n} \<Longrightarrow> \<pi>' (\<pi> i) = i" unfolding \<pi>'_def apply(rule inv_into_f_eq)
    using \<pi> unfolding n_def bij_betw_def by auto
  have "{c..d} \<noteq> {}" using assms by auto
  let ?p1 = "\<lambda>l. {(\<chi>\<chi> i. if \<pi>' i < l then c$$i else a$$i)::'a .. (\<chi>\<chi> i. if \<pi>' i < l then d$$i else if \<pi>' i = l then c$$\<pi> l else b$$i)}"
  let ?p2 = "\<lambda>l. {(\<chi>\<chi> i. if \<pi>' i < l then c$$i else if \<pi>' i = l then d$$\<pi> l else a$$i)::'a .. (\<chi>\<chi> i. if \<pi>' i < l then d$$i else b$$i)}"
  let ?p =  "{?p1 l |l. l \<in> {1..n+1}} \<union> {?p2 l |l. l \<in> {1..n+1}}"
  have abcd:"\<And>i. i<DIM('a) \<Longrightarrow> a $$ i \<le> c $$ i \<and> c$$i \<le> d$$i \<and> d $$ i \<le> b $$ i" using assms
    unfolding subset_interval interval_eq_empty by auto
  show ?thesis apply(rule that[of ?p]) apply(rule division_ofI)
  proof- have "\<And>i. i<DIM('a) \<Longrightarrow> \<pi>' i < Suc n"
    proof(rule ccontr,unfold not_less) fix i assume i:"i<DIM('a)" and "Suc n \<le> \<pi>' i"
      hence "\<pi>' i \<notin> {1..n}" by auto thus False using \<pi>' i unfolding bij_betw_def by auto
    qed hence "c = (\<chi>\<chi> i. if \<pi>' i < Suc n then c $$ i else a $$ i)"
        "d = (\<chi>\<chi> i. if \<pi>' i < Suc n then d $$ i else if \<pi>' i = n + 1 then c $$ \<pi> (n + 1) else b $$ i)"
      unfolding euclidean_eq[where 'a='a] using \<pi>' unfolding bij_betw_def by auto
    thus cdp:"{c..d} \<in> ?p" apply-apply(rule UnI1) unfolding mem_Collect_eq apply(rule_tac x="n + 1" in exI) by auto
    have "\<And>l. l\<in>{1..n+1} \<Longrightarrow> ?p1 l \<subseteq> {a..b}"  "\<And>l. l\<in>{1..n+1} \<Longrightarrow> ?p2 l \<subseteq> {a..b}"
      unfolding subset_eq apply(rule_tac[!] ballI,rule_tac[!] ccontr)
    proof- fix l assume l:"l\<in>{1..n+1}" fix x assume "x\<notin>{a..b}"
      then guess i unfolding mem_interval not_all not_imp .. note i=conjunctD2[OF this]
      show "x \<in> ?p1 l \<Longrightarrow> False" "x \<in> ?p2 l \<Longrightarrow> False" unfolding mem_interval apply(erule_tac[!] x=i in allE)
        apply(case_tac[!] "\<pi>' i < l", case_tac[!] "\<pi>' i = l") using abcd[of i] i by auto 
    qed moreover have "\<And>x. x \<in> {a..b} \<Longrightarrow> x \<in> \<Union>?p"
    proof- fix x assume x:"x\<in>{a..b}"
      { presume "x\<notin>{c..d} \<Longrightarrow> x \<in> \<Union>?p" thus "x \<in> \<Union>?p" using cdp by blast }
      let ?M = "{i. i\<in>{1..n+1} \<and> \<not> (c $$ \<pi> i \<le> x $$ \<pi> i \<and> x $$ \<pi> i \<le> d $$ \<pi> i)}"
      assume "x\<notin>{c..d}" then guess i0 unfolding mem_interval not_all not_imp ..
      hence "\<pi>' i0 \<in> ?M" using \<pi>' unfolding bij_betw_def by(auto intro!:le_SucI)
      hence M:"finite ?M" "?M \<noteq> {}" by auto
      def l \<equiv> "Min ?M" note l = Min_less_iff[OF M,unfolded l_def[symmetric]] Min_in[OF M,unfolded mem_Collect_eq l_def[symmetric]]
        Min_gr_iff[OF M,unfolded l_def[symmetric]]
      have "x\<in>?p1 l \<or> x\<in>?p2 l" using l(2)[THEN conjunct2] unfolding de_Morgan_conj not_le
        apply- apply(erule disjE) apply(rule disjI1) defer apply(rule disjI2)
      proof- assume as:"x $$ \<pi> l < c $$ \<pi> l"
        show "x \<in> ?p1 l" unfolding mem_interval apply safe unfolding euclidean_lambda_beta'
        proof- case goal1 have "\<pi>' i \<in> {1..n}" using \<pi>' unfolding bij_betw_def not_le using goal1 by auto
          thus ?case using as x[unfolded mem_interval,rule_format,of i]
            apply auto using l(3)[of "\<pi>' i"] using goal1 by(auto elim!:ballE[where x="\<pi>' i"])
        next case goal2 have "\<pi>' i \<in> {1..n}" using \<pi>' unfolding bij_betw_def not_le using goal2 by auto
          thus ?case using as x[unfolded mem_interval,rule_format,of i]
            apply auto using l(3)[of "\<pi>' i"] using goal2 by(auto elim!:ballE[where x="\<pi>' i"])
        qed
      next assume as:"x $$ \<pi> l > d $$ \<pi> l"
        show "x \<in> ?p2 l" unfolding mem_interval apply safe unfolding euclidean_lambda_beta'
        proof- fix i assume i:"i<DIM('a)"
          have "\<pi>' i \<in> {1..n}" using \<pi>' unfolding bij_betw_def not_le using i by auto
          thus "(if \<pi>' i < l then c $$ i else if \<pi>' i = l then d $$ \<pi> l else a $$ i) \<le> x $$ i"
            "x $$ i \<le> (if \<pi>' i < l then d $$ i else b $$ i)"
            using as x[unfolded mem_interval,rule_format,of i]
            apply auto using l(3)[of "\<pi>' i"] i by(auto elim!:ballE[where x="\<pi>' i"])
        qed qed
      thus "x \<in> \<Union>?p" using l(2) by blast 
    qed ultimately show "\<Union>?p = {a..b}" apply-apply(rule) defer apply(rule) by(assumption,blast)
    
    show "finite ?p" by auto
    fix k assume k:"k\<in>?p" then obtain l where l:"k = ?p1 l \<or> k = ?p2 l" "l \<in> {1..n + 1}" by auto
    show "k\<subseteq>{a..b}" apply(rule,unfold mem_interval,rule,rule) 
    proof fix i x assume i:"i<DIM('a)" assume "x \<in> k" moreover have "\<pi>' i < l \<or> \<pi>' i = l \<or> \<pi>' i > l" by auto
      ultimately show "a$$i \<le> x$$i" "x$$i \<le> b$$i" using abcd[of i] using l using i
        by(auto elim!:allE[where x=i] simp add:eucl_le[where 'a='a]) (* FIXME: SLOW *)
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
        case True hence "\<And>i. i<DIM('a) \<Longrightarrow> \<pi>' i < l'" using \<pi>'i using l' by(auto simp add:less_Suc_eq_le)
        hence *:"\<And> P Q. (\<chi>\<chi> i. if \<pi>' i < l' then P i else Q i) = ((\<chi>\<chi> i. P i)::'a)" apply-apply(subst euclidean_eq) by auto
        hence k':"k' = {c..d}" using l'(1) unfolding * by auto
        have ln:"l < n + 1" 
        proof(rule ccontr) case goal1 hence l2:"l = n+1" using l by auto
          hence "\<And>i. i<DIM('a) \<Longrightarrow> \<pi>' i < l" using \<pi>'i by(auto simp add:less_Suc_eq_le)
          hence *:"\<And> P Q. (\<chi>\<chi> i. if \<pi>' i < l then P i else Q i) = ((\<chi>\<chi> i. P i)::'a)" apply-apply(subst euclidean_eq) by auto
          hence "k = {c..d}" using l(1) \<pi>'i unfolding * by(auto)
          thus False using `k\<noteq>k'` k' by auto
        qed have **:"\<pi>' (\<pi> l) = l" using \<pi>'\<pi>[of l] using l ln by auto
        have "x $$ \<pi> l < c $$ \<pi> l \<or> d $$ \<pi> l < x $$ \<pi> l" using l(1) apply-
        proof(erule disjE)
          assume as:"k = ?p1 l" note * = conjunct1[OF x[unfolded as Int_iff interior_closed_interval mem_interval],rule_format]
          show ?thesis using *[of "\<pi> l"] using ln l(2) using \<pi>i[of l] by(auto simp add:** not_less)
        next assume as:"k = ?p2 l" note * = conjunct1[OF x[unfolded as Int_iff interior_closed_interval mem_interval],rule_format]
          show ?thesis using *[of "\<pi> l"] using ln l(2) using \<pi>i[of l] unfolding ** by auto
        qed thus False using x unfolding k' unfolding Int_iff interior_closed_interval mem_interval
          by(auto elim!:allE[where x="\<pi> l"])
      next case False hence "l < n + 1" using l'(2) using `l\<le>l'` by auto
        hence ln:"l \<in> {1..n}" "l' \<in> {1..n}" using l l' False by auto
        note \<pi>l = \<pi>'\<pi>[OF ln(1)] \<pi>'\<pi>[OF ln(2)]
        assume x:"x \<in> interior k \<inter> interior k'"
        show False using l(1) l'(1) apply-
        proof(erule_tac[!] disjE)+
          assume as:"k = ?p1 l" "k' = ?p1 l'"
          note * = conjunctD2[OF x[unfolded as Int_iff interior_closed_interval mem_interval],rule_format]
          have "l \<noteq> l'" using k'(2)[unfolded as] by auto
          thus False using *[of "\<pi> l'"] *[of "\<pi> l"] ln using \<pi>i[OF ln(1)] \<pi>i[OF ln(2)] apply(cases "l<l'")
            by(auto simp add:euclidean_lambda_beta' \<pi>l \<pi>i n_def)
        next assume as:"k = ?p2 l" "k' = ?p2 l'"
          note * = conjunctD2[OF x[unfolded as Int_iff interior_closed_interval mem_interval],rule_format]
          have "l \<noteq> l'" apply(rule) using k'(2)[unfolded as] by auto
          thus False using *[of "\<pi> l"] *[of "\<pi> l'"]  `l \<le> l'` ln by(auto simp add:euclidean_lambda_beta' \<pi>l \<pi>i n_def)
        next assume as:"k = ?p1 l" "k' = ?p2 l'"
          note * = conjunctD2[OF x[unfolded as Int_iff interior_closed_interval mem_interval],rule_format]
          show False using abcd[of "\<pi> l'"] using *[of "\<pi> l"] *[of "\<pi> l'"]  `l \<le> l'` ln apply(cases "l=l'")
            by(auto simp add:euclidean_lambda_beta' \<pi>l \<pi>i n_def)
        next assume as:"k = ?p2 l" "k' = ?p1 l'"
          note * = conjunctD2[OF x[unfolded as Int_iff interior_closed_interval mem_interval],rule_format]
          show False using *[of "\<pi> l"] *[of "\<pi> l'"] ln `l \<le> l'` apply(cases "l=l'") using abcd[of "\<pi> l'"] 
            by(auto simp add:euclidean_lambda_beta' \<pi>l \<pi>i n_def)
        qed qed } 
    from this[OF k l k' l'] this[OF k'(1) l' k _ l] have "\<And>x. x \<notin> interior k \<inter> interior k'"
      apply - apply(cases "l' \<le> l") using k'(2) by auto            
    thus "interior k \<inter> interior k' = {}" by auto        
qed qed

lemma partial_division_extend_interval: assumes "p division_of (\<Union>p)" "(\<Union>p) \<subseteq> {a..b}"
  obtains q where "p \<subseteq> q" "q division_of {a..b::'a::ordered_euclidean_space}" proof(cases "p = {}")
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
          apply(rule interior_mono *)+ using k by auto qed qed qed auto qed

lemma elementary_bounded[dest]: "p division_of s \<Longrightarrow> bounded (s::('a::ordered_euclidean_space) set)"
  unfolding division_of_def by(metis bounded_Union bounded_interval) 

lemma elementary_subset_interval: "p division_of s \<Longrightarrow> \<exists>a b. s \<subseteq> {a..b::'a::ordered_euclidean_space}"
  by(meson elementary_bounded bounded_subset_closed_interval)

lemma division_union_intervals_exists: assumes "{a..b::'a::ordered_euclidean_space} \<noteq> {}"
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
  obtains q where "q division_of ({a..b::'a::ordered_euclidean_space} \<union> \<Union>p)" proof-
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
    using assm(2-4) as apply- by(fastforce dest: assm(5))+
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
  assumes "finite f" "\<And>s. s \<in> f \<Longrightarrow> \<exists>a b. s = {a..b::'a::ordered_euclidean_space}"
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

lemma elementary_union: assumes "ps division_of s" "pt division_of (t::('a::ordered_euclidean_space) set)"
  obtains p where "p division_of (s \<union> t)"
proof- have "s \<union> t = \<Union>ps \<union> \<Union>pt" using assms unfolding division_of_def by auto
  hence *:"\<Union>(ps \<union> pt) = s \<union> t" by auto
  show ?thesis apply-apply(rule elementary_unions_intervals[of "ps\<union>pt"])
    unfolding * prefer 3 apply(rule_tac p=p in that)
    using assms[unfolded division_of_def] by auto qed

lemma partial_division_extend: fixes t::"('a::ordered_euclidean_space) set"
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

lemma tagged_division_of_finite: "s tagged_division_of i \<Longrightarrow> finite s"
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
  thus  "k \<subseteq> i" "k \<noteq> {}" "\<exists>a b. k = {a..b}" using assm apply- by fastforce+
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

lemma setsum_over_tagged_division_lemma: fixes d::"('m::ordered_euclidean_space) set \<Rightarrow> 'a::real_normed_vector"
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
  have *:"\<And>a b. a\<subseteq> s1 \<Longrightarrow> b\<subseteq> s2 \<Longrightarrow> interior a \<inter> interior b = {}" using assms(3) interior_mono by blast
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
    using assms(3)[rule_format] interior_mono by blast
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
"((f::('n::ordered_euclidean_space \<Rightarrow> 'b::real_normed_vector)) has_integral y) i \<equiv>
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

lemma division_of_closed: "s division_of i \<Longrightarrow> closed (i::('n::ordered_euclidean_space) set)"
  unfolding division_of_def by fastforce

subsection {* General bisection principle for intervals; might be useful elsewhere. *}

lemma interval_bisection_step:  fixes type::"'a::ordered_euclidean_space"
  assumes "P {}" "(\<forall>s t. P s \<and> P t \<and> interior(s) \<inter> interior(t) = {} \<longrightarrow> P(s \<union> t))" "~(P {a..b::'a})"
  obtains c d where "~(P{c..d})"
  "\<forall>i<DIM('a). a$$i \<le> c$$i \<and> c$$i \<le> d$$i \<and> d$$i \<le> b$$i \<and> 2 * (d$$i - c$$i) \<le> b$$i - a$$i"
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
  let ?A = "{{c..d} | c d::'a. \<forall>i<DIM('a). (c$$i = a$$i) \<and> (d$$i = (a$$i + b$$i) / 2) \<or> (c$$i = (a$$i + b$$i) / 2) \<and> (d$$i = b$$i)}"
  let ?PP = "\<lambda>c d. \<forall>i<DIM('a). a$$i \<le> c$$i \<and> c$$i \<le> d$$i \<and> d$$i \<le> b$$i \<and> 2 * (d$$i - c$$i) \<le> b$$i - a$$i"
  { presume "\<forall>c d. ?PP c d \<longrightarrow> P {c..d} \<Longrightarrow> False"
    thus thesis unfolding atomize_not not_all apply-apply(erule exE)+ apply(rule_tac c=x and d=xa in that) by auto }
  assume as:"\<forall>c d. ?PP c d \<longrightarrow> P {c..d}"
  have "P (\<Union> ?A)" proof(rule *, rule_tac[2-] ballI, rule_tac[4] ballI, rule_tac[4] impI) 
    let ?B = "(\<lambda>s.{(\<chi>\<chi> i. if i \<in> s then a$$i else (a$$i + b$$i) / 2)::'a ..
      (\<chi>\<chi> i. if i \<in> s then (a$$i + b$$i) / 2 else b$$i)}) ` {s. s \<subseteq> {..<DIM('a)}}"
    have "?A \<subseteq> ?B" proof case goal1
      then guess c unfolding mem_Collect_eq .. then guess d apply- by(erule exE,(erule conjE)+) note c_d=this[rule_format]
      have *:"\<And>a b c d. a = c \<Longrightarrow> b = d \<Longrightarrow> {a..b} = {c..d}" by auto
      show "x\<in>?B" unfolding image_iff apply(rule_tac x="{i. i<DIM('a) \<and> c$$i = a$$i}" in bexI)
        unfolding c_d apply(rule * ) unfolding euclidean_eq[where 'a='a] apply safe unfolding euclidean_lambda_beta' mem_Collect_eq
      proof- fix i assume "i<DIM('a)" thus " c $$ i = (if i < DIM('a) \<and> c $$ i = a $$ i then a $$ i else (a $$ i + b $$ i) / 2)"
          "d $$ i = (if i < DIM('a) \<and> c $$ i = a $$ i then (a $$ i + b $$ i) / 2 else b $$ i)"
          using c_d(2)[of i] ab[THEN spec[where x=i]] by(auto simp add:field_simps)
      qed qed
    thus "finite ?A" apply(rule finite_subset) by auto
    fix s assume "s\<in>?A" then guess c unfolding mem_Collect_eq .. then guess d apply- by(erule exE,(erule conjE)+)
    note c_d=this[rule_format]
    show "P s" unfolding c_d apply(rule as[rule_format]) proof- case goal1 thus ?case 
        using c_d(2)[of i] using ab[THEN spec[where x=i]] by auto qed
    show "\<exists>a b. s = {a..b}" unfolding c_d by auto
    fix t assume "t\<in>?A" then guess e unfolding mem_Collect_eq .. then guess f apply- by(erule exE,(erule conjE)+)
    note e_f=this[rule_format]
    assume "s \<noteq> t" hence "\<not> (c = e \<and> d = f)" unfolding c_d e_f by auto
    then obtain i where "c$$i \<noteq> e$$i \<or> d$$i \<noteq> f$$i" and i':"i<DIM('a)" unfolding de_Morgan_conj euclidean_eq[where 'a='a] by auto
    hence i:"c$$i \<noteq> e$$i" "d$$i \<noteq> f$$i" apply- apply(erule_tac[!] disjE)
    proof- assume "c$$i \<noteq> e$$i" thus "d$$i \<noteq> f$$i" using c_d(2)[of i] e_f(2)[of i] by fastforce
    next   assume "d$$i \<noteq> f$$i" thus "c$$i \<noteq> e$$i" using c_d(2)[of i] e_f(2)[of i] by fastforce
    qed have *:"\<And>s t. (\<And>a. a\<in>s \<Longrightarrow> a\<in>t \<Longrightarrow> False) \<Longrightarrow> s \<inter> t = {}" by auto
    show "interior s \<inter> interior t = {}" unfolding e_f c_d interior_closed_interval proof(rule *)
      fix x assume "x\<in>{c<..<d}" "x\<in>{e<..<f}"
      hence x:"c$$i < d$$i" "e$$i < f$$i" "c$$i < f$$i" "e$$i < d$$i" unfolding mem_interval using i'
        apply-apply(erule_tac[!] x=i in allE)+ by auto
      show False using c_d(2)[OF i'] apply- apply(erule_tac disjE)
      proof(erule_tac[!] conjE) assume as:"c $$ i = a $$ i" "d $$ i = (a $$ i + b $$ i) / 2"
        show False using e_f(2)[of i] and i x unfolding as by(fastforce simp add:field_simps)
      next assume as:"c $$ i = (a $$ i + b $$ i) / 2" "d $$ i = b $$ i"
        show False using e_f(2)[of i] and i x unfolding as by(fastforce simp add:field_simps)
      qed qed qed
  also have "\<Union> ?A = {a..b}" proof(rule set_eqI,rule)
    fix x assume "x\<in>\<Union>?A" then guess Y unfolding Union_iff ..
    from this(1) guess c unfolding mem_Collect_eq .. then guess d ..
    note c_d = this[THEN conjunct2,rule_format] `x\<in>Y`[unfolded this[THEN conjunct1]]
    show "x\<in>{a..b}" unfolding mem_interval proof safe
      fix i assume "i<DIM('a)" thus "a $$ i \<le> x $$ i" "x $$ i \<le> b $$ i"
        using c_d(1)[of i] c_d(2)[unfolded mem_interval,THEN spec[where x=i]] by auto qed
  next fix x assume x:"x\<in>{a..b}"
    have "\<forall>i<DIM('a). \<exists>c d. (c = a$$i \<and> d = (a$$i + b$$i) / 2 \<or> c = (a$$i + b$$i) / 2 \<and> d = b$$i) \<and> c\<le>x$$i \<and> x$$i \<le> d"
      (is "\<forall>i<DIM('a). \<exists>c d. ?P i c d") unfolding mem_interval proof(rule,rule) fix i
      have "?P i (a$$i) ((a $$ i + b $$ i) / 2) \<or> ?P i ((a $$ i + b $$ i) / 2) (b$$i)"
        using x[unfolded mem_interval,THEN spec[where x=i]] by auto thus "\<exists>c d. ?P i c d" by blast
    qed thus "x\<in>\<Union>?A" unfolding Union_iff unfolding lambda_skolem' unfolding Bex_def mem_Collect_eq
      apply-apply(erule exE)+ apply(rule_tac x="{xa..xaa}" in exI) unfolding mem_interval by auto
  qed finally show False using assms by auto qed

lemma interval_bisection: fixes type::"'a::ordered_euclidean_space"
  assumes "P {}" "(\<forall>s t. P s \<and> P t \<and> interior(s) \<inter> interior(t) = {} \<longrightarrow> P(s \<union> t))" "\<not> P {a..b::'a}"
  obtains x where "x \<in> {a..b}" "\<forall>e>0. \<exists>c d. x \<in> {c..d} \<and> {c..d} \<subseteq> ball x e \<and> {c..d} \<subseteq> {a..b} \<and> ~P({c..d})"
proof-
  have "\<forall>x. \<exists>y. \<not> P {fst x..snd x} \<longrightarrow> (\<not> P {fst y..snd y} \<and>
    (\<forall>i<DIM('a). fst x$$i \<le> fst y$$i \<and> fst y$$i \<le> snd y$$i \<and> snd y$$i \<le> snd x$$i \<and>
                           2 * (snd y$$i - fst y$$i) \<le> snd x$$i - fst x$$i))" proof case goal1 thus ?case proof-
      presume "\<not> P {fst x..snd x} \<Longrightarrow> ?thesis"
      thus ?thesis apply(cases "P {fst x..snd x}") by auto
    next assume as:"\<not> P {fst x..snd x}" from interval_bisection_step[of P, OF assms(1-2) as] guess c d . 
      thus ?thesis apply- apply(rule_tac x="(c,d)" in exI) by auto
    qed qed then guess f apply-apply(drule choice) by(erule exE) note f=this
  def AB \<equiv> "\<lambda>n. (f ^^ n) (a,b)" def A \<equiv> "\<lambda>n. fst(AB n)" and B \<equiv> "\<lambda>n. snd(AB n)" note ab_def = this AB_def
  have "A 0 = a" "B 0 = b" "\<And>n. \<not> P {A(Suc n)..B(Suc n)} \<and>
    (\<forall>i<DIM('a). A(n)$$i \<le> A(Suc n)$$i \<and> A(Suc n)$$i \<le> B(Suc n)$$i \<and> B(Suc n)$$i \<le> B(n)$$i \<and> 
    2 * (B(Suc n)$$i - A(Suc n)$$i) \<le> B(n)$$i - A(n)$$i)" (is "\<And>n. ?P n")
  proof- show "A 0 = a" "B 0 = b" unfolding ab_def by auto
    case goal3 note S = ab_def funpow.simps o_def id_apply show ?case
    proof(induct n) case 0 thus ?case unfolding S apply(rule f[rule_format]) using assms(3) by auto
    next case (Suc n) show ?case unfolding S apply(rule f[rule_format]) using Suc unfolding S by auto
    qed qed note AB = this(1-2) conjunctD2[OF this(3),rule_format]

  have interv:"\<And>e. 0 < e \<Longrightarrow> \<exists>n. \<forall>x\<in>{A n..B n}. \<forall>y\<in>{A n..B n}. dist x y < e"
  proof- case goal1 guess n using real_arch_pow2[of "(setsum (\<lambda>i. b$$i - a$$i) {..<DIM('a)}) / e"] .. note n=this
    show ?case apply(rule_tac x=n in exI) proof(rule,rule)
      fix x y assume xy:"x\<in>{A n..B n}" "y\<in>{A n..B n}"
      have "dist x y \<le> setsum (\<lambda>i. abs((x - y)$$i)) {..<DIM('a)}" unfolding dist_norm by(rule norm_le_l1)
      also have "\<dots> \<le> setsum (\<lambda>i. B n$$i - A n$$i) {..<DIM('a)}"
      proof(rule setsum_mono) fix i show "\<bar>(x - y) $$ i\<bar> \<le> B n $$ i - A n $$ i"
          using xy[unfolded mem_interval,THEN spec[where x=i]] by auto qed
      also have "\<dots> \<le> setsum (\<lambda>i. b$$i - a$$i) {..<DIM('a)} / 2^n" unfolding setsum_divide_distrib
      proof(rule setsum_mono) case goal1 thus ?case
        proof(induct n) case 0 thus ?case unfolding AB by auto
        next case (Suc n) have "B (Suc n) $$ i - A (Suc n) $$ i \<le> (B n $$ i - A n $$ i) / 2"
            using AB(4)[of i n] using goal1 by auto
          also have "\<dots> \<le> (b $$ i - a $$ i) / 2 ^ Suc n" using Suc by(auto simp add:field_simps) finally show ?case .
        qed qed
      also have "\<dots> < e" using n using goal1 by(auto simp add:field_simps) finally show "dist x y < e" .
    qed qed
  { fix n m ::nat assume "m \<le> n" then guess d unfolding le_Suc_ex_iff .. note d=this
    have "{A n..B n} \<subseteq> {A m..B m}" unfolding d 
    proof(induct d) case 0 thus ?case by auto
    next case (Suc d) show ?case apply(rule subset_trans[OF _ Suc])
        apply(rule) unfolding mem_interval apply(rule,erule_tac x=i in allE)
      proof- case goal1 thus ?case using AB(4)[of i "m + d"] by(auto simp add:field_simps)
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
  obtains p where "p tagged_division_of {a..b::'a::ordered_euclidean_space}" "g fine p"
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

lemma has_integral_unique: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral k1) i" "(f has_integral k2) i" shows "k1 = k2"
proof(rule ccontr) let ?e = "norm(k1 - k2) / 2" assume as:"k1 \<noteq> k2" hence e:"?e > 0" by auto
  have lem:"\<And>f::'n \<Rightarrow> 'a.  \<And> a b k1 k2.
    (f has_integral k1) ({a..b}) \<Longrightarrow> (f has_integral k2) ({a..b}) \<Longrightarrow> k1 \<noteq> k2 \<Longrightarrow> False"
  proof- case goal1 let ?e = "norm(k1 - k2) / 2" from goal1(3) have e:"?e > 0" by auto
    guess d1 by(rule has_integralD[OF goal1(1) e]) note d1=this
    guess d2 by(rule has_integralD[OF goal1(2) e]) note d2=this
    guess p by(rule fine_division_exists[OF gauge_inter[OF d1(1) d2(1)],of a b]) note p=this
    let ?c = "(\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)" have "norm (k1 - k2) \<le> norm (?c - k2) + norm (?c - k1)"
      using norm_triangle_ineq4[of "k1 - ?c" "k2 - ?c"] by(auto simp add:algebra_simps norm_minus_commute)
    also have "\<dots> < norm (k1 - k2) / 2 + norm (k1 - k2) / 2"
      apply(rule add_strict_mono) apply(rule_tac[!] d2(2) d1(2)) using p unfolding fine_def by auto
    finally show False by auto
  qed { presume "\<not> (\<exists>a b. i = {a..b}) \<Longrightarrow> False"
    thus False apply-apply(cases "\<exists>a b. i = {a..b}")
      using assms by(auto simp add:has_integral intro:lem[OF _ _ as]) }
  assume as:"\<not> (\<exists>a b. i = {a..b})"
  guess B1 by(rule has_integral_altD[OF assms(1) as,OF e]) note B1=this[rule_format]
  guess B2 by(rule has_integral_altD[OF assms(2) as,OF e]) note B2=this[rule_format]
  have "\<exists>a b::'n. ball 0 B1 \<union> ball 0 B2 \<subseteq> {a..b}" apply(rule bounded_subset_closed_interval)
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

lemma has_integral_is_0: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::real_normed_vector" 
  assumes "\<forall>x\<in>s. f x = 0" shows "(f has_integral 0) s"
proof- have lem:"\<And>a b. \<And>f::'n \<Rightarrow> 'a.
    (\<forall>x\<in>{a..b}. f(x) = 0) \<Longrightarrow> (f has_integral 0) ({a..b})" unfolding has_integral
  proof(rule,rule) fix a b e and f::"'n \<Rightarrow> 'a"
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
    thus "\<exists>z. ((\<lambda>x::'n. 0::'a) has_integral z) {a..b} \<and> norm (z - 0) < e"
      apply(rule_tac x=0 in exI) apply(rule,rule lem) by auto
  qed auto qed

lemma has_integral_0[simp]: "((\<lambda>x::'n::ordered_euclidean_space. 0) has_integral 0) s"
  apply(rule has_integral_is_0) by auto 

lemma has_integral_0_eq[simp]: "((\<lambda>x. 0) has_integral i) s \<longleftrightarrow> i = 0"
  using has_integral_unique[OF has_integral_0] by auto

lemma has_integral_linear: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral y) s" "bounded_linear h" shows "((h o f) has_integral ((h y))) s"
proof- interpret bounded_linear h using assms(2) . from pos_bounded guess B .. note B=conjunctD2[OF this,rule_format]
  have lem:"\<And>f::'n \<Rightarrow> 'a. \<And> y a b.
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
  by(rule bounded_linear_scaleR_right)

lemma has_integral_neg:
  shows "(f has_integral k) s \<Longrightarrow> ((\<lambda>x. -(f x)) has_integral (-k)) s"
  apply(drule_tac c="-1" in has_integral_cmul) by auto

lemma has_integral_add: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::real_normed_vector" 
  assumes "(f has_integral k) s" "(g has_integral l) s"
  shows "((\<lambda>x. f x + g x) has_integral (k + l)) s"
proof- have lem:"\<And>f g::'n \<Rightarrow> 'a. \<And>a b k l.
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
          unfolding * by(auto simp add:algebra_simps) also let ?res = "\<dots>"
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
    proof(rule,rule,rule) fix a b assume "ball 0 (max B1 B2) \<subseteq> {a..b::'n}"
      hence *:"ball 0 B1 \<subseteq> {a..b::'n}" "ball 0 B2 \<subseteq> {a..b::'n}" by auto
      guess w using B1(2)[OF *(1)] .. note w=conjunctD2[OF this]
      guess z using B2(2)[OF *(2)] .. note z=conjunctD2[OF this]
      have *:"\<And>x. (if x \<in> s then f x + g x else 0) = (if x \<in> s then f x else 0) + (if x \<in> s then g x else 0)" by auto
      show "\<exists>z. ((\<lambda>x. if x \<in> s then f x + g x else 0) has_integral z) {a..b} \<and> norm (z - (k + l)) < e"
        apply(rule_tac x="w + z" in exI) apply(rule,rule lem[OF w(1) z(1), unfolded *[THEN sym]])
        using norm_triangle_ineq[of "w - k" "z - l"] w(2) z(2) by(auto simp add:field_simps)
    qed qed qed

lemma has_integral_sub:
  shows "(f has_integral k) s \<Longrightarrow> (g has_integral l) s \<Longrightarrow> ((\<lambda>x. f(x) - g(x)) has_integral (k - l)) s"
  using has_integral_add[OF _ has_integral_neg,of f k s g l] unfolding algebra_simps by auto

lemma integral_0: "integral s (\<lambda>x::'n::ordered_euclidean_space. 0::'m::real_normed_vector) = 0"
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

lemma integral_component_eq[simp]: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space"
  assumes "f integrable_on s" shows "integral s (\<lambda>x. f x $$ k) = integral s f $$ k"
  unfolding integral_linear[OF assms(1) bounded_linear_component,unfolded o_def] ..

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
  using has_integral_eq[of s f g] has_integral_eq[of s g f] by rule auto

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

lemma has_integral_refl[intro]: shows "(f has_integral 0) {a..a}" "(f has_integral 0) {a::'a::ordered_euclidean_space}"
proof- have *:"{a} = {a..a}" apply(rule set_eqI) unfolding mem_interval singleton_iff euclidean_eq[where 'a='a]
    apply safe prefer 3 apply(erule_tac x=i in allE) by(auto simp add: field_simps)
  show "(f has_integral 0) {a..a}" "(f has_integral 0) {a}" unfolding *
    apply(rule_tac[!] has_integral_null) unfolding content_eq_0_interior
    unfolding interior_closed_interval using interval_sing by auto qed

lemma integrable_on_refl[intro]: shows "f integrable_on {a..a}" unfolding integrable_on_def by auto

lemma integral_refl: shows "integral {a..a} f = 0" apply(rule integral_unique) by auto

subsection {* Cauchy-type criterion for integrability. *}

(* XXXXXXX *)
lemma integrable_cauchy: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::{real_normed_vector,complete_space}" 
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
        apply(rule dist_triangle_half_l[where y=y,unfolded dist_norm])
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
  then guess y unfolding convergent_eq_cauchy[THEN sym] .. note y=this[THEN LIMSEQ_D]
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
        using N2[rule_format,of "N1+N2"]
        using as dp[of "N1 - 1 + 1 + N2" "N1 + N2"] using p(1)[of "N1 + N2"] using N1 by auto qed qed qed

subsection {* Additivity of integral on abutting intervals. *}

lemma interval_split: fixes a::"'a::ordered_euclidean_space" assumes "k<DIM('a)" shows
  "{a..b} \<inter> {x. x$$k \<le> c} = {a .. (\<chi>\<chi> i. if i = k then min (b$$k) c else b$$i)}"
  "{a..b} \<inter> {x. x$$k \<ge> c} = {(\<chi>\<chi> i. if i = k then max (a$$k) c else a$$i) .. b}"
  apply(rule_tac[!] set_eqI) unfolding Int_iff mem_interval mem_Collect_eq using assms by auto

lemma content_split: fixes a::"'a::ordered_euclidean_space" assumes "k<DIM('a)" shows
  "content {a..b} = content({a..b} \<inter> {x. x$$k \<le> c}) + content({a..b} \<inter> {x. x$$k >= c})"
proof- note simps = interval_split[OF assms] content_closed_interval_cases eucl_le[where 'a='a]
  { presume "a\<le>b \<Longrightarrow> ?thesis" thus ?thesis apply(cases "a\<le>b") unfolding simps using assms by auto }
  have *:"{..<DIM('a)} = insert k ({..<DIM('a)} - {k})" "\<And>x. finite ({..<DIM('a)}-{x})" "\<And>x. x\<notin>{..<DIM('a)}-{x}"
    using assms by auto
  have *:"\<And>X Y Z. (\<Prod>i\<in>{..<DIM('a)}. Z i (if i = k then X else Y i)) = Z k X * (\<Prod>i\<in>{..<DIM('a)}-{k}. Z i (Y i))"
    "(\<Prod>i\<in>{..<DIM('a)}. b$$i - a$$i) = (\<Prod>i\<in>{..<DIM('a)}-{k}. b$$i - a$$i) * (b$$k - a$$k)" 
    apply(subst *(1)) defer apply(subst *(1)) unfolding setprod_insert[OF *(2-)] by auto
  assume as:"a\<le>b" moreover have "\<And>x. min (b $$ k) c = max (a $$ k) c
    \<Longrightarrow> x* (b$$k - a$$k) = x*(max (a $$ k) c - a $$ k) + x*(b $$ k - max (a $$ k) c)"
    by  (auto simp add:field_simps)
  moreover have **:"(\<Prod>i<DIM('a). ((\<chi>\<chi> i. if i = k then min (b $$ k) c else b $$ i)::'a) $$ i - a $$ i) = 
    (\<Prod>i<DIM('a). (if i = k then min (b $$ k) c else b $$ i) - a $$ i)"
    "(\<Prod>i<DIM('a). b $$ i - ((\<chi>\<chi> i. if i = k then max (a $$ k) c else a $$ i)::'a) $$ i) =
    (\<Prod>i<DIM('a). b $$ i - (if i = k then max (a $$ k) c else a $$ i))"
    apply(rule_tac[!] setprod.cong) by auto
  have "\<not> a $$ k \<le> c \<Longrightarrow> \<not> c \<le> b $$ k \<Longrightarrow> False"
    unfolding not_le using as[unfolded eucl_le[where 'a='a],rule_format,of k] assms by auto
  ultimately show ?thesis using assms unfolding simps **
    unfolding *(1)[of "\<lambda>i x. b$$i - x"] *(1)[of "\<lambda>i x. x - a$$i"] unfolding  *(2) 
    apply(subst(2) euclidean_lambda_beta''[where 'a='a])
    apply(subst(3) euclidean_lambda_beta''[where 'a='a]) by auto
qed

lemma division_split_left_inj: fixes type::"'a::ordered_euclidean_space"
  assumes "d division_of i" "k1 \<in> d" "k2 \<in> d"  "k1 \<noteq> k2" 
  "k1 \<inter> {x::'a. x$$k \<le> c} = k2 \<inter> {x. x$$k \<le> c}"and k:"k<DIM('a)"
  shows "content(k1 \<inter> {x. x$$k \<le> c}) = 0"
proof- note d=division_ofD[OF assms(1)]
  have *:"\<And>a b::'a. \<And> c. (content({a..b} \<inter> {x. x$$k \<le> c}) = 0 \<longleftrightarrow> interior({a..b} \<inter> {x. x$$k \<le> c}) = {})"
    unfolding  interval_split[OF k] content_eq_0_interior by auto
  guess u1 v1 using d(4)[OF assms(2)] apply-by(erule exE)+ note uv1=this
  guess u2 v2 using d(4)[OF assms(3)] apply-by(erule exE)+ note uv2=this
  have **:"\<And>s t u. s \<inter> t = {} \<Longrightarrow> u \<subseteq> s \<Longrightarrow> u \<subseteq> t \<Longrightarrow> u = {}" by auto
  show ?thesis unfolding uv1 uv2 * apply(rule **[OF d(5)[OF assms(2-4)]])
    defer apply(subst assms(5)[unfolded uv1 uv2]) unfolding uv1 uv2 by auto qed
 
lemma division_split_right_inj: fixes type::"'a::ordered_euclidean_space"
  assumes "d division_of i" "k1 \<in> d" "k2 \<in> d"  "k1 \<noteq> k2"
  "k1 \<inter> {x::'a. x$$k \<ge> c} = k2 \<inter> {x. x$$k \<ge> c}" and k:"k<DIM('a)"
  shows "content(k1 \<inter> {x. x$$k \<ge> c}) = 0"
proof- note d=division_ofD[OF assms(1)]
  have *:"\<And>a b::'a. \<And> c. (content({a..b} \<inter> {x. x$$k >= c}) = 0 \<longleftrightarrow> interior({a..b} \<inter> {x. x$$k >= c}) = {})"
    unfolding interval_split[OF k] content_eq_0_interior by auto
  guess u1 v1 using d(4)[OF assms(2)] apply-by(erule exE)+ note uv1=this
  guess u2 v2 using d(4)[OF assms(3)] apply-by(erule exE)+ note uv2=this
  have **:"\<And>s t u. s \<inter> t = {} \<Longrightarrow> u \<subseteq> s \<Longrightarrow> u \<subseteq> t \<Longrightarrow> u = {}" by auto
  show ?thesis unfolding uv1 uv2 * apply(rule **[OF d(5)[OF assms(2-4)]])
    defer apply(subst assms(5)[unfolded uv1 uv2]) unfolding uv1 uv2 by auto qed

lemma tagged_division_split_left_inj: fixes x1::"'a::ordered_euclidean_space"
  assumes "d tagged_division_of i" "(x1,k1) \<in> d" "(x2,k2) \<in> d" "k1 \<noteq> k2"  "k1 \<inter> {x. x$$k \<le> c} = k2 \<inter> {x. x$$k \<le> c}" 
  and k:"k<DIM('a)"
  shows "content(k1 \<inter> {x. x$$k \<le> c}) = 0"
proof- have *:"\<And>a b c. (a,b) \<in> c \<Longrightarrow> b \<in> snd ` c" unfolding image_iff apply(rule_tac x="(a,b)" in bexI) by auto
  show ?thesis apply(rule division_split_left_inj[OF division_of_tagged_division[OF assms(1)]])
    apply(rule_tac[1-2] *) using assms(2-) by auto qed

lemma tagged_division_split_right_inj: fixes x1::"'a::ordered_euclidean_space"
  assumes "d tagged_division_of i" "(x1,k1) \<in> d" "(x2,k2) \<in> d" "k1 \<noteq> k2"  "k1 \<inter> {x. x$$k \<ge> c} = k2 \<inter> {x. x$$k \<ge> c}" 
  and k:"k<DIM('a)"
  shows "content(k1 \<inter> {x. x$$k \<ge> c}) = 0"
proof- have *:"\<And>a b c. (a,b) \<in> c \<Longrightarrow> b \<in> snd ` c" unfolding image_iff apply(rule_tac x="(a,b)" in bexI) by auto
  show ?thesis apply(rule division_split_right_inj[OF division_of_tagged_division[OF assms(1)]])
    apply(rule_tac[1-2] *) using assms(2-) by auto qed

lemma division_split: fixes a::"'a::ordered_euclidean_space"
  assumes "p division_of {a..b}" and k:"k<DIM('a)"
  shows "{l \<inter> {x. x$$k \<le> c} | l. l \<in> p \<and> ~(l \<inter> {x. x$$k \<le> c} = {})} division_of({a..b} \<inter> {x. x$$k \<le> c})" (is "?p1 division_of ?I1") and 
        "{l \<inter> {x. x$$k \<ge> c} | l. l \<in> p \<and> ~(l \<inter> {x. x$$k \<ge> c} = {})} division_of ({a..b} \<inter> {x. x$$k \<ge> c})" (is "?p2 division_of ?I2")
proof(rule_tac[!] division_ofI) note p=division_ofD[OF assms(1)]
  show "finite ?p1" "finite ?p2" using p(1) by auto show "\<Union>?p1 = ?I1" "\<Union>?p2 = ?I2" unfolding p(6)[THEN sym] by auto
  { fix k assume "k\<in>?p1" then guess l unfolding mem_Collect_eq apply-by(erule exE,(erule conjE)+) note l=this
    guess u v using p(4)[OF l(2)] apply-by(erule exE)+ note uv=this
    show "k\<subseteq>?I1" "k \<noteq> {}" "\<exists>a b. k = {a..b}" unfolding l
      using p(2-3)[OF l(2)] l(3) unfolding uv apply- prefer 3 apply(subst interval_split[OF k]) by auto
    fix k' assume "k'\<in>?p1" then guess l' unfolding mem_Collect_eq apply-by(erule exE,(erule conjE)+) note l'=this
    assume "k\<noteq>k'" thus "interior k \<inter> interior k' = {}" unfolding l l' using p(5)[OF l(2) l'(2)] by auto }
  { fix k assume "k\<in>?p2" then guess l unfolding mem_Collect_eq apply-by(erule exE,(erule conjE)+) note l=this
    guess u v using p(4)[OF l(2)] apply-by(erule exE)+ note uv=this
    show "k\<subseteq>?I2" "k \<noteq> {}" "\<exists>a b. k = {a..b}" unfolding l
      using p(2-3)[OF l(2)] l(3) unfolding uv apply- prefer 3 apply(subst interval_split[OF k]) by auto
    fix k' assume "k'\<in>?p2" then guess l' unfolding mem_Collect_eq apply-by(erule exE,(erule conjE)+) note l'=this
    assume "k\<noteq>k'" thus "interior k \<inter> interior k' = {}" unfolding l l' using p(5)[OF l(2) l'(2)] by auto }
qed

lemma has_integral_split: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_integral i) ({a..b} \<inter> {x. x$$k \<le> c})"  "(f has_integral j) ({a..b} \<inter> {x. x$$k \<ge> c})" and k:"k<DIM('a)"
  shows "(f has_integral (i + j)) ({a..b})"
proof(unfold has_integral,rule,rule) case goal1 hence e:"e/2>0" by auto
  guess d1 using has_integralD[OF assms(1)[unfolded interval_split[OF k]] e] . note d1=this[unfolded interval_split[THEN sym,OF k]]
  guess d2 using has_integralD[OF assms(2)[unfolded interval_split[OF k]] e] . note d2=this[unfolded interval_split[THEN sym,OF k]]
  let ?d = "\<lambda>x. if x$$k = c then (d1 x \<inter> d2 x) else ball x (abs(x$$k - c)) \<inter> d1 x \<inter> d2 x"
  show ?case apply(rule_tac x="?d" in exI,rule) defer apply(rule,rule,(erule conjE)+)
  proof- show "gauge ?d" using d1(1) d2(1) unfolding gauge_def by auto
    fix p assume "p tagged_division_of {a..b}" "?d fine p" note p = this tagged_division_ofD[OF this(1)]
    have lem0:"\<And>x kk. (x,kk) \<in> p \<Longrightarrow> ~(kk \<inter> {x. x$$k \<le> c} = {}) \<Longrightarrow> x$$k \<le> c"
         "\<And>x kk. (x,kk) \<in> p \<Longrightarrow> ~(kk \<inter> {x. x$$k \<ge> c} = {}) \<Longrightarrow> x$$k \<ge> c"
    proof- fix x kk assume as:"(x,kk)\<in>p"
      show "~(kk \<inter> {x. x$$k \<le> c} = {}) \<Longrightarrow> x$$k \<le> c"
      proof(rule ccontr) case goal1
        from this(2)[unfolded not_le] have "kk \<subseteq> ball x \<bar>x $$ k - c\<bar>"
          using p(2)[unfolded fine_def,rule_format,OF as,unfolded split_conv] by auto
        hence "\<exists>y. y \<in> ball x \<bar>x $$ k - c\<bar> \<inter> {x. x $$ k \<le> c}" using goal1(1) by blast 
        then guess y .. hence "\<bar>x $$ k - y $$ k\<bar> < \<bar>x $$ k - c\<bar>" "y$$k \<le> c" apply-apply(rule le_less_trans)
          using component_le_norm[of "x - y" k] by(auto simp add:dist_norm)
        thus False using goal1(2)[unfolded not_le] by(auto simp add:field_simps)
      qed
      show "~(kk \<inter> {x. x$$k \<ge> c} = {}) \<Longrightarrow> x$$k \<ge> c"
      proof(rule ccontr) case goal1
        from this(2)[unfolded not_le] have "kk \<subseteq> ball x \<bar>x $$ k - c\<bar>"
          using p(2)[unfolded fine_def,rule_format,OF as,unfolded split_conv] by auto
        hence "\<exists>y. y \<in> ball x \<bar>x $$ k - c\<bar> \<inter> {x. x $$ k \<ge> c}" using goal1(1) by blast 
        then guess y .. hence "\<bar>x $$ k - y $$ k\<bar> < \<bar>x $$ k - c\<bar>" "y$$k \<ge> c" apply-apply(rule le_less_trans)
          using component_le_norm[of "x - y" k] by(auto simp add:dist_norm)
        thus False using goal1(2)[unfolded not_le] by(auto simp add:field_simps)
      qed
    qed

    have lem1: "\<And>f P Q. (\<forall>x k. (x,k) \<in> {(x,f k) | x k. P x k} \<longrightarrow> Q x k) \<longleftrightarrow> (\<forall>x k. P x k \<longrightarrow> Q x (f k))" by auto
    have lem2: "\<And>f s P f. finite s \<Longrightarrow> finite {(x,f k) | x k. (x,k) \<in> s \<and> P x k}"
    proof- case goal1 thus ?case apply-apply(rule finite_subset[of _ "(\<lambda>(x,k). (x,f k)) ` s"]) by auto qed
    have lem3: "\<And>g::'a set \<Rightarrow> 'a set. finite p \<Longrightarrow>
      setsum (\<lambda>(x,k). content k *\<^sub>R f x) {(x,g k) |x k. (x,k) \<in> p \<and> ~(g k = {})}
               = setsum (\<lambda>(x,k). content k *\<^sub>R f x) ((\<lambda>(x,k). (x,g k)) ` p)"
      apply(rule setsum_mono_zero_left) prefer 3
    proof fix g::"'a set \<Rightarrow> 'a set" and i::"('a) \<times> (('a) set)"
      assume "i \<in> (\<lambda>(x, k). (x, g k)) ` p - {(x, g k) |x k. (x, k) \<in> p \<and> g k \<noteq> {}}"
      then obtain x k where xk:"i=(x,g k)" "(x,k)\<in>p" "(x,g k) \<notin> {(x, g k) |x k. (x, k) \<in> p \<and> g k \<noteq> {}}" by auto
      have "content (g k) = 0" using xk using content_empty by auto
      thus "(\<lambda>(x, k). content k *\<^sub>R f x) i = 0" unfolding xk split_conv by auto
    qed auto
    have lem4:"\<And>g. (\<lambda>(x,l). content (g l) *\<^sub>R f x) = (\<lambda>(x,l). content l *\<^sub>R f x) o (\<lambda>(x,l). (x,g l))" apply(rule ext) by auto

    let ?M1 = "{(x,kk \<inter> {x. x$$k \<le> c}) |x kk. (x,kk) \<in> p \<and> kk \<inter> {x. x$$k \<le> c} \<noteq> {}}"
    have "norm ((\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) - i) < e/2" apply(rule d1(2),rule tagged_division_ofI)
      apply(rule lem2 p(3))+ prefer 6 apply(rule fineI)
    proof- show "\<Union>{k. \<exists>x. (x, k) \<in> ?M1} = {a..b} \<inter> {x. x$$k \<le> c}" unfolding p(8)[THEN sym] by auto
      fix x l assume xl:"(x,l)\<in>?M1"
      then guess x' l' unfolding mem_Collect_eq apply- unfolding Pair_eq apply((erule exE)+,(erule conjE)+) .  note xl'=this
      have "l' \<subseteq> d1 x'" apply(rule order_trans[OF fineD[OF p(2) xl'(3)]]) by auto
      thus "l \<subseteq> d1 x" unfolding xl' by auto
      show "x\<in>l" "l \<subseteq> {a..b} \<inter> {x. x $$ k \<le> c}" unfolding xl' using p(4-6)[OF xl'(3)] using xl'(4)
        using lem0(1)[OF xl'(3-4)] by auto
      show  "\<exists>a b. l = {a..b}" unfolding xl' using p(6)[OF xl'(3)] by(fastforce simp add: interval_split[OF k,where c=c])
      fix y r let ?goal = "interior l \<inter> interior r = {}" assume yr:"(y,r)\<in>?M1"
      then guess y' r' unfolding mem_Collect_eq apply- unfolding Pair_eq apply((erule exE)+,(erule conjE)+) .  note yr'=this
      assume as:"(x,l) \<noteq> (y,r)" show "interior l \<inter> interior r = {}"
      proof(cases "l' = r' \<longrightarrow> x' = y'")
        case False thus ?thesis using p(7)[OF xl'(3) yr'(3)] using as unfolding xl' yr' by auto
      next case True hence "l' \<noteq> r'" using as unfolding xl' yr' by auto
        thus ?thesis using p(7)[OF xl'(3) yr'(3)] using as unfolding xl' yr' by auto
      qed qed moreover

    let ?M2 = "{(x,kk \<inter> {x. x$$k \<ge> c}) |x kk. (x,kk) \<in> p \<and> kk \<inter> {x. x$$k \<ge> c} \<noteq> {}}" 
    have "norm ((\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - j) < e/2" apply(rule d2(2),rule tagged_division_ofI)
      apply(rule lem2 p(3))+ prefer 6 apply(rule fineI)
    proof- show "\<Union>{k. \<exists>x. (x, k) \<in> ?M2} = {a..b} \<inter> {x. x$$k \<ge> c}" unfolding p(8)[THEN sym] by auto
      fix x l assume xl:"(x,l)\<in>?M2"
      then guess x' l' unfolding mem_Collect_eq apply- unfolding Pair_eq apply((erule exE)+,(erule conjE)+) .  note xl'=this
      have "l' \<subseteq> d2 x'" apply(rule order_trans[OF fineD[OF p(2) xl'(3)]]) by auto
      thus "l \<subseteq> d2 x" unfolding xl' by auto
      show "x\<in>l" "l \<subseteq> {a..b} \<inter> {x. x $$ k \<ge> c}" unfolding xl' using p(4-6)[OF xl'(3)] using xl'(4)
        using lem0(2)[OF xl'(3-4)] by auto
      show  "\<exists>a b. l = {a..b}" unfolding xl' using p(6)[OF xl'(3)] by(fastforce simp add: interval_split[OF k, where c=c])
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
    also { have *:"\<And>x y. x = (0::real) \<Longrightarrow> x *\<^sub>R (y::'b) = 0" using scaleR_zero_left by auto
      have "((\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) - i) + ((\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - j)
       = (\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - (i + j)" by auto
      also have "\<dots> = (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. x $$ k \<le> c}) *\<^sub>R f x) +
        (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. c \<le> x $$ k}) *\<^sub>R f x) - (i + j)"
        unfolding lem3[OF p(3)] apply(subst setsum_reindex_nonzero[OF p(3)]) defer apply(subst setsum_reindex_nonzero[OF p(3)])
        defer unfolding lem4[THEN sym] apply(rule refl) unfolding split_paired_all split_conv apply(rule_tac[!] *)
      proof- case goal1 thus ?case apply- apply(rule tagged_division_split_left_inj [OF p(1), of a b aa ba]) using k by auto
      next case   goal2 thus ?case apply- apply(rule tagged_division_split_right_inj[OF p(1), of a b aa ba]) using k by auto
      qed also note setsum_addf[THEN sym]
      also have *:"\<And>x. x\<in>p \<Longrightarrow> (\<lambda>(x, ka). content (ka \<inter> {x. x $$ k \<le> c}) *\<^sub>R f x) x + (\<lambda>(x, ka). content (ka \<inter> {x. c \<le> x $$ k}) *\<^sub>R f x) x
        = (\<lambda>(x,ka). content ka *\<^sub>R f x) x" unfolding split_paired_all split_conv
      proof- fix a b assume "(a,b) \<in> p" from p(6)[OF this] guess u v apply-by(erule exE)+ note uv=this
        thus "content (b \<inter> {x. x $$ k \<le> c}) *\<^sub>R f a + content (b \<inter> {x. c \<le> x $$ k}) *\<^sub>R f a = content b *\<^sub>R f a"
          unfolding scaleR_left_distrib[THEN sym] unfolding uv content_split[OF k,of u v c] by auto
      qed note setsum_cong2[OF this]
      finally have "(\<Sum>(x, k)\<in>{(x, kk \<inter> {x. x $$ k \<le> c}) |x kk. (x, kk) \<in> p \<and> kk \<inter> {x. x $$ k \<le> c} \<noteq> {}}. content k *\<^sub>R f x) - i +
        ((\<Sum>(x, k)\<in>{(x, kk \<inter> {x. c \<le> x $$ k}) |x kk. (x, kk) \<in> p \<and> kk \<inter> {x. c \<le> x $$ k} \<noteq> {}}. content k *\<^sub>R f x) - j) =
        (\<Sum>(x, ka)\<in>p. content ka *\<^sub>R f x) - (i + j)" by auto }
    finally show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - (i + j)) < e" by auto qed qed

(*lemma has_integral_split_cart: fixes f::"real^'n \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral i) ({a..b} \<inter> {x. x$k \<le> c})"  "(f has_integral j) ({a..b} \<inter> {x. x$k \<ge> c})"
  shows "(f has_integral (i + j)) ({a..b})" *)

subsection {* A sort of converse, integrability on subintervals. *}

lemma tagged_division_union_interval: fixes a::"'a::ordered_euclidean_space"
  assumes "p1 tagged_division_of ({a..b} \<inter> {x. x$$k \<le> (c::real)})"  "p2 tagged_division_of ({a..b} \<inter> {x. x$$k \<ge> c})"
  and k:"k<DIM('a)"
  shows "(p1 \<union> p2) tagged_division_of ({a..b})"
proof- have *:"{a..b} = ({a..b} \<inter> {x. x$$k \<le> c}) \<union> ({a..b} \<inter> {x. x$$k \<ge> c})" by auto
  show ?thesis apply(subst *) apply(rule tagged_division_union[OF assms(1-2)])
    unfolding interval_split[OF k] interior_closed_interval using k
    by(auto simp add: eucl_less[where 'a='a] elim!:allE[where x=k]) qed

lemma has_integral_separate_sides: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_integral i) ({a..b})" "e>0" and k:"k<DIM('a)"
  obtains d where "gauge d" "(\<forall>p1 p2. p1 tagged_division_of ({a..b} \<inter> {x. x$$k \<le> c}) \<and> d fine p1 \<and>
                                p2 tagged_division_of ({a..b} \<inter> {x. x$$k \<ge> c}) \<and> d fine p2
                                \<longrightarrow> norm((setsum (\<lambda>(x,k). content k *\<^sub>R f x) p1 +
                                          setsum (\<lambda>(x,k). content k *\<^sub>R f x) p2) - i) < e)"
proof- guess d using has_integralD[OF assms(1-2)] . note d=this
  show ?thesis apply(rule that[of d]) apply(rule d) apply(rule,rule,rule,(erule conjE)+)
  proof- fix p1 p2 assume "p1 tagged_division_of {a..b} \<inter> {x. x $$ k \<le> c}" "d fine p1" note p1=tagged_division_ofD[OF this(1)] this
                   assume "p2 tagged_division_of {a..b} \<inter> {x. c \<le> x $$ k}" "d fine p2" note p2=tagged_division_ofD[OF this(1)] this
    note tagged_division_union_interval[OF p1(7) p2(7)] note p12 = tagged_division_ofD[OF this] this
    have "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x) - i) = norm ((\<Sum>(x, k)\<in>p1 \<union> p2. content k *\<^sub>R f x) - i)"
      apply(subst setsum_Un_zero) apply(rule p1 p2)+ apply(rule) unfolding split_paired_all split_conv
    proof- fix a b assume ab:"(a,b) \<in> p1 \<inter> p2"
      have "(a,b) \<in> p1" using ab by auto from p1(4)[OF this] guess u v apply-by(erule exE)+ note uv =this
      have "b \<subseteq> {x. x$$k = c}" using ab p1(3)[of a b] p2(3)[of a b] by fastforce
      moreover have "interior {x::'a. x $$ k = c} = {}" 
      proof(rule ccontr) case goal1 then obtain x where x:"x\<in>interior {x::'a. x$$k = c}" by auto
        then guess e unfolding mem_interior .. note e=this
        have x:"x$$k = c" using x interior_subset by fastforce
        have *:"\<And>i. i<DIM('a) \<Longrightarrow> \<bar>(x - (x + (\<chi>\<chi> i. if i = k then e / 2 else 0))) $$ i\<bar>
          = (if i = k then e/2 else 0)" using e by auto
        have "(\<Sum>i<DIM('a). \<bar>(x - (x + (\<chi>\<chi> i. if i = k then e / 2 else 0))) $$ i\<bar>) =
          (\<Sum>i<DIM('a). (if i = k then e / 2 else 0))" apply(rule setsum_cong2) apply(subst *) by auto
        also have "... < e" apply(subst setsum_delta) using e by auto 
        finally have "x + (\<chi>\<chi> i. if i = k then e/2 else 0) \<in> ball x e" unfolding mem_ball dist_norm
          by(rule le_less_trans[OF norm_le_l1])
        hence "x + (\<chi>\<chi> i. if i = k then e/2 else 0) \<in> {x. x$$k = c}" using e by auto
        thus False unfolding mem_Collect_eq using e x k by auto
      qed ultimately have "content b = 0" unfolding uv content_eq_0_interior apply-apply(drule interior_mono) by auto
      thus "content b *\<^sub>R f a = 0" by auto
    qed auto
    also have "\<dots> < e" by(rule k d(2) p12 fine_union p1 p2)+
    finally show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x) - i) < e" . qed qed

lemma integrable_split[intro]: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::{real_normed_vector,complete_space}"
  assumes "f integrable_on {a..b}" and k:"k<DIM('a)"
  shows "f integrable_on ({a..b} \<inter> {x. x$$k \<le> c})" (is ?t1) and "f integrable_on ({a..b} \<inter> {x. x$$k \<ge> c})" (is ?t2) 
proof- guess y using assms(1) unfolding integrable_on_def .. note y=this
  def b' \<equiv> "(\<chi>\<chi> i. if i = k then min (b$$k) c else b$$i)::'a"
  and a' \<equiv> "(\<chi>\<chi> i. if i = k then max (a$$k) c else a$$i)::'a"
  show ?t1 ?t2 unfolding interval_split[OF k] integrable_cauchy unfolding interval_split[THEN sym,OF k]
  proof(rule_tac[!] allI impI)+ fix e::real assume "e>0" hence "e/2>0" by auto
    from has_integral_separate_sides[OF y this k,of c] guess d . note d=this[rule_format]
    let ?P = "\<lambda>A. \<exists>d. gauge d \<and> (\<forall>p1 p2. p1 tagged_division_of {a..b} \<inter> A \<and> d fine p1
      \<and> p2 tagged_division_of {a..b} \<inter> A \<and> d fine p2 \<longrightarrow>
      norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e)"
    show "?P {x. x $$ k \<le> c}" apply(rule_tac x=d in exI) apply(rule,rule d) apply(rule,rule,rule)
    proof- fix p1 p2 assume as:"p1 tagged_division_of {a..b} \<inter> {x. x $$ k \<le> c} \<and> d fine p1
        \<and> p2 tagged_division_of {a..b} \<inter> {x. x $$ k \<le> c} \<and> d fine p2"
      show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e"
      proof- guess p using fine_division_exists[OF d(1), of a' b] . note p=this
        show ?thesis using norm_triangle_half_l[OF d(2)[of p1 p] d(2)[of p2 p]]
          using as unfolding interval_split[OF k] b'_def[symmetric] a'_def[symmetric]
          using p using assms by(auto simp add:algebra_simps)
      qed qed  
    show "?P {x. x $$ k \<ge> c}" apply(rule_tac x=d in exI) apply(rule,rule d) apply(rule,rule,rule)
    proof- fix p1 p2 assume as:"p1 tagged_division_of {a..b} \<inter> {x. x $$ k \<ge> c} \<and> d fine p1
        \<and> p2 tagged_division_of {a..b} \<inter> {x. x $$ k \<ge> c} \<and> d fine p2"
      show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e"
      proof- guess p using fine_division_exists[OF d(1), of a b'] . note p=this
        show ?thesis using norm_triangle_half_l[OF d(2)[of p p1] d(2)[of p p2]]
          using as unfolding interval_split[OF k] b'_def[symmetric] a'_def[symmetric]
          using p using assms by(auto simp add:algebra_simps) qed qed qed qed

subsection {* Generalized notion of additivity. *}

definition "neutral opp = (SOME x. \<forall>y. opp x y = y \<and> opp y x = y)"

definition operative :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (('b::ordered_euclidean_space) set \<Rightarrow> 'a) \<Rightarrow> bool" where
  "operative opp f \<equiv> 
    (\<forall>a b. content {a..b} = 0 \<longrightarrow> f {a..b} = neutral(opp)) \<and>
    (\<forall>a b c. \<forall>k<DIM('b). f({a..b}) =
                   opp (f({a..b} \<inter> {x. x$$k \<le> c}))
                       (f({a..b} \<inter> {x. x$$k \<ge> c})))"

lemma operativeD[dest]: fixes type::"'a::ordered_euclidean_space"  assumes "operative opp f"
  shows "\<And>a b. content {a..b} = 0 \<Longrightarrow> f {a..b::'a} = neutral(opp)"
  "\<And>a b c k. k<DIM('a) \<Longrightarrow> f({a..b}) = opp (f({a..b} \<inter> {x. x$$k \<le> c})) (f({a..b} \<inter> {x. x$$k \<ge> c}))"
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
  by (metis option.nchotomy)

lemma exists_option:
 "(\<exists>x. P x) \<longleftrightarrow> P None \<or> (\<exists>x. P(Some x))" 
  by (metis option.nchotomy)

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
  unfolding monoidal_def using assms by fastforce

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
definition "fold' opp e s \<equiv> (if finite s then Finite_Set.fold opp e s else e)"
definition "iterate opp s f \<equiv> fold' (\<lambda>x a. opp (f x) a) (neutral opp) (support opp f s)"

lemma support_subset[intro]:"support opp f s \<subseteq> s" unfolding support_def by auto
lemma support_empty[simp]:"support opp f {} = {}" using support_subset[of opp f "{}"] by auto

lemma comp_fun_commute_monoidal[intro]: assumes "monoidal opp" shows "comp_fun_commute opp"
  unfolding comp_fun_commute_def using monoidal_ac[OF assms] by auto

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
  note * = comp_fun_commute.comp_comp_fun_commute [OF comp_fun_commute_monoidal[OF assms(1)]]
  show ?thesis proof(cases "f x = neutral opp")
    case True show ?thesis unfolding iterate_def if_not_P[OF x] support_clauses if_P[OF True]
      unfolding True monoidal_simps[OF assms(1)] by auto
  next case False show ?thesis unfolding iterate_def fold'_def  if_not_P[OF x] support_clauses if_not_P[OF False]
      apply(subst comp_fun_commute.fold_insert[OF * finite_support, simplified comp_def])
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
  unfolding operative_def neutral_add apply safe 
  unfolding content_split[THEN sym] ..

lemma neutral_monoid: "neutral ((op +)::('a::comm_monoid_add) \<Rightarrow> 'a \<Rightarrow> 'a) = 0"
  by (rule neutral_add) (* FIXME: duplicate *)

lemma monoidal_monoid[intro]:
  shows "monoidal ((op +)::('a::comm_monoid_add) \<Rightarrow> 'a \<Rightarrow> 'a)"
  unfolding monoidal_def neutral_monoid by(auto simp add: algebra_simps) 

lemma operative_integral: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::banach"
  shows "operative (lifted(op +)) (\<lambda>i. if f integrable_on i then Some(integral i f) else None)"
  unfolding operative_def unfolding neutral_lifted[OF monoidal_monoid] neutral_add
  apply(rule,rule,rule,rule) defer apply(rule allI impI)+
proof- fix a b c k assume k:"k<DIM('a)" show "(if f integrable_on {a..b} then Some (integral {a..b} f) else None) =
    lifted op + (if f integrable_on {a..b} \<inter> {x. x $$ k \<le> c} then Some (integral ({a..b} \<inter> {x. x $$ k \<le> c}) f) else None)
    (if f integrable_on {a..b} \<inter> {x. c \<le> x $$ k} then Some (integral ({a..b} \<inter> {x. c \<le> x $$ k}) f) else None)"
  proof(cases "f integrable_on {a..b}") 
    case True show ?thesis unfolding if_P[OF True] using k apply-
      unfolding if_P[OF integrable_split(1)[OF True]] unfolding if_P[OF integrable_split(2)[OF True]]
      unfolding lifted.simps option.inject apply(rule integral_unique) apply(rule has_integral_split[OF _ _ k]) 
      apply(rule_tac[!] integrable_integral integrable_split)+ using True k by auto
  next case False have "(\<not> (f integrable_on {a..b} \<inter> {x. x $$ k \<le> c})) \<or> (\<not> ( f integrable_on {a..b} \<inter> {x. c \<le> x $$ k}))"
    proof(rule ccontr) case goal1 hence "f integrable_on {a..b}" apply- unfolding integrable_on_def
        apply(rule_tac x="integral ({a..b} \<inter> {x. x $$ k \<le> c}) f + integral ({a..b} \<inter> {x. x $$ k \<ge> c}) f" in exI)
        apply(rule has_integral_split[OF _ _ k]) apply(rule_tac[!] integrable_integral) by auto
      thus False using False by auto
    qed thus ?thesis using False by auto 
  qed next 
  fix a b assume as:"content {a..b::'a} = 0"
  thus "(if f integrable_on {a..b} then Some (integral {a..b} f) else None) = Some 0"
    unfolding if_P[OF integrable_on_null[OF as]] using has_integral_null_eq[OF as] by auto qed

subsection {* Points of division of a partition. *}

definition "division_points (k::('a::ordered_euclidean_space) set) d = 
    {(j,x). j<DIM('a) \<and> (interval_lowerbound k)$$j < x \<and> x < (interval_upperbound k)$$j \<and>
           (\<exists>i\<in>d. (interval_lowerbound i)$$j = x \<or> (interval_upperbound i)$$j = x)}"

lemma division_points_finite: fixes i::"('a::ordered_euclidean_space) set"
  assumes "d division_of i" shows "finite (division_points i d)"
proof- note assm = division_ofD[OF assms]
  let ?M = "\<lambda>j. {(j,x)|x. (interval_lowerbound i)$$j < x \<and> x < (interval_upperbound i)$$j \<and>
           (\<exists>i\<in>d. (interval_lowerbound i)$$j = x \<or> (interval_upperbound i)$$j = x)}"
  have *:"division_points i d = \<Union>(?M ` {..<DIM('a)})"
    unfolding division_points_def by auto
  show ?thesis unfolding * using assm by auto qed

lemma division_points_subset: fixes a::"'a::ordered_euclidean_space"
  assumes "d division_of {a..b}" "\<forall>i<DIM('a). a$$i < b$$i"  "a$$k < c" "c < b$$k" and k:"k<DIM('a)"
  shows "division_points ({a..b} \<inter> {x. x$$k \<le> c}) {l \<inter> {x. x$$k \<le> c} | l . l \<in> d \<and> ~(l \<inter> {x. x$$k \<le> c} = {})}
                  \<subseteq> division_points ({a..b}) d" (is ?t1) and
        "division_points ({a..b} \<inter> {x. x$$k \<ge> c}) {l \<inter> {x. x$$k \<ge> c} | l . l \<in> d \<and> ~(l \<inter> {x. x$$k \<ge> c} = {})}
                  \<subseteq> division_points ({a..b}) d" (is ?t2)
proof- note assm = division_ofD[OF assms(1)]
  have *:"\<forall>i<DIM('a). a$$i \<le> b$$i"   "\<forall>i<DIM('a). a$$i \<le> ((\<chi>\<chi> i. if i = k then min (b $$ k) c else b $$ i)::'a) $$ i"
    "\<forall>i<DIM('a). ((\<chi>\<chi> i. if i = k then max (a $$ k) c else a $$ i)::'a) $$ i \<le> b$$i"  "min (b $$ k) c = c" "max (a $$ k) c = c"
    using assms using less_imp_le by auto
  show ?t1 unfolding division_points_def interval_split[OF k, of a b]
    unfolding interval_bounds[OF *(1)] interval_bounds[OF *(2)] interval_bounds[OF *(3)] unfolding *
    unfolding subset_eq apply(rule) unfolding mem_Collect_eq split_beta apply(erule bexE conjE)+
    unfolding mem_Collect_eq apply(erule exE conjE)+ unfolding euclidean_lambda_beta'
  proof- fix i l x assume as:"a $$ fst x < snd x" "snd x < (if fst x = k then c else b $$ fst x)"
      "interval_lowerbound i $$ fst x = snd x \<or> interval_upperbound i $$ fst x = snd x"
      "i = l \<inter> {x. x $$ k \<le> c}" "l \<in> d" "l \<inter> {x. x $$ k \<le> c} \<noteq> {}" and fstx:"fst x <DIM('a)"
    from assm(4)[OF this(5)] guess u v apply-by(erule exE)+ note l=this
    have *:"\<forall>i<DIM('a). u $$ i \<le> ((\<chi>\<chi> i. if i = k then min (v $$ k) c else v $$ i)::'a) $$ i"
      using as(6) unfolding l interval_split[OF k] interval_ne_empty as .
    have **:"\<forall>i<DIM('a). u$$i \<le> v$$i" using l using as(6) unfolding interval_ne_empty[THEN sym] by auto
    show "fst x <DIM('a) \<and> a $$ fst x < snd x \<and> snd x < b $$ fst x \<and> (\<exists>i\<in>d. interval_lowerbound i $$ fst x = snd x
      \<or> interval_upperbound i $$ fst x = snd x)" apply(rule,rule fstx)
      using as(1-3,5) unfolding l interval_split[OF k] interval_ne_empty as interval_bounds[OF *] apply-
      apply(rule,assumption,rule) defer apply(rule_tac x="{u..v}" in bexI) unfolding interval_bounds[OF **]
      apply(case_tac[!] "fst x = k") using assms fstx apply- unfolding euclidean_lambda_beta by auto
  qed
  show ?t2 unfolding division_points_def interval_split[OF k, of a b]
    unfolding interval_bounds[OF *(1)] interval_bounds[OF *(2)] interval_bounds[OF *(3)] unfolding *
    unfolding subset_eq apply(rule) unfolding mem_Collect_eq split_beta apply(erule bexE conjE)+
    unfolding mem_Collect_eq apply(erule exE conjE)+ unfolding euclidean_lambda_beta' apply(rule,assumption)
  proof- fix i l x assume as:"(if fst x = k then c else a $$ fst x) < snd x" "snd x < b $$ fst x"
      "interval_lowerbound i $$ fst x = snd x \<or> interval_upperbound i $$ fst x = snd x" 
      "i = l \<inter> {x. c \<le> x $$ k}" "l \<in> d" "l \<inter> {x. c \<le> x $$ k} \<noteq> {}" and fstx:"fst x < DIM('a)"
    from assm(4)[OF this(5)] guess u v apply-by(erule exE)+ note l=this
    have *:"\<forall>i<DIM('a). ((\<chi>\<chi> i. if i = k then max (u $$ k) c else u $$ i)::'a) $$ i \<le> v $$ i"
      using as(6) unfolding l interval_split[OF k] interval_ne_empty as .
    have **:"\<forall>i<DIM('a). u$$i \<le> v$$i" using l using as(6) unfolding interval_ne_empty[THEN sym] by auto
    show "a $$ fst x < snd x \<and> snd x < b $$ fst x \<and> (\<exists>i\<in>d. interval_lowerbound i $$ fst x = snd x \<or>
      interval_upperbound i $$ fst x = snd x)"
      using as(1-3,5) unfolding l interval_split[OF k] interval_ne_empty as interval_bounds[OF *] apply-
      apply rule defer apply(rule,assumption) apply(rule_tac x="{u..v}" in bexI) unfolding interval_bounds[OF **]
      apply(case_tac[!] "fst x = k") using assms fstx apply-  by(auto simp add:euclidean_lambda_beta'[OF k]) qed qed

lemma division_points_psubset: fixes a::"'a::ordered_euclidean_space"
  assumes "d division_of {a..b}"  "\<forall>i<DIM('a). a$$i < b$$i"  "a$$k < c" "c < b$$k"
  "l \<in> d" "interval_lowerbound l$$k = c \<or> interval_upperbound l$$k = c" and k:"k<DIM('a)"
  shows "division_points ({a..b} \<inter> {x. x$$k \<le> c}) {l \<inter> {x. x$$k \<le> c} | l. l\<in>d \<and> l \<inter> {x. x$$k \<le> c} \<noteq> {}}
              \<subset> division_points ({a..b}) d" (is "?D1 \<subset> ?D") 
        "division_points ({a..b} \<inter> {x. x$$k \<ge> c}) {l \<inter> {x. x$$k \<ge> c} | l. l\<in>d \<and> l \<inter> {x. x$$k \<ge> c} \<noteq> {}}
              \<subset> division_points ({a..b}) d" (is "?D2 \<subset> ?D") 
proof- have ab:"\<forall>i<DIM('a). a$$i \<le> b$$i" using assms(2) by(auto intro!:less_imp_le)
  guess u v using division_ofD(4)[OF assms(1,5)] apply-by(erule exE)+ note l=this
  have uv:"\<forall>i<DIM('a). u$$i \<le> v$$i" "\<forall>i<DIM('a). a$$i \<le> u$$i \<and> v$$i \<le> b$$i"
    using division_ofD(2,2,3)[OF assms(1,5)] unfolding l interval_ne_empty
    unfolding subset_eq apply- defer apply(erule_tac x=u in ballE, erule_tac x=v in ballE) unfolding mem_interval by auto
  have *:"interval_upperbound ({a..b} \<inter> {x. x $$ k \<le> interval_upperbound l $$ k}) $$ k = interval_upperbound l $$ k"
         "interval_upperbound ({a..b} \<inter> {x. x $$ k \<le> interval_lowerbound l $$ k}) $$ k = interval_lowerbound l $$ k"
    unfolding interval_split[OF k] apply(subst interval_bounds) prefer 3 apply(subst interval_bounds)
    unfolding l interval_bounds[OF uv(1)] using uv[rule_format,of k] ab k by auto
  have "\<exists>x. x \<in> ?D - ?D1" using assms(2-) apply-apply(erule disjE)
    apply(rule_tac x="(k,(interval_lowerbound l)$$k)" in exI) defer
    apply(rule_tac x="(k,(interval_upperbound l)$$k)" in exI)
    unfolding division_points_def unfolding interval_bounds[OF ab] by(auto simp add:*) 
  thus "?D1 \<subset> ?D" apply-apply(rule,rule division_points_subset[OF assms(1-4)]) using k by auto

  have *:"interval_lowerbound ({a..b} \<inter> {x. x $$ k \<ge> interval_lowerbound l $$ k}) $$ k = interval_lowerbound l $$ k"
         "interval_lowerbound ({a..b} \<inter> {x. x $$ k \<ge> interval_upperbound l $$ k}) $$ k = interval_upperbound l $$ k"
    unfolding interval_split[OF k] apply(subst interval_bounds) prefer 3 apply(subst interval_bounds)
    unfolding l interval_bounds[OF uv(1)] using uv[rule_format,of k] ab k by auto
  have "\<exists>x. x \<in> ?D - ?D2" using assms(2-) apply-apply(erule disjE)
    apply(rule_tac x="(k,(interval_lowerbound l)$$k)" in exI) defer
    apply(rule_tac x="(k,(interval_upperbound l)$$k)" in exI)
    unfolding division_points_def unfolding interval_bounds[OF ab] by(auto simp add:*) 
  thus "?D2 \<subset> ?D" apply-apply(rule,rule division_points_subset[OF assms(1-4) k]) by auto qed

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

lemma operative_division: fixes f::"('a::ordered_euclidean_space) set \<Rightarrow> 'b"
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
    hence ab':"\<forall>i<DIM('a). a$$i \<le> b$$i" by (auto intro!: less_imp_le) show ?case 
    proof(cases "division_points {a..b} d = {}")
      case True have d':"\<forall>i\<in>d. \<exists>u v. i = {u..v} \<and>
        (\<forall>j<DIM('a). u$$j = a$$j \<and> v$$j = a$$j \<or> u$$j = b$$j \<and> v$$j = b$$j \<or> u$$j = a$$j \<and> v$$j = b$$j)"
        unfolding forall_in_division[OF goal1(4)] apply(rule,rule,rule)
        apply(rule_tac x=a in exI,rule_tac x=b in exI) apply(rule,rule refl) apply(rule,rule)
      proof- fix u v j assume j:"j<DIM('a)" assume as:"{u..v} \<in> d" note division_ofD(3)[OF goal1(4) this]
        hence uv:"\<forall>i<DIM('a). u$$i \<le> v$$i" "u$$j \<le> v$$j" using j unfolding interval_ne_empty by auto
        have *:"\<And>p r Q. \<not> j<DIM('a) \<or> p \<or> r \<or> (\<forall>x\<in>d. Q x) \<Longrightarrow> p \<or> r \<or> (Q {u..v})" using as j by auto
        have "(j, u$$j) \<notin> division_points {a..b} d"
          "(j, v$$j) \<notin> division_points {a..b} d" using True by auto
        note this[unfolded de_Morgan_conj division_points_def mem_Collect_eq split_conv interval_bounds[OF ab'] bex_simps]
        note *[OF this(1)] *[OF this(2)] note this[unfolded interval_bounds[OF uv(1)]]
        moreover have "a$$j \<le> u$$j" "v$$j \<le> b$$j" using division_ofD(2,2,3)[OF goal1(4) as] 
          unfolding subset_eq apply- apply(erule_tac x=u in ballE,erule_tac[3] x=v in ballE)
          unfolding interval_ne_empty mem_interval using j by auto
        ultimately show "u$$j = a$$j \<and> v$$j = a$$j \<or> u$$j = b$$j \<and> v$$j = b$$j \<or> u$$j = a$$j \<and> v$$j = b$$j"
          unfolding not_less de_Morgan_disj using ab[rule_format,of j] uv(2) j by auto
      qed have "(1/2) *\<^sub>R (a+b) \<in> {a..b}" unfolding mem_interval using ab by(auto intro!:less_imp_le)
      note this[unfolded division_ofD(6)[OF goal1(4),THEN sym] Union_iff]
      then guess i .. note i=this guess u v using d'[rule_format,OF i(1)] apply-by(erule exE conjE)+ note uv=this
      have "{a..b} \<in> d"
      proof- { presume "i = {a..b}" thus ?thesis using i by auto }
        { presume "u = a" "v = b" thus "i = {a..b}" using uv by auto }
        show "u = a" "v = b" unfolding euclidean_eq[where 'a='a]
        proof(safe) fix j assume j:"j<DIM('a)" note i(2)[unfolded uv mem_interval,rule_format,of j]
          thus "u $$ j = a $$ j" "v $$ j = b $$ j" using uv(2)[rule_format,of j] j by auto
        qed qed
      hence *:"d = insert {a..b} (d - {{a..b}})" by auto
      have "iterate opp (d - {{a..b}}) f = neutral opp" apply(rule iterate_eq_neutral[OF goal1(2)])
      proof fix x assume x:"x \<in> d - {{a..b}}" hence "x\<in>d" by auto note d'[rule_format,OF this]
        then guess u v apply-by(erule exE conjE)+ note uv=this
        have "u\<noteq>a \<or> v\<noteq>b" using x[unfolded uv] by auto  
        then obtain j where "u$$j \<noteq> a$$j \<or> v$$j \<noteq> b$$j" and j:"j<DIM('a)" unfolding euclidean_eq[where 'a='a] by auto
        hence "u$$j = v$$j" using uv(2)[rule_format,OF j] by auto
        hence "content {u..v} = 0"  unfolding content_eq_0 apply(rule_tac x=j in exI) using j by auto
        thus "f x = neutral opp" unfolding uv(1) by(rule operativeD(1)[OF goal1(3)])
      qed thus "iterate opp d f = f {a..b}" apply-apply(subst *) 
        apply(subst iterate_insert[OF goal1(2)]) using goal1(2,4) by auto
    next case False hence "\<exists>x. x\<in>division_points {a..b} d" by auto
      then guess k c unfolding split_paired_Ex apply- unfolding division_points_def mem_Collect_eq split_conv
        by(erule exE conjE)+ note this(2-4,1) note kc=this[unfolded interval_bounds[OF ab']]
      from this(3) guess j .. note j=this
      def d1 \<equiv> "{l \<inter> {x. x$$k \<le> c} | l. l \<in> d \<and> l \<inter> {x. x$$k \<le> c} \<noteq> {}}"
      def d2 \<equiv> "{l \<inter> {x. x$$k \<ge> c} | l. l \<in> d \<and> l \<inter> {x. x$$k \<ge> c} \<noteq> {}}"
      def cb \<equiv> "(\<chi>\<chi> i. if i = k then c else b$$i)::'a" and ca \<equiv> "(\<chi>\<chi> i. if i = k then c else a$$i)::'a"
      note division_points_psubset[OF goal1(4) ab kc(1-2) j]
      note psubset_card_mono[OF _ this(1)] psubset_card_mono[OF _ this(2)]
      hence *:"(iterate opp d1 f) = f ({a..b} \<inter> {x. x$$k \<le> c})" "(iterate opp d2 f) = f ({a..b} \<inter> {x. x$$k \<ge> c})"
        apply- unfolding interval_split[OF kc(4)] apply(rule_tac[!] goal1(1)[rule_format])
        using division_split[OF goal1(4), where k=k and c=c]
        unfolding interval_split[OF kc(4)] d1_def[symmetric] d2_def[symmetric] unfolding goal1(2) Suc_le_mono
        using goal1(2-3) using division_points_finite[OF goal1(4)] using kc(4) by auto
      have "f {a..b} = opp (iterate opp d1 f) (iterate opp d2 f)" (is "_ = ?prev")
        unfolding * apply(rule operativeD(2)) using goal1(3) using kc(4) by auto 
      also have "iterate opp d1 f = iterate opp d (\<lambda>l. f(l \<inter> {x. x$$k \<le> c}))"
        unfolding d1_def apply(rule iterate_nonzero_image_lemma[unfolded o_def])
        unfolding empty_as_interval apply(rule goal1 division_of_finite operativeD[OF goal1(3)])+
        unfolding empty_as_interval[THEN sym] apply(rule content_empty)
      proof(rule,rule,rule,erule conjE) fix l y assume as:"l \<in> d" "y \<in> d" "l \<inter> {x. x $$ k \<le> c} = y \<inter> {x. x $$ k \<le> c}" "l \<noteq> y" 
        from division_ofD(4)[OF goal1(4) this(1)] guess u v apply-by(erule exE)+ note l=this
        show "f (l \<inter> {x. x $$ k \<le> c}) = neutral opp" unfolding l interval_split[OF kc(4)] 
          apply(rule operativeD(1) goal1)+ unfolding interval_split[THEN sym,OF kc(4)] apply(rule division_split_left_inj)
          apply(rule goal1) unfolding l[THEN sym] apply(rule as(1),rule as(2)) by(rule kc(4) as)+
      qed also have "iterate opp d2 f = iterate opp d (\<lambda>l. f(l \<inter> {x. x$$k \<ge> c}))"
        unfolding d2_def apply(rule iterate_nonzero_image_lemma[unfolded o_def])
        unfolding empty_as_interval apply(rule goal1 division_of_finite operativeD[OF goal1(3)])+
        unfolding empty_as_interval[THEN sym] apply(rule content_empty)
      proof(rule,rule,rule,erule conjE) fix l y assume as:"l \<in> d" "y \<in> d" "l \<inter> {x. c \<le> x $$ k} = y \<inter> {x. c \<le> x $$ k}" "l \<noteq> y" 
        from division_ofD(4)[OF goal1(4) this(1)] guess u v apply-by(erule exE)+ note l=this
        show "f (l \<inter> {x. x $$ k \<ge> c}) = neutral opp" unfolding l interval_split[OF kc(4)] 
          apply(rule operativeD(1) goal1)+ unfolding interval_split[THEN sym,OF kc(4)] apply(rule division_split_right_inj)
          apply(rule goal1) unfolding l[THEN sym] apply(rule as(1),rule as(2)) by(rule as kc(4))+
      qed also have *:"\<forall>x\<in>d. f x = opp (f (x \<inter> {x. x $$ k \<le> c})) (f (x \<inter> {x. c \<le> x $$ k}))"
        unfolding forall_in_division[OF goal1(4)] apply(rule,rule,rule,rule operativeD(2)) using goal1(3) kc by auto 
      have "opp (iterate opp d (\<lambda>l. f (l \<inter> {x. x $$ k \<le> c}))) (iterate opp d (\<lambda>l. f (l \<inter> {x. c \<le> x $$ k})))
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

subsection {* Finally, the integral of a constant *}

lemma has_integral_const[intro]:
  "((\<lambda>x. c) has_integral (content({a..b::'a::ordered_euclidean_space}) *\<^sub>R c)) ({a..b})"
  unfolding has_integral apply(rule,rule,rule_tac x="\<lambda>x. ball x 1" in exI)
  apply(rule,rule gauge_trivial)apply(rule,rule,erule conjE)
  unfolding split_def apply(subst scaleR_left.setsum[THEN sym, unfolded o_def])
  defer apply(subst additive_content_tagged_division[unfolded split_def]) apply assumption by auto

subsection {* Bounds on the norm of Riemann sums and the integral itself. *}

lemma dsum_bound: assumes "p division_of {a..b}" "norm(c) \<le> e"
  shows "norm(setsum (\<lambda>l. content l *\<^sub>R c) p) \<le> e * content({a..b})" (is "?l \<le> ?r")
  apply(rule order_trans,rule norm_setsum) unfolding norm_scaleR setsum_left_distrib[THEN sym]
  apply(rule order_trans[OF mult_left_mono],rule assms,rule setsum_abs_ge_zero)
  apply(subst mult_commute) apply(rule mult_left_mono)
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
    apply(rule order_trans,rule norm_setsum) unfolding split_def norm_scaleR
    apply(rule order_trans[OF setsum_mono]) apply(rule mult_left_mono[OF _ abs_ge_zero, of _ e]) defer
    unfolding setsum_left_distrib[THEN sym] apply(subst mult_commute) apply(rule mult_left_mono)
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
  qed qed

lemma rsum_diff_bound:
  assumes "p tagged_division_of {a..b}"  "\<forall>x\<in>{a..b}. norm(f x - g x) \<le> e"
  shows "norm(setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - setsum (\<lambda>(x,k). content k *\<^sub>R g x) p) \<le> e * content({a..b})"
  apply(rule order_trans[OF _ rsum_bound[OF assms]]) apply(rule eq_refl) apply(rule arg_cong[where f=norm])
  unfolding setsum_subtractf[THEN sym] apply(rule setsum_cong2) unfolding scaleR_diff_right by auto

lemma has_integral_bound: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::real_normed_vector"
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

lemma rsum_component_le: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "p tagged_division_of {a..b}"  "\<forall>x\<in>{a..b}. (f x)$$i \<le> (g x)$$i"
  shows "(setsum (\<lambda>(x,k). content k *\<^sub>R f x) p)$$i \<le> (setsum (\<lambda>(x,k). content k *\<^sub>R g x) p)$$i"
  unfolding  euclidean_component_setsum apply(rule setsum_mono) apply safe
proof- fix a b assume ab:"(a,b) \<in> p" note assm = tagged_division_ofD(2-4)[OF assms(1) ab]
  from this(3) guess u v apply-by(erule exE)+ note b=this
  show "(content b *\<^sub>R f a) $$ i \<le> (content b *\<^sub>R g a) $$ i" unfolding b
    unfolding euclidean_simps real_scaleR_def apply(rule mult_left_mono)
    defer apply(rule content_pos_le,rule assms(2)[rule_format]) using assm by auto qed

lemma has_integral_component_le: fixes f g::"'a::ordered_euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "(f has_integral i) s" "(g has_integral j) s"  "\<forall>x\<in>s. (f x)$$k \<le> (g x)$$k"
  shows "i$$k \<le> j$$k"
proof- have lem:"\<And>a b i (j::'b). \<And>g f::'a \<Rightarrow> 'b. (f has_integral i) ({a..b}) \<Longrightarrow> 
    (g has_integral j) ({a..b}) \<Longrightarrow> \<forall>x\<in>{a..b}. (f x)$$k \<le> (g x)$$k \<Longrightarrow> i$$k \<le> j$$k"
  proof(rule ccontr) case goal1 hence *:"0 < (i$$k - j$$k) / 3" by auto
    guess d1 using goal1(1)[unfolded has_integral,rule_format,OF *] apply-by(erule exE conjE)+ note d1=this[rule_format]
    guess d2 using goal1(2)[unfolded has_integral,rule_format,OF *] apply-by(erule exE conjE)+ note d2=this[rule_format]
    guess p using fine_division_exists[OF gauge_inter[OF d1(1) d2(1)], of a b] unfolding fine_inter .
    note p = this(1) conjunctD2[OF this(2)]  note le_less_trans[OF component_le_norm, of _ _ k] term g
    note this[OF d1(2)[OF conjI[OF p(1,2)]]] this[OF d2(2)[OF conjI[OF p(1,3)]]]
    thus False unfolding euclidean_simps using rsum_component_le[OF p(1) goal1(3)] apply simp by smt
  qed let ?P = "\<exists>a b. s = {a..b}"
  { presume "\<not> ?P \<Longrightarrow> ?thesis" thus ?thesis proof(cases ?P)
      case True then guess a b apply-by(erule exE)+ note s=this
      show ?thesis apply(rule lem) using assms[unfolded s] by auto
    qed auto } assume as:"\<not> ?P"
  { presume "\<not> ?thesis \<Longrightarrow> False" thus ?thesis by auto }
  assume "\<not> i$$k \<le> j$$k" hence ij:"(i$$k - j$$k) / 3 > 0" by auto
  note has_integral_altD[OF _ as this] from this[OF assms(1)] this[OF assms(2)] guess B1 B2 . note B=this[rule_format]
  have "bounded (ball 0 B1 \<union> ball (0::'a) B2)" unfolding bounded_Un by(rule conjI bounded_ball)+
  from bounded_subset_closed_interval[OF this] guess a b apply- by(erule exE)+
  note ab = conjunctD2[OF this[unfolded Un_subset_iff]]
  guess w1 using B(2)[OF ab(1)] .. note w1=conjunctD2[OF this]
  guess w2 using B(4)[OF ab(2)] .. note w2=conjunctD2[OF this]
  have *:"\<And>w1 w2 j i::real .\<bar>w1 - i\<bar> < (i - j) / 3 \<Longrightarrow> \<bar>w2 - j\<bar> < (i - j) / 3 \<Longrightarrow> w1 \<le> w2 \<Longrightarrow> False" by smt
  note le_less_trans[OF component_le_norm[of _ k]] note this[OF w1(2)] this[OF w2(2)] moreover
  have "w1$$k \<le> w2$$k" apply(rule lem[OF w1(1) w2(1)]) using assms by auto ultimately
  show False unfolding euclidean_simps by(rule *) qed

lemma integral_component_le: fixes g f::"'a::ordered_euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on s" "g integrable_on s"  "\<forall>x\<in>s. (f x)$$k \<le> (g x)$$k"
  shows "(integral s f)$$k \<le> (integral s g)$$k"
  apply(rule has_integral_component_le) using integrable_integral assms by auto

(*lemma has_integral_dest_vec1_le: fixes f::"'a::ordered_euclidean_space \<Rightarrow> real^1"
  assumes "(f has_integral i) s"  "(g has_integral j) s" "\<forall>x\<in>s. f x \<le> g x"
  shows "dest_vec1 i \<le> dest_vec1 j" apply(rule has_integral_component_le[OF assms(1-2)])
  using assms(3) unfolding vector_le_def by auto

lemma integral_dest_vec1_le: fixes f::"real^'n \<Rightarrow> real^1"
  assumes "f integrable_on s" "g integrable_on s" "\<forall>x\<in>s. f x \<le> g x"
  shows "dest_vec1(integral s f) \<le> dest_vec1(integral s g)"
  apply(rule has_integral_dest_vec1_le) apply(rule_tac[1-2] integrable_integral) using assms by auto*)

lemma has_integral_component_nonneg: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "(f has_integral i) s" "\<forall>x\<in>s. 0 \<le> (f x)$$k" shows "0 \<le> i$$k" 
  using has_integral_component_le[OF has_integral_0 assms(1)] using assms(2-) by auto

lemma integral_component_nonneg: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on s" "\<forall>x\<in>s. 0 \<le> (f x)$$k" shows "0 \<le> (integral s f)$$k"
  apply(rule has_integral_component_nonneg) using assms by auto

(*lemma has_integral_dest_vec1_nonneg: fixes f::"real^'n \<Rightarrow> real^1"
  assumes "(f has_integral i) s" "\<forall>x\<in>s. 0 \<le> f x" shows "0 \<le> i"
  using has_integral_component_nonneg[OF assms(1), of 1]
  using assms(2) unfolding vector_le_def by auto

lemma integral_dest_vec1_nonneg: fixes f::"real^'n \<Rightarrow> real^1"
  assumes "f integrable_on s" "\<forall>x\<in>s. 0 \<le> f x" shows "0 \<le> integral s f"
  apply(rule has_integral_dest_vec1_nonneg) using assms by auto*)

lemma has_integral_component_neg: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::ordered_euclidean_space"
  assumes "(f has_integral i) s" "\<forall>x\<in>s. (f x)$$k \<le> 0"shows "i$$k \<le> 0" 
  using has_integral_component_le[OF assms(1) has_integral_0] assms(2-) by auto

(*lemma has_integral_dest_vec1_neg: fixes f::"real^'n \<Rightarrow> real^1"
  assumes "(f has_integral i) s" "\<forall>x\<in>s. f x \<le> 0" shows "i \<le> 0"
  using has_integral_component_neg[OF assms(1),of 1] using assms(2) by auto*)

lemma has_integral_component_lbound: fixes f::"'a::ordered_euclidean_space => 'b::ordered_euclidean_space"
  assumes "(f has_integral i) {a..b}"  "\<forall>x\<in>{a..b}. B \<le> f(x)$$k" "k<DIM('b)" shows "B * content {a..b} \<le> i$$k"
  using has_integral_component_le[OF has_integral_const assms(1),of "(\<chi>\<chi> i. B)::'b" k] assms(2-)
  unfolding euclidean_simps euclidean_lambda_beta'[OF assms(3)] by(auto simp add:field_simps)

lemma has_integral_component_ubound: fixes f::"'a::ordered_euclidean_space => 'b::ordered_euclidean_space"
  assumes "(f has_integral i) {a..b}" "\<forall>x\<in>{a..b}. f x$$k \<le> B" "k<DIM('b)"
  shows "i$$k \<le> B * content({a..b})"
  using has_integral_component_le[OF assms(1) has_integral_const, of k "\<chi>\<chi> i. B"]
  unfolding euclidean_simps euclidean_lambda_beta'[OF assms(3)] using assms(2) by(auto simp add:field_simps)

lemma integral_component_lbound: fixes f::"'a::ordered_euclidean_space => 'b::ordered_euclidean_space"
  assumes "f integrable_on {a..b}" "\<forall>x\<in>{a..b}. B \<le> f(x)$$k" "k<DIM('b)"
  shows "B * content({a..b}) \<le> (integral({a..b}) f)$$k"
  apply(rule has_integral_component_lbound) using assms unfolding has_integral_integral by auto

lemma integral_component_ubound: fixes f::"'a::ordered_euclidean_space => 'b::ordered_euclidean_space"
  assumes "f integrable_on {a..b}" "\<forall>x\<in>{a..b}. f(x)$$k \<le> B" "k<DIM('b)" 
  shows "(integral({a..b}) f)$$k \<le> B * content({a..b})"
  apply(rule has_integral_component_ubound) using assms unfolding has_integral_integral by auto

subsection {* Uniform limit of integrable functions is integrable. *}

lemma integrable_uniform_limit: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::banach"
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
          using norm_triangle_ineq[of "s1 - s2" "s2 - i2"] by(auto simp add:algebra_simps)
        also have "\<dots> < e" using goal1 unfolding norm_minus_commute by(auto simp add:algebra_simps)
        finally show ?case .
      qed
      show ?case unfolding dist_norm apply(rule lem2) defer
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
        also have "\<dots> = 2 / real M" unfolding divide_inverse by auto
        finally show "norm (g n x - g m x) \<le> 2 / real M"
          using norm_triangle_le[of "g n x - f x" "f x - g m x" "2 / real M"]
          by(auto simp add:algebra_simps simp add:norm_minus_commute)
      qed qed qed
  from this[unfolded convergent_eq_cauchy[THEN sym]] guess s .. note s=this

  show ?thesis unfolding integrable_on_def apply(rule_tac x=s in exI) unfolding has_integral
  proof(rule,rule)  
    case goal1 hence *:"e/3 > 0" by auto
    from LIMSEQ_D [OF s this] guess N1 .. note N1=this
    from goal1 as have "e / 3 / content {a..b} > 0" by(auto simp add:field_simps)
    from real_arch_invD[OF this] guess N2 apply-by(erule exE conjE)+ note N2=this
    from i[of "N1 + N2",unfolded has_integral,rule_format,OF *] guess g' .. note g'=conjunctD2[OF this,rule_format]
    have lem:"\<And>sf sg i. norm(sf - sg) \<le> e / 3 \<Longrightarrow> norm(i - s) < e / 3 \<Longrightarrow> norm(sg - i) < e / 3 \<Longrightarrow> norm(sf - s) < e"
    proof- case goal1 have "norm (sf - s) \<le> norm (sf - sg) + norm (sg - i) + norm (i - s)"
        using norm_triangle_ineq[of "sf - sg" "sg - s"]
        using norm_triangle_ineq[of "sg -  i" " i - s"] by(auto simp add:algebra_simps)
      also have "\<dots> < e" using goal1 unfolding norm_minus_commute by(auto simp add:algebra_simps)
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
        show "norm (i (N1 + N2) - s) < e / 3" by(rule N1[rule_format],auto)
      qed qed qed qed

subsection {* Negligible sets. *}

definition "negligible (s::('a::ordered_euclidean_space) set) \<equiv> (\<forall>a b. ((indicator s :: 'a\<Rightarrow>real) has_integral 0) {a..b})"

subsection {* Negligibility of hyperplane. *}

lemma vsum_nonzero_image_lemma: 
  assumes "finite s" "g(a) = 0"
  "\<forall>x\<in>s. \<forall>y\<in>s. f x = f y \<and> x \<noteq> y \<longrightarrow> g(f x) = 0"
  shows "setsum g {f x |x. x \<in> s \<and> f x \<noteq> a} = setsum (g o f) s"
  unfolding setsum_iterate[OF assms(1)] apply(subst setsum_iterate) defer
  apply(rule iterate_nonzero_image_lemma) apply(rule assms monoidal_monoid)+
  unfolding assms using neutral_add unfolding neutral_add using assms by auto 

lemma interval_doublesplit:  fixes a::"'a::ordered_euclidean_space" assumes "k<DIM('a)"
  shows "{a..b} \<inter> {x . abs(x$$k - c) \<le> (e::real)} = 
  {(\<chi>\<chi> i. if i = k then max (a$$k) (c - e) else a$$i) .. (\<chi>\<chi> i. if i = k then min (b$$k) (c + e) else b$$i)}"
proof- have *:"\<And>x c e::real. abs(x - c) \<le> e \<longleftrightarrow> x \<ge> c - e \<and> x \<le> c + e" by auto
  have **:"\<And>s P Q. s \<inter> {x. P x \<and> Q x} = (s \<inter> {x. Q x}) \<inter> {x. P x}" by blast
  show ?thesis unfolding * ** interval_split[OF assms] by(rule refl) qed

lemma division_doublesplit: fixes a::"'a::ordered_euclidean_space" assumes "p division_of {a..b}" and k:"k<DIM('a)"
  shows "{l \<inter> {x. abs(x$$k - c) \<le> e} |l. l \<in> p \<and> l \<inter> {x. abs(x$$k - c) \<le> e} \<noteq> {}} division_of ({a..b} \<inter> {x. abs(x$$k - c) \<le> e})"
proof- have *:"\<And>x c. abs(x - c) \<le> e \<longleftrightarrow> x \<ge> c - e \<and> x \<le> c + e" by auto
  have **:"\<And>p q p' q'. p division_of q \<Longrightarrow> p = p' \<Longrightarrow> q = q' \<Longrightarrow> p' division_of q'" by auto
  note division_split(1)[OF assms, where c="c+e",unfolded interval_split[OF k]]
  note division_split(2)[OF this, where c="c-e" and k=k,OF k] 
  thus ?thesis apply(rule **) using k apply- unfolding interval_doublesplit unfolding * unfolding interval_split interval_doublesplit
    apply(rule set_eqI) unfolding mem_Collect_eq apply rule apply(erule conjE exE)+ apply(rule_tac x=la in exI) defer
    apply(erule conjE exE)+ apply(rule_tac x="l \<inter> {x. c + e \<ge> x $$ k}" in exI) apply rule defer apply rule
    apply(rule_tac x=l in exI) by blast+ qed

lemma content_doublesplit: fixes a::"'a::ordered_euclidean_space" assumes "0 < e" and k:"k<DIM('a)"
  obtains d where "0 < d" "content({a..b} \<inter> {x. abs(x$$k - c) \<le> d}) < e"
proof(cases "content {a..b} = 0")
  case True show ?thesis apply(rule that[of 1]) defer unfolding interval_doublesplit[OF k]
    apply(rule le_less_trans[OF content_subset]) defer apply(subst True)
    unfolding interval_doublesplit[THEN sym,OF k] using assms by auto 
next case False def d \<equiv> "e / 3 / setprod (\<lambda>i. b$$i - a$$i) ({..<DIM('a)} - {k})"
  note False[unfolded content_eq_0 not_ex not_le, rule_format]
  hence "\<And>x. x<DIM('a) \<Longrightarrow> b$$x > a$$x" by(auto simp add:not_le)
  hence prod0:"0 < setprod (\<lambda>i. b$$i - a$$i) ({..<DIM('a)} - {k})" apply-apply(rule setprod_pos) by(auto simp add:field_simps)
  hence "d > 0" unfolding d_def using assms by(auto simp add:field_simps) thus ?thesis
  proof(rule that[of d]) have *:"{..<DIM('a)} = insert k ({..<DIM('a)} - {k})" using k by auto
    have **:"{a..b} \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d} \<noteq> {} \<Longrightarrow> 
      (\<Prod>i\<in>{..<DIM('a)} - {k}. interval_upperbound ({a..b} \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d}) $$ i
      - interval_lowerbound ({a..b} \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d}) $$ i)
      = (\<Prod>i\<in>{..<DIM('a)} - {k}. b$$i - a$$i)" apply(rule setprod_cong,rule refl) 
      unfolding interval_doublesplit[OF k] apply(subst interval_bounds) defer apply(subst interval_bounds)
      unfolding interval_eq_empty not_ex not_less by auto
    show "content ({a..b} \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d}) < e" apply(cases) unfolding content_def apply(subst if_P,assumption,rule assms)
      unfolding if_not_P apply(subst *) apply(subst setprod_insert) unfolding **
      unfolding interval_doublesplit[OF k] interval_eq_empty not_ex not_less prefer 3
      apply(subst interval_bounds) defer apply(subst interval_bounds) unfolding euclidean_lambda_beta'[OF k] if_P[OF refl]
    proof- have "(min (b $$ k) (c + d) - max (a $$ k) (c - d)) \<le> 2 * d" by auto
      also have "... < e / (\<Prod>i\<in>{..<DIM('a)} - {k}. b $$ i - a $$ i)" unfolding d_def using assms prod0 by(auto simp add:field_simps)
      finally show "(min (b $$ k) (c + d) - max (a $$ k) (c - d)) * (\<Prod>i\<in>{..<DIM('a)} - {k}. b $$ i - a $$ i) < e"
        unfolding pos_less_divide_eq[OF prod0] . qed auto qed qed

lemma negligible_standard_hyperplane[intro]: fixes type::"'a::ordered_euclidean_space" assumes k:"k<DIM('a)"
  shows "negligible {x::'a. x$$k = (c::real)}" 
  unfolding negligible_def has_integral apply(rule,rule,rule,rule)
proof-
  case goal1 from content_doublesplit[OF this k,of a b c] guess d . note d=this
  let ?i = "indicator {x::'a. x$$k = c} :: 'a\<Rightarrow>real"
  show ?case apply(rule_tac x="\<lambda>x. ball x d" in exI) apply(rule,rule gauge_ball,rule d)
  proof(rule,rule) fix p assume p:"p tagged_division_of {a..b} \<and> (\<lambda>x. ball x d) fine p"
    have *:"(\<Sum>(x, ka)\<in>p. content ka *\<^sub>R ?i x) = (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. abs(x$$k - c) \<le> d}) *\<^sub>R ?i x)"
      apply(rule setsum_cong2) unfolding split_paired_all real_scaleR_def mult_cancel_right split_conv
      apply(cases,rule disjI1,assumption,rule disjI2)
    proof- fix x l assume as:"(x,l)\<in>p" "?i x \<noteq> 0" hence xk:"x$$k = c" unfolding indicator_def apply-by(rule ccontr,auto)
      show "content l = content (l \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d})" apply(rule arg_cong[where f=content])
        apply(rule set_eqI,rule,rule) unfolding mem_Collect_eq
      proof- fix y assume y:"y\<in>l" note p[THEN conjunct2,unfolded fine_def,rule_format,OF as(1),unfolded split_conv]
        note this[unfolded subset_eq mem_ball dist_norm,rule_format,OF y] note le_less_trans[OF component_le_norm[of _ k] this]
        thus "\<bar>y $$ k - c\<bar> \<le> d" unfolding euclidean_simps xk by auto
      qed auto qed
    note p'= tagged_division_ofD[OF p[THEN conjunct1]] and p''=division_of_tagged_division[OF p[THEN conjunct1]]
    show "norm ((\<Sum>(x, ka)\<in>p. content ka *\<^sub>R ?i x) - 0) < e" unfolding diff_0_right * unfolding real_scaleR_def real_norm_def
      apply(subst abs_of_nonneg) apply(rule setsum_nonneg,rule) unfolding split_paired_all split_conv
      apply(rule mult_nonneg_nonneg) apply(drule p'(4)) apply(erule exE)+ apply(rule_tac b=b in back_subst)
      prefer 2 apply(subst(asm) eq_commute) apply assumption
      apply(subst interval_doublesplit[OF k]) apply(rule content_pos_le) apply(rule indicator_pos_le)
    proof- have "(\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d}) * ?i x) \<le> (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d}))"
        apply(rule setsum_mono) unfolding split_paired_all split_conv 
        apply(rule mult_right_le_one_le) apply(drule p'(4)) by(auto simp add:interval_doublesplit[OF k])
      also have "... < e" apply(subst setsum_over_tagged_division_lemma[OF p[THEN conjunct1]])
      proof- case goal1 have "content ({u..v} \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d}) \<le> content {u..v}"
          unfolding interval_doublesplit[OF k] apply(rule content_subset) unfolding interval_doublesplit[THEN sym,OF k] by auto
        thus ?case unfolding goal1 unfolding interval_doublesplit[OF k] using content_pos_le by smt
      next have *:"setsum content {l \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d} |l. l \<in> snd ` p \<and> l \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d} \<noteq> {}} \<ge> 0"
          apply(rule setsum_nonneg,rule) unfolding mem_Collect_eq image_iff apply(erule exE bexE conjE)+ unfolding split_paired_all 
        proof- fix x l a b assume as:"x = l \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d}" "(a, b) \<in> p" "l = snd (a, b)"
          guess u v using p'(4)[OF as(2)] apply-by(erule exE)+ note * = this
          show "content x \<ge> 0" unfolding as snd_conv * interval_doublesplit[OF k] by(rule content_pos_le)
        qed have **:"norm (1::real) \<le> 1" by auto note division_doublesplit[OF p'' k,unfolded interval_doublesplit[OF k]]
        note dsum_bound[OF this **,unfolded interval_doublesplit[THEN sym,OF k]]
        note this[unfolded real_scaleR_def real_norm_def mult_1_right mult_1, of c d] note le_less_trans[OF this d(2)]
        from this[unfolded abs_of_nonneg[OF *]] show "(\<Sum>ka\<in>snd ` p. content (ka \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d})) < e"
          apply(subst vsum_nonzero_image_lemma[of "snd ` p" content "{}", unfolded o_def,THEN sym])
          apply(rule finite_imageI p' content_empty)+ unfolding forall_in_division[OF p'']
        proof(rule,rule,rule,rule,rule,rule,rule,erule conjE) fix m n u v
          assume as:"{m..n} \<in> snd ` p" "{u..v} \<in> snd ` p" "{m..n} \<noteq> {u..v}"  "{m..n} \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d} = {u..v} \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d}"
          have "({m..n} \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d}) \<inter> ({u..v} \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d}) \<subseteq> {m..n} \<inter> {u..v}" by blast
          note interior_mono[OF this, unfolded division_ofD(5)[OF p'' as(1-3)] interior_inter[of "{m..n}"]]
          hence "interior ({m..n} \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d}) = {}" unfolding as Int_absorb by auto
          thus "content ({m..n} \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d}) = 0" unfolding interval_doublesplit[OF k] content_eq_0_interior[THEN sym] .
        qed qed
      finally show "(\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. \<bar>x $$ k - c\<bar> \<le> d}) * ?i x) < e" .
    qed qed qed

subsection {* A technical lemma about "refinement" of division. *}

lemma tagged_division_finer: fixes p::"(('a::ordered_euclidean_space) \<times> (('a::ordered_euclidean_space) set)) set"
  assumes "p tagged_division_of {a..b}" "gauge d"
  obtains q where "q tagged_division_of {a..b}" "d fine q" "\<forall>(x,k) \<in> p. k \<subseteq> d(x) \<longrightarrow> (x,k) \<in> q"
proof-
  let ?P = "\<lambda>p. p tagged_partial_division_of {a..b} \<longrightarrow> gauge d \<longrightarrow>
    (\<exists>q. q tagged_division_of (\<Union>{k. \<exists>x. (x,k) \<in> p}) \<and> d fine q \<and>
                   (\<forall>(x,k) \<in> p. k \<subseteq> d(x) \<longrightarrow> (x,k) \<in> q))"
  { have *:"finite p" "p tagged_partial_division_of {a..b}" using assms(1) unfolding tagged_division_of_def by auto
    presume "\<And>p. finite p \<Longrightarrow> ?P p" from this[rule_format,OF * assms(2)] guess q .. note q=this
    thus ?thesis apply-apply(rule that[of q]) unfolding tagged_division_ofD[OF assms(1)] by auto
  } fix p::"(('a::ordered_euclidean_space) \<times> (('a::ordered_euclidean_space) set)) set" assume as:"finite p"
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

lemma has_integral_negligible: fixes f::"'b::ordered_euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "negligible s" "\<forall>x\<in>(t - s). f x = 0"
  shows "(f has_integral 0) t"
proof- presume P:"\<And>f::'b::ordered_euclidean_space \<Rightarrow> 'a. \<And>a b. (\<forall>x. ~(x \<in> s) \<longrightarrow> f x = 0) \<Longrightarrow> (f has_integral 0) ({a..b})"
  let ?f = "(\<lambda>x. if x \<in> t then f x else 0)"
  show ?thesis apply(rule_tac f="?f" in has_integral_eq) apply(rule) unfolding if_P apply(rule refl)
    apply(subst has_integral_alt) apply(cases,subst if_P,assumption) unfolding if_not_P
  proof- assume "\<exists>a b. t = {a..b}" then guess a b apply-by(erule exE)+ note t = this
    show "(?f has_integral 0) t" unfolding t apply(rule P) using assms(2) unfolding t by auto
  next show "\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> {a..b} \<longrightarrow> (\<exists>z. ((\<lambda>x. if x \<in> t then ?f x else 0) has_integral z) {a..b} \<and> norm (z - 0) < e)"
      apply(safe,rule_tac x=1 in exI,rule) apply(rule zero_less_one,safe) apply(rule_tac x=0 in exI)
      apply(rule,rule P) using assms(2) by auto
  qed
next fix f::"'b \<Rightarrow> 'a" and a b::"'b" assume assm:"\<forall>x. x \<notin> s \<longrightarrow> f x = 0" 
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
      have *:"\<And>i. (\<Sum>(x, k)\<in>q i. content k *\<^sub>R indicator s x) \<ge> (0::real)" apply(rule setsum_nonneg,safe) 
        unfolding real_scaleR_def apply(rule mult_nonneg_nonneg) apply(drule tagged_division_ofD(4)[OF q(1)]) by auto
      have **:"\<And>f g s t. finite s \<Longrightarrow> finite t \<Longrightarrow> (\<forall>(x,y) \<in> t. (0::real) \<le> g(x,y)) \<Longrightarrow> (\<forall>y\<in>s. \<exists>x. (x,y) \<in> t \<and> f(y) \<le> g(x,y)) \<Longrightarrow> setsum f s \<le> setsum g t"
      proof- case goal1 thus ?case apply-apply(rule setsum_le_included[of s t g snd f]) prefer 4
          apply safe apply(erule_tac x=x in ballE) apply(erule exE) apply(rule_tac x="(xa,x)" in bexI) by auto qed
      have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) \<le> setsum (\<lambda>i. (real i + 1) *
                     norm(setsum (\<lambda>(x,k). content k *\<^sub>R indicator s x :: real) (q i))) {0..N+1}"
        unfolding real_norm_def setsum_right_distrib abs_of_nonneg[OF *] diff_0_right
        apply(rule order_trans,rule norm_setsum) apply(subst sum_sum_product) prefer 3 
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
      qed also have "... < e * inverse 2 * 2" unfolding divide_inverse setsum_right_distrib[THEN sym]
        apply(rule mult_strict_left_mono) unfolding power_inverse atLeastLessThanSuc_atLeastAtMost[THEN sym]
        apply(subst sumr_geometric) using goal1 by auto
      finally show "?goal" by auto qed qed qed

lemma has_integral_spike: fixes f::"'b::ordered_euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "negligible s" "(\<forall>x\<in>(t - s). g x = f x)" "(f has_integral y) t"
  shows "(g has_integral y) t"
proof- { fix a b::"'b" and f g ::"'b \<Rightarrow> 'a" and y::'a
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
  apply(rule,rule has_integral_spike) by fastforce+

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

lemma negligible_sing[intro]: "negligible {a::_::ordered_euclidean_space}" 
  using negligible_standard_hyperplane[of 0 "a$$0"] by auto 

lemma negligible_insert[simp]: "negligible(insert a s) \<longleftrightarrow> negligible s"
  apply(subst insert_is_Un) unfolding negligible_union_eq by auto

lemma negligible_empty[intro]: "negligible {}" by auto

lemma negligible_finite[intro]: assumes "finite s" shows "negligible s"
  using assms apply(induct s) by auto

lemma negligible_unions[intro]: assumes "finite s" "\<forall>t\<in>s. negligible t" shows "negligible(\<Union>s)"
  using assms by(induct,auto) 

lemma negligible:  "negligible s \<longleftrightarrow> (\<forall>t::('a::ordered_euclidean_space) set. ((indicator s::'a\<Rightarrow>real) has_integral 0) t)"
  apply safe defer apply(subst negligible_def)
proof -
  fix t::"'a set" assume as:"negligible s"
  have *:"(\<lambda>x. if x \<in> s \<inter> t then 1 else 0) = (\<lambda>x. if x\<in>t then if x\<in>s then 1 else 0 else 0)"
    by auto
  show "((indicator s::'a\<Rightarrow>real) has_integral 0) t"
    apply(subst has_integral_alt)
    apply(cases,subst if_P,assumption)
    unfolding if_not_P
    apply(safe,rule as[unfolded negligible_def,rule_format])
    apply(rule_tac x=1 in exI)
    apply(safe,rule zero_less_one)
    apply(rule_tac x=0 in exI)
    using negligible_subset[OF as,of "s \<inter> t"]
    unfolding negligible_def indicator_def [abs_def]
    unfolding *
    apply auto
    done
qed auto

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

lemma negligible_frontier_interval: "negligible({a::'a::ordered_euclidean_space..b} - {a<..<b})"
proof- let ?A = "\<Union>((\<lambda>k. {x. x$$k = a$$k} \<union> {x::'a. x$$k = b$$k}) ` {..<DIM('a)})"
  have "{a..b} - {a<..<b} \<subseteq> ?A" apply rule unfolding Diff_iff mem_interval not_all
    apply(erule conjE exE)+ apply(rule_tac X="{x. x $$ xa = a $$ xa} \<union> {x. x $$ xa = b $$ xa}" in UnionI)
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

lemma operative_approximable: assumes "0 \<le> e" fixes f::"'b::ordered_euclidean_space \<Rightarrow> 'a::banach"
  shows "operative op \<and> (\<lambda>i. \<exists>g. (\<forall>x\<in>i. norm (f x - g (x::'b)) \<le> e) \<and> g integrable_on i)" unfolding operative_def neutral_and
proof safe fix a b::"'b" { assume "content {a..b} = 0"
    thus "\<exists>g. (\<forall>x\<in>{a..b}. norm (f x - g x) \<le> e) \<and> g integrable_on {a..b}" 
      apply(rule_tac x=f in exI) using assms by(auto intro!:integrable_on_null) }
  { fix c k g assume as:"\<forall>x\<in>{a..b}. norm (f x - g x) \<le> e" "g integrable_on {a..b}" and k:"k<DIM('b)"
    show "\<exists>g. (\<forall>x\<in>{a..b} \<inter> {x. x $$ k \<le> c}. norm (f x - g x) \<le> e) \<and> g integrable_on {a..b} \<inter> {x. x $$ k \<le> c}"
      "\<exists>g. (\<forall>x\<in>{a..b} \<inter> {x. c \<le> x $$ k}. norm (f x - g x) \<le> e) \<and> g integrable_on {a..b} \<inter> {x. c \<le> x $$ k}"
      apply(rule_tac[!] x=g in exI) using as(1) integrable_split[OF as(2) k] by auto }
  fix c k g1 g2 assume as:"\<forall>x\<in>{a..b} \<inter> {x. x $$ k \<le> c}. norm (f x - g1 x) \<le> e" "g1 integrable_on {a..b} \<inter> {x. x $$ k \<le> c}"
                          "\<forall>x\<in>{a..b} \<inter> {x. c \<le> x $$ k}. norm (f x - g2 x) \<le> e" "g2 integrable_on {a..b} \<inter> {x. c \<le> x $$ k}"
  assume k:"k<DIM('b)"
  let ?g = "\<lambda>x. if x$$k = c then f x else if x$$k \<le> c then g1 x else g2 x"
  show "\<exists>g. (\<forall>x\<in>{a..b}. norm (f x - g x) \<le> e) \<and> g integrable_on {a..b}" apply(rule_tac x="?g" in exI)
  proof safe case goal1 thus ?case apply- apply(cases "x$$k=c", case_tac "x$$k < c") using as assms by auto
  next case goal2 presume "?g integrable_on {a..b} \<inter> {x. x $$ k \<le> c}" "?g integrable_on {a..b} \<inter> {x. x $$ k \<ge> c}"
    then guess h1 h2 unfolding integrable_on_def by auto from has_integral_split[OF this k] 
    show ?case unfolding integrable_on_def by auto
  next show "?g integrable_on {a..b} \<inter> {x. x $$ k \<le> c}" "?g integrable_on {a..b} \<inter> {x. x $$ k \<ge> c}"
      apply(rule_tac[!] integrable_spike[OF negligible_standard_hyperplane[of k c]]) using k as(2,4) by auto qed qed

lemma approximable_on_division: fixes f::"'b::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "0 \<le> e" "d division_of {a..b}" "\<forall>i\<in>d. \<exists>g. (\<forall>x\<in>i. norm (f x - g x) \<le> e) \<and> g integrable_on i"
  obtains g where "\<forall>x\<in>{a..b}. norm (f x - g x) \<le> e" "g integrable_on {a..b}"
proof- note * = operative_division[OF monoidal_and operative_approximable[OF assms(1)] assms(2)]
  note this[unfolded iterate_and[OF division_of_finite[OF assms(2)]]] from assms(3)[unfolded this[of f]]
  guess g .. thus thesis apply-apply(rule that[of g]) by auto qed

lemma integrable_continuous: fixes f::"'b::ordered_euclidean_space \<Rightarrow> 'a::banach"
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
      thus "norm (f y - f x) \<le> e" using y p'(2-3)[OF as] unfolding dist_norm l norm_minus_commute by fastforce qed qed
  from e have "0 \<le> e" by auto from approximable_on_division[OF this division_of_tagged_division[OF p(1)] *] guess g .
  thus "\<exists>g. (\<forall>x\<in>{a..b}. norm (f x - g x) \<le> e) \<and> g integrable_on {a..b}" by auto qed 

subsection {* Specialization of additivity to one dimension. *}

lemma operative_1_lt: assumes "monoidal opp"
  shows "operative opp f \<longleftrightarrow> ((\<forall>a b. b \<le> a \<longrightarrow> f {a..b::real} = neutral opp) \<and>
                (\<forall>a b c. a < c \<and> c < b \<longrightarrow> opp (f{a..c})(f{c..b}) = f {a..b}))"
  unfolding operative_def content_eq_0 DIM_real less_one simp_thms(39,41) Eucl_real_simps
    (* The dnf_simps simplify "\<exists> x. x= _ \<and> _" and "\<forall>k. k = _ \<longrightarrow> _" *)
proof safe fix a b c::"real" assume as:"\<forall>a b c. f {a..b} = opp (f ({a..b} \<inter> {x. x \<le> c}))
    (f ({a..b} \<inter> {x. c \<le> x}))" "a < c" "c < b"
    from this(2-) have "{a..b} \<inter> {x. x \<le> c} = {a..c}" "{a..b} \<inter> {x. x \<ge> c} = {c..b}" by auto
    thus "opp (f {a..c}) (f {c..b}) = f {a..b}" unfolding as(1)[rule_format,of a b "c"] by auto
next fix a b c::real
  assume as:"\<forall>a b. b \<le> a \<longrightarrow> f {a..b} = neutral opp" "\<forall>a b c. a < c \<and> c < b \<longrightarrow> opp (f {a..c}) (f {c..b}) = f {a..b}"
  show "f {a..b} = opp (f ({a..b} \<inter> {x. x \<le> c})) (f ({a..b} \<inter> {x. c \<le> x}))"
  proof(cases "c \<in> {a .. b}")
    case False hence "c<a \<or> c>b" by auto
    thus ?thesis apply-apply(erule disjE)
    proof- assume "c<a" hence *:"{a..b} \<inter> {x. x \<le> c} = {1..0}"  "{a..b} \<inter> {x. c \<le> x} = {a..b}" by auto
      show ?thesis unfolding * apply(subst as(1)[rule_format,of 0 1]) using assms by auto
    next   assume "b<c" hence *:"{a..b} \<inter> {x. x \<le> c} = {a..b}"  "{a..b} \<inter> {x. c \<le> x} = {1..0}" by auto
      show ?thesis unfolding * apply(subst as(1)[rule_format,of 0 1]) using assms by auto
    qed
  next case True hence *:"min (b) c = c" "max a c = c" by auto
    have **:"0 < DIM(real)" by auto
    have ***:"\<And>P Q. (\<chi>\<chi> i. if i = 0 then P i else Q i) = (P 0::real)" apply(subst euclidean_eq)
      apply safe unfolding euclidean_lambda_beta' by auto
    show ?thesis unfolding interval_split[OF **,unfolded Eucl_real_simps(1,3)] unfolding *** *
    proof(cases "c = a \<or> c = b")
      case False thus "f {a..b} = opp (f {a..c}) (f {c..b})"
        apply-apply(subst as(2)[rule_format]) using True by auto
    next case True thus "f {a..b} = opp (f {a..c}) (f {c..b})" apply-
      proof(erule disjE) assume *:"c=a"
        hence "f {a..c} = neutral opp" apply-apply(rule as(1)[rule_format]) by auto
        thus ?thesis using assms unfolding * by auto
      next assume *:"c=b" hence "f {c..b} = neutral opp" apply-apply(rule as(1)[rule_format]) by auto
        thus ?thesis using assms unfolding * by auto qed qed qed qed

lemma operative_1_le: assumes "monoidal opp"
  shows "operative opp f \<longleftrightarrow> ((\<forall>a b. b \<le> a \<longrightarrow> f {a..b::real} = neutral opp) \<and>
                (\<forall>a b c. a \<le> c \<and> c \<le> b \<longrightarrow> opp (f{a..c})(f{c..b}) = f {a..b}))"
unfolding operative_1_lt[OF assms]
proof safe fix a b c::"real" assume as:"\<forall>a b c. a \<le> c \<and> c \<le> b \<longrightarrow> opp (f {a..c}) (f {c..b}) = f {a..b}" "a < c" "c < b"
  show "opp (f {a..c}) (f {c..b}) = f {a..b}" apply(rule as(1)[rule_format]) using as(2-) by auto
next fix a b c ::"real" assume "\<forall>a b. b \<le> a \<longrightarrow> f {a..b} = neutral opp"
    "\<forall>a b c. a < c \<and> c < b \<longrightarrow> opp (f {a..c}) (f {c..b}) = f {a..b}" "a \<le> c" "c \<le> b"
  note as = this[rule_format]
  show "opp (f {a..c}) (f {c..b}) = f {a..b}"
  proof(cases "c = a \<or> c = b")
    case False thus ?thesis apply-apply(subst as(2)) using as(3-) by(auto)
    next case True thus ?thesis apply-
      proof(erule disjE) assume *:"c=a" hence "f {a..c} = neutral opp" apply-apply(rule as(1)[rule_format]) by auto
        thus ?thesis using assms unfolding * by auto
      next               assume *:"c=b" hence "f {c..b} = neutral opp" apply-apply(rule as(1)[rule_format]) by auto
        thus ?thesis using assms unfolding * by auto qed qed qed 

subsection {* Special case of additivity we need for the FCT. *}

lemma interval_bound_sing[simp]: "interval_upperbound {a} = a"  "interval_lowerbound {a} = a"
  unfolding interval_upperbound_def interval_lowerbound_def  by auto

lemma additive_tagged_division_1: fixes f::"real \<Rightarrow> 'a::real_normed_vector"
  assumes "a \<le> b" "p tagged_division_of {a..b}"
  shows "setsum (\<lambda>(x,k). f(interval_upperbound k) - f(interval_lowerbound k)) p = f b - f a"
proof- let ?f = "(\<lambda>k::(real) set. if k = {} then 0 else f(interval_upperbound k) - f(interval_lowerbound k))"
  have ***:"\<forall>i<DIM(real). a $$ i \<le> b $$ i" using assms by auto 
  have *:"operative op + ?f" unfolding operative_1_lt[OF monoidal_monoid] interval_eq_empty by auto
  have **:"{a..b} \<noteq> {}" using assms(1) by auto note operative_tagged_division[OF monoidal_monoid * assms(2)]
  note * = this[unfolded if_not_P[OF **] interval_bounds[OF ***],THEN sym]
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

lemma interval_bounds_real: assumes "a\<le>(b::real)"
  shows "interval_upperbound {a..b} = b" "interval_lowerbound {a..b} = a"
  apply(rule_tac[!] interval_bounds) using assms by auto

lemma fundamental_theorem_of_calculus: fixes f::"real \<Rightarrow> 'a::banach"
  assumes "a \<le> b"  "\<forall>x\<in>{a..b}. (f has_vector_derivative f' x) (at x within {a..b})"
  shows "(f' has_integral (f b - f a)) ({a..b})"
unfolding has_integral_factor_content
proof safe fix e::real assume e:"e>0"
  note assm = assms(2)[unfolded has_vector_derivative_def has_derivative_within_alt]
  have *:"\<And>P Q. \<forall>x\<in>{a..b}. P x \<and> (\<forall>e>0. \<exists>d>0. Q x e d) \<Longrightarrow> \<forall>x. \<exists>(d::real)>0. x\<in>{a..b} \<longrightarrow> Q x e d" using e by blast
  note this[OF assm,unfolded gauge_existence_lemma] from choice[OF this,unfolded Ball_def[symmetric]]
  guess d .. note d=conjunctD2[OF this[rule_format],rule_format]
  show "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a..b} \<and> d fine p \<longrightarrow>
                 norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f' x) - (f b - f a)) \<le> e * content {a..b})"
    apply(rule_tac x="\<lambda>x. ball x (d x)" in exI,safe)
    apply(rule gauge_ball_dependent,rule,rule d(1))
  proof- fix p assume as:"p tagged_division_of {a..b}" "(\<lambda>x. ball x (d x)) fine p"
    show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f' x) - (f b - f a)) \<le> e * content {a..b}" 
      unfolding content_real[OF assms(1)] additive_tagged_division_1[OF assms(1) as(1),of f,THEN sym]
      unfolding additive_tagged_division_1[OF assms(1) as(1),of "\<lambda>x. x",THEN sym]
      unfolding setsum_right_distrib defer unfolding setsum_subtractf[THEN sym] 
    proof(rule setsum_norm_le,safe) fix x k assume "(x,k)\<in>p"
      note xk = tagged_division_ofD(2-4)[OF as(1) this] from this(3) guess u v apply-by(erule exE)+ note k=this
      have *:"u \<le> v" using xk unfolding k by auto
      have ball:"\<forall>xa\<in>k. xa \<in> ball x (d x)" using as(2)[unfolded fine_def,rule_format,OF `(x,k)\<in>p`,
        unfolded split_conv subset_eq] .
      have "norm ((v - u) *\<^sub>R f' x - (f v - f u)) \<le>
        norm (f u - f x - (u - x) *\<^sub>R f' x) + norm (f v - f x - (v - x) *\<^sub>R f' x)"
        apply(rule order_trans[OF _ norm_triangle_ineq4]) apply(rule eq_refl) apply(rule arg_cong[where f=norm])
        unfolding scaleR_diff_left by(auto simp add:algebra_simps)
      also have "... \<le> e * norm (u - x) + e * norm (v - x)"
        apply(rule add_mono) apply(rule d(2)[of "x" "u",unfolded o_def]) prefer 4
        apply(rule d(2)[of "x" "v",unfolded o_def])
        using ball[rule_format,of u] ball[rule_format,of v] 
        using xk(1-2) unfolding k subset_eq by(auto simp add:dist_real_def) 
      also have "... \<le> e * (interval_upperbound k - interval_lowerbound k)"
        unfolding k interval_bounds_real[OF *] using xk(1) unfolding k by(auto simp add:dist_real_def field_simps)
      finally show "norm (content k *\<^sub>R f' x - (f (interval_upperbound k) - f (interval_lowerbound k))) \<le>
        e * (interval_upperbound k - interval_lowerbound k)" unfolding k interval_bounds_real[OF *] content_real[OF *] .
    qed qed qed

subsection {* Attempt a systematic general set of "offset" results for components. *}

lemma gauge_modify:
  assumes "(\<forall>s. open s \<longrightarrow> open {x. f(x) \<in> s})" "gauge d"
  shows "gauge (\<lambda>x. {y. f y \<in> d (f x)})"
  using assms unfolding gauge_def apply safe defer apply(erule_tac x="f x" in allE)
  apply(erule_tac x="d (f x)" in allE) by auto

subsection {* Only need trivial subintervals if the interval itself is trivial. *}

lemma division_of_nontrivial: fixes s::"('a::ordered_euclidean_space) set set"
  assumes "s division_of {a..b}" "content({a..b}) \<noteq> 0"
  shows "{k. k \<in> s \<and> content k \<noteq> 0} division_of {a..b}" using assms(1) apply-
proof(induct "card s" arbitrary:s rule:nat_less_induct)
  fix s::"'a set set" assume assm:"s division_of {a..b}"
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
    hence i:"c$$i = d$$i" "i<DIM('a)" using s(3)[OF k(1),unfolded k] unfolding interval_ne_empty by auto
    hence xi:"x$$i = d$$i" using as unfolding k mem_interval by smt
    def y \<equiv> "(\<chi>\<chi> j. if j = i then if c$$i \<le> (a$$i + b$$i) / 2 then c$$i +
      min e (b$$i - c$$i) / 2 else c$$i - min e (c$$i - a$$i) / 2 else x$$j)::'a"
    show "\<exists>x'\<in>\<Union>(s - {k}). x' \<noteq> x \<and> dist x' x < e" apply(rule_tac x=y in bexI) 
    proof have "d \<in> {c..d}" using s(3)[OF k(1)] unfolding k interval_eq_empty mem_interval by(fastforce simp add: not_less)
      hence "d \<in> {a..b}" using s(2)[OF k(1)] unfolding k by auto note di = this[unfolded mem_interval,THEN spec[where x=i]]
      hence xyi:"y$$i \<noteq> x$$i" unfolding y_def unfolding i xi euclidean_lambda_beta'[OF i(2)] if_P[OF refl]
        apply(cases) apply(subst if_P,assumption) unfolding if_not_P not_le using as(2)
        using assms(2)[unfolded content_eq_0] using i(2) by smt+ 
      thus "y \<noteq> x" unfolding euclidean_eq[where 'a='a] using i by auto
      have *:"{..<DIM('a)} = insert i ({..<DIM('a)} - {i})" using i by auto
      have "norm (y - x) < e + setsum (\<lambda>i. 0) {..<DIM('a)}" apply(rule le_less_trans[OF norm_le_l1])
        apply(subst *,subst setsum_insert) prefer 3 apply(rule add_less_le_mono)
      proof- show "\<bar>(y - x) $$ i\<bar> < e" unfolding y_def euclidean_simps euclidean_lambda_beta'[OF i(2)] if_P[OF refl]
          apply(cases) apply(subst if_P,assumption) unfolding if_not_P unfolding i xi using di as(2) by auto
        show "(\<Sum>i\<in>{..<DIM('a)} - {i}. \<bar>(y - x) $$ i\<bar>) \<le> (\<Sum>i\<in>{..<DIM('a)}. 0)" unfolding y_def by auto 
      qed auto thus "dist y x < e" unfolding dist_norm by auto
      have "y\<notin>k" unfolding k mem_interval apply rule apply(erule_tac x=i in allE) using xyi unfolding k i xi by auto
      moreover have "y \<in> \<Union>s" unfolding s mem_interval
      proof(rule,rule) note simps = y_def euclidean_lambda_beta' if_not_P
        fix j assume j:"j<DIM('a)" show "a $$ j \<le> y $$ j \<and> y $$ j \<le> b $$ j" 
        proof(cases "j = i") case False have "x \<in> {a..b}" using s(2)[OF k(1)] as(1) by auto
          thus ?thesis using j apply- unfolding simps if_not_P[OF False] unfolding mem_interval by auto
        next case True note T = this show ?thesis
          proof(cases "c $$ i \<le> (a $$ i + b $$ i) / 2")
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

subsection {* Integrability on subintervals. *}

lemma operative_integrable: fixes f::"'b::ordered_euclidean_space \<Rightarrow> 'a::banach" shows
  "operative op \<and> (\<lambda>i. f integrable_on i)"
  unfolding operative_def neutral_and apply safe apply(subst integrable_on_def)
  unfolding has_integral_null_eq apply(rule,rule refl) apply(rule,assumption,assumption)+
  unfolding integrable_on_def by(auto intro!: has_integral_split)

lemma integrable_subinterval: fixes f::"'b::ordered_euclidean_space \<Rightarrow> 'a::banach" 
  assumes "f integrable_on {a..b}" "{c..d} \<subseteq> {a..b}" shows "f integrable_on {c..d}" 
  apply(cases "{c..d} = {}") defer apply(rule partial_division_extend_1[OF assms(2)],assumption)
  using operative_division_and[OF operative_integrable,THEN sym,of _ _ _ f] assms(1) by auto

subsection {* Combining adjacent intervals in 1 dimension. *}

lemma has_integral_combine: assumes "(a::real) \<le> c" "c \<le> b"
  "(f has_integral i) {a..c}" "(f has_integral (j::'a::banach)) {c..b}"
  shows "(f has_integral (i + j)) {a..b}"
proof- note operative_integral[of f, unfolded operative_1_le[OF monoidal_lifted[OF monoidal_monoid]]]
  note conjunctD2[OF this,rule_format] note * = this(2)[OF conjI[OF assms(1-2)],unfolded if_P[OF assms(3)]]
  hence "f integrable_on {a..b}" apply- apply(rule ccontr) apply(subst(asm) if_P) defer
    apply(subst(asm) if_P) using assms(3-) by auto
  with * show ?thesis apply-apply(subst(asm) if_P) defer apply(subst(asm) if_P) defer apply(subst(asm) if_P)
    unfolding lifted.simps using assms(3-) by(auto simp add: integrable_on_def integral_unique) qed

lemma integral_combine: fixes f::"real \<Rightarrow> 'a::banach"
  assumes "a \<le> c" "c \<le> b" "f integrable_on ({a..b})"
  shows "integral {a..c} f + integral {c..b} f = integral({a..b}) f"
  apply(rule integral_unique[THEN sym]) apply(rule has_integral_combine[OF assms(1-2)])
  apply(rule_tac[!] integrable_integral integrable_subinterval[OF assms(3)])+ using assms(1-2) by auto

lemma integrable_combine: fixes f::"real \<Rightarrow> 'a::banach"
  assumes "a \<le> c" "c \<le> b" "f integrable_on {a..c}" "f integrable_on {c..b}"
  shows "f integrable_on {a..b}" using assms unfolding integrable_on_def by(fastforce intro!:has_integral_combine)

subsection {* Reduce integrability to "local" integrability. *}

lemma integrable_on_little_subintervals: fixes f::"'b::ordered_euclidean_space \<Rightarrow> 'a::banach"
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
  shows "((\<lambda>u. integral {a..u} f) has_vector_derivative f(x)) (at x within {a..b})"
  unfolding has_vector_derivative_def has_derivative_within_alt
apply safe apply(rule bounded_linear_scaleR_left)
proof- fix e::real assume e:"e>0"
  note compact_uniformly_continuous[OF assms(1) compact_interval,unfolded uniformly_continuous_on_def]
  from this[rule_format,OF e] guess d apply-by(erule conjE exE)+ note d=this[rule_format]
  let ?I = "\<lambda>a b. integral {a..b} f"
  show "\<exists>d>0. \<forall>y\<in>{a..b}. norm (y - x) < d \<longrightarrow> norm (?I a y - ?I a x - (y - x) *\<^sub>R f x) \<le> e * norm (y - x)"
  proof(rule,rule,rule d,safe) case goal1 show ?case proof(cases "y < x")
      case False have "f integrable_on {a..y}" apply(rule integrable_subinterval,rule integrable_continuous)
        apply(rule assms)  unfolding not_less using assms(2) goal1 by auto
      hence *:"?I a y - ?I a x = ?I x y" unfolding algebra_simps apply(subst eq_commute) apply(rule integral_combine)
        using False unfolding not_less using assms(2) goal1 by auto
      have **:"norm (y - x) = content {x..y}" apply(subst content_real) using False unfolding not_less by auto
      show ?thesis unfolding ** apply(rule has_integral_bound[where f="(\<lambda>u. f u - f x)"]) unfolding * unfolding o_def
        defer apply(rule has_integral_sub) apply(rule integrable_integral)
        apply(rule integrable_subinterval,rule integrable_continuous) apply(rule assms)+
      proof- show "{x..y} \<subseteq> {a..b}" using goal1 assms(2) by auto
        have *:"y - x = norm(y - x)" using False by auto
        show "((\<lambda>xa. f x) has_integral (y - x) *\<^sub>R f x) {x.. y}" apply(subst *) unfolding ** by auto
        show "\<forall>xa\<in>{x..y}. norm (f xa - f x) \<le> e" apply safe apply(rule less_imp_le)
          apply(rule d(2)[unfolded dist_norm]) using assms(2) using goal1 by auto
      qed(insert e,auto)
    next case True have "f integrable_on {a..x}" apply(rule integrable_subinterval,rule integrable_continuous)
        apply(rule assms)+  unfolding not_less using assms(2) goal1 by auto
      hence *:"?I a x - ?I a y = ?I y x" unfolding algebra_simps apply(subst eq_commute) apply(rule integral_combine)
        using True using assms(2) goal1 by auto
      have **:"norm (y - x) = content {y..x}" apply(subst content_real) using True unfolding not_less by auto
      have ***:"\<And>fy fx c::'a. fx - fy - (y - x) *\<^sub>R c = -(fy - fx - (x - y) *\<^sub>R c)" unfolding scaleR_left.diff by auto 
      show ?thesis apply(subst ***) unfolding norm_minus_cancel **
        apply(rule has_integral_bound[where f="(\<lambda>u. f u - f x)"]) unfolding * unfolding o_def
        defer apply(rule has_integral_sub) apply(subst minus_minus[THEN sym]) unfolding minus_minus
        apply(rule integrable_integral) apply(rule integrable_subinterval,rule integrable_continuous) apply(rule assms)+
      proof- show "{y..x} \<subseteq> {a..b}" using goal1 assms(2) by auto
        have *:"x - y = norm(y - x)" using True by auto
        show "((\<lambda>xa. f x) has_integral (x - y) *\<^sub>R f x) {y..x}" apply(subst *) unfolding ** by auto
        show "\<forall>xa\<in>{y..x}. norm (f xa - f x) \<le> e" apply safe apply(rule less_imp_le)
          apply(rule d(2)[unfolded dist_norm]) using assms(2) using goal1 by auto
      qed(insert e,auto) qed qed qed

lemma antiderivative_continuous: assumes "continuous_on {a..b::real} f"
  obtains g where "\<forall>x\<in> {a..b}. (g has_vector_derivative (f(x)::_::banach)) (at x within {a..b})"
  apply(rule that,rule) using integral_has_vector_derivative[OF assms] by auto

subsection {* Combined fundamental theorem of calculus. *}

lemma antiderivative_integral_continuous: fixes f::"real \<Rightarrow> 'a::banach" assumes "continuous_on {a..b} f"
  obtains g where "\<forall>u\<in>{a..b}. \<forall>v \<in> {a..b}. u \<le> v \<longrightarrow> (f has_integral (g v - g u)) {u..v}"
proof- from antiderivative_continuous[OF assms] guess g . note g=this
  show ?thesis apply(rule that[of g])
  proof safe case goal1 have "\<forall>x\<in>{u..v}. (g has_vector_derivative f x) (at x within {u..v})"
      apply(rule,rule has_vector_derivative_within_subset) apply(rule g[rule_format]) using goal1(1-2) by auto
    thus ?case using fundamental_theorem_of_calculus[OF goal1(3),of "g" "f"] by auto qed qed

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
    def d' \<equiv> "\<lambda>x. {y. g y \<in> d (g x)}" have d':"\<And>x. d' x = {y. g y \<in> (d (g x))}" unfolding d'_def ..
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
      qed note ** = d(2)[OF this] have *:"inj_on (\<lambda>(x, k). (g x, g ` k)) p" using inj(1) unfolding inj_on_def by fastforce
       have "(\<Sum>(x, k)\<in>(\<lambda>(x, k). (g x, g ` k)) ` p. content k *\<^sub>R f x) - i = r *\<^sub>R (\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - i" (is "?l = _") unfolding algebra_simps add_left_cancel
        unfolding setsum_reindex[OF *] apply(subst scaleR_right.setsum) defer apply(rule setsum_cong2) unfolding o_def split_paired_all split_conv
        apply(drule p(4)) apply safe unfolding assms(7)[rule_format] using p by auto
      also have "... = r *\<^sub>R ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - (1 / r) *\<^sub>R i)" (is "_ = ?r") unfolding scaleR_diff_right scaleR_scaleR
        using assms(1) by auto finally have *:"?l = ?r" .
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - (1 / r) *\<^sub>R i) < e" using ** unfolding * unfolding norm_scaleR
        using assms(1) by(auto simp add:field_simps) qed qed qed

subsection {* Special case of a basic affine transformation. *}

lemma interval_image_affinity_interval: shows "\<exists>u v. (\<lambda>x. m *\<^sub>R (x::'a::ordered_euclidean_space) + c) ` {a..b} = {u..v}"
  unfolding image_affinity_interval by auto

lemma setprod_cong2: assumes "\<And>x. x \<in> A \<Longrightarrow> f x = g x" shows "setprod f A = setprod g A"
  apply(rule setprod_cong) using assms by auto

lemma content_image_affinity_interval: 
 "content((\<lambda>x::'a::ordered_euclidean_space. m *\<^sub>R x + c) ` {a..b}) = (abs m) ^ DIM('a) * content {a..b}" (is "?l = ?r")
proof- { presume *:"{a..b}\<noteq>{} \<Longrightarrow> ?thesis" show ?thesis apply(cases,rule *,assumption)
      unfolding not_not using content_empty by auto }
  have *:"DIM('a) = card {..<DIM('a)}" by auto
  assume as:"{a..b}\<noteq>{}" show ?thesis proof(cases "m \<ge> 0")
    case True show ?thesis unfolding image_affinity_interval if_not_P[OF as] if_P[OF True]
      unfolding content_closed_interval'[OF as] apply(subst content_closed_interval') defer apply(subst(2) *)
      apply(subst setprod_constant[THEN sym]) apply(rule finite_lessThan) unfolding setprod_timesf[THEN sym]
      apply(rule setprod_cong2) using True as unfolding interval_ne_empty euclidean_simps not_le  
      by(auto simp add:field_simps intro:mult_left_mono)
  next case False show ?thesis unfolding image_affinity_interval if_not_P[OF as] if_not_P[OF False]
      unfolding content_closed_interval'[OF as] apply(subst content_closed_interval') defer apply(subst(2) *)
      apply(subst setprod_constant[THEN sym]) apply(rule finite_lessThan) unfolding setprod_timesf[THEN sym]
      apply(rule setprod_cong2) using False as unfolding interval_ne_empty euclidean_simps not_le 
      by(auto simp add:field_simps mult_le_cancel_left_neg) qed qed

lemma has_integral_affinity: fixes a::"'a::ordered_euclidean_space" assumes "(f has_integral i) {a..b}" "m \<noteq> 0"
  shows "((\<lambda>x. f(m *\<^sub>R x + c)) has_integral ((1 / (abs(m) ^ DIM('a))) *\<^sub>R i)) ((\<lambda>x. (1 / m) *\<^sub>R x + -((1 / m) *\<^sub>R c)) ` {a..b})"
  apply(rule has_integral_twiddle,safe) apply(rule zero_less_power) unfolding euclidean_eq[where 'a='a]
  unfolding scaleR_right_distrib euclidean_simps scaleR_scaleR
  defer apply(insert assms(2), simp add:field_simps) apply(insert assms(2), simp add:field_simps)
  apply(rule continuous_intros)+ apply(rule interval_image_affinity_interval)+ apply(rule content_image_affinity_interval) using assms by auto

lemma integrable_affinity: assumes "f integrable_on {a..b}" "m \<noteq> 0"
  shows "(\<lambda>x. f(m *\<^sub>R x + c)) integrable_on ((\<lambda>x. (1 / m) *\<^sub>R x + -((1/m) *\<^sub>R c)) ` {a..b})"
  using assms unfolding integrable_on_def apply safe apply(drule has_integral_affinity) by auto

subsection {* Special case of stretching coordinate axes separately. *}

lemma image_stretch_interval:
  "(\<lambda>x. \<chi>\<chi> k. m k * x$$k) ` {a..b::'a::ordered_euclidean_space} =
  (if {a..b} = {} then {} else {(\<chi>\<chi> k. min (m(k) * a$$k) (m(k) * b$$k))::'a ..  (\<chi>\<chi> k. max (m(k) * a$$k) (m(k) * b$$k))})"
  (is "?l = ?r")
proof(cases "{a..b}={}") case True thus ?thesis unfolding True by auto
next have *:"\<And>P Q. (\<forall>i<DIM('a). P i) \<and> (\<forall>i<DIM('a). Q i) \<longleftrightarrow> (\<forall>i<DIM('a). P i \<and> Q i)" by auto
  case False note ab = this[unfolded interval_ne_empty]
  show ?thesis apply-apply(rule set_eqI)
  proof- fix x::"'a" have **:"\<And>P Q. (\<forall>i<DIM('a). P i = Q i) \<Longrightarrow> (\<forall>i<DIM('a). P i) = (\<forall>i<DIM('a). Q i)" by auto
    show "x \<in> ?l \<longleftrightarrow> x \<in> ?r" unfolding if_not_P[OF False] 
      unfolding image_iff mem_interval Bex_def euclidean_simps euclidean_eq[where 'a='a] *
      unfolding imp_conjR[THEN sym] apply(subst euclidean_lambda_beta'') apply(subst lambda_skolem'[THEN sym])
      apply(rule **,rule,rule) unfolding euclidean_lambda_beta'
    proof- fix i assume i:"i<DIM('a)" show "(\<exists>xa. (a $$ i \<le> xa \<and> xa \<le> b $$ i) \<and> x $$ i = m i * xa) =
        (min (m i * a $$ i) (m i * b $$ i) \<le> x $$ i \<and> x $$ i \<le> max (m i * a $$ i) (m i * b $$ i))"
      proof(cases "m i = 0") case True thus ?thesis using ab i by auto
      next case False hence "0 < m i \<or> 0 > m i" by auto thus ?thesis apply-
        proof(erule disjE) assume as:"0 < m i" hence *:"min (m i * a $$ i) (m i * b $$ i) = m i * a $$ i"
            "max (m i * a $$ i) (m i * b $$ i) = m i * b $$ i" using ab i unfolding min_def max_def by auto
          show ?thesis unfolding * apply rule defer apply(rule_tac x="1 / m i * x$$i" in exI)
            using as by(auto simp add:field_simps)
        next assume as:"0 > m i" hence *:"max (m i * a $$ i) (m i * b $$ i) = m i * a $$ i"
            "min (m i * a $$ i) (m i * b $$ i) = m i * b $$ i" using ab as i unfolding min_def max_def 
            by(auto simp add:field_simps mult_le_cancel_left_neg intro: order_antisym)
          show ?thesis unfolding * apply rule defer apply(rule_tac x="1 / m i * x$$i" in exI)
            using as by(auto simp add:field_simps) qed qed qed qed qed 

lemma interval_image_stretch_interval: "\<exists>u v. (\<lambda>x. \<chi>\<chi> k. m k * x$$k) ` {a..b::'a::ordered_euclidean_space} = {u..v::'a}"
  unfolding image_stretch_interval by auto 

lemma content_image_stretch_interval:
  "content((\<lambda>x::'a::ordered_euclidean_space. (\<chi>\<chi> k. m k * x$$k)::'a) ` {a..b}) = abs(setprod m {..<DIM('a)}) * content({a..b})"
proof(cases "{a..b} = {}") case True thus ?thesis
    unfolding content_def image_is_empty image_stretch_interval if_P[OF True] by auto
next case False hence "(\<lambda>x. (\<chi>\<chi> k. m k * x $$ k)::'a) ` {a..b} \<noteq> {}" by auto
  thus ?thesis using False unfolding content_def image_stretch_interval apply- unfolding interval_bounds' if_not_P
    unfolding abs_setprod setprod_timesf[THEN sym] apply(rule setprod_cong2) unfolding lessThan_iff euclidean_lambda_beta'
  proof- fix i assume i:"i<DIM('a)" have "(m i < 0 \<or> m i > 0) \<or> m i = 0" by auto
    thus "max (m i * a $$ i) (m i * b $$ i) - min (m i * a $$ i) (m i * b $$ i) = \<bar>m i\<bar> * (b $$ i - a $$ i)"
      apply-apply(erule disjE)+ unfolding min_def max_def using False[unfolded interval_ne_empty,rule_format,of i] i 
      by(auto simp add:field_simps not_le mult_le_cancel_left_neg mult_le_cancel_left_pos) qed qed

lemma has_integral_stretch: fixes f::"'a::ordered_euclidean_space => 'b::real_normed_vector"
  assumes "(f has_integral i) {a..b}" "\<forall>k<DIM('a). ~(m k = 0)"
  shows "((\<lambda>x. f(\<chi>\<chi> k. m k * x$$k)) has_integral
             ((1/(abs(setprod m {..<DIM('a)}))) *\<^sub>R i)) ((\<lambda>x. (\<chi>\<chi> k. 1/(m k) * x$$k)::'a) ` {a..b})"
  apply(rule has_integral_twiddle[where f=f]) unfolding zero_less_abs_iff content_image_stretch_interval
  unfolding image_stretch_interval empty_as_interval euclidean_eq[where 'a='a] using assms
proof- show "\<forall>y::'a. continuous (at y) (\<lambda>x. (\<chi>\<chi> k. m k * x $$ k)::'a)"
   apply(rule,rule linear_continuous_at) unfolding linear_linear
   unfolding linear_def euclidean_simps euclidean_eq[where 'a='a] by(auto simp add:field_simps) qed auto

lemma integrable_stretch:  fixes f::"'a::ordered_euclidean_space => 'b::real_normed_vector"
  assumes "f integrable_on {a..b}" "\<forall>k<DIM('a). ~(m k = 0)"
  shows "(\<lambda>x::'a. f(\<chi>\<chi> k. m k * x$$k)) integrable_on ((\<lambda>x. \<chi>\<chi> k. 1/(m k) * x$$k) ` {a..b})"
  using assms unfolding integrable_on_def apply-apply(erule exE) 
  apply(drule has_integral_stretch,assumption) by auto

subsection {* even more special cases. *}

lemma uminus_interval_vector[simp]:"uminus ` {a..b} = {-b .. -a::'a::ordered_euclidean_space}"
  apply(rule set_eqI,rule) defer unfolding image_iff
  apply(rule_tac x="-x" in bexI) by(auto simp add:minus_le_iff le_minus_iff eucl_le[where 'a='a])

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

lemma bgauge_existence_lemma: "(\<forall>x\<in>s. \<exists>d::real. 0 < d \<and> q d x) \<longleftrightarrow> (\<forall>x. \<exists>d>0. x\<in>s \<longrightarrow> q d x)" by(meson zero_less_one)

lemma additive_tagged_division_1': fixes f::"real \<Rightarrow> 'a::real_normed_vector"
  assumes "a \<le> b" "p tagged_division_of {a..b}"
  shows "setsum (\<lambda>(x,k). f (interval_upperbound k) - f(interval_lowerbound k)) p = f b - f a"
  using additive_tagged_division_1[OF _ assms(2), of f] using assms(1) by auto

lemma split_minus[simp]:"(\<lambda>(x, k). f x k) x - (\<lambda>(x, k). g x k) x = (\<lambda>(x, k). f x k - g x k) x"
  unfolding split_def by(rule refl)

lemma norm_triangle_le_sub: "norm x + norm y \<le> e \<Longrightarrow> norm (x - y) \<le> e"
  apply(subst(asm)(2) norm_minus_cancel[THEN sym])
  apply(drule norm_triangle_le) by(auto simp add:algebra_simps)

lemma fundamental_theorem_of_calculus_interior: fixes f::"real => 'a::real_normed_vector"
  assumes"a \<le> b" "continuous_on {a..b} f" "\<forall>x\<in>{a<..<b}. (f has_vector_derivative f'(x)) (at x)"
  shows "(f' has_integral (f b - f a)) {a..b}"
proof- { presume *:"a < b \<Longrightarrow> ?thesis" 
    show ?thesis proof(cases,rule *,assumption)
      assume "\<not> a < b" hence "a = b" using assms(1) by auto
      hence *:"{a .. b} = {b}" "f b - f a = 0" by(auto simp add:  order_antisym)
      show ?thesis unfolding *(2) apply(rule has_integral_null) unfolding content_eq_0 using * `a=b` by auto
    qed } assume ab:"a < b"
  let ?P = "\<lambda>e. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a..b} \<and> d fine p \<longrightarrow>
                   norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f' x) - (f b - f a)) \<le> e * content {a..b})"
  { presume "\<And>e. e>0 \<Longrightarrow> ?P e" thus ?thesis unfolding has_integral_factor_content by auto }
  fix e::real assume e:"e>0"
  note assms(3)[unfolded has_vector_derivative_def has_derivative_at_alt ball_conj_distrib]
  note conjunctD2[OF this] note bounded=this(1) and this(2)
  from this(2) have "\<forall>x\<in>{a<..<b}. \<exists>d>0. \<forall>y. norm (y - x) < d \<longrightarrow> norm (f y - f x - (y - x) *\<^sub>R f' x) \<le> e/2 * norm (y - x)"
    apply-apply safe apply(erule_tac x=x in ballE,erule_tac x="e/2" in allE) using e by auto note this[unfolded bgauge_existence_lemma]
  from choice[OF this] guess d .. note conjunctD2[OF this[rule_format]] note d = this[rule_format]
  have "bounded (f ` {a..b})" apply(rule compact_imp_bounded compact_continuous_image)+ using compact_interval assms by auto
  from this[unfolded bounded_pos] guess B .. note B = this[rule_format]

  have "\<exists>da. 0 < da \<and> (\<forall>c. a \<le> c \<and> {a..c} \<subseteq> {a..b} \<and> {a..c} \<subseteq> ball a da
    \<longrightarrow> norm(content {a..c} *\<^sub>R f' a - (f c - f a)) \<le> (e * (b - a)) / 4)"
  proof- have "a\<in>{a..b}" using ab by auto
    note assms(2)[unfolded continuous_on_eq_continuous_within,rule_format,OF this]
    note * = this[unfolded continuous_within Lim_within,rule_format] have "(e * (b - a)) / 8 > 0" using e ab by(auto simp add:field_simps)
    from *[OF this] guess k .. note k = conjunctD2[OF this,rule_format]
    have "\<exists>l. 0 < l \<and> norm(l *\<^sub>R f' a) \<le> (e * (b - a)) / 8"
    proof(cases "f' a = 0") case True
      thus ?thesis apply(rule_tac x=1 in exI) using ab e by(auto intro!:mult_nonneg_nonneg) 
    next case False thus ?thesis
        apply(rule_tac x="(e * (b - a)) / 8 / norm (f' a)" in exI) using ab e by(auto simp add:field_simps) 
    qed then guess l .. note l = conjunctD2[OF this]
    show ?thesis apply(rule_tac x="min k l" in exI) apply safe unfolding min_less_iff_conj apply(rule,(rule l k)+)
    proof- fix c assume as:"a \<le> c" "{a..c} \<subseteq> {a..b}" "{a..c} \<subseteq> ball a (min k l)" 
      note as' = this[unfolded subset_eq Ball_def mem_ball dist_real_def mem_interval]
      have "norm ((c - a) *\<^sub>R f' a - (f c - f a)) \<le> norm ((c - a) *\<^sub>R f' a) + norm (f c - f a)" by(rule norm_triangle_ineq4)
      also have "... \<le> e * (b - a) / 8 + e * (b - a) / 8" 
      proof(rule add_mono) case goal1 have "\<bar>c - a\<bar> \<le> \<bar>l\<bar>" using as' by auto
        thus ?case apply-apply(rule order_trans[OF _ l(2)]) unfolding norm_scaleR apply(rule mult_right_mono) by auto
      next case goal2 show ?case apply(rule less_imp_le) apply(cases "a = c") defer
          apply(rule k(2)[unfolded dist_norm]) using as' e ab by(auto simp add:field_simps)
      qed finally show "norm (content {a..c} *\<^sub>R f' a - (f c - f a)) \<le> e * (b - a) / 4"
        unfolding content_real[OF as(1)] by auto
    qed qed then guess da .. note da=conjunctD2[OF this,rule_format]

  have "\<exists>db>0. \<forall>c\<le>b. {c..b} \<subseteq> {a..b} \<and> {c..b} \<subseteq> ball b db \<longrightarrow>
    norm(content {c..b} *\<^sub>R f' b - (f b - f c)) \<le> (e * (b - a)) / 4"
  proof- have "b\<in>{a..b}" using ab by auto
    note assms(2)[unfolded continuous_on_eq_continuous_within,rule_format,OF this]
    note * = this[unfolded continuous_within Lim_within,rule_format] have "(e * (b - a)) / 8 > 0"
      using e ab by(auto simp add:field_simps)
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
          apply(rule k(2)[unfolded dist_norm]) using as' e ab by(auto simp add:field_simps)
      qed finally show "norm (content {c..b} *\<^sub>R f' b - (f b - f c)) \<le> e * (b - a) / 4"
        unfolding content_real[OF as(1)] by auto
    qed qed then guess db .. note db=conjunctD2[OF this,rule_format]

  let ?d = "(\<lambda>x. ball x (if x=a then da else if x=b then db else d x))"
  show "?P e" apply(rule_tac x="?d" in exI)
  proof safe case goal1 show ?case apply(rule gauge_ball_dependent) using ab db(1) da(1) d(1) by auto
  next case goal2 note as=this let ?A = "{t. fst t \<in> {a, b}}" note p = tagged_division_ofD[OF goal2(1)]
    have pA:"p = (p \<inter> ?A) \<union> (p - ?A)" "finite (p \<inter> ?A)" "finite (p - ?A)" "(p \<inter> ?A) \<inter> (p - ?A) = {}"  using goal2 by auto
    note * = additive_tagged_division_1'[OF assms(1) goal2(1), THEN sym]
    have **:"\<And>n1 s1 n2 s2::real. n2 \<le> s2 / 2 \<Longrightarrow> n1 - s1 \<le> s2 / 2 \<Longrightarrow> n1 + n2 \<le> s1 + s2" by arith
    show ?case unfolding content_real[OF assms(1)] and *[of "\<lambda>x. x"] *[of f] setsum_subtractf[THEN sym] split_minus
      unfolding setsum_right_distrib apply(subst(2) pA,subst pA) unfolding setsum_Un_disjoint[OF pA(2-)]
    proof(rule norm_triangle_le,rule **) 
      case goal1 show ?case apply(rule order_trans,rule setsum_norm_le) defer apply(subst setsum_divide_distrib)
      proof(rule order_refl,safe,unfold not_le o_def split_conv fst_conv,rule ccontr) fix x k assume as:"(x,k) \<in> p"
          "e * (interval_upperbound k -  interval_lowerbound k) / 2
          < norm (content k *\<^sub>R f' x - (f (interval_upperbound k) - f (interval_lowerbound k)))"
        from p(4)[OF this(1)] guess u v apply-by(erule exE)+ note k=this
        hence "u \<le> v" and uv:"{u,v}\<subseteq>{u..v}" using p(2)[OF as(1)] by auto
        note result = as(2)[unfolded k interval_bounds_real[OF this(1)] content_real[OF this(1)]]

        assume as':"x \<noteq> a" "x \<noteq> b" hence "x \<in> {a<..<b}" using p(2-3)[OF as(1)] by auto
        note  * = d(2)[OF this]
        have "norm ((v - u) *\<^sub>R f' (x) - (f (v) - f (u))) =
          norm ((f (u) - f (x) - (u - x) *\<^sub>R f' (x)) - (f (v) - f (x) - (v - x) *\<^sub>R f' (x)))" 
          apply(rule arg_cong[of _ _ norm]) unfolding scaleR_left.diff by auto 
        also have "... \<le> e / 2 * norm (u - x) + e / 2 * norm (v - x)" apply(rule norm_triangle_le_sub)
          apply(rule add_mono) apply(rule_tac[!] *) using fineD[OF goal2(2) as(1)] as' unfolding k subset_eq
          apply- apply(erule_tac x=u in ballE,erule_tac[3] x=v in ballE) using uv by(auto simp:dist_real_def)
        also have "... \<le> e / 2 * norm (v - u)" using p(2)[OF as(1)] unfolding k by(auto simp add:field_simps)
        finally have "e * (v - u) / 2 < e * (v - u) / 2"
          apply- apply(rule less_le_trans[OF result]) using uv by auto thus False by auto qed

    next have *:"\<And>x s1 s2::real. 0 \<le> s1 \<Longrightarrow> x \<le> (s1 + s2) / 2 \<Longrightarrow> x - s1 \<le> s2 / 2" by auto
      case goal2 show ?case apply(rule *) apply(rule setsum_nonneg) apply(rule,unfold split_paired_all split_conv)
        defer unfolding setsum_Un_disjoint[OF pA(2-),THEN sym] pA(1)[THEN sym] unfolding setsum_right_distrib[THEN sym] 
        apply(subst additive_tagged_division_1[OF _ as(1)]) apply(rule assms)
      proof- fix x k assume "(x,k) \<in> p \<inter> {t. fst t \<in> {a, b}}" note xk=IntD1[OF this]
        from p(4)[OF this] guess u v apply-by(erule exE)+ note uv=this
        with p(2)[OF xk] have "{u..v} \<noteq> {}" by auto
        thus "0 \<le> e * ((interval_upperbound k) - (interval_lowerbound k))"
          unfolding uv using e by(auto simp add:field_simps)
      next have *:"\<And>s f t e. setsum f s = setsum f t \<Longrightarrow> norm(setsum f t) \<le> e \<Longrightarrow> norm(setsum f s) \<le> e" by auto
        show "norm (\<Sum>(x, k)\<in>p \<inter> ?A. content k *\<^sub>R f' x -
          (f ((interval_upperbound k)) - f ((interval_lowerbound k)))) \<le> e * (b - a) / 2" 
          apply(rule *[where t="p \<inter> {t. fst t \<in> {a, b} \<and> content(snd t) \<noteq> 0}"])
          apply(rule setsum_mono_zero_right[OF pA(2)]) defer apply(rule) unfolding split_paired_all split_conv o_def
        proof- fix x k assume "(x,k) \<in> p \<inter> {t. fst t \<in> {a, b}} - p \<inter> {t. fst t \<in> {a, b} \<and> content (snd t) \<noteq> 0}"
          hence xk:"(x,k)\<in>p" "content k = 0" by auto from p(4)[OF xk(1)] guess u v apply-by(erule exE)+ note uv=this
          have "k\<noteq>{}" using p(2)[OF xk(1)] by auto hence *:"u = v" using xk
            unfolding uv content_eq_0 interval_eq_empty by auto
          thus "content k *\<^sub>R (f' (x)) - (f ((interval_upperbound k)) - f ((interval_lowerbound k))) = 0" using xk unfolding uv by auto
        next have *:"p \<inter> {t. fst t \<in> {a, b} \<and> content(snd t) \<noteq> 0} = 
            {t. t\<in>p \<and> fst t = a \<and> content(snd t) \<noteq> 0} \<union> {t. t\<in>p \<and> fst t = b \<and> content(snd t) \<noteq> 0}" by blast
          have **:"\<And>s f. \<And>e::real. (\<forall>x y. x \<in> s \<and> y \<in> s \<longrightarrow> x = y) \<Longrightarrow> (\<forall>x. x \<in> s \<longrightarrow> norm(f x) \<le> e)
            \<Longrightarrow> e>0 \<Longrightarrow> norm(setsum f s) \<le> e"
          proof(case_tac "s={}") case goal2 then obtain x where "x\<in>s" by auto hence *:"s = {x}" using goal2(1) by auto
            thus ?case using `x\<in>s` goal2(2) by auto
          qed auto
          case goal2 show ?case apply(subst *, subst setsum_Un_disjoint) prefer 4
            apply(rule order_trans[of _ "e * (b - a)/4 + e * (b - a)/4"]) 
            apply(rule norm_triangle_le,rule add_mono) apply(rule_tac[1-2] **)
          proof- let ?B = "\<lambda>x. {t \<in> p. fst t = x \<and> content (snd t) \<noteq> 0}"
            have pa:"\<And>k. (a, k) \<in> p \<Longrightarrow> \<exists>v. k = {a .. v} \<and> a \<le> v" 
            proof- case goal1 guess u v using p(4)[OF goal1] apply-by(erule exE)+ note uv=this
              have *:"u \<le> v" using p(2)[OF goal1] unfolding uv by auto
              have u:"u = a" proof(rule ccontr)  have "u \<in> {u..v}" using p(2-3)[OF goal1(1)] unfolding uv by auto 
                have "u \<ge> a" using p(2-3)[OF goal1(1)] unfolding uv subset_eq by auto moreover assume "u\<noteq>a" ultimately
                have "u > a" by auto
                thus False using p(2)[OF goal1(1)] unfolding uv by(auto simp add:)
              qed thus ?case apply(rule_tac x=v in exI) unfolding uv using * by auto
            qed
            have pb:"\<And>k. (b, k) \<in> p \<Longrightarrow> \<exists>v. k = {v .. b} \<and> b \<ge> v" 
            proof- case goal1 guess u v using p(4)[OF goal1] apply-by(erule exE)+ note uv=this
              have *:"u \<le> v" using p(2)[OF goal1] unfolding uv by auto
              have u:"v =  b" proof(rule ccontr)  have "u \<in> {u..v}" using p(2-3)[OF goal1(1)] unfolding uv by auto 
                have "v \<le>  b" using p(2-3)[OF goal1(1)] unfolding uv subset_eq by auto moreover assume "v\<noteq> b" ultimately
                have "v <  b" by auto
                thus False using p(2)[OF goal1(1)] unfolding uv by(auto simp add:)
              qed thus ?case apply(rule_tac x=u in exI) unfolding uv using * by auto
            qed

            show "\<forall>x y. x \<in> ?B a \<and> y \<in> ?B a \<longrightarrow> x = y" apply(rule,rule,rule,unfold split_paired_all)
              unfolding mem_Collect_eq fst_conv snd_conv apply safe
            proof- fix x k k' assume k:"( a, k) \<in> p" "( a, k') \<in> p" "content k \<noteq> 0" "content k' \<noteq> 0"
              guess v using pa[OF k(1)] .. note v = conjunctD2[OF this]
              guess v' using pa[OF k(2)] .. note v' = conjunctD2[OF this] let ?v = " (min (v) (v'))"
              have "{ a <..< ?v} \<subseteq> k \<inter> k'" unfolding v v' by(auto simp add:) note interior_mono[OF this,unfolded interior_inter]
              moreover have " ((a + ?v)/2) \<in> { a <..< ?v}" using k(3-)
                unfolding v v' content_eq_0 not_le by(auto simp add:not_le)
              ultimately have " ((a + ?v)/2) \<in> interior k \<inter> interior k'" unfolding interior_open[OF open_interval] by auto
              hence *:"k = k'" apply- apply(rule ccontr) using p(5)[OF k(1-2)] by auto
              { assume "x\<in>k" thus "x\<in>k'" unfolding * . } { assume "x\<in>k'" thus "x\<in>k" unfolding * . }
            qed 
            show "\<forall>x y. x \<in> ?B b \<and> y \<in> ?B b \<longrightarrow> x = y" apply(rule,rule,rule,unfold split_paired_all)
              unfolding mem_Collect_eq fst_conv snd_conv apply safe
            proof- fix x k k' assume k:"( b, k) \<in> p" "( b, k') \<in> p" "content k \<noteq> 0" "content k' \<noteq> 0"
              guess v using pb[OF k(1)] .. note v = conjunctD2[OF this]
              guess v' using pb[OF k(2)] .. note v' = conjunctD2[OF this] let ?v = " (max (v) (v'))"
              have "{?v <..<  b} \<subseteq> k \<inter> k'" unfolding v v' by(auto simp add:) note interior_mono[OF this,unfolded interior_inter]
              moreover have " ((b + ?v)/2) \<in> {?v <..<  b}" using k(3-) unfolding v v' content_eq_0 not_le by auto
              ultimately have " ((b + ?v)/2) \<in> interior k \<inter> interior k'" unfolding interior_open[OF open_interval] by auto
              hence *:"k = k'" apply- apply(rule ccontr) using p(5)[OF k(1-2)] by auto
              { assume "x\<in>k" thus "x\<in>k'" unfolding * . } { assume "x\<in>k'" thus "x\<in>k" unfolding * . }
            qed

            let ?a = a and ?b = b (* a is something else while proofing the next theorem. *)
            show "\<forall>x. x \<in> ?B a \<longrightarrow> norm ((\<lambda>(x, k). content k *\<^sub>R f' (x) - (f ((interval_upperbound k)) -
              f ((interval_lowerbound k)))) x) \<le> e * (b - a) / 4" apply(rule,rule) unfolding mem_Collect_eq
              unfolding split_paired_all fst_conv snd_conv 
            proof safe case goal1 guess v using pa[OF goal1(1)] .. note v = conjunctD2[OF this]
              have " ?a\<in>{ ?a..v}" using v(2) by auto hence "v \<le> ?b" using p(3)[OF goal1(1)] unfolding subset_eq v by auto
              moreover have "{?a..v} \<subseteq> ball ?a da" using fineD[OF as(2) goal1(1)]
                apply-apply(subst(asm) if_P,rule refl) unfolding subset_eq apply safe apply(erule_tac x=" x" in ballE)
                by(auto simp add:subset_eq dist_real_def v) ultimately
              show ?case unfolding v interval_bounds_real[OF v(2)] apply- apply(rule da(2)[of "v"])
                using goal1 fineD[OF as(2) goal1(1)] unfolding v content_eq_0 by auto
            qed
            show "\<forall>x. x \<in> ?B b \<longrightarrow> norm ((\<lambda>(x, k). content k *\<^sub>R f' (x) -
              (f ((interval_upperbound k)) - f ((interval_lowerbound k)))) x) \<le> e * (b - a) / 4"
              apply(rule,rule) unfolding mem_Collect_eq unfolding split_paired_all fst_conv snd_conv 
            proof safe case goal1 guess v using pb[OF goal1(1)] .. note v = conjunctD2[OF this]
              have " ?b\<in>{v.. ?b}" using v(2) by auto hence "v \<ge> ?a" using p(3)[OF goal1(1)]
                unfolding subset_eq v by auto
              moreover have "{v..?b} \<subseteq> ball ?b db" using fineD[OF as(2) goal1(1)]
                apply-apply(subst(asm) if_P,rule refl) unfolding subset_eq apply safe
                apply(erule_tac x=" x" in ballE) using ab
                by(auto simp add:subset_eq v dist_real_def) ultimately
              show ?case unfolding v unfolding interval_bounds_real[OF v(2)] apply- apply(rule db(2)[of "v"])
                using goal1 fineD[OF as(2) goal1(1)] unfolding v content_eq_0 by auto
            qed
          qed(insert p(1) ab e, auto simp add:field_simps) qed auto qed qed qed qed

subsection {* Stronger form with finite number of exceptional points. *}

lemma fundamental_theorem_of_calculus_interior_strong: fixes f::"real \<Rightarrow> 'a::banach"
  assumes"finite s" "a \<le> b" "continuous_on {a..b} f"
  "\<forall>x\<in>{a<..<b} - s. (f has_vector_derivative f'(x)) (at x)"
  shows "(f' has_integral (f b - f a)) {a..b}" using assms apply- 
proof(induct "card s" arbitrary:s a b)
  case 0 show ?case apply(rule fundamental_theorem_of_calculus_interior) using 0 by auto
next case (Suc n) from this(2) guess c s' apply-apply(subst(asm) eq_commute) unfolding card_Suc_eq
    apply(subst(asm)(2) eq_commute) by(erule exE conjE)+ note cs = this[rule_format]
  show ?case proof(cases "c\<in>{a<..<b}")
    case False thus ?thesis apply- apply(rule Suc(1)[OF cs(3) _ Suc(4,5)]) apply safe defer
      apply(rule Suc(6)[rule_format]) using Suc(3) unfolding cs by auto
  next have *:"f b - f a = (f c - f a) + (f b - f c)" by auto
    case True hence "a \<le> c" "c \<le> b" by auto
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
  shows "(f' has_integral (f(b) - f(a))) {a..b}"
  apply(rule fundamental_theorem_of_calculus_interior_strong[OF assms(1-3), of f'])
  using assms(4) by auto

lemma indefinite_integral_continuous_left: fixes f::"real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}" "a < c" "c \<le> b" "0 < e"
  obtains d where "0 < d" "\<forall>t. c - d < t \<and> t \<le> c \<longrightarrow> norm(integral {a..c} f - integral {a..t} f) < e"
proof- have "\<exists>w>0. \<forall>t. c - w < t \<and> t < c \<longrightarrow> norm(f c) * norm(c - t) < e / 3"
  proof(cases "f c = 0") case False hence "0 < e / 3 / norm (f c)"
      apply-apply(rule divide_pos_pos) using `e>0` by auto
    thus ?thesis apply-apply(rule,rule,assumption,safe)
    proof- fix t assume as:"t < c" and "c - e / 3 / norm (f c) < t"
      hence "c - t < e / 3 / norm (f c)" by auto
      hence "norm (c - t) < e / 3 / norm (f c)" using as by auto
      thus "norm (f c) * norm (c - t) < e / 3" using False apply-
        apply(subst mult_commute) apply(subst pos_less_divide_eq[THEN sym]) by auto
    qed next case True show ?thesis apply(rule_tac x=1 in exI) unfolding True using `e>0` by auto
  qed then guess w .. note w = conjunctD2[OF this,rule_format]
  
  have *:"e / 3 > 0" using assms by auto
  have "f integrable_on {a..c}" apply(rule integrable_subinterval[OF assms(1)]) using assms(2-3) by auto
  from integrable_integral[OF this,unfolded has_integral,rule_format,OF *] guess d1 ..
  note d1 = conjunctD2[OF this,rule_format] def d \<equiv> "\<lambda>x. ball x w \<inter> d1 x"
  have "gauge d" unfolding d_def using w(1) d1 by auto
  note this[unfolded gauge_def,rule_format,of c] note conjunctD2[OF this]
  from this(2)[unfolded open_contains_ball,rule_format,OF this(1)] guess k .. note k=conjunctD2[OF this]

  let ?d = "min k (c - a)/2" show ?thesis apply(rule that[of ?d])
  proof safe show "?d > 0" using k(1) using assms(2) by auto
    fix t assume as:"c - ?d < t" "t \<le> c" let ?thesis = "norm (integral {a..c} f - integral {a..t} f) < e"
    { presume *:"t < c \<Longrightarrow> ?thesis"
      show ?thesis apply(cases "t = c") defer apply(rule *)
        apply(subst less_le) using `e>0` as(2) by auto } assume "t < c"

    have "f integrable_on {a..t}" apply(rule integrable_subinterval[OF assms(1)]) using assms(2-3) as(2) by auto
    from integrable_integral[OF this,unfolded has_integral,rule_format,OF *] guess d2 ..
    note d2 = conjunctD2[OF this,rule_format]
    def d3 \<equiv> "\<lambda>x. if x \<le> t then d1 x \<inter> d2 x else d1 x"
    have "gauge d3" using d2(1) d1(1) unfolding d3_def gauge_def by auto
    from fine_division_exists[OF this, of a t] guess p . note p=this
    note p'=tagged_division_ofD[OF this(1)]
    have pt:"\<forall>(x,k)\<in>p. x \<le> t" proof safe case goal1 from p'(2,3)[OF this] show ?case by auto qed
    with p(2) have "d2 fine p" unfolding fine_def d3_def apply safe apply(erule_tac x="(a,b)" in ballE)+ by auto
    note d2_fin = d2(2)[OF conjI[OF p(1) this]]
    
    have *:"{a..c} \<inter> {x. x $$0 \<le> t} = {a..t}" "{a..c} \<inter> {x. x$$0 \<ge> t} = {t..c}"
      using assms(2-3) as by(auto simp add:field_simps)
    have "p \<union> {(c, {t..c})} tagged_division_of {a..c} \<and> d1 fine p \<union> {(c, {t..c})}" apply rule
      apply(rule tagged_division_union_interval[of _ _ _ 0 "t"]) unfolding * apply(rule p)
      apply(rule tagged_division_of_self) unfolding fine_def
    proof safe fix x k y assume "(x,k)\<in>p" "y\<in>k" thus "y\<in>d1 x"
        using p(2) pt unfolding fine_def d3_def apply- apply(erule_tac x="(x,k)" in ballE)+ by auto
    next fix x assume "x\<in>{t..c}" hence "dist c x < k" unfolding dist_real_def
        using as(1) by(auto simp add:field_simps) 
      thus "x \<in> d1 c" using k(2) unfolding d_def by auto
    qed(insert as(2), auto) note d1_fin = d1(2)[OF this]

    have *:"integral{a..c} f - integral {a..t} f = -(((c - t) *\<^sub>R f c + (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)) -
        integral {a..c} f) + ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - integral {a..t} f) + (c - t) *\<^sub>R f c" 
      "e = (e/3 + e/3) + e/3" by auto
    have **:"(\<Sum>(x, k)\<in>p \<union> {(c, {t..c})}. content k *\<^sub>R f x) = (c - t) *\<^sub>R f c + (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)"
    proof- have **:"\<And>x F. F \<union> {x} = insert x F" by auto
      have "(c, {t..c}) \<notin> p" proof safe case goal1 from p'(2-3)[OF this]
        have "c \<in> {a..t}" by auto thus False using `t<c` by auto
      qed thus ?thesis unfolding ** apply- apply(subst setsum_insert) apply(rule p')
        unfolding split_conv defer apply(subst content_real) using as(2) by auto qed 

    have ***:"c - w < t \<and> t < c"
    proof- have "c - k < t" using `k>0` as(1) by(auto simp add:field_simps)
      moreover have "k \<le> w" apply(rule ccontr) using k(2) 
        unfolding subset_eq apply(erule_tac x="c + ((k + w)/2)" in ballE)
        unfolding d_def using `k>0` `w>0` by(auto simp add:field_simps not_le not_less dist_real_def)
      ultimately show  ?thesis using `t<c` by(auto simp add:field_simps) qed

    show ?thesis unfolding *(1) apply(subst *(2)) apply(rule norm_triangle_lt add_strict_mono)+
      unfolding norm_minus_cancel apply(rule d1_fin[unfolded **]) apply(rule d2_fin)
      using w(2)[OF ***] unfolding norm_scaleR by(auto simp add:field_simps) qed qed 

lemma indefinite_integral_continuous_right: fixes f::"real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}" "a \<le> c" "c < b" "0 < e"
  obtains d where "0 < d" "\<forall>t. c \<le> t \<and> t < c + d \<longrightarrow> norm(integral{a..c} f - integral{a..t} f) < e"
proof- have *:"(\<lambda>x. f (- x)) integrable_on {- b..- a}" "- b < - c" "- c \<le> - a" using assms by auto
  from indefinite_integral_continuous_left[OF * `e>0`] guess d . note d = this let ?d = "min d (b - c)"
  show ?thesis apply(rule that[of "?d"])
  proof safe show "0 < ?d" using d(1) assms(3) by auto
    fix t::"real" assume as:"c \<le> t" "t < c + ?d"
    have *:"integral{a..c} f = integral{a..b} f - integral{c..b} f"
      "integral{a..t} f = integral{a..b} f - integral{t..b} f" unfolding algebra_simps
      apply(rule_tac[!] integral_combine) using assms as by auto
    have "(- c) - d < (- t) \<and> - t \<le> - c" using as by auto note d(2)[rule_format,OF this]
    thus "norm (integral {a..c} f - integral {a..t} f) < e" unfolding * 
      unfolding integral_reflect apply-apply(subst norm_minus_commute) by(auto simp add:algebra_simps) qed qed
   
lemma indefinite_integral_continuous: fixes f::"real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}" shows  "continuous_on {a..b} (\<lambda>x. integral {a..x} f)"
proof(unfold continuous_on_iff, safe)  fix x e assume as:"x\<in>{a..b}" "0<(e::real)"
  let ?thesis = "\<exists>d>0. \<forall>x'\<in>{a..b}. dist x' x < d \<longrightarrow> dist (integral {a..x'} f) (integral {a..x} f) < e"
  { presume *:"a<b \<Longrightarrow> ?thesis"
    show ?thesis apply(cases,rule *,assumption)
    proof- case goal1 hence "{a..b} = {x}" using as(1) apply-apply(rule set_eqI)
        unfolding atLeastAtMost_iff by(auto simp only:field_simps not_less DIM_real)
      thus ?case using `e>0` by auto
    qed } assume "a<b"
  have "(x=a \<or> x=b) \<or> (a<x \<and> x<b)" using as(1) by (auto simp add:)
  thus ?thesis apply-apply(erule disjE)+
  proof- assume "x=a" have "a \<le> a" by auto
    from indefinite_integral_continuous_right[OF assms(1) this `a<b` `e>0`] guess d . note d=this
    show ?thesis apply(rule,rule,rule d,safe) apply(subst dist_commute)
      unfolding `x=a` dist_norm apply(rule d(2)[rule_format]) by auto
  next   assume "x=b" have "b \<le> b" by auto
    from indefinite_integral_continuous_left[OF assms(1) `a<b` this `e>0`] guess d . note d=this
    show ?thesis apply(rule,rule,rule d,safe) apply(subst dist_commute)
      unfolding `x=b` dist_norm apply(rule d(2)[rule_format])  by auto
  next assume "a<x \<and> x<b" hence xl:"a<x" "x\<le>b" and xr:"a\<le>x" "x<b" by(auto simp add: )
    from indefinite_integral_continuous_left [OF assms(1) xl `e>0`] guess d1 . note d1=this
    from indefinite_integral_continuous_right[OF assms(1) xr `e>0`] guess d2 . note d2=this
    show ?thesis apply(rule_tac x="min d1 d2" in exI)
    proof safe show "0 < min d1 d2" using d1 d2 by auto
      fix y assume "y\<in>{a..b}" "dist y x < min d1 d2"
      thus "dist (integral {a..y} f) (integral {a..x} f) < e" apply-apply(subst dist_commute)
        apply(cases "y < x") unfolding dist_norm apply(rule d1(2)[rule_format]) defer
        apply(rule d2(2)[rule_format]) unfolding not_less by(auto simp add:field_simps)
    qed qed qed 

subsection {* This doesn't directly involve integration, but that gives an easy proof. *}

lemma has_derivative_zero_unique_strong_interval: fixes f::"real \<Rightarrow> 'a::banach"
  assumes "finite k" "continuous_on {a..b} f" "f a = y"
  "\<forall>x\<in>({a..b} - k). (f has_derivative (\<lambda>h. 0)) (at x within {a..b})" "x \<in> {a..b}"
  shows "f x = y"
proof- have ab:"a\<le>b" using assms by auto
  have *:"a\<le>x" using assms(5) by auto
  have "((\<lambda>x. 0\<Colon>'a) has_integral f x - f a) {a..x}"
    apply(rule fundamental_theorem_of_calculus_interior_strong[OF assms(1) *])
    apply(rule continuous_on_subset[OF assms(2)]) defer
    apply safe unfolding has_vector_derivative_def apply(subst has_derivative_within_open[THEN sym])
    apply assumption apply(rule open_interval) apply(rule has_derivative_within_subset[where s="{a..b}"])
    using assms(4) assms(5) by auto note this[unfolded *]
  note has_integral_unique[OF has_integral_0 this]
  thus ?thesis unfolding assms by auto qed

subsection {* Generalize a bit to any convex set. *}

lemma has_derivative_zero_unique_strong_convex: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::banach"
  assumes "convex s" "finite k" "continuous_on s f" "c \<in> s" "f c = y"
  "\<forall>x\<in>(s - k). (f has_derivative (\<lambda>h. 0)) (at x within s)" "x \<in> s"
  shows "f x = y"
proof- { presume *:"x \<noteq> c \<Longrightarrow> ?thesis" show ?thesis apply(cases,rule *,assumption)
      unfolding assms(5)[THEN sym] by auto } assume "x\<noteq>c"
  note conv = assms(1)[unfolded convex_alt,rule_format]
  have as1:"continuous_on {0..1} (f \<circ> (\<lambda>t. (1 - t) *\<^sub>R c + t *\<^sub>R x))"
    apply(rule continuous_on_intros)+ apply(rule continuous_on_subset[OF assms(3)])
    apply safe apply(rule conv) using assms(4,7) by auto
  have *:"\<And>t xa. (1 - t) *\<^sub>R c + t *\<^sub>R x = (1 - xa) *\<^sub>R c + xa *\<^sub>R x \<Longrightarrow> t = xa"
  proof- case goal1 hence "(t - xa) *\<^sub>R x = (t - xa) *\<^sub>R c" 
      unfolding scaleR_simps by(auto simp add:algebra_simps)
    thus ?case using `x\<noteq>c` by auto qed
  have as2:"finite {t. ((1 - t) *\<^sub>R c + t *\<^sub>R x) \<in> k}" using assms(2) 
    apply(rule finite_surj[where f="\<lambda>z. SOME t. (1-t) *\<^sub>R c + t *\<^sub>R x = z"])
    apply safe unfolding image_iff apply rule defer apply assumption
    apply(rule sym) apply(rule some_equality) defer apply(drule *) by auto
  have "(f \<circ> (\<lambda>t. (1 - t) *\<^sub>R c + t *\<^sub>R x)) 1 = y"
    apply(rule has_derivative_zero_unique_strong_interval[OF as2 as1, of ])
    unfolding o_def using assms(5) defer apply-apply(rule)
  proof- fix t assume as:"t\<in>{0..1} - {t. (1 - t) *\<^sub>R c + t *\<^sub>R x \<in> k}"
    have *:"c - t *\<^sub>R c + t *\<^sub>R x \<in> s - k" apply safe apply(rule conv[unfolded scaleR_simps]) 
      using `x\<in>s` `c\<in>s` as by(auto simp add: algebra_simps)
    have "(f \<circ> (\<lambda>t. (1 - t) *\<^sub>R c + t *\<^sub>R x) has_derivative (\<lambda>x. 0) \<circ> (\<lambda>z. (0 - z *\<^sub>R c) + z *\<^sub>R x)) (at t within {0..1})"
      apply(rule diff_chain_within) apply(rule has_derivative_add)
      unfolding scaleR_simps
      apply(intro has_derivative_intros)
      apply(intro has_derivative_intros)
      apply(rule has_derivative_within_subset,rule assms(6)[rule_format])
      apply(rule *) apply safe apply(rule conv[unfolded scaleR_simps]) using `x\<in>s` `c\<in>s` by auto
    thus "((\<lambda>xa. f ((1 - xa) *\<^sub>R c + xa *\<^sub>R x)) has_derivative (\<lambda>h. 0)) (at t within {0..1})" unfolding o_def .
  qed auto thus ?thesis by auto qed

subsection {* Also to any open connected set with finite set of exceptions. Could 
 generalize to locally convex set with limpt-free set of exceptions. *}

lemma has_derivative_zero_unique_strong_connected: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::banach"
  assumes "connected s" "open s" "finite k" "continuous_on s f" "c \<in> s" "f c = y"
  "\<forall>x\<in>(s - k). (f has_derivative (\<lambda>h. 0)) (at x within s)" "x\<in>s"
  shows "f x = y"
proof- have "{x \<in> s. f x \<in> {y}} = {} \<or> {x \<in> s. f x \<in> {y}} = s"
    apply(rule assms(1)[unfolded connected_clopen,rule_format]) apply rule defer
    apply(rule continuous_closed_in_preimage[OF assms(4) closed_singleton])
    apply(rule open_openin_trans[OF assms(2)]) unfolding open_contains_ball
  proof safe fix x assume "x\<in>s" 
    from assms(2)[unfolded open_contains_ball,rule_format,OF this] guess e .. note e=conjunctD2[OF this]
    show "\<exists>e>0. ball x e \<subseteq> {xa \<in> s. f xa \<in> {f x}}" apply(rule,rule,rule e)
    proof safe fix y assume y:"y \<in> ball x e" thus "y\<in>s" using e by auto
      show "f y = f x" apply(rule has_derivative_zero_unique_strong_convex[OF convex_ball])
        apply(rule assms) apply(rule continuous_on_subset,rule assms) apply(rule e)+
        apply(subst centre_in_ball,rule e,rule) apply safe
        apply(rule has_derivative_within_subset) apply(rule assms(7)[rule_format])
        using y e by auto qed qed
  thus ?thesis using `x\<in>s` `f c = y` `c\<in>s` by auto qed

subsection {* Integrating characteristic function of an interval. *}

lemma has_integral_restrict_open_subinterval: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::banach"
  assumes "(f has_integral i) {c..d}" "{c..d} \<subseteq> {a..b}"
  shows "((\<lambda>x. if x \<in> {c<..<d} then f x else 0) has_integral i) {a..b}"
proof- def g \<equiv> "\<lambda>x. if x \<in>{c<..<d} then f x else 0"
  { presume *:"{c..d}\<noteq>{} \<Longrightarrow> ?thesis"
    show ?thesis apply(cases,rule *,assumption)
    proof- case goal1 hence *:"{c<..<d} = {}" using interval_open_subset_closed by auto 
      show ?thesis using assms(1) unfolding * using goal1 by auto
    qed } assume "{c..d}\<noteq>{}"
  from partial_division_extend_1[OF assms(2) this] guess p . note p=this
  note mon = monoidal_lifted[OF monoidal_monoid] 
  note operat = operative_division[OF this operative_integral p(1), THEN sym]
  let ?P = "(if g integrable_on {a..b} then Some (integral {a..b} g) else None) = Some i"
  { presume "?P" hence "g integrable_on {a..b} \<and> integral {a..b} g = i"
      apply- apply(cases,subst(asm) if_P,assumption) by auto
    thus ?thesis using integrable_integral unfolding g_def by auto }

  note iterate_eq_neutral[OF mon,unfolded neutral_lifted[OF monoidal_monoid]]
  note * = this[unfolded neutral_monoid]
  have iterate:"iterate (lifted op +) (p - {{c..d}})
      (\<lambda>i. if g integrable_on i then Some (integral i g) else None) = Some 0"
  proof(rule *,rule) case goal1 hence "x\<in>p" by auto note div = division_ofD(2-5)[OF p(1) this]
    from div(3) guess u v apply-by(erule exE)+ note uv=this
    have "interior x \<inter> interior {c..d} = {}" using div(4)[OF p(2)] goal1 by auto
    hence "(g has_integral 0) x" unfolding uv apply-apply(rule has_integral_spike_interior[where f="\<lambda>x. 0"])
      unfolding g_def interior_closed_interval by auto thus ?case by auto
  qed

  have *:"p = insert {c..d} (p - {{c..d}})" using p by auto
  have **:"g integrable_on {c..d}" apply(rule integrable_spike_interior[where f=f])
    unfolding g_def defer apply(rule has_integral_integrable) using assms(1) by auto
  moreover have "integral {c..d} g = i" apply(rule has_integral_unique[OF _ assms(1)])
    apply(rule has_integral_spike_interior[where f=g]) defer
    apply(rule integrable_integral[OF **]) unfolding g_def by auto
  ultimately show ?P unfolding operat apply- apply(subst *) apply(subst iterate_insert) apply rule+
    unfolding iterate defer apply(subst if_not_P) defer using p by auto qed

lemma has_integral_restrict_closed_subinterval: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::banach"
  assumes "(f has_integral i) ({c..d})" "{c..d} \<subseteq> {a..b}" 
  shows "((\<lambda>x. if x \<in> {c..d} then f x else 0) has_integral i) {a..b}"
proof- note has_integral_restrict_open_subinterval[OF assms]
  note * = has_integral_spike[OF negligible_frontier_interval _ this]
  show ?thesis apply(rule *[of c d]) using interval_open_subset_closed[of c d] by auto qed

lemma has_integral_restrict_closed_subintervals_eq: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::banach" assumes "{c..d} \<subseteq> {a..b}" 
  shows "((\<lambda>x. if x \<in> {c..d} then f x else 0) has_integral i) {a..b} \<longleftrightarrow> (f has_integral i) {c..d}" (is "?l = ?r")
proof(cases "{c..d} = {}") case False let ?g = "\<lambda>x. if x \<in> {c..d} then f x else 0"
  show ?thesis apply rule defer apply(rule has_integral_restrict_closed_subinterval[OF _ assms])
  proof assumption assume ?l hence "?g integrable_on {c..d}"
      apply-apply(rule integrable_subinterval[OF _ assms]) by auto
    hence *:"f integrable_on {c..d}"apply-apply(rule integrable_eq) by auto
    hence "i = integral {c..d} f" apply-apply(rule has_integral_unique)
      apply(rule `?l`) apply(rule has_integral_restrict_closed_subinterval[OF _ assms]) by auto
    thus ?r using * by auto qed qed auto

subsection {* Hence we can apply the limit process uniformly to all integrals. *}

lemma has_integral': fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach" shows
 "(f has_integral i) s \<longleftrightarrow> (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> {a..b}
  \<longrightarrow> (\<exists>z. ((\<lambda>x. if x \<in> s then f(x) else 0) has_integral z) {a..b} \<and> norm(z - i) < e))" (is "?l \<longleftrightarrow> (\<forall>e>0. ?r e)")
proof- { presume *:"\<exists>a b. s = {a..b} \<Longrightarrow> ?thesis"
    show ?thesis apply(cases,rule *,assumption)
      apply(subst has_integral_alt) by auto }
  assume "\<exists>a b. s = {a..b}" then guess a b apply-by(erule exE)+ note s=this
  from bounded_interval[of a b, THEN conjunct1, unfolded bounded_pos] guess B ..
  note B = conjunctD2[OF this,rule_format] show ?thesis apply safe
  proof- fix e assume ?l "e>(0::real)"
    show "?r e" apply(rule_tac x="B+1" in exI) apply safe defer apply(rule_tac x=i in exI)
    proof fix c d assume as:"ball 0 (B+1) \<subseteq> {c..d::'n::ordered_euclidean_space}"
      thus "((\<lambda>x. if x \<in> s then f x else 0) has_integral i) {c..d}" unfolding s
        apply-apply(rule has_integral_restrict_closed_subinterval) apply(rule `?l`[unfolded s])
        apply safe apply(drule B(2)[rule_format]) unfolding subset_eq apply(erule_tac x=x in ballE)
        by(auto simp add:dist_norm)
    qed(insert B `e>0`, auto)
  next assume as:"\<forall>e>0. ?r e" 
    from this[rule_format,OF zero_less_one] guess C .. note C=conjunctD2[OF this,rule_format]
    def c \<equiv> "(\<chi>\<chi> i. - max B C)::'n::ordered_euclidean_space" and d \<equiv> "(\<chi>\<chi> i. max B C)::'n::ordered_euclidean_space"
    have c_d:"{a..b} \<subseteq> {c..d}" apply safe apply(drule B(2)) unfolding mem_interval
    proof case goal1 thus ?case using component_le_norm[of x i] unfolding c_def d_def
        by(auto simp add:field_simps) qed
    have "ball 0 C \<subseteq> {c..d}" apply safe unfolding mem_interval mem_ball dist_norm 
    proof case goal1 thus ?case using component_le_norm[of x i] unfolding c_def d_def by auto qed
    from C(2)[OF this] have "\<exists>y. (f has_integral y) {a..b}"
      unfolding has_integral_restrict_closed_subintervals_eq[OF c_d,THEN sym] unfolding s by auto
    then guess y .. note y=this

    have "y = i" proof(rule ccontr) assume "y\<noteq>i" hence "0 < norm (y - i)" by auto
      from as[rule_format,OF this] guess C ..  note C=conjunctD2[OF this,rule_format]
      def c \<equiv> "(\<chi>\<chi> i. - max B C)::'n::ordered_euclidean_space" and d \<equiv> "(\<chi>\<chi> i. max B C)::'n::ordered_euclidean_space"
      have c_d:"{a..b} \<subseteq> {c..d}" apply safe apply(drule B(2)) unfolding mem_interval
      proof case goal1 thus ?case using component_le_norm[of x i] unfolding c_def d_def
          by(auto simp add:field_simps) qed
      have "ball 0 C \<subseteq> {c..d}" apply safe unfolding mem_interval mem_ball dist_norm 
      proof case goal1 thus ?case using component_le_norm[of x i] unfolding c_def d_def by auto qed
      note C(2)[OF this] then guess z .. note z = conjunctD2[OF this, unfolded s]
      note this[unfolded has_integral_restrict_closed_subintervals_eq[OF c_d]]
      hence "z = y" "norm (z - i) < norm (y - i)" apply- apply(rule has_integral_unique[OF _ y(1)]) .
      thus False by auto qed
    thus ?l using y unfolding s by auto qed qed 

(*lemma has_integral_trans[simp]: fixes f::"'n::ordered_euclidean_space \<Rightarrow> real" shows
  "((\<lambda>x. vec1 (f x)) has_integral vec1 i) s \<longleftrightarrow> (f has_integral i) s"
  unfolding has_integral'[unfolded has_integral] 
proof case goal1 thus ?case apply safe
  apply(erule_tac x=e in allE,safe) apply(rule_tac x=B in exI,safe)
  apply(erule_tac x=a in allE, erule_tac x=b in allE,safe) 
  apply(rule_tac x="dest_vec1 z" in exI,safe) apply(erule_tac x=ea in allE,safe) 
  apply(rule_tac x=d in exI,safe) apply(erule_tac x=p in allE,safe)
  apply(subst(asm)(2) norm_vector_1) unfolding split_def
  unfolding setsum_component Cart_nth.diff cond_value_iff[of dest_vec1]
    Cart_nth.scaleR vec1_dest_vec1 zero_index apply assumption
  apply(subst(asm)(2) norm_vector_1) by auto
next case goal2 thus ?case apply safe
  apply(erule_tac x=e in allE,safe) apply(rule_tac x=B in exI,safe)
  apply(erule_tac x=a in allE, erule_tac x=b in allE,safe) 
  apply(rule_tac x="vec1 z" in exI,safe) apply(erule_tac x=ea in allE,safe) 
  apply(rule_tac x=d in exI,safe) apply(erule_tac x=p in allE,safe)
  apply(subst norm_vector_1) unfolding split_def
  unfolding setsum_component Cart_nth.diff cond_value_iff[of dest_vec1]
    Cart_nth.scaleR vec1_dest_vec1 zero_index apply assumption
  apply(subst norm_vector_1) by auto qed

lemma integral_trans[simp]: assumes "(f::'n::ordered_euclidean_space \<Rightarrow> real) integrable_on s"
  shows "integral s (\<lambda>x. vec1 (f x)) = vec1 (integral s f)"
  apply(rule integral_unique) using assms by auto

lemma integrable_on_trans[simp]: fixes f::"'n::ordered_euclidean_space \<Rightarrow> real" shows
  "(\<lambda>x. vec1 (f x)) integrable_on s \<longleftrightarrow> (f integrable_on s)"
  unfolding integrable_on_def
  apply(subst(2) vec1_dest_vec1(1)[THEN sym]) unfolding has_integral_trans
  apply safe defer apply(rule_tac x="vec1 y" in exI) by auto *)

lemma has_integral_le: fixes f::"'n::ordered_euclidean_space \<Rightarrow> real"
  assumes "(f has_integral i) s" "(g has_integral j) s"  "\<forall>x\<in>s. (f x) \<le> (g x)"
  shows "i \<le> j" using has_integral_component_le[OF assms(1-2), of 0] using assms(3) by auto

lemma integral_le: fixes f::"'n::ordered_euclidean_space \<Rightarrow> real"
  assumes "f integrable_on s" "g integrable_on s" "\<forall>x\<in>s. f x \<le> g x"
  shows "integral s f \<le> integral s g"
  using has_integral_le[OF assms(1,2)[unfolded has_integral_integral] assms(3)] .

lemma has_integral_nonneg: fixes f::"'n::ordered_euclidean_space \<Rightarrow> real"
  assumes "(f has_integral i) s" "\<forall>x\<in>s. 0 \<le> f x" shows "0 \<le> i" 
  using has_integral_component_nonneg[of "f" "i" s 0]
  unfolding o_def using assms by auto

lemma integral_nonneg: fixes f::"'n::ordered_euclidean_space \<Rightarrow> real"
  assumes "f integrable_on s" "\<forall>x\<in>s. 0 \<le> f x" shows "0 \<le> integral s f" 
  using has_integral_nonneg[OF assms(1)[unfolded has_integral_integral] assms(2)] .

subsection {* Hence a general restriction property. *}

lemma has_integral_restrict[simp]: assumes "s \<subseteq> t" shows
  "((\<lambda>x. if x \<in> s then f x else (0::'a::banach)) has_integral i) t \<longleftrightarrow> (f has_integral i) s"
proof- have *:"\<And>x. (if x \<in> t then if x \<in> s then f x else 0 else 0) =  (if x\<in>s then f x else 0)" using assms by auto
  show ?thesis apply(subst(2) has_integral') apply(subst has_integral') unfolding * by rule qed

lemma has_integral_restrict_univ: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach" shows
  "((\<lambda>x. if x \<in> s then f x else 0) has_integral i) UNIV \<longleftrightarrow> (f has_integral i) s" by auto

lemma has_integral_on_superset: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach" 
  assumes "\<forall>x. ~(x \<in> s) \<longrightarrow> f x = 0" "s \<subseteq> t" "(f has_integral i) s"
  shows "(f has_integral i) t"
proof- have "(\<lambda>x. if x \<in> s then f x else 0) = (\<lambda>x. if x \<in> t then f x else 0)"
    apply(rule) using assms(1-2) by auto
  thus ?thesis apply- using assms(3) apply(subst has_integral_restrict_univ[THEN sym])
  apply- apply(subst(asm) has_integral_restrict_univ[THEN sym]) by auto qed

lemma integrable_on_superset: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach" 
  assumes "\<forall>x. ~(x \<in> s) \<longrightarrow> f x = 0" "s \<subseteq> t" "f integrable_on s"
  shows "f integrable_on t"
  using assms unfolding integrable_on_def by(auto intro:has_integral_on_superset)

lemma integral_restrict_univ[intro]: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach" 
  shows "f integrable_on s \<Longrightarrow> integral UNIV (\<lambda>x. if x \<in> s then f x else 0) = integral s f"
  apply(rule integral_unique) unfolding has_integral_restrict_univ by auto

lemma integrable_restrict_univ: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach" shows
 "(\<lambda>x. if x \<in> s then f x else 0) integrable_on UNIV \<longleftrightarrow> f integrable_on s"
  unfolding integrable_on_def by auto

lemma negligible_on_intervals: "negligible s \<longleftrightarrow> (\<forall>a b. negligible(s \<inter> {a..b}))" (is "?l = ?r")
proof assume ?r show ?l unfolding negligible_def
  proof safe case goal1 show ?case apply(rule has_integral_negligible[OF `?r`[rule_format,of a b]])
      unfolding indicator_def by auto qed qed auto

lemma has_integral_spike_set_eq: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach" 
  assumes "negligible((s - t) \<union> (t - s))" shows "((f has_integral y) s \<longleftrightarrow> (f has_integral y) t)"
  unfolding has_integral_restrict_univ[THEN sym,of f] apply(rule has_integral_spike_eq[OF assms]) by (safe, auto split: split_if_asm)

lemma has_integral_spike_set[dest]: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible((s - t) \<union> (t - s))" "(f has_integral y) s"
  shows "(f has_integral y) t"
  using assms has_integral_spike_set_eq by auto

lemma integrable_spike_set[dest]: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible((s - t) \<union> (t - s))" "f integrable_on s"
  shows "f integrable_on t" using assms(2) unfolding integrable_on_def 
  unfolding has_integral_spike_set_eq[OF assms(1)] .

lemma integrable_spike_set_eq: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible((s - t) \<union> (t - s))"
  shows "(f integrable_on s \<longleftrightarrow> f integrable_on t)"
  apply(rule,rule_tac[!] integrable_spike_set) using assms by auto

(*lemma integral_spike_set:
 "\<forall>f:real^M->real^N g s t.
        negligible(s DIFF t \<union> t DIFF s)
        \<longrightarrow> integral s f = integral t f"
qed  REPEAT STRIP_TAC THEN REWRITE_TAC[integral] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  ASM_MESON_TAC[]);;

lemma has_integral_interior:
 "\<forall>f:real^M->real^N y s.
        negligible(frontier s)
        \<longrightarrow> ((f has_integral y) (interior s) \<longleftrightarrow> (f has_integral y) s)"
qed  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `s:real^M->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^M->bool` CLOSURE_SUBSET) THEN
  SET_TAC[]);;

lemma has_integral_closure:
 "\<forall>f:real^M->real^N y s.
        negligible(frontier s)
        \<longrightarrow> ((f has_integral y) (closure s) \<longleftrightarrow> (f has_integral y) s)"
qed  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `s:real^M->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^M->bool` CLOSURE_SUBSET) THEN
  SET_TAC[]);;*)

subsection {* More lemmas that are useful later. *}

lemma has_integral_subset_component_le: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space"
  assumes "s \<subseteq> t" "(f has_integral i) s" "(f has_integral j) t" "\<forall>x\<in>t. 0 \<le> f(x)$$k"
  shows "i$$k \<le> j$$k"
proof- note has_integral_restrict_univ[THEN sym, of f]
  note assms(2-3)[unfolded this] note * = has_integral_component_le[OF this]
  show ?thesis apply(rule *) using assms(1,4) by auto qed

lemma has_integral_subset_le: fixes f::"'n::ordered_euclidean_space \<Rightarrow> real"
  assumes "s \<subseteq> t" "(f has_integral i) s" "(f has_integral j) t" "\<forall>x\<in>t. 0 \<le> f(x)"
  shows "i \<le> j" using has_integral_subset_component_le[OF assms(1), of "f" "i" "j" 0] using assms by auto

lemma integral_subset_component_le: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space"
  assumes "s \<subseteq> t" "f integrable_on s" "f integrable_on t" "\<forall>x \<in> t. 0 \<le> f(x)$$k"
  shows "(integral s f)$$k \<le> (integral t f)$$k"
  apply(rule has_integral_subset_component_le) using assms by auto

lemma integral_subset_le: fixes f::"'n::ordered_euclidean_space \<Rightarrow> real"
  assumes "s \<subseteq> t" "f integrable_on s" "f integrable_on t" "\<forall>x \<in> t. 0 \<le> f(x)"
  shows "(integral s f) \<le> (integral t f)"
  apply(rule has_integral_subset_le) using assms by auto

lemma has_integral_alt': fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  shows "(f has_integral i) s \<longleftrightarrow> (\<forall>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on {a..b}) \<and>
  (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> {a..b} \<longrightarrow> norm(integral {a..b} (\<lambda>x. if x \<in> s then f x else 0) - i) < e)" (is "?l = ?r")
proof assume ?r
  show ?l apply- apply(subst has_integral')
  proof safe case goal1 from `?r`[THEN conjunct2,rule_format,OF this] guess B .. note B=conjunctD2[OF this]
    show ?case apply(rule,rule,rule B,safe)
      apply(rule_tac x="integral {a..b} (\<lambda>x. if x \<in> s then f x else 0)" in exI)
      apply(drule B(2)[rule_format]) using integrable_integral[OF `?r`[THEN conjunct1,rule_format]] by auto
  qed next
  assume ?l note as = this[unfolded has_integral'[of f],rule_format]
  let ?f = "\<lambda>x. if x \<in> s then f x else 0"
  show ?r proof safe fix a b::"'n::ordered_euclidean_space"
    from as[OF zero_less_one] guess B .. note B=conjunctD2[OF this,rule_format]
    let ?a = "(\<chi>\<chi> i. min (a$$i) (-B))::'n::ordered_euclidean_space" and ?b = "(\<chi>\<chi> i. max (b$$i) B)::'n::ordered_euclidean_space"
    show "?f integrable_on {a..b}" apply(rule integrable_subinterval[of _ ?a ?b])
    proof- have "ball 0 B \<subseteq> {?a..?b}" apply safe unfolding mem_ball mem_interval dist_norm
      proof case goal1 thus ?case using component_le_norm[of x i] by(auto simp add:field_simps) qed
      from B(2)[OF this] guess z .. note conjunct1[OF this]
      thus "?f integrable_on {?a..?b}" unfolding integrable_on_def by auto
      show "{a..b} \<subseteq> {?a..?b}" apply safe unfolding mem_interval apply(rule,erule_tac x=i in allE) by auto qed

    fix e::real assume "e>0" from as[OF this] guess B .. note B=conjunctD2[OF this,rule_format]
    show "\<exists>B>0. \<forall>a b. ball 0 B \<subseteq> {a..b} \<longrightarrow>
                    norm (integral {a..b} (\<lambda>x. if x \<in> s then f x else 0) - i) < e"
    proof(rule,rule,rule B,safe) case goal1 from B(2)[OF this] guess z .. note z=conjunctD2[OF this]
      from integral_unique[OF this(1)] show ?case using z(2) by auto qed qed qed 


subsection {* Continuity of the integral (for a 1-dimensional interval). *}

lemma integrable_alt: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach" shows 
  "f integrable_on s \<longleftrightarrow>
          (\<forall>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on {a..b}) \<and>
          (\<forall>e>0. \<exists>B>0. \<forall>a b c d. ball 0 B \<subseteq> {a..b} \<and> ball 0 B \<subseteq> {c..d}
  \<longrightarrow> norm(integral {a..b} (\<lambda>x. if x \<in> s then f x else 0) -
          integral {c..d}  (\<lambda>x. if x \<in> s then f x else 0)) < e)" (is "?l = ?r")
proof assume ?l then guess y unfolding integrable_on_def .. note this[unfolded has_integral_alt'[of f]]
  note y=conjunctD2[OF this,rule_format] show ?r apply safe apply(rule y)
  proof- case goal1 hence "e/2 > 0" by auto from y(2)[OF this] guess B .. note B=conjunctD2[OF this,rule_format]
    show ?case apply(rule,rule,rule B)
    proof safe case goal1 show ?case apply(rule norm_triangle_half_l)
        using B(2)[OF goal1(1)] B(2)[OF goal1(2)] by auto qed qed
        
next assume ?r note as = conjunctD2[OF this,rule_format]
  have "Cauchy (\<lambda>n. integral ({(\<chi>\<chi> i. - real n)::'n .. (\<chi>\<chi> i. real n)}) (\<lambda>x. if x \<in> s then f x else 0))"
  proof(unfold Cauchy_def,safe) case goal1
    from as(2)[OF this] guess B .. note B = conjunctD2[OF this,rule_format]
    from real_arch_simple[of B] guess N .. note N = this
    { fix n assume n:"n \<ge> N" have "ball 0 B \<subseteq> {(\<chi>\<chi> i. - real n)::'n..\<chi>\<chi> i. real n}" apply safe
        unfolding mem_ball mem_interval dist_norm
      proof case goal1 thus ?case using component_le_norm[of x i]
          using n N by(auto simp add:field_simps) qed }
    thus ?case apply-apply(rule_tac x=N in exI) apply safe unfolding dist_norm apply(rule B(2)) by auto
  qed from this[unfolded convergent_eq_cauchy[THEN sym]] guess i ..
  note i = this[THEN LIMSEQ_D]

  show ?l unfolding integrable_on_def has_integral_alt'[of f] apply(rule_tac x=i in exI)
    apply safe apply(rule as(1)[unfolded integrable_on_def])
  proof- case goal1 hence *:"e/2 > 0" by auto
    from i[OF this] guess N .. note N =this[rule_format]
    from as(2)[OF *] guess B .. note B=conjunctD2[OF this,rule_format] let ?B = "max (real N) B"
    show ?case apply(rule_tac x="?B" in exI)
    proof safe show "0 < ?B" using B(1) by auto
      fix a b assume ab:"ball 0 ?B \<subseteq> {a..b::'n::ordered_euclidean_space}"
      from real_arch_simple[of ?B] guess n .. note n=this
      show "norm (integral {a..b} (\<lambda>x. if x \<in> s then f x else 0) - i) < e"
        apply(rule norm_triangle_half_l) apply(rule B(2)) defer apply(subst norm_minus_commute)
        apply(rule N[of n])
      proof safe show "N \<le> n" using n by auto
        fix x::"'n::ordered_euclidean_space" assume x:"x \<in> ball 0 B" hence "x\<in> ball 0 ?B" by auto
        thus "x\<in>{a..b}" using ab by blast 
        show "x\<in>{\<chi>\<chi> i. - real n..\<chi>\<chi> i. real n}" using x unfolding mem_interval mem_ball dist_norm apply-
        proof case goal1 thus ?case using component_le_norm[of x i]
            using n by(auto simp add:field_simps) qed qed qed qed qed

lemma integrable_altD: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s"
  shows "\<And>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on {a..b}"
  "\<And>e. e>0 \<Longrightarrow> \<exists>B>0. \<forall>a b c d. ball 0 B \<subseteq> {a..b} \<and> ball 0 B \<subseteq> {c..d}
  \<longrightarrow> norm(integral {a..b} (\<lambda>x. if x \<in> s then f x else 0) - integral {c..d}  (\<lambda>x. if x \<in> s then f x else 0)) < e"
  using assms[unfolded integrable_alt[of f]] by auto

lemma integrable_on_subinterval: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s" "{a..b} \<subseteq> s" shows "f integrable_on {a..b}"
  apply(rule integrable_eq) defer apply(rule integrable_altD(1)[OF assms(1)])
  using assms(2) by auto

subsection {* A straddling criterion for integrability. *}

lemma integrable_straddle_interval: fixes f::"'n::ordered_euclidean_space \<Rightarrow> real"
  assumes "\<forall>e>0. \<exists>g  h i j. (g has_integral i) ({a..b}) \<and> (h has_integral j) ({a..b}) \<and>
  norm(i - j) < e \<and> (\<forall>x\<in>{a..b}. (g x) \<le> (f x) \<and> (f x) \<le>(h x))"
  shows "f integrable_on {a..b}"
proof(subst integrable_cauchy,safe)
  case goal1 hence e:"e/3 > 0" by auto note assms[rule_format,OF this]
  then guess g h i j apply- by(erule exE conjE)+ note obt = this
  from obt(1)[unfolded has_integral[of g], rule_format, OF e] guess d1 .. note d1=conjunctD2[OF this,rule_format]
  from obt(2)[unfolded has_integral[of h], rule_format, OF e] guess d2 .. note d2=conjunctD2[OF this,rule_format]
  show ?case apply(rule_tac x="\<lambda>x. d1 x \<inter> d2 x" in exI) apply(rule conjI gauge_inter d1 d2)+ unfolding fine_inter
  proof safe have **:"\<And>i j g1 g2 h1 h2 f1 f2. g1 - h2 \<le> f1 - f2 \<Longrightarrow> f1 - f2 \<le> h1 - g2 \<Longrightarrow>
      abs(i - j) < e / 3 \<Longrightarrow> abs(g2 - i) < e / 3 \<Longrightarrow>  abs(g1 - i) < e / 3 \<Longrightarrow> 
      abs(h2 - j) < e / 3 \<Longrightarrow> abs(h1 - j) < e / 3 \<Longrightarrow> abs(f1 - f2) < e" using `e>0` by arith
    case goal1 note tagged_division_ofD(2-4) note * = this[OF goal1(1)] this[OF goal1(4)]

    have "(\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p1. content k *\<^sub>R g x) \<ge> 0"
      "0 \<le> (\<Sum>(x, k)\<in>p2. content k *\<^sub>R h x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)" 
      "(\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R g x) \<ge> 0"
      "0 \<le> (\<Sum>(x, k)\<in>p1. content k *\<^sub>R h x) - (\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x)" 
      unfolding setsum_subtractf[THEN sym] apply- apply(rule_tac[!] setsum_nonneg)
      apply safe unfolding real_scaleR_def right_diff_distrib[THEN sym]
      apply(rule_tac[!] mult_nonneg_nonneg)
    proof- fix a b assume ab:"(a,b) \<in> p1"
      show "0 \<le> content b" using *(3)[OF ab] apply safe using content_pos_le . thus "0 \<le> content b" .
      show "0 \<le> f a - g a" "0 \<le> h a - f a" using *(1-2)[OF ab] using obt(4)[rule_format,of a] by auto
    next fix a b assume ab:"(a,b) \<in> p2"
      show "0 \<le> content b" using *(6)[OF ab] apply safe using content_pos_le . thus "0 \<le> content b" .
      show "0 \<le> f a - g a" "0 \<le> h a - f a" using *(4-5)[OF ab] using obt(4)[rule_format,of a] by auto qed 

    thus ?case apply- unfolding real_norm_def apply(rule **) defer defer
      unfolding real_norm_def[THEN sym] apply(rule obt(3))
      apply(rule d1(2)[OF conjI[OF goal1(4,5)]])
      apply(rule d1(2)[OF conjI[OF goal1(1,2)]])
      apply(rule d2(2)[OF conjI[OF goal1(4,6)]])
      apply(rule d2(2)[OF conjI[OF goal1(1,3)]]) by auto qed qed 
     
lemma integrable_straddle: fixes f::"'n::ordered_euclidean_space \<Rightarrow> real"
  assumes "\<forall>e>0. \<exists>g h i j. (g has_integral i) s \<and> (h has_integral j) s \<and>
  norm(i - j) < e \<and> (\<forall>x\<in>s. (g x) \<le>(f x) \<and>(f x) \<le>(h x))"
  shows "f integrable_on s"
proof- have "\<And>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on {a..b}"
  proof(rule integrable_straddle_interval,safe) case goal1 hence *:"e/4 > 0" by auto
    from assms[rule_format,OF this] guess g h i j apply-by(erule exE conjE)+ note obt=this
    note obt(1)[unfolded has_integral_alt'[of g]] note conjunctD2[OF this, rule_format]
    note g = this(1) and this(2)[OF *] from this(2) guess B1 .. note B1 = conjunctD2[OF this,rule_format]
    note obt(2)[unfolded has_integral_alt'[of h]] note conjunctD2[OF this, rule_format]
    note h = this(1) and this(2)[OF *] from this(2) guess B2 .. note B2 = conjunctD2[OF this,rule_format]
    def c \<equiv> "(\<chi>\<chi> i. min (a$$i) (- (max B1 B2)))::'n" and d \<equiv> "(\<chi>\<chi> i. max (b$$i) (max B1 B2))::'n"
    have *:"ball 0 B1 \<subseteq> {c..d}" "ball 0 B2 \<subseteq> {c..d}" apply safe unfolding mem_ball mem_interval dist_norm
    proof(rule_tac[!] allI)
      case goal1 thus ?case using component_le_norm[of x i] unfolding c_def d_def by auto next
      case goal2 thus ?case using component_le_norm[of x i] unfolding c_def d_def by auto qed
    have **:"\<And>ch cg ag ah::real. norm(ah - ag) \<le> norm(ch - cg) \<Longrightarrow> norm(cg - i) < e / 4 \<Longrightarrow>
      norm(ch - j) < e / 4 \<Longrightarrow> norm(ag - ah) < e"
      using obt(3) unfolding real_norm_def by arith 
    show ?case apply(rule_tac x="\<lambda>x. if x \<in> s then g x else 0" in exI)
               apply(rule_tac x="\<lambda>x. if x \<in> s then h x else 0" in exI)
      apply(rule_tac x="integral {a..b} (\<lambda>x. if x \<in> s then g x else 0)" in exI)
      apply(rule_tac x="integral {a..b} (\<lambda>x. if x \<in> s then h x else 0)" in exI)
      apply safe apply(rule_tac[1-2] integrable_integral,rule g,rule h)
      apply(rule **[OF _ B1(2)[OF *(1)] B2(2)[OF *(2)]])
    proof- have *:"\<And>x f g. (if x \<in> s then f x else 0) - (if x \<in> s then g x else 0) =
        (if x \<in> s then f x - g x else (0::real))" by auto
      note ** = abs_of_nonneg[OF integral_nonneg[OF integrable_sub, OF h g]]
      show " norm (integral {a..b} (\<lambda>x. if x \<in> s then h x else 0) -
                   integral {a..b} (\<lambda>x. if x \<in> s then g x else 0))
           \<le> norm (integral {c..d} (\<lambda>x. if x \<in> s then h x else 0) -
                   integral {c..d} (\<lambda>x. if x \<in> s then g x else 0))"
        unfolding integral_sub[OF h g,THEN sym] real_norm_def apply(subst **) defer apply(subst **) defer
        apply(rule has_integral_subset_le) defer apply(rule integrable_integral integrable_sub h g)+
      proof safe fix x assume "x\<in>{a..b}" thus "x\<in>{c..d}" unfolding mem_interval c_def d_def
          apply - apply rule apply(erule_tac x=i in allE) by auto
      qed(insert obt(4), auto) qed(insert obt(4), auto) qed note interv = this

  show ?thesis unfolding integrable_alt[of f] apply safe apply(rule interv)
  proof- case goal1 hence *:"e/3 > 0" by auto
    from assms[rule_format,OF this] guess g h i j apply-by(erule exE conjE)+ note obt=this
    note obt(1)[unfolded has_integral_alt'[of g]] note conjunctD2[OF this, rule_format]
    note g = this(1) and this(2)[OF *] from this(2) guess B1 .. note B1 = conjunctD2[OF this,rule_format]
    note obt(2)[unfolded has_integral_alt'[of h]] note conjunctD2[OF this, rule_format]
    note h = this(1) and this(2)[OF *] from this(2) guess B2 .. note B2 = conjunctD2[OF this,rule_format]
    show ?case apply(rule_tac x="max B1 B2" in exI) apply safe apply(rule min_max.less_supI1,rule B1)
    proof- fix a b c d::"'n::ordered_euclidean_space" assume as:"ball 0 (max B1 B2) \<subseteq> {a..b}" "ball 0 (max B1 B2) \<subseteq> {c..d}"
      have **:"ball 0 B1 \<subseteq> ball (0::'n::ordered_euclidean_space) (max B1 B2)" "ball 0 B2 \<subseteq> ball (0::'n::ordered_euclidean_space) (max B1 B2)" by auto
      have *:"\<And>ga gc ha hc fa fc::real. abs(ga - i) < e / 3 \<and> abs(gc - i) < e / 3 \<and> abs(ha - j) < e / 3 \<and>
        abs(hc - j) < e / 3 \<and> abs(i - j) < e / 3 \<and> ga \<le> fa \<and> fa \<le> ha \<and> gc \<le> fc \<and> fc \<le> hc\<Longrightarrow> abs(fa - fc) < e" by smt
      show "norm (integral {a..b} (\<lambda>x. if x \<in> s then f x else 0) - integral {c..d} (\<lambda>x. if x \<in> s then f x else 0)) < e"
        unfolding real_norm_def apply(rule *, safe) unfolding real_norm_def[THEN sym]
        apply(rule B1(2),rule order_trans,rule **,rule as(1)) 
        apply(rule B1(2),rule order_trans,rule **,rule as(2)) 
        apply(rule B2(2),rule order_trans,rule **,rule as(1)) 
        apply(rule B2(2),rule order_trans,rule **,rule as(2)) 
        apply(rule obt) apply(rule_tac[!] integral_le) using obt
        by(auto intro!: h g interv) qed qed qed 

subsection {* Adding integrals over several sets. *}

lemma has_integral_union: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "(f has_integral i) s" "(f has_integral j) t" "negligible(s \<inter> t)"
  shows "(f has_integral (i + j)) (s \<union> t)"
proof- note * = has_integral_restrict_univ[THEN sym, of f]
  show ?thesis unfolding * apply(rule has_integral_spike[OF assms(3)])
    defer apply(rule has_integral_add[OF assms(1-2)[unfolded *]]) by auto qed

lemma has_integral_unions: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "finite t" "\<forall>s\<in>t. (f has_integral (i s)) s"  "\<forall>s\<in>t. \<forall>s'\<in>t. ~(s = s') \<longrightarrow> negligible(s \<inter> s')"
  shows "(f has_integral (setsum i t)) (\<Union>t)"
proof- note * = has_integral_restrict_univ[THEN sym, of f]
  have **:"negligible (\<Union>((\<lambda>(a,b). a \<inter> b) ` {(a,b). a \<in> t \<and> b \<in> {y. y \<in> t \<and> ~(a = y)}}))"
    apply(rule negligible_unions) apply(rule finite_imageI) apply(rule finite_subset[of _ "t \<times> t"]) defer 
    apply(rule finite_cartesian_product[OF assms(1,1)]) using assms(3) by auto 
  note assms(2)[unfolded *] note has_integral_setsum[OF assms(1) this]
  thus ?thesis unfolding * apply-apply(rule has_integral_spike[OF **]) defer apply assumption
  proof safe case goal1 thus ?case
    proof(cases "x\<in>\<Union>t") case True then guess s unfolding Union_iff .. note s=this
      hence *:"\<forall>b\<in>t. x \<in> b \<longleftrightarrow> b = s" using goal1(3) by blast
      show ?thesis unfolding if_P[OF True] apply(rule trans) defer
        apply(rule setsum_cong2) apply(subst *, assumption) apply(rule refl)
        unfolding setsum_delta[OF assms(1)] using s by auto qed auto qed qed

subsection {* In particular adding integrals over a division, maybe not of an interval. *}

lemma has_integral_combine_division: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "d division_of s" "\<forall>k\<in>d. (f has_integral (i k)) k"
  shows "(f has_integral (setsum i d)) s"
proof- note d = division_ofD[OF assms(1)]
  show ?thesis unfolding d(6)[THEN sym] apply(rule has_integral_unions)
    apply(rule d assms)+ apply(rule,rule,rule)
  proof- case goal1 from d(4)[OF this(1)] d(4)[OF this(2)]
    guess a c b d apply-by(erule exE)+ note obt=this
    from d(5)[OF goal1] show ?case unfolding obt interior_closed_interval
      apply-apply(rule negligible_subset[of "({a..b}-{a<..<b}) \<union> ({c..d}-{c<..<d})"])
      apply(rule negligible_union negligible_frontier_interval)+ by auto qed qed

lemma integral_combine_division_bottomup: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "d division_of s" "\<forall>k\<in>d. f integrable_on k"
  shows "integral s f = setsum (\<lambda>i. integral i f) d"
  apply(rule integral_unique) apply(rule has_integral_combine_division[OF assms(1)])
  using assms(2) unfolding has_integral_integral .

lemma has_integral_combine_division_topdown: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s" "d division_of k" "k \<subseteq> s"
  shows "(f has_integral (setsum (\<lambda>i. integral i f) d)) k"
  apply(rule has_integral_combine_division[OF assms(2)])
  apply safe unfolding has_integral_integral[THEN sym]
proof- case goal1 from division_ofD(2,4)[OF assms(2) this]
  show ?case apply safe apply(rule integrable_on_subinterval)
    apply(rule assms) using assms(3) by auto qed

lemma integral_combine_division_topdown: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s" "d division_of s"
  shows "integral s f = setsum (\<lambda>i. integral i f) d"
  apply(rule integral_unique,rule has_integral_combine_division_topdown) using assms by auto

lemma integrable_combine_division: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "d division_of s" "\<forall>i\<in>d. f integrable_on i"
  shows "f integrable_on s"
  using assms(2) unfolding integrable_on_def
  by(metis has_integral_combine_division[OF assms(1)])

lemma integrable_on_subdivision: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "d division_of i" "f integrable_on s" "i \<subseteq> s"
  shows "f integrable_on i"
  apply(rule integrable_combine_division assms)+
proof safe case goal1 note division_ofD(2,4)[OF assms(1) this]
  thus ?case apply safe apply(rule integrable_on_subinterval[OF assms(2)])
    using assms(3) by auto qed

subsection {* Also tagged divisions. *}

lemma has_integral_combine_tagged_division: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "p tagged_division_of s" "\<forall>(x,k) \<in> p. (f has_integral (i k)) k"
  shows "(f has_integral (setsum (\<lambda>(x,k). i k) p)) s"
proof- have *:"(f has_integral (setsum (\<lambda>k. integral k f) (snd ` p))) s"
    apply(rule has_integral_combine_division) apply(rule division_of_tagged_division[OF assms(1)])
    using assms(2) unfolding has_integral_integral[THEN sym] by(safe,auto)
  thus ?thesis apply- apply(rule subst[where P="\<lambda>i. (f has_integral i) s"]) defer apply assumption
    apply(rule trans[of _ "setsum (\<lambda>(x,k). integral k f) p"]) apply(subst eq_commute)
    apply(rule setsum_over_tagged_division_lemma[OF assms(1)]) apply(rule integral_null,assumption)
    apply(rule setsum_cong2) using assms(2) by auto qed

lemma integral_combine_tagged_division_bottomup: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "p tagged_division_of {a..b}" "\<forall>(x,k)\<in>p. f integrable_on k"
  shows "integral {a..b} f = setsum (\<lambda>(x,k). integral k f) p"
  apply(rule integral_unique) apply(rule has_integral_combine_tagged_division[OF assms(1)])
  using assms(2) by auto

lemma has_integral_combine_tagged_division_topdown: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}" "p tagged_division_of {a..b}"
  shows "(f has_integral (setsum (\<lambda>(x,k). integral k f) p)) {a..b}"
  apply(rule has_integral_combine_tagged_division[OF assms(2)])
proof safe case goal1 note tagged_division_ofD(3-4)[OF assms(2) this]
  thus ?case using integrable_subinterval[OF assms(1)] by auto qed

lemma integral_combine_tagged_division_topdown: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}" "p tagged_division_of {a..b}"
  shows "integral {a..b} f = setsum (\<lambda>(x,k). integral k f) p"
  apply(rule integral_unique,rule has_integral_combine_tagged_division_topdown) using assms by auto

subsection {* Henstock's lemma. *}

lemma henstock_lemma_part1: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}" "0 < e" "gauge d"
  "(\<forall>p. p tagged_division_of {a..b} \<and> d fine p \<longrightarrow> norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - integral({a..b}) f) < e)"
  and p:"p tagged_partial_division_of {a..b}" "d fine p"
  shows "norm(setsum (\<lambda>(x,k). content k *\<^sub>R f x - integral k f) p) \<le> e" (is "?x \<le> e")
proof-  { presume "\<And>k. 0<k \<Longrightarrow> ?x \<le> e + k" thus ?thesis by (blast intro: field_le_epsilon) }
  fix k::real assume k:"k>0" note p' = tagged_partial_division_ofD[OF p(1)]
  have "\<Union>snd ` p \<subseteq> {a..b}" using p'(3) by fastforce
  note partial_division_of_tagged_division[OF p(1)] this
  from partial_division_extend_interval[OF this] guess q . note q=this and q' = division_ofD[OF this(2)]
  def r \<equiv> "q - snd ` p" have "snd ` p \<inter> r = {}" unfolding r_def by auto
  have r:"finite r" using q' unfolding r_def by auto

  have "\<forall>i\<in>r. \<exists>p. p tagged_division_of i \<and> d fine p \<and>
    norm(setsum (\<lambda>(x,j). content j *\<^sub>R f x) p - integral i f) < k / (real (card r) + 1)"
  proof safe case goal1 hence i:"i \<in> q" unfolding r_def by auto
    from q'(4)[OF this] guess u v apply-by(erule exE)+ note uv=this
    have *:"k / (real (card r) + 1) > 0" apply(rule divide_pos_pos,rule k) by auto
    have "f integrable_on {u..v}" apply(rule integrable_subinterval[OF assms(1)])
      using q'(2)[OF i] unfolding uv by auto
    note integrable_integral[OF this, unfolded has_integral[of f]]
    from this[rule_format,OF *] guess dd .. note dd=conjunctD2[OF this,rule_format]
    note gauge_inter[OF `gauge d` dd(1)] from fine_division_exists[OF this,of u v] guess qq .
    thus ?case apply(rule_tac x=qq in exI) using dd(2)[of qq] unfolding fine_inter uv by auto qed
  from bchoice[OF this] guess qq .. note qq=this[rule_format]

  let ?p = "p \<union> \<Union>qq ` r" have "norm ((\<Sum>(x, k)\<in>?p. content k *\<^sub>R f x) - integral {a..b} f) < e"
    apply(rule assms(4)[rule_format])
  proof show "d fine ?p" apply(rule fine_union,rule p) apply(rule fine_unions) using qq by auto 
    note * = tagged_partial_division_of_union_self[OF p(1)]
    have "p \<union> \<Union>qq ` r tagged_division_of \<Union>snd ` p \<union> \<Union>r"
    proof(rule tagged_division_union[OF * tagged_division_unions])
      show "finite r" by fact case goal2 thus ?case using qq by auto
    next case goal3 thus ?case apply(rule,rule,rule) apply(rule q'(5)) unfolding r_def by auto
    next case goal4 thus ?case apply(rule inter_interior_unions_intervals) apply(fact,rule)
        apply(rule,rule q') defer apply(rule,subst Int_commute) 
        apply(rule inter_interior_unions_intervals) apply(rule finite_imageI,rule p',rule) defer
        apply(rule,rule q') using q(1) p' unfolding r_def by auto qed
    moreover have "\<Union>snd ` p \<union> \<Union>r = {a..b}" "{qq i |i. i \<in> r} = qq ` r"
      unfolding Union_Un_distrib[THEN sym] r_def using q by auto
    ultimately show "?p tagged_division_of {a..b}" by fastforce qed

  hence "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>\<Union>qq ` r. content k *\<^sub>R f x) -
    integral {a..b} f) < e" apply(subst setsum_Un_zero[THEN sym]) apply(rule p') prefer 3 
    apply assumption apply rule apply(rule finite_imageI,rule r) apply safe apply(drule qq)
  proof- fix x l k assume as:"(x,l)\<in>p" "(x,l)\<in>qq k" "k\<in>r"
    note qq[OF this(3)] note tagged_division_ofD(3,4)[OF conjunct1[OF this] as(2)]
    from this(2) guess u v apply-by(erule exE)+ note uv=this
    have "l\<in>snd ` p" unfolding image_iff apply(rule_tac x="(x,l)" in bexI) using as by auto
    hence "l\<in>q" "k\<in>q" "l\<noteq>k" using as(1,3) q(1) unfolding r_def by auto
    note q'(5)[OF this] hence "interior l = {}" using interior_mono[OF `l \<subseteq> k`] by blast
    thus "content l *\<^sub>R f x = 0" unfolding uv content_eq_0_interior[THEN sym] by auto qed auto

  hence "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) + setsum (setsum (\<lambda>(x, k). content k *\<^sub>R f x))
    (qq ` r) - integral {a..b} f) < e" apply(subst(asm) setsum_UNION_zero)
    prefer 4 apply assumption apply(rule finite_imageI,fact)
    unfolding split_paired_all split_conv image_iff defer apply(erule bexE)+
  proof- fix x m k l T1 T2 assume "(x,m)\<in>T1" "(x,m)\<in>T2" "T1\<noteq>T2" "k\<in>r" "l\<in>r" "T1 = qq k" "T2 = qq l"
    note as = this(1-5)[unfolded this(6-)] note kl = tagged_division_ofD(3,4)[OF qq[THEN conjunct1]]
    from this(2)[OF as(4,1)] guess u v apply-by(erule exE)+ note uv=this
    have *:"interior (k \<inter> l) = {}" unfolding interior_inter apply(rule q')
      using as unfolding r_def by auto
    have "interior m = {}" unfolding subset_empty[THEN sym] unfolding *[THEN sym]
      apply(rule interior_mono) using kl(1)[OF as(4,1)] kl(1)[OF as(5,2)] by auto
    thus "content m *\<^sub>R f x = 0" unfolding uv content_eq_0_interior[THEN sym] by auto 
  qed(insert qq, auto)

  hence **:"norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) + setsum (setsum (\<lambda>(x, k). content k *\<^sub>R f x) \<circ> qq) r -
    integral {a..b} f) < e" apply(subst(asm) setsum_reindex_nonzero) apply fact
    apply(rule setsum_0',rule) unfolding split_paired_all split_conv defer apply assumption
  proof- fix k l x m assume as:"k\<in>r" "l\<in>r" "k\<noteq>l" "qq k = qq l" "(x,m)\<in>qq k"
    note tagged_division_ofD(6)[OF qq[THEN conjunct1]] from this[OF as(1)] this[OF as(2)] 
    show "content m *\<^sub>R f x = 0"  using as(3) unfolding as by auto qed
  
  have *:"\<And>ir ip i cr cp. norm((cp + cr) - i) < e \<Longrightarrow> norm(cr - ir) < k \<Longrightarrow> 
    ip + ir = i \<Longrightarrow> norm(cp - ip) \<le> e + k" 
  proof- case goal1 thus ?case  using norm_triangle_le[of "cp + cr - i" "- (cr - ir)"]  
      unfolding goal1(3)[THEN sym] norm_minus_cancel by(auto simp add:algebra_simps) qed
  
  have "?x =  norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p. integral k f))"
    unfolding split_def setsum_subtractf ..
  also have "... \<le> e + k" apply(rule *[OF **, where ir="setsum (\<lambda>k. integral k f) r"])
  proof- case goal2 have *:"(\<Sum>(x, k)\<in>p. integral k f) = (\<Sum>k\<in>snd ` p. integral k f)"
      apply(subst setsum_reindex_nonzero) apply fact
      unfolding split_paired_all snd_conv split_def o_def
    proof- fix x l y m assume as:"(x,l)\<in>p" "(y,m)\<in>p" "(x,l)\<noteq>(y,m)" "l = m"
      from p'(4)[OF as(1)] guess u v apply-by(erule exE)+ note uv=this
      show "integral l f = 0" unfolding uv apply(rule integral_unique)
        apply(rule has_integral_null) unfolding content_eq_0_interior
        using p'(5)[OF as(1-3)] unfolding uv as(4)[THEN sym] by auto
    qed auto 
    show ?case unfolding integral_combine_division_topdown[OF assms(1) q(2)] * r_def
      apply(rule setsum_Un_disjoint'[THEN sym]) using q(1) q'(1) p'(1) by auto
  next  case goal1 have *:"k * real (card r) / (1 + real (card r)) < k" using k by(auto simp add:field_simps)
    show ?case apply(rule le_less_trans[of _ "setsum (\<lambda>x. k / (real (card r) + 1)) r"])
      unfolding setsum_subtractf[THEN sym] apply(rule setsum_norm_le)
      apply rule apply(drule qq) defer unfolding divide_inverse setsum_left_distrib[THEN sym]
      unfolding divide_inverse[THEN sym] using * by(auto simp add:field_simps real_eq_of_nat)
  qed finally show "?x \<le> e + k" . qed

lemma henstock_lemma_part2: fixes f::"'m::ordered_euclidean_space \<Rightarrow> 'n::ordered_euclidean_space"
  assumes "f integrable_on {a..b}" "0 < e" "gauge d"
  "\<forall>p. p tagged_division_of {a..b} \<and> d fine p \<longrightarrow> norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p -
          integral({a..b}) f) < e"    "p tagged_partial_division_of {a..b}" "d fine p"
  shows "setsum (\<lambda>(x,k). norm(content k *\<^sub>R f x - integral k f)) p \<le> 2 * real (DIM('n)) * e"
  unfolding split_def apply(rule setsum_norm_allsubsets_bound) defer 
  apply(rule henstock_lemma_part1[unfolded split_def,OF assms(1-3)])
  apply safe apply(rule assms[rule_format,unfolded split_def]) defer
  apply(rule tagged_partial_division_subset,rule assms,assumption)
  apply(rule fine_subset,assumption,rule assms) using assms(5) by auto
  
lemma henstock_lemma: fixes f::"'m::ordered_euclidean_space \<Rightarrow> 'n::ordered_euclidean_space"
  assumes "f integrable_on {a..b}" "e>0"
  obtains d where "gauge d"
  "\<forall>p. p tagged_partial_division_of {a..b} \<and> d fine p
  \<longrightarrow> setsum (\<lambda>(x,k). norm(content k *\<^sub>R f x - integral k f)) p < e"
proof- have *:"e / (2 * (real DIM('n) + 1)) > 0" apply(rule divide_pos_pos) using assms(2) by auto
  from integrable_integral[OF assms(1),unfolded has_integral[of f],rule_format,OF this]
  guess d .. note d = conjunctD2[OF this] show thesis apply(rule that,rule d)
  proof safe case goal1 note * = henstock_lemma_part2[OF assms(1) * d this]
    show ?case apply(rule le_less_trans[OF *]) using `e>0` by(auto simp add:field_simps) qed qed

subsection {* Geometric progression *}

text {* FIXME: Should one or more of these theorems be moved to @{file
"~~/src/HOL/SetInterval.thy"}, alongside @{text geometric_sum}? *}

lemma sum_gp_basic:
  fixes x :: "'a::ring_1"
  shows "(1 - x) * setsum (\<lambda>i. x^i) {0 .. n} = (1 - x^(Suc n))"
proof-
  def y \<equiv> "1 - x"
  have "y * (\<Sum>i=0..n. (1 - y) ^ i) = 1 - (1 - y) ^ Suc n"
    by (induct n, simp, simp add: algebra_simps)
  thus ?thesis
    unfolding y_def by simp
qed

lemma sum_gp_multiplied: assumes mn: "m <= n"
  shows "((1::'a::{field}) - x) * setsum (op ^ x) {m..n} = x^m - x^ Suc n"
  (is "?lhs = ?rhs")
proof-
  let ?S = "{0..(n - m)}"
  from mn have mn': "n - m \<ge> 0" by arith
  let ?f = "op + m"
  have i: "inj_on ?f ?S" unfolding inj_on_def by auto
  have f: "?f ` ?S = {m..n}"
    using mn apply (auto simp add: image_iff Bex_def) by arith
  have th: "op ^ x o op + m = (\<lambda>i. x^m * x^i)"
    by (rule ext, simp add: power_add power_mult)
  from setsum_reindex[OF i, of "op ^ x", unfolded f th setsum_right_distrib[symmetric]]
  have "?lhs = x^m * ((1 - x) * setsum (op ^ x) {0..n - m})" by simp
  then show ?thesis unfolding sum_gp_basic using mn
    by (simp add: field_simps power_add[symmetric])
qed

lemma sum_gp: "setsum (op ^ (x::'a::{field})) {m .. n} =
   (if n < m then 0 else if x = 1 then of_nat ((n + 1) - m)
                    else (x^ m - x^ (Suc n)) / (1 - x))"
proof-
  {assume nm: "n < m" hence ?thesis by simp}
  moreover
  {assume "\<not> n < m" hence nm: "m \<le> n" by arith
    {assume x: "x = 1"  hence ?thesis by simp}
    moreover
    {assume x: "x \<noteq> 1" hence nz: "1 - x \<noteq> 0" by simp
      from sum_gp_multiplied[OF nm, of x] nz have ?thesis by (simp add: field_simps)}
    ultimately have ?thesis by metis
  }
  ultimately show ?thesis by metis
qed

lemma sum_gp_offset: "setsum (op ^ (x::'a::{field})) {m .. m+n} =
  (if x = 1 then of_nat n + 1 else x^m * (1 - x^Suc n) / (1 - x))"
  unfolding sum_gp[of x m "m + n"] power_Suc
  by (simp add: field_simps power_add)

subsection {* monotone convergence (bounded interval first). *}

lemma monotone_convergence_interval: fixes f::"nat \<Rightarrow> 'n::ordered_euclidean_space \<Rightarrow> real"
  assumes "\<forall>k. (f k) integrable_on {a..b}"
  "\<forall>k. \<forall>x\<in>{a..b}.(f k x) \<le> (f (Suc k) x)"
  "\<forall>x\<in>{a..b}. ((\<lambda>k. f k x) ---> g x) sequentially"
  "bounded {integral {a..b} (f k) | k . k \<in> UNIV}"
  shows "g integrable_on {a..b} \<and> ((\<lambda>k. integral ({a..b}) (f k)) ---> integral ({a..b}) g) sequentially"
proof(case_tac[!] "content {a..b} = 0") assume as:"content {a..b} = 0"
  show ?thesis using integrable_on_null[OF as] unfolding integral_null[OF as] using tendsto_const by auto
next assume ab:"content {a..b} \<noteq> 0"
  have fg:"\<forall>x\<in>{a..b}. \<forall> k. (f k x) $$ 0 \<le> (g x) $$ 0"
  proof safe case goal1 note assms(3)[rule_format,OF this]
    note * = Lim_component_ge[OF this trivial_limit_sequentially]
    show ?case apply(rule *) unfolding eventually_sequentially
      apply(rule_tac x=k in exI) apply- apply(rule transitive_stepwise_le)
      using assms(2)[rule_format,OF goal1] by auto qed
  have "\<exists>i. ((\<lambda>k. integral ({a..b}) (f k)) ---> i) sequentially"
    apply(rule bounded_increasing_convergent) defer
    apply rule apply(rule integral_le) apply safe
    apply(rule assms(1-2)[rule_format])+ using assms(4) by auto
  then guess i .. note i=this
  have i':"\<And>k. (integral({a..b}) (f k)) \<le> i$$0"
    apply(rule Lim_component_ge,rule i) apply(rule trivial_limit_sequentially)
    unfolding eventually_sequentially apply(rule_tac x=k in exI)
    apply(rule transitive_stepwise_le) prefer 3 unfolding Eucl_real_simps apply(rule integral_le)
    apply(rule assms(1-2)[rule_format])+ using assms(2) by auto

  have "(g has_integral i) {a..b}" unfolding has_integral
  proof safe case goal1 note e=this
    hence "\<forall>k. (\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a..b} \<and> d fine p \<longrightarrow>
             norm ((\<Sum>(x, ka)\<in>p. content ka *\<^sub>R f k x) - integral {a..b} (f k)) < e / 2 ^ (k + 2)))"
      apply-apply(rule,rule assms(1)[unfolded has_integral_integral has_integral,rule_format])
      apply(rule divide_pos_pos) by auto
    from choice[OF this] guess c .. note c=conjunctD2[OF this[rule_format],rule_format]

    have "\<exists>r. \<forall>k\<ge>r. 0 \<le> i$$0 - (integral {a..b} (f k)) \<and> i$$0 - (integral {a..b} (f k)) < e / 4"
    proof- case goal1 have "e/4 > 0" using e by auto
      from LIMSEQ_D [OF i this] guess r ..
      thus ?case apply(rule_tac x=r in exI) apply rule
        apply(erule_tac x=k in allE)
      proof- case goal1 thus ?case using i'[of k] by auto qed qed
    then guess r .. note r=conjunctD2[OF this[rule_format]]

    have "\<forall>x\<in>{a..b}. \<exists>n\<ge>r. \<forall>k\<ge>n. 0 \<le> (g x)$$0 - (f k x)$$0 \<and>
           (g x)$$0 - (f k x)$$0 < e / (4 * content({a..b}))"
    proof case goal1 have "e / (4 * content {a..b}) > 0" apply(rule divide_pos_pos,fact)
        using ab content_pos_le[of a b] by auto
      from assms(3)[rule_format, OF goal1, THEN LIMSEQ_D, OF this]
      guess n .. note n=this
      thus ?case apply(rule_tac x="n + r" in exI) apply safe apply(erule_tac[2-3] x=k in allE)
        unfolding dist_real_def using fg[rule_format,OF goal1] by(auto simp add:field_simps) qed
    from bchoice[OF this] guess m .. note m=conjunctD2[OF this[rule_format],rule_format]
    def d \<equiv> "\<lambda>x. c (m x) x" 

    show ?case apply(rule_tac x=d in exI)
    proof safe show "gauge d" using c(1) unfolding gauge_def d_def by auto
    next fix p assume p:"p tagged_division_of {a..b}" "d fine p"
      note p'=tagged_division_ofD[OF p(1)]
      have "\<exists>a. \<forall>x\<in>p. m (fst x) \<le> a"
        by (metis finite_imageI finite_nat_set_iff_bounded_le p'(1) rev_image_eqI)
      then guess s .. note s=this
      have *:"\<forall>a b c d. norm(a - b) \<le> e / 4 \<and> norm(b - c) < e / 2 \<and>
            norm(c - d) < e / 4 \<longrightarrow> norm(a - d) < e" 
      proof safe case goal1 thus ?case using norm_triangle_lt[of "a - b" "b - c" "3* e/4"]
          norm_triangle_lt[of "a - b + (b - c)" "c - d" e] unfolding norm_minus_cancel
          by(auto simp add:algebra_simps) qed
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R g x) - i) < e" apply(rule *[rule_format,where
          b="\<Sum>(x, k)\<in>p. content k *\<^sub>R f (m x) x" and c="\<Sum>(x, k)\<in>p. integral k (f (m x))"])
      proof safe case goal1
         show ?case apply(rule order_trans[of _ "\<Sum>(x, k)\<in>p. content k * (e / (4 * content {a..b}))"])
           unfolding setsum_subtractf[THEN sym] apply(rule order_trans,rule norm_setsum)
           apply(rule setsum_mono) unfolding split_paired_all split_conv
           unfolding split_def setsum_left_distrib[THEN sym] scaleR_diff_right[THEN sym]
           unfolding additive_content_tagged_division[OF p(1), unfolded split_def]
         proof- fix x k assume xk:"(x,k) \<in> p" hence x:"x\<in>{a..b}" using p'(2-3)[OF xk] by auto
           from p'(4)[OF xk] guess u v apply-by(erule exE)+ note uv=this
           show " norm (content k *\<^sub>R (g x - f (m x) x)) \<le> content k * (e / (4 * content {a..b}))"
             unfolding norm_scaleR uv unfolding abs_of_nonneg[OF content_pos_le] 
             apply(rule mult_left_mono) using m(2)[OF x,of "m x"] by auto
         qed(insert ab,auto)
         
       next case goal2 show ?case apply(rule le_less_trans[of _ "norm (\<Sum>j = 0..s.
           \<Sum>(x, k)\<in>{xk\<in>p. m (fst xk) = j}. content k *\<^sub>R f (m x) x - integral k (f (m x)))"])
           apply(subst setsum_group) apply fact apply(rule finite_atLeastAtMost) defer
           apply(subst split_def)+ unfolding setsum_subtractf apply rule
         proof- show "norm (\<Sum>j = 0..s. \<Sum>(x, k)\<in>{xk \<in> p.
             m (fst xk) = j}. content k *\<^sub>R f (m x) x - integral k (f (m x))) < e / 2"
             apply(rule le_less_trans[of _ "setsum (\<lambda>i. e / 2^(i+2)) {0..s}"])
             apply(rule setsum_norm_le)
           proof show "(\<Sum>i = 0..s. e / 2 ^ (i + 2)) < e / 2"
               unfolding power_add divide_inverse inverse_mult_distrib
               unfolding setsum_right_distrib[THEN sym] setsum_left_distrib[THEN sym]
               unfolding power_inverse sum_gp apply(rule mult_strict_left_mono[OF _ e])
               unfolding power2_eq_square by auto
             fix t assume "t\<in>{0..s}"
             show "norm (\<Sum>(x, k)\<in>{xk \<in> p. m (fst xk) = t}. content k *\<^sub>R f (m x) x -
               integral k (f (m x))) \<le> e / 2 ^ (t + 2)"apply(rule order_trans[of _
               "norm(setsum (\<lambda>(x,k). content k *\<^sub>R f t x - integral k (f t)) {xk \<in> p. m (fst xk) = t})"])
               apply(rule eq_refl) apply(rule arg_cong[where f=norm]) apply(rule setsum_cong2) defer
               apply(rule henstock_lemma_part1) apply(rule assms(1)[rule_format])
               apply(rule divide_pos_pos,rule e) defer  apply safe apply(rule c)+
               apply rule apply assumption+ apply(rule tagged_partial_division_subset[of p])
               apply(rule p(1)[unfolded tagged_division_of_def,THEN conjunct1]) defer
               unfolding fine_def apply safe apply(drule p(2)[unfolded fine_def,rule_format])
               unfolding d_def by auto qed
         qed(insert s, auto)

       next case goal3
         note comb = integral_combine_tagged_division_topdown[OF assms(1)[rule_format] p(1)]
         have *:"\<And>sr sx ss ks kr::real. kr = sr \<longrightarrow> ks = ss \<longrightarrow> ks \<le> i \<and> sr \<le> sx \<and> sx \<le> ss \<and> 0 \<le> i$$0 - kr$$0
           \<and> i$$0 - kr$$0 < e/4 \<longrightarrow> abs(sx - i) < e/4" by auto 
         show ?case unfolding real_norm_def apply(rule *[rule_format],safe)
           apply(rule comb[of r],rule comb[of s]) apply(rule i'[unfolded Eucl_real_simps]) 
           apply(rule_tac[1-2] setsum_mono) unfolding split_paired_all split_conv
           apply(rule_tac[1-2] integral_le[OF ])
         proof safe show "0 \<le> i$$0 - (integral {a..b} (f r))$$0" using r(1) by auto
           show "i$$0 - (integral {a..b} (f r))$$0 < e / 4" using r(2) by auto
           fix x k assume xk:"(x,k)\<in>p" from p'(4)[OF this] guess u v apply-by(erule exE)+ note uv=this
           show "f r integrable_on k" "f s integrable_on k" "f (m x) integrable_on k" "f (m x) integrable_on k" 
             unfolding uv apply(rule_tac[!] integrable_on_subinterval[OF assms(1)[rule_format]])
             using p'(3)[OF xk] unfolding uv by auto 
           fix y assume "y\<in>k" hence "y\<in>{a..b}" using p'(3)[OF xk] by auto
           hence *:"\<And>m. \<forall>n\<ge>m. (f m y) \<le> (f n y)" apply-apply(rule transitive_stepwise_le) using assms(2) by auto
           show "(f r y) \<le> (f (m x) y)" "(f (m x) y) \<le> (f s y)"
             apply(rule_tac[!] *[rule_format]) using s[rule_format,OF xk] m(1)[of x] p'(2-3)[OF xk] by auto
         qed qed qed qed note * = this 

   have "integral {a..b} g = i" apply(rule integral_unique) using * .
   thus ?thesis using i * by auto qed

lemma monotone_convergence_increasing: fixes f::"nat \<Rightarrow> 'n::ordered_euclidean_space \<Rightarrow> real"
  assumes "\<forall>k. (f k) integrable_on s"  "\<forall>k. \<forall>x\<in>s. (f k x) \<le> (f (Suc k) x)"
  "\<forall>x\<in>s. ((\<lambda>k. f k x) ---> g x) sequentially" "bounded {integral s (f k)| k. True}"
  shows "g integrable_on s \<and> ((\<lambda>k. integral s (f k)) ---> integral s g) sequentially"
proof- have lem:"\<And>f::nat \<Rightarrow> 'n::ordered_euclidean_space \<Rightarrow> real. \<And> g s. \<forall>k.\<forall>x\<in>s. 0 \<le> (f k x) \<Longrightarrow> \<forall>k. (f k) integrable_on s \<Longrightarrow>
    \<forall>k. \<forall>x\<in>s. (f k x) \<le> (f (Suc k) x) \<Longrightarrow> \<forall>x\<in>s. ((\<lambda>k. f k x) ---> g x) sequentially  \<Longrightarrow>
    bounded {integral s (f k)| k. True} \<Longrightarrow> g integrable_on s \<and> ((\<lambda>k. integral s (f k)) ---> integral s g) sequentially"
  proof- case goal1 note assms=this[rule_format]
    have "\<forall>x\<in>s. \<forall>k. (f k x)$$0 \<le> (g x)$$0" apply safe apply(rule Lim_component_ge)
      apply(rule goal1(4)[rule_format],assumption) apply(rule trivial_limit_sequentially)
      unfolding eventually_sequentially apply(rule_tac x=k in exI)
      apply(rule transitive_stepwise_le) using goal1(3) by auto note fg=this[rule_format]

    have "\<exists>i. ((\<lambda>k. integral s (f k)) ---> i) sequentially" apply(rule bounded_increasing_convergent)
      apply(rule goal1(5)) apply(rule,rule integral_le) apply(rule goal1(2)[rule_format])+
      using goal1(3) by auto then guess i .. note i=this
    have "\<And>k. \<forall>x\<in>s. \<forall>n\<ge>k. f k x \<le> f n x" apply(rule,rule transitive_stepwise_le) using goal1(3) by auto
    hence i':"\<forall>k. (integral s (f k))$$0 \<le> i$$0" apply-apply(rule,rule Lim_component_ge)
      apply(rule i,rule trivial_limit_sequentially) unfolding eventually_sequentially
      apply(rule_tac x=k in exI,safe) apply(rule integral_component_le)
      apply(rule goal1(2)[rule_format])+ by auto 

    note int = assms(2)[unfolded integrable_alt[of _ s],THEN conjunct1,rule_format]
    have ifif:"\<And>k t. (\<lambda>x. if x \<in> t then if x \<in> s then f k x else 0 else 0) =
      (\<lambda>x. if x \<in> t\<inter>s then f k x else 0)" apply(rule ext) by auto
    have int':"\<And>k a b. f k integrable_on {a..b} \<inter> s" apply(subst integrable_restrict_univ[THEN sym])
      apply(subst ifif[THEN sym]) apply(subst integrable_restrict_univ) using int .
    have "\<And>a b. (\<lambda>x. if x \<in> s then g x else 0) integrable_on {a..b} \<and>
      ((\<lambda>k. integral {a..b} (\<lambda>x. if x \<in> s then f k x else 0)) --->
      integral {a..b} (\<lambda>x. if x \<in> s then g x else 0)) sequentially"
    proof(rule monotone_convergence_interval,safe)
      case goal1 show ?case using int .
    next case goal2 thus ?case apply-apply(cases "x\<in>s") using assms(3) by auto
    next case goal3 thus ?case apply-apply(cases "x\<in>s")
        using assms(4) by auto
    next case goal4 note * = integral_nonneg
      have "\<And>k. norm (integral {a..b} (\<lambda>x. if x \<in> s then f k x else 0)) \<le> norm (integral s (f k))"
        unfolding real_norm_def apply(subst abs_of_nonneg) apply(rule *[OF int])
        apply(safe,case_tac "x\<in>s") apply(drule assms(1)) prefer 3
        apply(subst abs_of_nonneg) apply(rule *[OF assms(2) goal1(1)[THEN spec]])
        apply(subst integral_restrict_univ[THEN sym,OF int]) 
        unfolding ifif unfolding integral_restrict_univ[OF int']
        apply(rule integral_subset_le[OF _ int' assms(2)]) using assms(1) by auto
      thus ?case using assms(5) unfolding bounded_iff apply safe
        apply(rule_tac x=aa in exI,safe) apply(erule_tac x="integral s (f k)" in ballE)
        apply(rule order_trans) apply assumption by auto qed note g = conjunctD2[OF this]

    have "(g has_integral i) s" unfolding has_integral_alt' apply safe apply(rule g(1))
    proof- case goal1 hence "e/4>0" by auto
      from LIMSEQ_D [OF i this] guess N .. note N=this
      note assms(2)[of N,unfolded has_integral_integral has_integral_alt'[of "f N"]]
      from this[THEN conjunct2,rule_format,OF `e/4>0`] guess B .. note B=conjunctD2[OF this]
      show ?case apply(rule,rule,rule B,safe)
      proof- fix a b::"'n::ordered_euclidean_space" assume ab:"ball 0 B \<subseteq> {a..b}"
        from `e>0` have "e/2>0" by auto
        from LIMSEQ_D [OF g(2)[of a b] this] guess M .. note M=this
        have **:"norm (integral {a..b} (\<lambda>x. if x \<in> s then f N x else 0) - i) < e/2"
          apply(rule norm_triangle_half_l) using B(2)[rule_format,OF ab] N[rule_format,of N]
          apply-defer apply(subst norm_minus_commute) by auto
        have *:"\<And>f1 f2 g. abs(f1 - i) < e / 2 \<longrightarrow> abs(f2 - g) < e / 2 \<longrightarrow> f1 \<le> f2 \<longrightarrow> f2 \<le> i
          \<longrightarrow> abs(g - i) < e" unfolding Eucl_real_simps by arith
        show "norm (integral {a..b} (\<lambda>x. if x \<in> s then g x else 0) - i) < e" 
          unfolding real_norm_def apply(rule *[rule_format])
          apply(rule **[unfolded real_norm_def])
          apply(rule M[rule_format,of "M + N",unfolded real_norm_def]) apply(rule le_add1)
          apply(rule integral_le[OF int int]) defer
          apply(rule order_trans[OF _ i'[rule_format,of "M + N",unfolded Eucl_real_simps]])
        proof safe case goal2 have "\<And>m. x\<in>s \<Longrightarrow> \<forall>n\<ge>m. (f m x)$$0 \<le> (f n x)$$0"
            apply(rule transitive_stepwise_le) using assms(3) by auto thus ?case by auto
        next case goal1 show ?case apply(subst integral_restrict_univ[THEN sym,OF int]) 
            unfolding ifif integral_restrict_univ[OF int']
            apply(rule integral_subset_le[OF _ int']) using assms by auto
        qed qed qed 
    thus ?case apply safe defer apply(drule integral_unique) using i by auto qed

  have sub:"\<And>k. integral s (\<lambda>x. f k x - f 0 x) = integral s (f k) - integral s (f 0)"
    apply(subst integral_sub) apply(rule assms(1)[rule_format])+ by rule
  have "\<And>x m. x\<in>s \<Longrightarrow> \<forall>n\<ge>m. (f m x) \<le> (f n x)" apply(rule transitive_stepwise_le)
    using assms(2) by auto note * = this[rule_format]
  have "(\<lambda>x. g x - f 0 x) integrable_on s \<and>((\<lambda>k. integral s (\<lambda>x. f (Suc k) x - f 0 x)) --->
      integral s (\<lambda>x. g x - f 0 x)) sequentially" apply(rule lem,safe)
  proof- case goal1 thus ?case using *[of x 0 "Suc k"] by auto
  next case goal2 thus ?case apply(rule integrable_sub) using assms(1) by auto
  next case goal3 thus ?case using *[of x "Suc k" "Suc (Suc k)"] by auto
  next case goal4 thus ?case apply-apply(rule tendsto_diff) 
      using seq_offset[OF assms(3)[rule_format],of x 1] by auto
  next case goal5 thus ?case using assms(4) unfolding bounded_iff
      apply safe apply(rule_tac x="a + norm (integral s (\<lambda>x. f 0 x))" in exI)
      apply safe apply(erule_tac x="integral s (\<lambda>x. f (Suc k) x)" in ballE) unfolding sub
      apply(rule order_trans[OF norm_triangle_ineq4]) by auto qed
  note conjunctD2[OF this] note tendsto_add[OF this(2) tendsto_const[of "integral s (f 0)"]]
    integrable_add[OF this(1) assms(1)[rule_format,of 0]]
  thus ?thesis unfolding sub apply-apply rule defer apply(subst(asm) integral_sub)
    using assms(1) apply auto apply(rule seq_offset_rev[where k=1]) by auto qed

lemma monotone_convergence_decreasing: fixes f::"nat \<Rightarrow> 'n::ordered_euclidean_space \<Rightarrow> real"
  assumes "\<forall>k. (f k) integrable_on s"  "\<forall>k. \<forall>x\<in>s. (f (Suc k) x) \<le> (f k x)"
  "\<forall>x\<in>s. ((\<lambda>k. f k x) ---> g x) sequentially" "bounded {integral s (f k)| k. True}"
  shows "g integrable_on s \<and> ((\<lambda>k. integral s (f k)) ---> integral s g) sequentially"
proof- note assm = assms[rule_format]
  have *:"{integral s (\<lambda>x. - f k x) |k. True} = op *\<^sub>R -1 ` {integral s (f k)| k. True}"
    apply safe unfolding image_iff apply(rule_tac x="integral s (f k)" in bexI) prefer 3
    apply(rule_tac x=k in exI) unfolding integral_neg[OF assm(1)] by auto
  have "(\<lambda>x. - g x) integrable_on s \<and> ((\<lambda>k. integral s (\<lambda>x. - f k x))
    ---> integral s (\<lambda>x. - g x))  sequentially" apply(rule monotone_convergence_increasing)
    apply(safe,rule integrable_neg) apply(rule assm) defer apply(rule tendsto_minus)
    apply(rule assm,assumption) unfolding * apply(rule bounded_scaling) using assm by auto
  note * = conjunctD2[OF this]
  show ?thesis apply rule using integrable_neg[OF *(1)] defer
    using tendsto_minus[OF *(2)] apply- unfolding integral_neg[OF assm(1)]
    unfolding integral_neg[OF *(1),THEN sym] by auto qed

subsection {* absolute integrability (this is the same as Lebesgue integrability). *}

definition absolutely_integrable_on (infixr "absolutely'_integrable'_on" 46) where
  "f absolutely_integrable_on s \<longleftrightarrow> f integrable_on s \<and> (\<lambda>x. (norm(f x))) integrable_on s"

lemma absolutely_integrable_onI[intro?]:
  "f integrable_on s \<Longrightarrow> (\<lambda>x. (norm(f x))) integrable_on s \<Longrightarrow> f absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def by auto

lemma absolutely_integrable_onD[dest]: assumes "f absolutely_integrable_on s"
  shows "f integrable_on s" "(\<lambda>x. (norm(f x))) integrable_on s"
  using assms unfolding absolutely_integrable_on_def by auto

(*lemma absolutely_integrable_on_trans[simp]: fixes f::"'n::ordered_euclidean_space \<Rightarrow> real" shows
  "(vec1 o f) absolutely_integrable_on s \<longleftrightarrow> f absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def o_def by auto*)

lemma integral_norm_bound_integral: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s" "g integrable_on s" "\<forall>x\<in>s. norm(f x) \<le> g x"
  shows "norm(integral s f) \<le> (integral s g)"
proof- have *:"\<And>x y. (\<forall>e::real. 0 < e \<longrightarrow> x < y + e) \<longrightarrow> x \<le> y" apply(safe,rule ccontr)
    apply(erule_tac x="x - y" in allE) by auto
  have "\<And>e sg dsa dia ig. norm(sg) \<le> dsa \<longrightarrow> abs(dsa - dia) < e / 2 \<longrightarrow> norm(sg - ig) < e / 2
    \<longrightarrow> norm(ig) < dia + e" 
  proof safe case goal1 show ?case apply(rule le_less_trans[OF norm_triangle_sub[of ig sg]])
      apply(subst real_sum_of_halves[of e,THEN sym]) unfolding add_assoc[symmetric]
      apply(rule add_le_less_mono) defer apply(subst norm_minus_commute,rule goal1)
      apply(rule order_trans[OF goal1(1)]) using goal1(2) by arith
  qed note norm=this[rule_format]
  have lem:"\<And>f::'n::ordered_euclidean_space \<Rightarrow> 'a. \<And> g a b. f integrable_on {a..b} \<Longrightarrow> g integrable_on {a..b} \<Longrightarrow>
    \<forall>x\<in>{a..b}. norm(f x) \<le> (g x) \<Longrightarrow> norm(integral({a..b}) f) \<le> (integral({a..b}) g)"
  proof(rule *[rule_format]) case goal1 hence *:"e/2>0" by auto
    from integrable_integral[OF goal1(1),unfolded has_integral[of f],rule_format,OF *]
    guess d1 .. note d1 = conjunctD2[OF this,rule_format]
    from integrable_integral[OF goal1(2),unfolded has_integral[of g],rule_format,OF *]
    guess d2 .. note d2 = conjunctD2[OF this,rule_format]
    note gauge_inter[OF d1(1) d2(1)]
    from fine_division_exists[OF this, of a b] guess p . note p=this
    show ?case apply(rule norm) defer
      apply(rule d2(2)[OF conjI[OF p(1)],unfolded real_norm_def]) defer
      apply(rule d1(2)[OF conjI[OF p(1)]]) defer apply(rule setsum_norm_le)
    proof safe fix x k assume "(x,k)\<in>p" note as = tagged_division_ofD(2-4)[OF p(1) this]
      from this(3) guess u v apply-by(erule exE)+ note uv=this
      show "norm (content k *\<^sub>R f x) \<le> content k *\<^sub>R g x" unfolding uv norm_scaleR
        unfolding abs_of_nonneg[OF content_pos_le] real_scaleR_def
        apply(rule mult_left_mono) using goal1(3) as by auto
    qed(insert p[unfolded fine_inter],auto) qed

  { presume "\<And>e. 0 < e \<Longrightarrow> norm (integral s f) < integral s g + e" 
    thus ?thesis apply-apply(rule *[rule_format]) by auto }
  fix e::real assume "e>0" hence e:"e/2 > 0" by auto
  note assms(1)[unfolded integrable_alt[of f]] note f=this[THEN conjunct1,rule_format]
  note assms(2)[unfolded integrable_alt[of g]] note g=this[THEN conjunct1,rule_format]
  from integrable_integral[OF assms(1),unfolded has_integral'[of f],rule_format,OF e]
  guess B1 .. note B1=conjunctD2[OF this[rule_format],rule_format]
  from integrable_integral[OF assms(2),unfolded has_integral'[of g],rule_format,OF e]
  guess B2 .. note B2=conjunctD2[OF this[rule_format],rule_format]
  from bounded_subset_closed_interval[OF bounded_ball, of "0::'n::ordered_euclidean_space" "max B1 B2"]
  guess a b apply-by(erule exE)+ note ab=this[unfolded ball_max_Un]

  have "ball 0 B1 \<subseteq> {a..b}" using ab by auto
  from B1(2)[OF this] guess z .. note z=conjunctD2[OF this]
  have "ball 0 B2 \<subseteq> {a..b}" using ab by auto
  from B2(2)[OF this] guess w .. note w=conjunctD2[OF this]

  show "norm (integral s f) < integral s g + e" apply(rule norm)
    apply(rule lem[OF f g, of a b]) unfolding integral_unique[OF z(1)] integral_unique[OF w(1)]
    defer apply(rule w(2)[unfolded real_norm_def],rule z(2))
    apply safe apply(case_tac "x\<in>s") unfolding if_P apply(rule assms(3)[rule_format]) by auto qed

lemma integral_norm_bound_integral_component: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  fixes g::"'n => 'b::ordered_euclidean_space"
  assumes "f integrable_on s" "g integrable_on s"  "\<forall>x\<in>s. norm(f x) \<le> (g x)$$k"
  shows "norm(integral s f) \<le> (integral s g)$$k"
proof- have "norm (integral s f) \<le> integral s ((\<lambda>x. x $$ k) o g)"
    apply(rule integral_norm_bound_integral[OF assms(1)])
    apply(rule integrable_linear[OF assms(2)],rule)
    unfolding o_def by(rule assms)
  thus ?thesis unfolding o_def integral_component_eq[OF assms(2)] . qed

lemma has_integral_norm_bound_integral_component: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  fixes g::"'n => 'b::ordered_euclidean_space"
  assumes "(f has_integral i) s" "(g has_integral j) s" "\<forall>x\<in>s. norm(f x) \<le> (g x)$$k"
  shows "norm(i) \<le> j$$k" using integral_norm_bound_integral_component[of f s g k]
  unfolding integral_unique[OF assms(1)] integral_unique[OF assms(2)]
  using assms by auto

lemma absolutely_integrable_le: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "f absolutely_integrable_on s"
  shows "norm(integral s f) \<le> integral s (\<lambda>x. norm(f x))"
  apply(rule integral_norm_bound_integral) using assms by auto

lemma absolutely_integrable_0[intro]: "(\<lambda>x. 0) absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def by auto

lemma absolutely_integrable_cmul[intro]:
 "f absolutely_integrable_on s \<Longrightarrow> (\<lambda>x. c *\<^sub>R f x) absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def using integrable_cmul[of f s c]
  using integrable_cmul[of "\<lambda>x. norm (f x)" s "abs c"] by auto

lemma absolutely_integrable_neg[intro]:
 "f absolutely_integrable_on s \<Longrightarrow> (\<lambda>x. -f(x)) absolutely_integrable_on s"
  apply(drule absolutely_integrable_cmul[where c="-1"]) by auto

lemma absolutely_integrable_norm[intro]:
 "f absolutely_integrable_on s \<Longrightarrow> (\<lambda>x. norm(f x)) absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def by auto

lemma absolutely_integrable_abs[intro]:
 "f absolutely_integrable_on s \<Longrightarrow> (\<lambda>x. abs(f x::real)) absolutely_integrable_on s"
  apply(drule absolutely_integrable_norm) unfolding real_norm_def .

lemma absolutely_integrable_on_subinterval: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach" shows
  "f absolutely_integrable_on s \<Longrightarrow> {a..b} \<subseteq> s \<Longrightarrow> f absolutely_integrable_on {a..b}" 
  unfolding absolutely_integrable_on_def by(meson integrable_on_subinterval)

lemma absolutely_integrable_bounded_variation: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "f absolutely_integrable_on UNIV"
  obtains B where "\<forall>d. d division_of (\<Union>d) \<longrightarrow> setsum (\<lambda>k. norm(integral k f)) d \<le> B"
  apply(rule that[of "integral UNIV (\<lambda>x. norm (f x))"])
proof safe case goal1 note d = division_ofD[OF this(2)]
  have "(\<Sum>k\<in>d. norm (integral k f)) \<le> (\<Sum>i\<in>d. integral i (\<lambda>x. norm (f x)))"
    apply(rule setsum_mono,rule absolutely_integrable_le) apply(drule d(4),safe)
    apply(rule absolutely_integrable_on_subinterval[OF assms]) by auto
  also have "... \<le> integral (\<Union>d) (\<lambda>x. norm (f x))"
    apply(subst integral_combine_division_topdown[OF _ goal1(2)])
    using integrable_on_subdivision[OF goal1(2)] using assms by auto
  also have "... \<le> integral UNIV (\<lambda>x. norm (f x))"
    apply(rule integral_subset_le) 
    using integrable_on_subdivision[OF goal1(2)] using assms by auto
  finally show ?case . qed

lemma helplemma:
  assumes "setsum (\<lambda>x. norm(f x - g x)) s < e" "finite s"
  shows "abs(setsum (\<lambda>x. norm(f x)) s - setsum (\<lambda>x. norm(g x)) s) < e"
  unfolding setsum_subtractf[THEN sym] apply(rule le_less_trans[OF setsum_abs])
  apply(rule le_less_trans[OF _ assms(1)]) apply(rule setsum_mono)
  using norm_triangle_ineq3 .

lemma bounded_variation_absolutely_integrable_interval:
  fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space" assumes "f integrable_on {a..b}"
  "\<forall>d. d division_of {a..b} \<longrightarrow> setsum (\<lambda>k. norm(integral k f)) d \<le> B"
  shows "f absolutely_integrable_on {a..b}"
proof- let ?S = "(\<lambda>d. setsum (\<lambda>k. norm(integral k f)) d) ` {d. d division_of {a..b} }" def i \<equiv> "Sup ?S"
  have i:"isLub UNIV ?S i" unfolding i_def apply(rule Sup)
    apply(rule elementary_interval) defer apply(rule_tac x=B in exI)
    apply(rule setleI) using assms(2) by auto
  show ?thesis apply(rule,rule assms) apply rule apply(subst has_integral[of _ i])
  proof safe case goal1 hence "i - e / 2 \<notin> Collect (isUb UNIV (setsum (\<lambda>k. norm (integral k f)) `
        {d. d division_of {a..b}}))" using isLub_ubs[OF i,rule_format]
      unfolding setge_def ubs_def by auto 
    hence " \<exists>y. y division_of {a..b} \<and> i - e / 2 < (\<Sum>k\<in>y. norm (integral k f))"
      unfolding mem_Collect_eq isUb_def setle_def by(simp add:not_le) then guess d .. note d=conjunctD2[OF this]
    note d' = division_ofD[OF this(1)]

    have "\<forall>x. \<exists>e>0. \<forall>i\<in>d. x \<notin> i \<longrightarrow> ball x e \<inter> i = {}"
    proof case goal1 have "\<exists>da>0. \<forall>xa\<in>\<Union>{i \<in> d. x \<notin> i}. da \<le> dist x xa"
        apply(rule separate_point_closed) apply(rule closed_Union)
        apply(rule finite_subset[OF _ d'(1)]) apply safe apply(drule d'(4)) by auto
      thus ?case apply safe apply(rule_tac x=da in exI,safe)
        apply(erule_tac x=xa in ballE) by auto
    qed from choice[OF this] guess k .. note k=conjunctD2[OF this[rule_format],rule_format]

    have "e/2 > 0" using goal1 by auto
    from henstock_lemma[OF assms(1) this] guess g . note g=this[rule_format]
    let ?g = "\<lambda>x. g x \<inter> ball x (k x)"
    show ?case apply(rule_tac x="?g" in exI) apply safe
    proof- show "gauge ?g" using g(1) unfolding gauge_def using k(1) by auto
      fix p assume "p tagged_division_of {a..b}" "?g fine p"
      note p = this(1) conjunctD2[OF this(2)[unfolded fine_inter]]
      note p' = tagged_division_ofD[OF p(1)]
      def p' \<equiv> "{(x,k) | x k. \<exists>i l. x \<in> i \<and> i \<in> d \<and> (x,l) \<in> p \<and> k = i \<inter> l}"
      have gp':"g fine p'" using p(2) unfolding p'_def fine_def by auto
      have p'':"p' tagged_division_of {a..b}" apply(rule tagged_division_ofI)
      proof- show "finite p'" apply(rule finite_subset[of _ "(\<lambda>(k,(x,l)). (x,k \<inter> l))
          ` {(k,xl) | k xl. k \<in> d \<and> xl \<in> p}"]) unfolding p'_def 
          defer apply(rule finite_imageI,rule finite_product_dependent[OF d'(1) p'(1)])
          apply safe unfolding image_iff apply(rule_tac x="(i,x,l)" in bexI) by auto
        fix x k assume "(x,k)\<in>p'"
        hence "\<exists>i l. x \<in> i \<and> i \<in> d \<and> (x, l) \<in> p \<and> k = i \<inter> l" unfolding p'_def by auto
        then guess i l apply-by(erule exE)+ note il=conjunctD4[OF this]
        show "x\<in>k" "k\<subseteq>{a..b}" using p'(2-3)[OF il(3)] il by auto
        show "\<exists>a b. k = {a..b}" unfolding il using p'(4)[OF il(3)] d'(4)[OF il(2)]
          apply safe unfolding inter_interval by auto
      next fix x1 k1 assume "(x1,k1)\<in>p'"
        hence "\<exists>i l. x1 \<in> i \<and> i \<in> d \<and> (x1, l) \<in> p \<and> k1 = i \<inter> l" unfolding p'_def by auto
        then guess i1 l1 apply-by(erule exE)+ note il1=conjunctD4[OF this]
        fix x2 k2 assume "(x2,k2)\<in>p'"
        hence "\<exists>i l. x2 \<in> i \<and> i \<in> d \<and> (x2, l) \<in> p \<and> k2 = i \<inter> l" unfolding p'_def by auto
        then guess i2 l2 apply-by(erule exE)+ note il2=conjunctD4[OF this]
        assume "(x1, k1) \<noteq> (x2, k2)"
        hence "interior(i1) \<inter> interior(i2) = {} \<or> interior(l1) \<inter> interior(l2) = {}"
          using d'(5)[OF il1(2) il2(2)] p'(5)[OF il1(3) il2(3)] unfolding il1 il2 by auto
        thus "interior k1 \<inter> interior k2 = {}" unfolding il1 il2 by auto
      next have *:"\<forall>(x, X) \<in> p'. X \<subseteq> {a..b}" unfolding p'_def using d' by auto
        show "\<Union>{k. \<exists>x. (x, k) \<in> p'} = {a..b}" apply rule apply(rule Union_least)
          unfolding mem_Collect_eq apply(erule exE) apply(drule *[rule_format]) apply safe
        proof- fix y assume y:"y\<in>{a..b}"
          hence "\<exists>x l. (x, l) \<in> p \<and> y\<in>l" unfolding p'(6)[THEN sym] by auto
          then guess x l apply-by(erule exE)+ note xl=conjunctD2[OF this]
          hence "\<exists>k. k\<in>d \<and> y\<in>k" using y unfolding d'(6)[THEN sym] by auto
          then guess i .. note i = conjunctD2[OF this]
          have "x\<in>i" using fineD[OF p(3) xl(1)] using k(2)[OF i(1), of x] using i(2) xl(2) by auto
          thus "y\<in>\<Union>{k. \<exists>x. (x, k) \<in> p'}" unfolding p'_def Union_iff apply(rule_tac x="i \<inter> l" in bexI)
            defer unfolding mem_Collect_eq apply(rule_tac x=x in exI)+ apply(rule_tac x="i\<inter>l" in exI)
            apply safe apply(rule_tac x=i in exI) apply(rule_tac x=l in exI) using i xl by auto 
        qed qed 

      hence "(\<Sum>(x, k)\<in>p'. norm (content k *\<^sub>R f x - integral k f)) < e / 2"
        apply-apply(rule g(2)[rule_format]) unfolding tagged_division_of_def apply safe using gp' .
      hence **:" \<bar>(\<Sum>(x,k)\<in>p'. norm (content k *\<^sub>R f x)) - (\<Sum>(x,k)\<in>p'. norm (integral k f))\<bar> < e / 2"
        unfolding split_def apply(rule helplemma) using p'' by auto

      have p'alt:"p' = {(x,(i \<inter> l)) | x i l. (x,l) \<in> p \<and> i \<in> d \<and> ~(i \<inter> l = {})}"
      proof safe case goal2
        have "x\<in>i" using fineD[OF p(3) goal2(1)] k(2)[OF goal2(2), of x] goal2(4-) by auto
        hence "(x, i \<inter> l) \<in> p'" unfolding p'_def apply safe
          apply(rule_tac x=x in exI,rule_tac x="i\<inter>l" in exI) apply safe using goal2 by auto
        thus ?case using goal2(3) by auto
      next fix x k assume "(x,k)\<in>p'"
        hence "\<exists>i l. x \<in> i \<and> i \<in> d \<and> (x, l) \<in> p \<and> k = i \<inter> l" unfolding p'_def by auto
        then guess i l apply-by(erule exE)+ note il=conjunctD4[OF this]
        thus "\<exists>y i l. (x, k) = (y, i \<inter> l) \<and> (y, l) \<in> p \<and> i \<in> d \<and> i \<inter> l \<noteq> {}"
          apply(rule_tac x=x in exI,rule_tac x=i in exI,rule_tac x=l in exI)
          using p'(2)[OF il(3)] by auto
      qed
      have sum_p':"(\<Sum>(x, k)\<in>p'. norm (integral k f)) = (\<Sum>k\<in>snd ` p'. norm (integral k f))"
        apply(subst setsum_over_tagged_division_lemma[OF p'',of "\<lambda>k. norm (integral k f)"])
        unfolding norm_eq_zero apply(rule integral_null,assumption) ..
      note snd_p = division_ofD[OF division_of_tagged_division[OF p(1)]]

      have *:"\<And>sni sni' sf sf'. abs(sf' - sni') < e / 2 \<longrightarrow> i - e / 2 < sni \<and> sni' \<le> i \<and>
        sni \<le> sni' \<and> sf' = sf \<longrightarrow> abs(sf - i) < e" by arith
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) - i) < e" 
        unfolding real_norm_def apply(rule *[rule_format,OF **],safe) apply(rule d(2))
      proof- case goal1 show ?case unfolding sum_p'
          apply(rule isLubD2[OF i]) using division_of_tagged_division[OF p''] by auto
      next case goal2 have *:"{k \<inter> l | k l. k \<in> d \<and> l \<in> snd ` p} =
          (\<lambda>(k,l). k \<inter> l) ` {(k,l)|k l. k \<in> d \<and> l \<in> snd ` p}" by auto
        have "(\<Sum>k\<in>d. norm (integral k f)) \<le> (\<Sum>i\<in>d. \<Sum>l\<in>snd ` p. norm (integral (i \<inter> l) f))"
        proof(rule setsum_mono) case goal1 note k=this
          from d'(4)[OF this] guess u v apply-by(erule exE)+ note uv=this
          def d' \<equiv> "{{u..v} \<inter> l |l. l \<in> snd ` p \<and>  ~({u..v} \<inter> l = {})}" note uvab = d'(2)[OF k[unfolded uv]]
          have "d' division_of {u..v}" apply(subst d'_def) apply(rule division_inter_1) 
            apply(rule division_of_tagged_division[OF p(1)]) using uvab .
          hence "norm (integral k f) \<le> setsum (\<lambda>k. norm (integral k f)) d'"
            unfolding uv apply(subst integral_combine_division_topdown[of _ _ d'])
            apply(rule integrable_on_subinterval[OF assms(1) uvab]) apply assumption
            apply(rule setsum_norm_le) by auto
          also have "... = (\<Sum>k\<in>{k \<inter> l |l. l \<in> snd ` p}. norm (integral k f))"
            apply(rule setsum_mono_zero_left) apply(subst simple_image)
            apply(rule finite_imageI)+ apply fact unfolding d'_def uv apply blast
          proof case goal1 hence "i \<in> {{u..v} \<inter> l |l. l \<in> snd ` p}" by auto
            from this[unfolded mem_Collect_eq] guess l .. note l=this
            hence "{u..v} \<inter> l = {}" using goal1 by auto thus ?case using l by auto
          qed also have "... = (\<Sum>l\<in>snd ` p. norm (integral (k \<inter> l) f))" unfolding  simple_image
            apply(rule setsum_reindex_nonzero[unfolded o_def])apply(rule finite_imageI,rule p')
          proof- case goal1 have "interior (k \<inter> l) \<subseteq> interior (l \<inter> y)" apply(subst(2) interior_inter)
              apply(rule Int_greatest) defer apply(subst goal1(4)) by auto
            hence *:"interior (k \<inter> l) = {}" using snd_p(5)[OF goal1(1-3)] by auto
            from d'(4)[OF k] snd_p(4)[OF goal1(1)] guess u1 v1 u2 v2 apply-by(erule exE)+ note uv=this
            show ?case using * unfolding uv inter_interval content_eq_0_interior[THEN sym] by auto
          qed finally show ?case .
        qed also have "... = (\<Sum>(i,l)\<in>{(i, l) |i l. i \<in> d \<and> l \<in> snd ` p}. norm (integral (i\<inter>l) f))"
          apply(subst sum_sum_product[THEN sym],fact) using p'(1) by auto
        also have "... = (\<Sum>x\<in>{(i, l) |i l. i \<in> d \<and> l \<in> snd ` p}. norm (integral (split op \<inter> x) f))"
          unfolding split_def ..
        also have "... = (\<Sum>k\<in>{i \<inter> l |i l. i \<in> d \<and> l \<in> snd ` p}. norm (integral k f))"
          unfolding * apply(rule setsum_reindex_nonzero[THEN sym,unfolded o_def])
          apply(rule finite_product_dependent) apply(fact,rule finite_imageI,rule p')
          unfolding split_paired_all mem_Collect_eq split_conv o_def
        proof- note * = division_ofD(4,5)[OF division_of_tagged_division,OF p(1)]
          fix l1 l2 k1 k2 assume as:"(l1, k1) \<noteq> (l2, k2)"  "l1 \<inter> k1 = l2 \<inter> k2" 
            "\<exists>i l. (l1, k1) = (i, l) \<and> i \<in> d \<and> l \<in> snd ` p"
            "\<exists>i l. (l2, k2) = (i, l) \<and> i \<in> d \<and> l \<in> snd ` p"
          hence "l1 \<in> d" "k1 \<in> snd ` p" by auto from d'(4)[OF this(1)] *(1)[OF this(2)]
          guess u1 v1 u2 v2 apply-by(erule exE)+ note uv=this
          have "l1 \<noteq> l2 \<or> k1 \<noteq> k2" using as by auto
          hence "(interior(k1) \<inter> interior(k2) = {} \<or> interior(l1) \<inter> interior(l2) = {})" apply-
            apply(erule disjE) apply(rule disjI2) apply(rule d'(5)) prefer 4 apply(rule disjI1)
            apply(rule *) using as by auto
          moreover have "interior(l1 \<inter> k1) = interior(l2 \<inter> k2)" using as(2) by auto
          ultimately have "interior(l1 \<inter> k1) = {}" by auto
          thus "norm (integral (l1 \<inter> k1) f) = 0" unfolding uv inter_interval
            unfolding content_eq_0_interior[THEN sym] by auto
        qed also have "... = (\<Sum>(x, k)\<in>p'. norm (integral k f))" unfolding sum_p'
          apply(rule setsum_mono_zero_right) apply(subst *)
          apply(rule finite_imageI[OF finite_product_dependent]) apply fact
          apply(rule finite_imageI[OF p'(1)]) apply safe
        proof- case goal2 have "ia \<inter> b = {}" using goal2 unfolding p'alt image_iff Bex_def not_ex
            apply(erule_tac x="(a,ia\<inter>b)" in allE) by auto thus ?case by auto
        next case goal1 thus ?case unfolding p'_def apply safe
            apply(rule_tac x=i in exI,rule_tac x=l in exI) unfolding snd_conv image_iff 
            apply safe apply(rule_tac x="(a,l)" in bexI) by auto
        qed finally show ?case .

      next case goal3
        let ?S = "{(x, i \<inter> l) |x i l. (x, l) \<in> p \<and> i \<in> d}"
        have Sigma_alt:"\<And>s t. s \<times> t = {(i, j) |i j. i \<in> s \<and> j \<in> t}" by auto
        have *:"?S = (\<lambda>(xl,i). (fst xl, snd xl \<inter> i)) ` (p \<times> d)" (*{(xl,i)|xl i. xl\<in>p \<and> i\<in>d}"**)
          apply safe unfolding image_iff apply(rule_tac x="((x,l),i)" in bexI) by auto
        note pdfin = finite_cartesian_product[OF p'(1) d'(1)]
        have "(\<Sum>(x, k)\<in>p'. norm (content k *\<^sub>R f x)) = (\<Sum>(x, k)\<in>?S. \<bar>content k\<bar> * norm (f x))"
          unfolding norm_scaleR apply(rule setsum_mono_zero_left)
          apply(subst *, rule finite_imageI) apply fact unfolding p'alt apply blast
          apply safe apply(rule_tac x=x in exI,rule_tac x=i in exI,rule_tac x=l in exI) by auto
        also have "... = (\<Sum>((x,l),i)\<in>p \<times> d. \<bar>content (l \<inter> i)\<bar> * norm (f x))" unfolding *
          apply(subst setsum_reindex_nonzero,fact) unfolding split_paired_all
          unfolding  o_def split_def snd_conv fst_conv mem_Sigma_iff Pair_eq apply(erule_tac conjE)+
        proof- fix x1 l1 k1 x2 l2 k2 assume as:"(x1,l1)\<in>p" "(x2,l2)\<in>p" "k1\<in>d" "k2\<in>d"
            "x1 = x2" "l1 \<inter> k1 = l2 \<inter> k2" "\<not> ((x1 = x2 \<and> l1 = l2) \<and> k1 = k2)"
          from d'(4)[OF as(3)] p'(4)[OF as(1)] guess u1 v1 u2 v2 apply-by(erule exE)+ note uv=this
          from as have "l1 \<noteq> l2 \<or> k1 \<noteq> k2" by auto
          hence "(interior(k1) \<inter> interior(k2) = {} \<or> interior(l1) \<inter> interior(l2) = {})" 
            apply-apply(erule disjE) apply(rule disjI2) defer apply(rule disjI1)
            apply(rule d'(5)[OF as(3-4)],assumption) apply(rule p'(5)[OF as(1-2)]) by auto
          moreover have "interior(l1 \<inter> k1) = interior(l2 \<inter> k2)" unfolding  as ..
          ultimately have "interior (l1 \<inter> k1) = {}" by auto
          thus "\<bar>content (l1 \<inter> k1)\<bar> * norm (f x1) = 0" unfolding uv inter_interval
            unfolding content_eq_0_interior[THEN sym] by auto
        qed safe also have "... = (\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x))" unfolding Sigma_alt
          apply(subst sum_sum_product[THEN sym]) apply(rule p', rule,rule d')
          apply(rule setsum_cong2) unfolding split_paired_all split_conv
        proof- fix x l assume as:"(x,l)\<in>p"
          note xl = p'(2-4)[OF this] from this(3) guess u v apply-by(erule exE)+ note uv=this
          have "(\<Sum>i\<in>d. \<bar>content (l \<inter> i)\<bar>) = (\<Sum>k\<in>d. content (k \<inter> {u..v}))"
            apply(rule setsum_cong2) apply(drule d'(4),safe) apply(subst Int_commute)
            unfolding inter_interval uv apply(subst abs_of_nonneg) by auto
          also have "... = setsum content {k\<inter>{u..v}| k. k\<in>d}" unfolding simple_image
            apply(rule setsum_reindex_nonzero[unfolded o_def,THEN sym]) apply(rule d')
          proof- case goal1 from d'(4)[OF this(1)] d'(4)[OF this(2)]
            guess u1 v1 u2 v2 apply- by(erule exE)+ note uv=this
            have "{} = interior ((k \<inter> y) \<inter> {u..v})" apply(subst interior_inter)
              using d'(5)[OF goal1(1-3)] by auto
            also have "... = interior (y \<inter> (k \<inter> {u..v}))" by auto
            also have "... = interior (k \<inter> {u..v})" unfolding goal1(4) by auto
            finally show ?case unfolding uv inter_interval content_eq_0_interior ..
          qed also have "... = setsum content {{u..v} \<inter> k |k. k \<in> d \<and> ~({u..v} \<inter> k = {})}"
            apply(rule setsum_mono_zero_right) unfolding simple_image
            apply(rule finite_imageI,rule d') apply blast apply safe
            apply(rule_tac x=k in exI)
          proof- case goal1 from d'(4)[OF this(1)] guess a b apply-by(erule exE)+ note ab=this
            have "interior (k \<inter> {u..v}) \<noteq> {}" using goal1(2)
              unfolding ab inter_interval content_eq_0_interior by auto
            thus ?case using goal1(1) using interior_subset[of "k \<inter> {u..v}"] by auto
          qed finally show "(\<Sum>i\<in>d. \<bar>content (l \<inter> i)\<bar> * norm (f x)) = content l *\<^sub>R norm (f x)"
            unfolding setsum_left_distrib[THEN sym] real_scaleR_def apply -
            apply(subst(asm) additive_content_division[OF division_inter_1[OF d(1)]])
            using xl(2)[unfolded uv] unfolding uv by auto
        qed finally show ?case . 
      qed qed qed qed 

lemma bounded_variation_absolutely_integrable:  fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space"
  assumes "f integrable_on UNIV" "\<forall>d. d division_of (\<Union>d) \<longrightarrow> setsum (\<lambda>k. norm(integral k f)) d \<le> B"
  shows "f absolutely_integrable_on UNIV"
proof(rule absolutely_integrable_onI,fact,rule)
  let ?S = "(\<lambda>d. setsum (\<lambda>k. norm(integral k f)) d) ` {d. d division_of  (\<Union>d)}" def i \<equiv> "Sup ?S"
  have i:"isLub UNIV ?S i" unfolding i_def apply(rule Sup)
    apply(rule elementary_interval) defer apply(rule_tac x=B in exI)
    apply(rule setleI) using assms(2) by auto
  have f_int:"\<And>a b. f absolutely_integrable_on {a..b}"
    apply(rule bounded_variation_absolutely_integrable_interval[where B=B])
    apply(rule integrable_on_subinterval[OF assms(1)]) defer apply safe
    apply(rule assms(2)[rule_format]) by auto 
  show "((\<lambda>x. norm (f x)) has_integral i) UNIV" apply(subst has_integral_alt',safe)
  proof- case goal1 show ?case using f_int[of a b] by auto
  next case goal2 have "\<exists>y\<in>setsum (\<lambda>k. norm (integral k f)) ` {d. d division_of \<Union>d}. \<not> y \<le> i - e"
    proof(rule ccontr) case goal1 hence "i \<le> i - e" apply-
        apply(rule isLub_le_isUb[OF i]) apply(rule isUbI) unfolding setle_def by auto
      thus False using goal2 by auto
    qed then guess K .. note * = this[unfolded image_iff not_le]
    from this(1) guess d .. note this[unfolded mem_Collect_eq]
    note d = this(1) *(2)[unfolded this(2)] note d'=division_ofD[OF this(1)]
    have "bounded (\<Union>d)" by(rule elementary_bounded,fact)
    from this[unfolded bounded_pos] guess K .. note K=conjunctD2[OF this]
    show ?case apply(rule_tac x="K + 1" in exI,safe)
    proof- fix a b assume ab:"ball 0 (K + 1) \<subseteq> {a..b::'n::ordered_euclidean_space}"
      have *:"\<forall>s s1. i - e < s1 \<and> s1 \<le> s \<and> s < i + e \<longrightarrow> abs(s - i) < (e::real)" by arith
      show "norm (integral {a..b} (\<lambda>x. if x \<in> UNIV then norm (f x) else 0) - i) < e"
        unfolding real_norm_def apply(rule *[rule_format],safe) apply(rule d(2))
      proof- case goal1 have "(\<Sum>k\<in>d. norm (integral k f)) \<le> setsum (\<lambda>k. integral k (\<lambda>x. norm (f x))) d"
          apply(rule setsum_mono) apply(rule absolutely_integrable_le)
          apply(drule d'(4),safe) by(rule f_int)
        also have "... = integral (\<Union>d) (\<lambda>x. norm(f x))" 
          apply(rule integral_combine_division_bottomup[THEN sym])
          apply(rule d) unfolding forall_in_division[OF d(1)] using f_int by auto
        also have "... \<le> integral {a..b} (\<lambda>x. if x \<in> UNIV then norm (f x) else 0)" 
        proof- case goal1 have "\<Union>d \<subseteq> {a..b}" apply rule apply(drule K(2)[rule_format]) 
            apply(rule ab[unfolded subset_eq,rule_format]) by(auto simp add:dist_norm)
          thus ?case apply- apply(subst if_P,rule) apply(rule integral_subset_le) defer
            apply(rule integrable_on_subdivision[of _ _ _ "{a..b}"])
            apply(rule d) using f_int[of a b] by auto
        qed finally show ?case .

      next note f = absolutely_integrable_onD[OF f_int[of a b]]
        note * = this(2)[unfolded has_integral_integral has_integral[of "\<lambda>x. norm (f x)"],rule_format]
        have "e/2>0" using `e>0` by auto from *[OF this] guess d1 .. note d1=conjunctD2[OF this]
        from henstock_lemma[OF f(1) `e/2>0`] guess d2 . note d2=this
        from fine_division_exists[OF gauge_inter[OF d1(1) d2(1)], of a b] guess p .
        note p=this(1) conjunctD2[OF this(2)[unfolded fine_inter]]
        have *:"\<And>sf sf' si di. sf' = sf \<longrightarrow> si \<le> i \<longrightarrow> abs(sf - si) < e / 2
          \<longrightarrow> abs(sf' - di) < e / 2 \<longrightarrow> di < i + e" by arith
        show "integral {a..b} (\<lambda>x. if x \<in> UNIV then norm (f x) else 0) < i + e" apply(subst if_P,rule)
        proof(rule *[rule_format]) 
          show "\<bar>(\<Sum>(x,k)\<in>p. norm (content k *\<^sub>R f x)) - (\<Sum>(x,k)\<in>p. norm (integral k f))\<bar> < e / 2"
            unfolding split_def apply(rule helplemma) using d2(2)[rule_format,of p]
            using p(1,3) unfolding tagged_division_of_def split_def by auto
          show "abs ((\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) - integral {a..b} (\<lambda>x. norm(f x))) < e / 2"
            using d1(2)[rule_format,OF conjI[OF p(1,2)]] unfolding real_norm_def .
          show "(\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) = (\<Sum>(x, k)\<in>p. norm (content k *\<^sub>R f x))"
            apply(rule setsum_cong2) unfolding split_paired_all split_conv
            apply(drule tagged_division_ofD(4)[OF p(1)]) unfolding norm_scaleR
            apply(subst abs_of_nonneg) by auto
          show "(\<Sum>(x, k)\<in>p. norm (integral k f)) \<le> i"
            apply(subst setsum_over_tagged_division_lemma[OF p(1)]) defer apply(rule isLubD2[OF i])
            unfolding image_iff apply(rule_tac x="snd ` p" in bexI) unfolding mem_Collect_eq defer
            apply(rule partial_division_of_tagged_division[of _ "{a..b}"])
            using p(1) unfolding tagged_division_of_def by auto
        qed qed qed(insert K,auto) qed qed 

lemma absolutely_integrable_restrict_univ:
 "(\<lambda>x. if x \<in> s then f x else (0::'a::banach)) absolutely_integrable_on UNIV \<longleftrightarrow> f absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def if_distrib norm_zero integrable_restrict_univ ..

lemma absolutely_integrable_add[intro]: fixes f g::"'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space"
  assumes "f absolutely_integrable_on s" "g absolutely_integrable_on s"
  shows "(\<lambda>x. f(x) + g(x)) absolutely_integrable_on s"
proof- let ?P = "\<And>f g::'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space. f absolutely_integrable_on UNIV \<Longrightarrow>
    g absolutely_integrable_on UNIV \<Longrightarrow> (\<lambda>x. f(x) + g(x)) absolutely_integrable_on UNIV"
  { presume as:"PROP ?P" note a = absolutely_integrable_restrict_univ[THEN sym]
    have *:"\<And>x. (if x \<in> s then f x else 0) + (if x \<in> s then g x else 0)
      = (if x \<in> s then f x + g x else 0)" by auto
    show ?thesis apply(subst a) using as[OF assms[unfolded a[of f] a[of g]]] unfolding * . }
  fix f g::"'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space" assume assms:"f absolutely_integrable_on UNIV"
    "g absolutely_integrable_on UNIV" 
  note absolutely_integrable_bounded_variation
  from this[OF assms(1)] this[OF assms(2)] guess B1 B2 . note B=this[rule_format]
  show "(\<lambda>x. f(x) + g(x)) absolutely_integrable_on UNIV"
    apply(rule bounded_variation_absolutely_integrable[of _ "B1+B2"])
    apply(rule integrable_add) prefer 3
  proof safe case goal1 have "\<And>k. k \<in> d \<Longrightarrow> f integrable_on k \<and> g integrable_on k"
      apply(drule division_ofD(4)[OF goal1]) apply safe
      apply(rule_tac[!] integrable_on_subinterval[of _ UNIV]) using assms by auto
    hence "(\<Sum>k\<in>d. norm (integral k (\<lambda>x. f x + g x))) \<le>
      (\<Sum>k\<in>d. norm (integral k f)) + (\<Sum>k\<in>d. norm (integral k g))" apply-
      unfolding setsum_addf[THEN sym] apply(rule setsum_mono)
      apply(subst integral_add) prefer 3 apply(rule norm_triangle_ineq) by auto
    also have "... \<le> B1 + B2" using B(1)[OF goal1] B(2)[OF goal1] by auto
    finally show ?case .
  qed(insert assms,auto) qed

lemma absolutely_integrable_sub[intro]: fixes f g::"'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space"
  assumes "f absolutely_integrable_on s" "g absolutely_integrable_on s"
  shows "(\<lambda>x. f(x) - g(x)) absolutely_integrable_on s"
  using absolutely_integrable_add[OF assms(1) absolutely_integrable_neg[OF assms(2)]]
  unfolding algebra_simps .

lemma absolutely_integrable_linear: fixes f::"'m::ordered_euclidean_space \<Rightarrow> 'n::ordered_euclidean_space" and h::"'n::ordered_euclidean_space \<Rightarrow> 'p::ordered_euclidean_space"
  assumes "f absolutely_integrable_on s" "bounded_linear h"
  shows "(h o f) absolutely_integrable_on s"
proof- { presume as:"\<And>f::'m::ordered_euclidean_space \<Rightarrow> 'n::ordered_euclidean_space. \<And>h::'n::ordered_euclidean_space \<Rightarrow> 'p::ordered_euclidean_space. 
    f absolutely_integrable_on UNIV \<Longrightarrow> bounded_linear h \<Longrightarrow>
    (h o f) absolutely_integrable_on UNIV" note a = absolutely_integrable_restrict_univ[THEN sym]
    show ?thesis apply(subst a) using as[OF assms[unfolded a[of f] a[of g]]]
      unfolding o_def if_distrib linear_simps[OF assms(2)] . }
  fix f::"'m::ordered_euclidean_space \<Rightarrow> 'n::ordered_euclidean_space" and h::"'n::ordered_euclidean_space \<Rightarrow> 'p::ordered_euclidean_space"
  assume assms:"f absolutely_integrable_on UNIV" "bounded_linear h" 
  from absolutely_integrable_bounded_variation[OF assms(1)] guess B . note B=this
  from bounded_linear.pos_bounded[OF assms(2)] guess b .. note b=conjunctD2[OF this]
  show "(h o f) absolutely_integrable_on UNIV"
    apply(rule bounded_variation_absolutely_integrable[of _ "B * b"])
    apply(rule integrable_linear[OF _ assms(2)]) 
  proof safe case goal2
    have "(\<Sum>k\<in>d. norm (integral k (h \<circ> f))) \<le> setsum (\<lambda>k. norm(integral k f)) d * b"
      unfolding setsum_left_distrib apply(rule setsum_mono)
    proof- case goal1 from division_ofD(4)[OF goal2 this]
      guess u v apply-by(erule exE)+ note uv=this
      have *:"f integrable_on k" unfolding uv apply(rule integrable_on_subinterval[of _ UNIV])
        using assms by auto note this[unfolded has_integral_integral]
      note has_integral_linear[OF this assms(2)] integrable_linear[OF * assms(2)]
      note * = has_integral_unique[OF this(2)[unfolded has_integral_integral] this(1)]
      show ?case unfolding * using b by auto
    qed also have "... \<le> B * b" apply(rule mult_right_mono) using B goal2 b by auto
    finally show ?case .
  qed(insert assms,auto) qed

lemma absolutely_integrable_setsum: fixes f::"'a \<Rightarrow> 'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space"
  assumes "finite t" "\<And>a. a \<in> t \<Longrightarrow> (f a) absolutely_integrable_on s"
  shows "(\<lambda>x. setsum (\<lambda>a. f a x) t) absolutely_integrable_on s"
  using assms(1,2) apply induct defer apply(subst setsum.insert) apply assumption+ by(rule,auto)

lemma absolutely_integrable_vector_abs: fixes f::"'a::ordered_euclidean_space => 'b::ordered_euclidean_space"
  assumes "f absolutely_integrable_on s"
  shows "(\<lambda>x. (\<chi>\<chi> i. abs(f x$$i))::'c::ordered_euclidean_space) absolutely_integrable_on s"
proof- have *:"\<And>x. ((\<chi>\<chi> i. abs(f x$$i))::'c::ordered_euclidean_space) = (setsum (\<lambda>i.
    (((\<lambda>y. (\<chi>\<chi> j. if j = i then y else 0)) o
    (((\<lambda>x. (norm((\<chi>\<chi> j. if j = i then x$$i else 0)::'c::ordered_euclidean_space))) o f))) x)) {..<DIM('c)})"
    unfolding euclidean_eq[where 'a='c] euclidean_component_setsum apply safe
    unfolding euclidean_lambda_beta'
  proof- case goal1 have *:"\<And>i xa. ((if i = xa then f x $$ xa else 0) * (if i = xa then f x $$ xa else 0)) =
      (if i = xa then (f x $$ xa) * (f x $$ xa) else 0)" by auto
    have *:"\<And>xa. norm ((\<chi>\<chi> j. if j = xa then f x $$ xa else 0)::'c) = (if xa<DIM('c) then abs (f x $$ xa) else 0)"
      unfolding norm_eq_sqrt_inner euclidean_inner[where 'a='c]
      by(auto simp add:setsum_delta[OF finite_lessThan] *)
    have "\<bar>f x $$ i\<bar> = (setsum (\<lambda>k. if k = i then abs ((f x)$$i) else 0) {..<DIM('c)})"
      unfolding setsum_delta[OF finite_lessThan] using goal1 by auto
    also have "... = (\<Sum>xa<DIM('c). ((\<lambda>y. (\<chi>\<chi> j. if j = xa then y else 0)::'c) \<circ>
                      (\<lambda>x. (norm ((\<chi>\<chi> j. if j = xa then x $$ xa else 0)::'c))) \<circ> f) x $$ i)"
      unfolding o_def * apply(rule setsum_cong2)
      unfolding euclidean_lambda_beta'[OF goal1 ] by auto
    finally show ?case unfolding o_def . qed
  show ?thesis unfolding * apply(rule absolutely_integrable_setsum) apply(rule finite_lessThan)
    apply(rule absolutely_integrable_linear) unfolding o_def apply(rule absolutely_integrable_norm)
    apply(rule absolutely_integrable_linear[OF assms,unfolded o_def]) unfolding linear_linear
    apply(rule_tac[!] linearI) unfolding euclidean_eq[where 'a='c]
    by(auto simp:euclidean_component_scaleR[where 'a=real,unfolded real_scaleR_def])
qed

lemma absolutely_integrable_max: fixes f g::"'m::ordered_euclidean_space \<Rightarrow> 'n::ordered_euclidean_space"
  assumes "f absolutely_integrable_on s" "g absolutely_integrable_on s"
  shows "(\<lambda>x. (\<chi>\<chi> i. max (f(x)$$i) (g(x)$$i))::'n::ordered_euclidean_space) absolutely_integrable_on s"
proof- have *:"\<And>x. (1 / 2) *\<^sub>R (((\<chi>\<chi> i. \<bar>(f x - g x) $$ i\<bar>)::'n) + (f x + g x)) = (\<chi>\<chi> i. max (f(x)$$i) (g(x)$$i))"
    unfolding euclidean_eq[where 'a='n] by auto
  note absolutely_integrable_sub[OF assms] absolutely_integrable_add[OF assms]
  note absolutely_integrable_vector_abs[OF this(1)] this(2)
  note absolutely_integrable_add[OF this] note absolutely_integrable_cmul[OF this,of "1/2"]
  thus ?thesis unfolding * . qed

lemma absolutely_integrable_min: fixes f g::"'m::ordered_euclidean_space \<Rightarrow> 'n::ordered_euclidean_space"
  assumes "f absolutely_integrable_on s" "g absolutely_integrable_on s"
  shows "(\<lambda>x. (\<chi>\<chi> i. min (f(x)$$i) (g(x)$$i))::'n::ordered_euclidean_space) absolutely_integrable_on s"
proof- have *:"\<And>x. (1 / 2) *\<^sub>R ((f x + g x) - ((\<chi>\<chi> i. \<bar>(f x - g x) $$ i\<bar>)::'n)) = (\<chi>\<chi> i. min (f(x)$$i) (g(x)$$i))"
    unfolding euclidean_eq[where 'a='n] by auto
  note absolutely_integrable_add[OF assms] absolutely_integrable_sub[OF assms]
  note this(1) absolutely_integrable_vector_abs[OF this(2)]
  note absolutely_integrable_sub[OF this] note absolutely_integrable_cmul[OF this,of "1/2"]
  thus ?thesis unfolding * . qed

lemma absolutely_integrable_abs_eq: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space"
  shows "f absolutely_integrable_on s \<longleftrightarrow> f integrable_on s \<and>
          (\<lambda>x. (\<chi>\<chi> i. abs(f x$$i))::'m) integrable_on s" (is "?l = ?r")
proof assume ?l thus ?r apply-apply rule defer
    apply(drule absolutely_integrable_vector_abs) by auto
next assume ?r { presume lem:"\<And>f::'n \<Rightarrow> 'm. f integrable_on UNIV \<Longrightarrow>
    (\<lambda>x. (\<chi>\<chi> i. abs(f(x)$$i))::'m) integrable_on UNIV \<Longrightarrow> f absolutely_integrable_on UNIV"
    have *:"\<And>x. (\<chi>\<chi> i. \<bar>(if x \<in> s then f x else 0) $$ i\<bar>) = (if x\<in>s then (\<chi>\<chi> i. \<bar>f x $$ i\<bar>) else (0::'m))"
      unfolding euclidean_eq[where 'a='m] by auto
    show ?l apply(subst absolutely_integrable_restrict_univ[THEN sym]) apply(rule lem)
      unfolding integrable_restrict_univ * using `?r` by auto }
  fix f::"'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space" assume assms:"f integrable_on UNIV"
    "(\<lambda>x. (\<chi>\<chi> i. abs(f(x)$$i))::'m::ordered_euclidean_space) integrable_on UNIV"
  let ?B = "setsum (\<lambda>i. integral UNIV (\<lambda>x. (\<chi>\<chi> j. abs(f x$$j)) ::'m::ordered_euclidean_space) $$ i) {..<DIM('m)}"
  show "f absolutely_integrable_on UNIV"
    apply(rule bounded_variation_absolutely_integrable[OF assms(1), where B="?B"],safe)
  proof- case goal1 note d=this and d'=division_ofD[OF this]
    have "(\<Sum>k\<in>d. norm (integral k f)) \<le>
      (\<Sum>k\<in>d. setsum (op $$ (integral k (\<lambda>x. (\<chi>\<chi> j. \<bar>f x $$ j\<bar>)::'m))) {..<DIM('m)})" apply(rule setsum_mono)
      apply(rule order_trans[OF norm_le_l1]) apply(rule setsum_mono) unfolding lessThan_iff
    proof- fix k and i assume "k\<in>d" and i:"i<DIM('m)"
      from d'(4)[OF this(1)] guess a b apply-by(erule exE)+ note ab=this
      show "\<bar>integral k f $$ i\<bar> \<le> integral k (\<lambda>x. (\<chi>\<chi> j. \<bar>f x $$ j\<bar>)::'m) $$ i" apply(rule abs_leI)
        unfolding euclidean_component_minus[THEN sym] defer apply(subst integral_neg[THEN sym])
        defer apply(rule_tac[1-2] integral_component_le) apply(rule integrable_neg)
        using integrable_on_subinterval[OF assms(1),of a b]
          integrable_on_subinterval[OF assms(2),of a b] unfolding ab by auto
    qed also have "... \<le> setsum (op $$ (integral UNIV (\<lambda>x. (\<chi>\<chi> j. \<bar>f x $$ j\<bar>))::'m)) {..<DIM('m)}"
      apply(subst setsum_commute,rule setsum_mono)
    proof- case goal1 have *:"(\<lambda>x. (\<chi>\<chi> j. \<bar>f x $$ j\<bar>)::'m) integrable_on \<Union>d"
        using integrable_on_subdivision[OF d assms(2)] by auto
      have "(\<Sum>i\<in>d. integral i (\<lambda>x. (\<chi>\<chi> j. \<bar>f x $$ j\<bar>)::'m) $$ j)
        = integral (\<Union>d) (\<lambda>x. (\<chi>\<chi> j. abs(f x$$j)) ::'m::ordered_euclidean_space) $$ j"
        unfolding euclidean_component_setsum[THEN sym] integral_combine_division_topdown[OF * d] ..
      also have "... \<le> integral UNIV (\<lambda>x. (\<chi>\<chi> j. \<bar>f x $$ j\<bar>)::'m) $$ j"
        apply(rule integral_subset_component_le) using assms * by auto
      finally show ?case .
    qed finally show ?case . qed qed

lemma nonnegative_absolutely_integrable: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space"
  assumes "\<forall>x\<in>s. \<forall>i<DIM('m). 0 \<le> f(x)$$i" "f integrable_on s"
  shows "f absolutely_integrable_on s"
  unfolding absolutely_integrable_abs_eq apply rule defer
  apply(rule integrable_eq[of _ f]) using assms apply-apply(subst euclidean_eq) by auto

lemma absolutely_integrable_integrable_bound: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space"
  assumes "\<forall>x\<in>s. norm(f x) \<le> g x" "f integrable_on s" "g integrable_on s"
  shows "f absolutely_integrable_on s"
proof- { presume *:"\<And>f::'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space. \<And> g. \<forall>x. norm(f x) \<le> g x \<Longrightarrow> f integrable_on UNIV
    \<Longrightarrow> g integrable_on UNIV \<Longrightarrow> f absolutely_integrable_on UNIV"
    show ?thesis apply(subst absolutely_integrable_restrict_univ[THEN sym])
      apply(rule *[of _ "\<lambda>x. if x\<in>s then g x else 0"])
      using assms unfolding integrable_restrict_univ by auto }
  fix g and f :: "'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space"
  assume assms:"\<forall>x. norm(f x) \<le> g x" "f integrable_on UNIV" "g integrable_on UNIV"
  show "f absolutely_integrable_on UNIV"
    apply(rule bounded_variation_absolutely_integrable[OF assms(2),where B="integral UNIV g"])
  proof safe case goal1 note d=this and d'=division_ofD[OF this]
    have "(\<Sum>k\<in>d. norm (integral k f)) \<le> (\<Sum>k\<in>d. integral k g)"
      apply(rule setsum_mono) apply(rule integral_norm_bound_integral) apply(drule_tac[!] d'(4),safe) 
      apply(rule_tac[1-2] integrable_on_subinterval) using assms by auto
    also have "... = integral (\<Union>d) g" apply(rule integral_combine_division_bottomup[THEN sym])
      apply(rule d,safe) apply(drule d'(4),safe)
      apply(rule integrable_on_subinterval[OF assms(3)]) by auto
    also have "... \<le> integral UNIV g" apply(rule integral_subset_le) defer
      apply(rule integrable_on_subdivision[OF d,of _ UNIV]) prefer 4
      apply(rule,rule_tac y="norm (f x)" in order_trans) using assms by auto
    finally show ?case . qed qed

lemma absolutely_integrable_integrable_bound_real: fixes f::"'n::ordered_euclidean_space \<Rightarrow> real"
  assumes "\<forall>x\<in>s. norm(f x) \<le> g x" "f integrable_on s" "g integrable_on s"
  shows "f absolutely_integrable_on s"
  apply(rule absolutely_integrable_integrable_bound[where g=g])
  using assms unfolding o_def by auto

lemma absolutely_integrable_absolutely_integrable_bound:
  fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space" and g::"'n::ordered_euclidean_space \<Rightarrow> 'p::ordered_euclidean_space"
  assumes "\<forall>x\<in>s. norm(f x) \<le> norm(g x)" "f integrable_on s" "g absolutely_integrable_on s"
  shows "f absolutely_integrable_on s"
  apply(rule absolutely_integrable_integrable_bound[of s f "\<lambda>x. norm (g x)"])
  using assms by auto

lemma absolutely_integrable_inf_real:
  assumes "finite k" "k \<noteq> {}"
  "\<forall>i\<in>k. (\<lambda>x. (fs x i)::real) absolutely_integrable_on s"
  shows "(\<lambda>x. (Inf ((fs x) ` k))) absolutely_integrable_on s" using assms
proof induct case (insert a k) let ?P = " (\<lambda>x. if fs x ` k = {} then fs x a
         else min (fs x a) (Inf (fs x ` k))) absolutely_integrable_on s"
  show ?case unfolding image_insert
    apply(subst Inf_insert_finite) apply(rule finite_imageI[OF insert(1)])
  proof(cases "k={}") case True
    thus ?P apply(subst if_P) defer apply(rule insert(5)[rule_format]) by auto
  next case False thus ?P apply(subst if_not_P) defer      
      apply(rule absolutely_integrable_min[where 'n=real,unfolded Eucl_real_simps])
      defer apply(rule insert(3)[OF False]) using insert(5) by auto
  qed qed auto

lemma absolutely_integrable_sup_real:
  assumes "finite k" "k \<noteq> {}"
  "\<forall>i\<in>k. (\<lambda>x. (fs x i)::real) absolutely_integrable_on s"
  shows "(\<lambda>x. (Sup ((fs x) ` k))) absolutely_integrable_on s" using assms
proof induct case (insert a k) let ?P = " (\<lambda>x. if fs x ` k = {} then fs x a
         else max (fs x a) (Sup (fs x ` k))) absolutely_integrable_on s"
  show ?case unfolding image_insert
    apply(subst Sup_insert_finite) apply(rule finite_imageI[OF insert(1)])
  proof(cases "k={}") case True
    thus ?P apply(subst if_P) defer apply(rule insert(5)[rule_format]) by auto
  next case False thus ?P apply(subst if_not_P) defer
      apply(rule absolutely_integrable_max[where 'n=real,unfolded Eucl_real_simps]) 
      defer apply(rule insert(3)[OF False]) using insert(5) by auto
  qed qed auto

subsection {* Dominated convergence. *}

lemma dominated_convergence: fixes f::"nat \<Rightarrow> 'n::ordered_euclidean_space \<Rightarrow> real"
  assumes "\<And>k. (f k) integrable_on s" "h integrable_on s"
  "\<And>k. \<forall>x \<in> s. norm(f k x) \<le> (h x)"
  "\<forall>x \<in> s. ((\<lambda>k. f k x) ---> g x) sequentially"
  shows "g integrable_on s" "((\<lambda>k. integral s (f k)) ---> integral s g) sequentially"
proof- have "\<And>m. (\<lambda>x. Inf {f j x |j. m \<le> j}) integrable_on s \<and>
    ((\<lambda>k. integral s (\<lambda>x. Inf {f j x |j. j \<in> {m..m + k}})) --->
    integral s (\<lambda>x. Inf {f j x |j. m \<le> j}))sequentially"
  proof(rule monotone_convergence_decreasing,safe) fix m::nat
    show "bounded {integral s (\<lambda>x. Inf {f j x |j. j \<in> {m..m + k}}) |k. True}"
      unfolding bounded_iff apply(rule_tac x="integral s h" in exI)
    proof safe fix k::nat
      show "norm (integral s (\<lambda>x. Inf {f j x |j. j \<in> {m..m + k}})) \<le> integral s h"
        apply(rule integral_norm_bound_integral) unfolding simple_image
        apply(rule absolutely_integrable_onD) apply(rule absolutely_integrable_inf_real)
        prefer 5 unfolding real_norm_def apply(rule) apply(rule Inf_abs_ge)
        prefer 5 apply rule apply(rule_tac g=h in absolutely_integrable_integrable_bound_real)
        using assms unfolding real_norm_def by auto
    qed fix k::nat show "(\<lambda>x. Inf {f j x |j. j \<in> {m..m + k}}) integrable_on s"
      unfolding simple_image apply(rule absolutely_integrable_onD)
      apply(rule absolutely_integrable_inf_real) prefer 3 
      using absolutely_integrable_integrable_bound_real[OF assms(3,1,2)] by auto
    fix x assume x:"x\<in>s" show "Inf {f j x |j. j \<in> {m..m + Suc k}}
      \<le> Inf {f j x |j. j \<in> {m..m + k}}" apply(rule Inf_ge) unfolding setge_def
      defer apply rule apply(subst Inf_finite_le_iff) prefer 3
      apply(rule_tac x=xa in bexI) by auto
    let ?S = "{f j x| j.  m \<le> j}" def i \<equiv> "Inf ?S"
    show "((\<lambda>k. Inf {f j x |j. j \<in> {m..m + k}}) ---> i) sequentially"
    proof (rule LIMSEQ_I) case goal1 note r=this have i:"isGlb UNIV ?S i" unfolding i_def apply(rule Inf)
        defer apply(rule_tac x="- h x - 1" in exI) unfolding setge_def
      proof safe case goal1 thus ?case using assms(3)[rule_format,OF x, of j] by auto
      qed auto

      have "\<exists>y\<in>?S. \<not> y \<ge> i + r"
      proof(rule ccontr) case goal1 hence "i \<ge> i + r" apply-
          apply(rule isGlb_le_isLb[OF i]) apply(rule isLbI) unfolding setge_def by fastforce+
        thus False using r by auto
      qed then guess y .. note y=this[unfolded not_le]
      from this(1)[unfolded mem_Collect_eq] guess N .. note N=conjunctD2[OF this]
      
      show ?case apply(rule_tac x=N in exI)
      proof safe case goal1
        have *:"\<And>y ix. y < i + r \<longrightarrow> i \<le> ix \<longrightarrow> ix \<le> y \<longrightarrow> abs(ix - i) < r" by arith
        show ?case unfolding real_norm_def apply(rule *[rule_format,OF y(2)])
          unfolding i_def apply(rule real_le_inf_subset) prefer 3
          apply(rule,rule isGlbD1[OF i]) prefer 3 apply(subst Inf_finite_le_iff)
          prefer 3 apply(rule_tac x=y in bexI) using N goal1 by auto
      qed qed qed note dec1 = conjunctD2[OF this]

  have "\<And>m. (\<lambda>x. Sup {f j x |j. m \<le> j}) integrable_on s \<and>
    ((\<lambda>k. integral s (\<lambda>x. Sup {f j x |j. j \<in> {m..m + k}})) --->
    integral s (\<lambda>x. Sup {f j x |j. m \<le> j})) sequentially"
  proof(rule monotone_convergence_increasing,safe) fix m::nat
    show "bounded {integral s (\<lambda>x. Sup {f j x |j. j \<in> {m..m + k}}) |k. True}"
      unfolding bounded_iff apply(rule_tac x="integral s h" in exI)
    proof safe fix k::nat
      show "norm (integral s (\<lambda>x. Sup {f j x |j. j \<in> {m..m + k}})) \<le> integral s h"
        apply(rule integral_norm_bound_integral) unfolding simple_image
        apply(rule absolutely_integrable_onD) apply(rule absolutely_integrable_sup_real)
        prefer 5 unfolding real_norm_def apply(rule) apply(rule Sup_abs_le)
        prefer 5 apply rule apply(rule_tac g=h in absolutely_integrable_integrable_bound_real)
        using assms unfolding real_norm_def by auto
    qed fix k::nat show "(\<lambda>x. Sup {f j x |j. j \<in> {m..m + k}}) integrable_on s"
      unfolding simple_image apply(rule absolutely_integrable_onD)
      apply(rule absolutely_integrable_sup_real) prefer 3 
      using absolutely_integrable_integrable_bound_real[OF assms(3,1,2)] by auto
    fix x assume x:"x\<in>s" show "Sup {f j x |j. j \<in> {m..m + Suc k}}
      \<ge> Sup {f j x |j. j \<in> {m..m + k}}" apply(rule Sup_le) unfolding setle_def
      defer apply rule apply(subst Sup_finite_ge_iff) prefer 3 apply(rule_tac x=y in bexI) by auto
    let ?S = "{f j x| j.  m \<le> j}" def i \<equiv> "Sup ?S"
    show "((\<lambda>k. Sup {f j x |j. j \<in> {m..m + k}}) ---> i) sequentially"
    proof (rule LIMSEQ_I) case goal1 note r=this have i:"isLub UNIV ?S i" unfolding i_def apply(rule Sup)
        defer apply(rule_tac x="h x" in exI) unfolding setle_def
      proof safe case goal1 thus ?case using assms(3)[rule_format,OF x, of j] by auto
      qed auto
      
      have "\<exists>y\<in>?S. \<not> y \<le> i - r"
      proof(rule ccontr) case goal1 hence "i \<le> i - r" apply-
          apply(rule isLub_le_isUb[OF i]) apply(rule isUbI) unfolding setle_def by fastforce+
        thus False using r by auto
      qed then guess y .. note y=this[unfolded not_le]
      from this(1)[unfolded mem_Collect_eq] guess N .. note N=conjunctD2[OF this]
      
      show ?case apply(rule_tac x=N in exI)
      proof safe case goal1
        have *:"\<And>y ix. i - r < y \<longrightarrow> ix \<le> i \<longrightarrow> y \<le> ix \<longrightarrow> abs(ix - i) < r" by arith
        show ?case unfolding real_norm_def apply(rule *[rule_format,OF y(2)])
          unfolding i_def apply(rule real_ge_sup_subset) prefer 3
          apply(rule,rule isLubD1[OF i]) prefer 3 apply(subst Sup_finite_ge_iff)
          prefer 3 apply(rule_tac x=y in bexI) using N goal1 by auto
      qed qed qed note inc1 = conjunctD2[OF this]

  have "g integrable_on s \<and> ((\<lambda>k. integral s (\<lambda>x. Inf {f j x |j. k \<le> j})) ---> integral s g) sequentially"
  apply(rule monotone_convergence_increasing,safe) apply fact 
  proof- show "bounded {integral s (\<lambda>x. Inf {f j x |j. k \<le> j}) |k. True}"
      unfolding bounded_iff apply(rule_tac x="integral s h" in exI)
    proof safe fix k::nat
      show "norm (integral s (\<lambda>x. Inf {f j x |j. k \<le> j})) \<le> integral s h"
        apply(rule integral_norm_bound_integral) apply fact+
        unfolding real_norm_def apply(rule) apply(rule Inf_abs_ge) using assms(3) by auto
    qed fix k::nat and x assume x:"x\<in>s"

    have *:"\<And>x y::real. x \<ge> - y \<Longrightarrow> - x \<le> y" by auto
    show "Inf {f j x |j. k \<le> j} \<le> Inf {f j x |j. Suc k \<le> j}" apply-
      apply(rule real_le_inf_subset) prefer 3 unfolding setge_def
      apply(rule_tac x="- h x" in exI) apply safe apply(rule *)
      using assms(3)[rule_format,OF x] unfolding real_norm_def abs_le_iff by auto
    show "((\<lambda>k. Inf {f j x |j. k \<le> j}) ---> g x) sequentially"
    proof (rule LIMSEQ_I) case goal1 hence "0<r/2" by auto
      from assms(4)[THEN bspec, THEN LIMSEQ_D, OF x this] guess N .. note N=this
      show ?case apply(rule_tac x=N in exI,safe) unfolding real_norm_def
        apply(rule le_less_trans[of _ "r/2"]) apply(rule Inf_asclose) apply safe
        defer apply(rule less_imp_le) using N goal1 by auto
    qed qed note inc2 = conjunctD2[OF this]

  have "g integrable_on s \<and> ((\<lambda>k. integral s (\<lambda>x. Sup {f j x |j. k \<le> j})) ---> integral s g) sequentially"
  apply(rule monotone_convergence_decreasing,safe) apply fact 
  proof- show "bounded {integral s (\<lambda>x. Sup {f j x |j. k \<le> j}) |k. True}"
      unfolding bounded_iff apply(rule_tac x="integral s h" in exI)
    proof safe fix k::nat
      show "norm (integral s (\<lambda>x. Sup {f j x |j. k \<le> j})) \<le> integral s h"
        apply(rule integral_norm_bound_integral) apply fact+
        unfolding real_norm_def apply(rule) apply(rule Sup_abs_le) using assms(3) by auto
    qed fix k::nat and x assume x:"x\<in>s"

    show "Sup {f j x |j. k \<le> j} \<ge> Sup {f j x |j. Suc k \<le> j}" apply-
      apply(rule real_ge_sup_subset) prefer 3 unfolding setle_def
      apply(rule_tac x="h x" in exI) apply safe
      using assms(3)[rule_format,OF x] unfolding real_norm_def abs_le_iff by auto
    show "((\<lambda>k. Sup {f j x |j. k \<le> j}) ---> g x) sequentially"
    proof (rule LIMSEQ_I) case goal1 hence "0<r/2" by auto
      from assms(4)[THEN bspec, THEN LIMSEQ_D, OF x this] guess N .. note N=this
      show ?case apply(rule_tac x=N in exI,safe) unfolding real_norm_def
        apply(rule le_less_trans[of _ "r/2"]) apply(rule Sup_asclose) apply safe
        defer apply(rule less_imp_le) using N goal1 by auto
    qed qed note dec2 = conjunctD2[OF this]

  show "g integrable_on s" by fact
  show "((\<lambda>k. integral s (f k)) ---> integral s g) sequentially"
  proof (rule LIMSEQ_I) case goal1
    from LIMSEQ_D [OF inc2(2) goal1] guess N1 .. note N1=this[unfolded real_norm_def]
    from LIMSEQ_D [OF dec2(2) goal1] guess N2 .. note N2=this[unfolded real_norm_def]
    show ?case apply(rule_tac x="N1+N2" in exI,safe)
    proof- fix n assume n:"n \<ge> N1 + N2"
      have *:"\<And>i0 i i1 g. \<bar>i0 - g\<bar> < r \<longrightarrow> \<bar>i1 - g\<bar> < r \<longrightarrow> i0 \<le> i \<longrightarrow> i \<le> i1 \<longrightarrow> \<bar>i - g\<bar> < r" by arith
      show "norm (integral s (f n) - integral s g) < r" unfolding real_norm_def
        apply(rule *[rule_format,OF N1[rule_format] N2[rule_format], of n n])
      proof- show "integral s (\<lambda>x. Inf {f j x |j. n \<le> j}) \<le> integral s (f n)"
        proof(rule integral_le[OF dec1(1) assms(1)],safe) 
          fix x assume x:"x \<in> s" have *:"\<And>x y::real. x \<ge> - y \<Longrightarrow> - x \<le> y" by auto
          show "Inf {f j x |j. n \<le> j} \<le> f n x" apply(rule Inf_lower[where z="- h x"]) defer
            apply(rule *) using assms(3)[rule_format,OF x] unfolding real_norm_def abs_le_iff by auto
        qed show "integral s (f n) \<le> integral s (\<lambda>x. Sup {f j x |j. n \<le> j})"
        proof(rule integral_le[OF assms(1) inc1(1)],safe) 
          fix x assume x:"x \<in> s"
          show "f n x \<le> Sup {f j x |j. n \<le> j}" apply(rule Sup_upper[where z="h x"]) defer
            using assms(3)[rule_format,OF x] unfolding real_norm_def abs_le_iff by auto
        qed qed(insert n,auto) qed qed qed

declare [[smt_certificates = ""]]
declare [[smt_read_only_certificates = false]]

end
