
header {* Lebsegue measure (defined via the gauge integral). *}
(*  Author:                     John Harrison
    Translation from HOL light: Robert Himmelmann, TU Muenchen *)

theory Gauge_Measure
  imports Integration 
begin

(* ------------------------------------------------------------------------- *)
(* Lebesgue measure (in the case where the measure is finite).               *)
(* For the non-finite version, please see Probability/Lebesgue_Measure.thy   *)
(* ------------------------------------------------------------------------- *)

definition has_gmeasure (infixr "has'_gmeasure" 80) where
  "s has_gmeasure m \<equiv> ((\<lambda>x. 1::real) has_integral m) s"

definition gmeasurable :: "('n::ordered_euclidean_space) set \<Rightarrow> bool" where 
  "gmeasurable s \<equiv> (\<exists>m. s has_gmeasure m)"

lemma gmeasurableI[dest]:"s has_gmeasure m \<Longrightarrow> gmeasurable s"
  unfolding gmeasurable_def by auto

definition gmeasure where
  "gmeasure s \<equiv> (if gmeasurable s then (SOME m. s has_gmeasure m) else 0)"

lemma has_gmeasure_measure: "gmeasurable s \<longleftrightarrow> s has_gmeasure (gmeasure s)"
  unfolding gmeasure_def gmeasurable_def
  apply meson apply(subst if_P) defer apply(rule someI) by auto

lemma has_gmeasure_measureI[intro]:"gmeasurable s \<Longrightarrow> s has_gmeasure (gmeasure s)"
  using has_gmeasure_measure by auto
  
lemma has_gmeasure_unique: "s has_gmeasure m1 \<Longrightarrow> s has_gmeasure m2 \<Longrightarrow> m1 = m2"
  unfolding has_gmeasure_def apply(rule has_integral_unique) by auto

lemma measure_unique[intro]: assumes "s has_gmeasure m" shows "gmeasure s = m"
  apply(rule has_gmeasure_unique[OF _ assms]) using assms 
  unfolding has_gmeasure_measure[THEN sym] by auto

lemma has_gmeasure_measurable_measure:
 "s has_gmeasure m \<longleftrightarrow> gmeasurable s \<and> gmeasure s = m"
  by(auto intro!:measure_unique simp:has_gmeasure_measure[THEN sym])

lemmas has_gmeasure_imp_measurable = gmeasurableI

lemma has_gmeasure:
 "s has_gmeasure m \<longleftrightarrow> ((\<lambda>x. if x \<in> s then 1 else 0) has_integral m) UNIV"
  unfolding has_integral_restrict_univ has_gmeasure_def ..

lemma gmeasurable: "gmeasurable s \<longleftrightarrow> (\<lambda>x. 1::real) integrable_on s"
  unfolding gmeasurable_def integrable_on_def has_gmeasure_def by auto

lemma gmeasurable_integrable:
 "gmeasurable s \<longleftrightarrow> (\<lambda>x. if x \<in> s then 1 else (0::real)) integrable_on UNIV"
  unfolding gmeasurable_def integrable_on_def has_gmeasure ..

lemma measure_integral:
  assumes "gmeasurable s" shows "gmeasure s = (integral s (\<lambda>x. 1))"
  apply(rule integral_unique[THEN sym])
  unfolding has_gmeasure_def[symmetric] using assms by auto 

lemma measure_integral_univ: assumes "gmeasurable s"
  shows "gmeasure s = (integral UNIV (\<lambda>x. if x \<in> s then 1 else 0))"
  apply(rule integral_unique[THEN sym])
  using assms by(auto simp:has_gmeasure[THEN sym])

lemmas integral_measure = measure_integral[THEN sym]

lemmas integral_measure_univ = measure_integral_univ[THEN sym]

lemma has_gmeasure_interval[intro]:
  "{a..b} has_gmeasure content{a..b}" (is ?t1)
  "{a<..<b} has_gmeasure content{a..b}" (is ?t2)
proof- show ?t1 unfolding has_gmeasure_def using has_integral_const[where c="1::real"] by auto
  show ?t2 unfolding has_gmeasure apply(rule has_integral_spike[of "{a..b} - {a<..<b}",
    where f="\<lambda>x. (if x \<in> {a..b} then 1 else 0)"]) apply(rule negligible_frontier_interval) 
    using interval_open_subset_closed[of a b]
    using `?t1` unfolding has_gmeasure by auto
qed

lemma gmeasurable_interval[intro]: "gmeasurable {a..b}" "gmeasurable {a<..<b}"
  by(auto intro:gmeasurableI)

lemma measure_interval[simp]: "gmeasure{a..b} = content{a..b}"  "gmeasure({a<..<b}) = content{a..b}"
  by(auto intro:measure_unique)

lemma nonnegative_absolutely_integrable: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'm::ordered_euclidean_space"
  assumes "\<forall>x\<in>s. \<forall>i<DIM('m). 0 \<le> f(x)$$i" "f integrable_on s"
  shows "f absolutely_integrable_on s"
  unfolding absolutely_integrable_abs_eq apply rule defer
  apply(rule integrable_eq[of _ f]) using assms apply-apply(subst euclidean_eq) by auto

lemma gmeasurable_inter[dest]: assumes "gmeasurable s" "gmeasurable t" shows "gmeasurable (s \<inter> t)"
proof- have *:"(\<lambda>x. if x \<in> s \<inter> t then 1 else (0::real)) =
    (\<lambda>x. \<chi>\<chi> i. min (((if x \<in> s then 1 else 0)::real)$$i) (((if x \<in> t then 1 else 0)::real)$$i))"
    apply(rule ext) by auto
  show ?thesis unfolding gmeasurable_integrable apply(rule absolutely_integrable_onD)
    unfolding * apply(rule absolutely_integrable_min)
    apply(rule_tac[!] nonnegative_absolutely_integrable)
    using assms unfolding gmeasurable_integrable by auto
qed

lemma gmeasurable_union: assumes "gmeasurable s" "gmeasurable t"
  shows "gmeasurable (s \<union> t)"
proof- have *:"(\<lambda>x. if x \<in> s \<union> t then 1 else (0::real)) =
    (\<lambda>x. \<chi>\<chi> i. max (((if x \<in> s then 1 else 0)::real)$$i) (((if x \<in> t then 1 else 0)::real)$$i)) "
    by(rule ext,auto)
  show ?thesis unfolding gmeasurable_integrable apply(rule absolutely_integrable_onD)
    unfolding * apply(rule absolutely_integrable_max)
    apply(rule_tac[!]nonnegative_absolutely_integrable)
    using assms unfolding gmeasurable_integrable by auto
qed

lemma has_gmeasure_disjoint_union: 
  assumes "s1 has_gmeasure m1" "s2 has_gmeasure m2" "s1 \<inter> s2 = {}"
  shows "(s1 \<union> s2) has_gmeasure (m1 + m2)"
proof- have *:"\<And>x. (if x \<in> s1 then 1 else 0) + (if x \<in> s2 then 1 else 0) =
    (if x \<in> s1 \<union> s2 then 1 else (0::real))" using assms(3) by auto
  show ?thesis using has_integral_add[OF assms(1-2)[unfolded has_gmeasure]]
    unfolding has_gmeasure * .
qed

lemma measure_disjoint_union: assumes "gmeasurable s" "gmeasurable t" "s \<inter> t = {}"
  shows "gmeasure(s \<union> t) = gmeasure s + gmeasure t"
  apply rule apply(rule has_gmeasure_disjoint_union) using assms by auto

lemma has_gmeasure_pos_le[dest]: assumes "s has_gmeasure m" shows "0 \<le> m"
  apply(rule has_integral_nonneg) using assms unfolding has_gmeasure by auto

lemma not_measurable_measure:"\<not> gmeasurable s \<Longrightarrow> gmeasure s = 0"
  unfolding gmeasure_def if_not_P ..

lemma measure_pos_le[intro]: "0 <= gmeasure s"
  apply(cases "gmeasurable s") unfolding not_measurable_measure
  unfolding has_gmeasure_measure by auto

lemma has_gmeasure_subset[dest]:
  assumes "s1 has_gmeasure m1" "s2 has_gmeasure m2" "s1 \<subseteq> s2"
  shows "m1 <= m2"
  using has_integral_subset_le[OF assms(3,1,2)[unfolded has_gmeasure_def]] by auto

lemma measure_subset[dest]: assumes "gmeasurable s" "gmeasurable t" "s \<subseteq> t"
  shows "gmeasure s \<le> gmeasure t"
  using assms unfolding has_gmeasure_measure by auto

lemma has_gmeasure_0:"s has_gmeasure 0 \<longleftrightarrow> negligible s" (is "?l = ?r")
proof assume ?r thus ?l unfolding indicator_def_raw negligible apply(erule_tac x="UNIV" in allE)
    unfolding has_integral_restrict_univ has_gmeasure_def .
next assume ?l note this[unfolded has_gmeasure_def has_integral_alt']
  note * = conjunctD2[OF this,rule_format]
  show ?r unfolding negligible_def 
  proof safe case goal1
    from *(1)[of a b,unfolded integrable_on_def] guess y apply-
      apply(subst (asm) has_integral_restrict_univ[THEN sym]) by (erule exE) note y=this
    have "0 \<le> y" apply(rule has_integral_nonneg[OF y]) by auto
    moreover have "y \<le> 0" apply(rule has_integral_le[OF y]) 
      apply(rule `?l`[unfolded has_gmeasure_def has_integral_restrict_univ[THEN sym,of"\<lambda>x. 1"]]) by auto
    ultimately have "y = 0" by auto
    thus ?case using y unfolding has_integral_restrict_univ indicator_def_raw by auto
  qed
qed

lemma measure_eq_0: "negligible s ==> gmeasure s = 0"
  apply(rule measure_unique) unfolding has_gmeasure_0 by auto

lemma has_gmeasure_empty[intro]: "{} has_gmeasure 0"
  unfolding has_gmeasure_0 by auto

lemma measure_empty[simp]: "gmeasure {} = 0"
  apply(rule measure_eq_0) by auto

lemma gmeasurable_empty[intro]: "gmeasurable {}" by(auto intro:gmeasurableI)

lemma gmeasurable_measure_eq_0:
  "gmeasurable s ==> (gmeasure s = 0 \<longleftrightarrow> negligible s)"
  unfolding has_gmeasure_measure has_gmeasure_0[THEN sym] by(auto intro:measure_unique)

lemma gmeasurable_measure_pos_lt:
 "gmeasurable s ==> (0 < gmeasure s \<longleftrightarrow> ~negligible s)"
  unfolding gmeasurable_measure_eq_0[THEN sym]
  using measure_pos_le[of s] unfolding le_less by fastsimp

lemma negligible_interval:True .. (*
 "(!a b. negligible{a..b} \<longleftrightarrow> {a<..<b} = {}) \<and>
   (!a b. negligible({a<..<b}) \<longleftrightarrow> {a<..<b} = {})"
qed   REWRITE_TAC[GSYM HAS_GMEASURE_0] THEN
  MESON_TAC[HAS_GMEASURE_INTERVAL; CONTENT_EQ_0_INTERIOR;
            INTERIOR_CLOSED_INTERVAL; HAS_GMEASURE_UNIQUE]);;*)

lemma gmeasurable_finite_unions:
  assumes "finite f" "\<And>s. s \<in> f \<Longrightarrow> gmeasurable s"
  shows "gmeasurable (\<Union> f)" using assms(1,2) 
proof induct case (insert s F)
  show ?case unfolding Union_insert apply(rule gmeasurable_union)
    using insert by auto
qed auto  

lemma has_gmeasure_diff_subset: assumes "s1 has_gmeasure m1" "s2 has_gmeasure m2" "s2 \<subseteq> s1"
  shows "(s1 - s2) has_gmeasure (m1 - m2)"
proof- have *:"(\<lambda>x. (if x \<in> s1 then 1 else 0) - (if x \<in> s2 then 1 else (0::real))) =
    (\<lambda>x. if x \<in> s1 - s2 then 1 else 0)" apply(rule ext) using assms(3) by auto
  show ?thesis using has_integral_sub[OF assms(1-2)[unfolded has_gmeasure]] 
    unfolding has_gmeasure * . 
qed

lemma gmeasurable_diff: assumes "gmeasurable s" "gmeasurable t" 
  shows "gmeasurable (s - t)"
proof- have *:"\<And>s t. gmeasurable s \<Longrightarrow> gmeasurable t \<Longrightarrow> t \<subseteq> s ==> gmeasurable (s - t)"
    unfolding gmeasurable_def apply(erule exE)+ apply(rule,rule has_gmeasure_diff_subset)
    by assumption+
  have **:"s - t = s - (s \<inter> t)" by auto
  show ?thesis unfolding ** apply(rule *) using assms by auto
qed

lemma measure_diff_subset: True .. (*
 "!s t. gmeasurable s \<and> gmeasurable t \<and> t \<subseteq> s
         ==> measure(s DIFF t) = gmeasure s - gmeasure t"
qed   REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_GMEASURE_DIFF_SUBSET; GSYM HAS_GMEASURE_MEASURE]);; *)

lemma has_gmeasure_union_negligible[dest]:
  assumes "s has_gmeasure m" "negligible t"
  shows "(s \<union> t) has_gmeasure m" unfolding has_gmeasure
  apply(rule has_integral_spike[OF assms(2) _ assms(1)[unfolded has_gmeasure]]) by auto

lemma has_gmeasure_diff_negligible[dest]:
  assumes "s has_gmeasure m" "negligible t" 
  shows "(s - t) has_gmeasure m" unfolding has_gmeasure
  apply(rule has_integral_spike[OF assms(2) _ assms(1)[unfolded has_gmeasure]]) by auto

lemma has_gmeasure_union_negligible_eq: True .. (*
 "!s t:real^N->bool m.
     negligible t ==> ((s \<union> t) has_gmeasure m \<longleftrightarrow> s has_gmeasure m)"
qed   REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[HAS_GMEASURE_UNION_NEGLIGIBLE] THEN
  SUBST1_TAC(SET_RULE `s:real^N->bool = (s \<union> t) DIFF (t DIFF s)`) THEN
  MATCH_MP_TAC HAS_GMEASURE_DIFF_NEGLIGIBLE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NEGLIGIBLE_DIFF THEN ASM_REWRITE_TAC[]);; *)

lemma has_gmeasure_diff_negligible_eq: True .. (*
 "!s t:real^N->bool m.
     negligible t ==> ((s DIFF t) has_gmeasure m \<longleftrightarrow> s has_gmeasure m)"
qed   REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[HAS_GMEASURE_DIFF_NEGLIGIBLE] THEN
  SUBST1_TAC(SET_RULE `s:real^N->bool = (s DIFF t) \<union> (t \<inter> s)`) THEN
  MATCH_MP_TAC HAS_GMEASURE_UNION_NEGLIGIBLE THEN
  ASM_SIMP_TAC[NEGLIGIBLE_INTER]);; *)

lemma has_gmeasure_almost: assumes "s has_gmeasure m" "negligible t" "s \<union> t = s' \<union> t"
  shows "s' has_gmeasure m"
proof- have *:"s' \<union> t - (t - s') = s'" by blast
  show ?thesis using has_gmeasure_union_negligible[OF assms(1-2)] unfolding assms(3)
    apply-apply(drule has_gmeasure_diff_negligible[where t="t - s'"])
    apply(rule negligible_diff) using assms(2) unfolding * by auto
qed

lemma has_gmeasure_almost_eq: True .. (*
 "!s s' t. negligible t \<and> s \<union> t = s' \<union> t
            ==> (s has_gmeasure m \<longleftrightarrow> s' has_gmeasure m)"
qed   MESON_TAC[HAS_GMEASURE_ALMOST]);; *)

lemma gmeasurable_almost: True .. (*
 "!s s' t. gmeasurable s \<and> negligible t \<and> s \<union> t = s' \<union> t
            ==> gmeasurable s'"
qed   REWRITE_TAC[measurable] THEN MESON_TAC[HAS_GMEASURE_ALMOST]);; *)

lemma has_gmeasure_negligible_union:
  assumes "s1 has_gmeasure m1" "s2 has_gmeasure m2" "negligible(s1 \<inter> s2)"
  shows "(s1 \<union> s2) has_gmeasure (m1 + m2)" 
  apply(rule has_gmeasure_almost[of "(s1 - (s1 \<inter> s2)) \<union> (s2 - (s1 \<inter> s2))" _ "s1 \<inter> s2"])
  apply(rule has_gmeasure_disjoint_union)
  apply(rule has_gmeasure_almost[of s1,OF _ assms(3)]) prefer 3
  apply(rule has_gmeasure_almost[of s2,OF _ assms(3)])
  using assms by auto

lemma measure_negligible_union: True .. (*
  "!s t. gmeasurable s \<and> gmeasurable t \<and> negligible(s \<inter> t)
         ==> measure(s \<union> t) = gmeasure s + gmeasure t"
qed   REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_GMEASURE_NEGLIGIBLE_UNION; GSYM HAS_GMEASURE_MEASURE]);; *)

lemma has_gmeasure_negligible_symdiff: True .. (*
 "!s t:real^N->bool m.
        s has_gmeasure m \<and>
        negligible((s DIFF t) \<union> (t DIFF s))
        ==> t has_gmeasure m"
qed   REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_GMEASURE_ALMOST THEN
  MAP_EVERY EXISTS_TAC
   [`s:real^N->bool`; `(s DIFF t) \<union> (t DIFF s):real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);; *)

lemma gmeasurable_negligible_symdiff: True .. (*
 "!s t:real^N->bool.
        gmeasurable s \<and> negligible((s DIFF t) \<union> (t DIFF s))
        ==> gmeasurable t"
qed   REWRITE_TAC[measurable] THEN
  MESON_TAC[HAS_GMEASURE_NEGLIGIBLE_SYMDIFF]);; *)

lemma measure_negligible_symdiff: True .. (*
 "!s t:real^N->bool.
        (measurable s \/ gmeasurable t) \<and>
        negligible((s DIFF t) \<union> (t DIFF s))
        ==> gmeasure s = gmeasure t"
qed   MESON_TAC[HAS_GMEASURE_NEGLIGIBLE_SYMDIFF; MEASURE_UNIQUE; UNION_COMM;
                HAS_GMEASURE_MEASURE]);; *)

lemma has_gmeasure_negligible_unions: assumes "finite f"
  "\<And>s. s \<in> f ==> s has_gmeasure (m s)"
  "\<And>s t. s \<in> f \<Longrightarrow> t \<in> f \<Longrightarrow> ~(s = t) ==> negligible(s \<inter> t)"
  shows "(\<Union> f) has_gmeasure (setsum m f)" using assms
proof induct case (insert x s)
  have *:"(x \<inter> \<Union>s) = \<Union>{x \<inter> y| y. y\<in>s}"by auto
  show ?case unfolding Union_insert setsum.insert [OF insert(1-2)] 
    apply(rule has_gmeasure_negligible_union) unfolding *
    apply(rule insert) defer apply(rule insert) apply(rule insert) defer
    apply(rule insert) prefer 4 apply(rule negligible_unions)
    defer apply safe apply(rule insert) using insert by auto
qed auto

lemma measure_negligible_unions: 
  assumes "finite f" "\<And>s. s \<in> f ==> s has_gmeasure (m s)"
  "\<And>s t. s \<in> f \<Longrightarrow> t \<in> f \<Longrightarrow> s \<noteq> t ==> negligible(s \<inter> t)"
  shows "gmeasure(\<Union> f) = setsum m f"
  apply rule apply(rule has_gmeasure_negligible_unions)
  using assms by auto

lemma has_gmeasure_disjoint_unions:
  assumes"finite f" "\<And>s. s \<in> f ==> s has_gmeasure (m s)"
  "\<And>s t. s \<in> f \<Longrightarrow> t \<in> f \<Longrightarrow> s \<noteq> t ==> s \<inter> t = {}"
  shows "(\<Union> f) has_gmeasure (setsum m f)"
  apply(rule has_gmeasure_negligible_unions[OF assms(1-2)]) using assms(3) by auto

lemma measure_disjoint_unions: 
  assumes "finite f" "\<And>s. s \<in> f ==> s has_gmeasure (m s)" 
  "\<And>s t. s \<in> f \<Longrightarrow> t \<in> f \<Longrightarrow> s \<noteq> t ==> s \<inter> t = {}"
  shows "gmeasure(\<Union> f) = setsum m f"
  apply rule apply(rule has_gmeasure_disjoint_unions[OF assms]) by auto

lemma has_gmeasure_negligible_unions_image:
  assumes "finite s" "\<And>x. x \<in> s ==> gmeasurable(f x)"
  "\<And>x y. x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> x \<noteq> y \<Longrightarrow> negligible((f x) \<inter> (f y))"
  shows "(\<Union> (f ` s)) has_gmeasure (setsum (\<lambda>x. gmeasure(f x)) s)"
proof- have *:"setsum (\<lambda>x. gmeasure(f x)) s = setsum gmeasure (f ` s)"
    apply(subst setsum_reindex_nonzero) defer
    apply(subst gmeasurable_measure_eq_0)
  proof- case goal2 thus ?case using assms(3)[of x y] by auto
  qed(insert assms, auto)
  show ?thesis unfolding * apply(rule has_gmeasure_negligible_unions) using assms by auto
qed

lemma measure_negligible_unions_image: True .. (*
 "!f:A->real^N->bool s.
        FINITE s \<and>
        (!x. x \<in> s ==> gmeasurable(f x)) \<and>
        (!x y. x \<in> s \<and> y \<in> s \<and> ~(x = y) ==> negligible((f x) \<inter> (f y)))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\<lambda>x. measure(f x))"
qed   REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_GMEASURE_NEGLIGIBLE_UNIONS_IMAGE]);;*)

lemma has_gmeasure_disjoint_unions_image: True .. (*
 "!f:A->real^N->bool s.
        FINITE s \<and>
        (!x. x \<in> s ==> gmeasurable(f x)) \<and>
        (!x y. x \<in> s \<and> y \<in> s \<and> ~(x = y) ==> DISJOINT (f x) (f y))
        ==> (UNIONS (IMAGE f s)) has_gmeasure (sum s (\<lambda>x. measure(f x)))"
qed   REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_GMEASURE_NEGLIGIBLE_UNIONS_IMAGE THEN
  ASM_SIMP_TAC[NEGLIGIBLE_EMPTY]);;*)

lemma measure_disjoint_unions_image: True .. (*
 "!f:A->real^N->bool s.
        FINITE s \<and>
        (!x. x \<in> s ==> gmeasurable(f x)) \<and>
        (!x y. x \<in> s \<and> y \<in> s \<and> ~(x = y) ==> DISJOINT (f x) (f y))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\<lambda>x. measure(f x))"
qed   REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_GMEASURE_DISJOINT_UNIONS_IMAGE]);;*)

lemma has_gmeasure_negligible_unions_image_strong: True .. (*
 "!f:A->real^N->bool s.
        FINITE {x | x \<in> s \<and> ~(f x = {})} \<and>
        (!x. x \<in> s ==> gmeasurable(f x)) \<and>
        (!x y. x \<in> s \<and> y \<in> s \<and> ~(x = y) ==> negligible((f x) \<inter> (f y)))
        ==> (UNIONS (IMAGE f s)) has_gmeasure (sum s (\<lambda>x. measure(f x)))"
qed   REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real^N->bool`;
                 `{x | x \<in> s \<and> ~((f:A->real^N->bool) x = {})}`]
        HAS_GMEASURE_NEGLIGIBLE_UNIONS_IMAGE) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; FINITE_RESTRICT] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[NOT_IN_EMPTY];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; TAUT `a \<and> ~(a \<and> b) \<longleftrightarrow> a \<and> ~b`] THEN
    REWRITE_TAC[MEASURE_EMPTY]]);; *)

lemma measure_negligible_unions_image_strong: True .. (*
 "!f:A->real^N->bool s.
        FINITE {x | x \<in> s \<and> ~(f x = {})} \<and>
        (!x. x \<in> s ==> gmeasurable(f x)) \<and>
        (!x y. x \<in> s \<and> y \<in> s \<and> ~(x = y) ==> negligible((f x) \<inter> (f y)))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\<lambda>x. measure(f x))"
qed   REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_GMEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG]);; *)

lemma has_gmeasure_disjoint_unions_image_strong: True .. (*
 "!f:A->real^N->bool s.
        FINITE {x | x \<in> s \<and> ~(f x = {})} \<and>
        (!x. x \<in> s ==> gmeasurable(f x)) \<and>
        (!x y. x \<in> s \<and> y \<in> s \<and> ~(x = y) ==> DISJOINT (f x) (f y))
        ==> (UNIONS (IMAGE f s)) has_gmeasure (sum s (\<lambda>x. measure(f x)))"
qed   REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_GMEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG THEN
  ASM_SIMP_TAC[NEGLIGIBLE_EMPTY]);; *)

lemma measure_disjoint_unions_image_strong: True .. (*
 "!f:A->real^N->bool s.
        FINITE {x | x \<in> s \<and> ~(f x = {})} \<and>
        (!x. x \<in> s ==> gmeasurable(f x)) \<and>
        (!x y. x \<in> s \<and> y \<in> s \<and> ~(x = y) ==> DISJOINT (f x) (f y))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\<lambda>x. measure(f x))"
qed   REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_GMEASURE_DISJOINT_UNIONS_IMAGE_STRONG]);; *)

lemma measure_union: True .. (*
 "!s t:real^N->bool.
        gmeasurable s \<and> gmeasurable t
        ==> measure(s \<union> t) = measure(s) + measure(t) - measure(s \<inter> t)"
qed   REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE
   `s \<union> t = (s \<inter> t) \<union> (s DIFF t) \<union> (t DIFF s)`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b - c = c + (a - c) + (b - c)`] THEN
  MP_TAC(ISPECL [`s DIFF t:real^N->bool`; `t DIFF s:real^N->bool`]
        MEASURE_DISJOINT_UNION) THEN
  ASM_SIMP_TAC[MEASURABLE_DIFF] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s \<inter> t:real^N->bool`;
                 `(s DIFF t) \<union> (t DIFF s):real^N->bool`]
                MEASURE_DISJOINT_UNION) THEN
  ASM_SIMP_TAC[MEASURABLE_DIFF; GMEASURABLE_UNION; GMEASURABLE_INTER] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN AP_TERM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[REAL_EQ_SUB_LADD] THEN MATCH_MP_TAC EQ_TRANS THENL
   [EXISTS_TAC `measure((s DIFF t) \<union> (s \<inter> t):real^N->bool)`;
    EXISTS_TAC `measure((t DIFF s) \<union> (s \<inter> t):real^N->bool)`] THEN
  (CONJ_TAC THENL
    [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_DISJOINT_UNION THEN
     ASM_SIMP_TAC[MEASURABLE_DIFF; GMEASURABLE_INTER];
     AP_TERM_TAC] THEN
   SET_TAC[]));; *)

lemma measure_union_le: True .. (*
 "!s t:real^N->bool.
        gmeasurable s \<and> gmeasurable t
        ==> measure(s \<union> t) <= gmeasure s + gmeasure t"
qed   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MEASURE_UNION] THEN
  REWRITE_TAC[REAL_ARITH `a + b - c <= a + b \<longleftrightarrow> 0 <= c`] THEN
  MATCH_MP_TAC MEASURE_POS_LE THEN ASM_SIMP_TAC[MEASURABLE_INTER]);; *)

lemma measure_unions_le: True .. (*
 "!f:(real^N->bool)->bool.
        FINITE f \<and> (!s. s \<in> f ==> gmeasurable s)
        ==> measure(UNIONS f) <= sum f (\<lambda>s. gmeasure s)"
qed   REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[UNIONS_0; UNIONS_INSERT; SUM_CLAUSES] THEN
  REWRITE_TAC[MEASURE_EMPTY; REAL_LE_REFL] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:(real^N->bool)->bool`] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(s:real^N->bool) + measure(UNIONS f:real^N->bool)` THEN
  ASM_SIMP_TAC[MEASURE_UNION_LE; GMEASURABLE_UNIONS] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[]);; *)

lemma measure_unions_le_image: True .. (*
 "!f:A->bool s:A->(real^N->bool).
        FINITE f \<and> (!a. a \<in> f ==> gmeasurable(s a))
        ==> measure(UNIONS (IMAGE s f)) <= sum f (\<lambda>a. measure(s a))"
qed   REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE s (f:A->bool)) (\<lambda>k:real^N->bool. gmeasure k)` THEN
  ASM_SIMP_TAC[MEASURE_UNIONS_LE; FORALL_IN_IMAGE; FINITE_IMAGE] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SUM_IMAGE_LE THEN
  ASM_SIMP_TAC[MEASURE_POS_LE]);; *)

lemma gmeasurable_inner_outer: True .. (*
 "!s:real^N->bool.
        gmeasurable s \<longleftrightarrow>
                !e. 0 < e
                    ==> ?t u. t \<subseteq> s \<and> s \<subseteq> u \<and>
                              gmeasurable t \<and> gmeasurable u \<and>
                              abs(measure t - gmeasure u) < e"
qed   GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REPEAT(EXISTS_TAC `s:real^N->bool`) THEN
    ASM_REWRITE_TAC[SUBSET_REFL; REAL_SUB_REFL; REAL_ABS_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[MEASURABLE_INTEGRABLE] THEN MATCH_MP_TAC INTEGRABLE_STRADDLE THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->bool`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(\<lambda>x. if x \<in> t then 1 else 0):real^N->real^1`;
    `(\<lambda>x. if x \<in> u then 1 else 0):real^N->real^1`;
    `lift(measure(t:real^N->bool))`;
    `lift(measure(u:real^N->bool))`] THEN
  ASM_REWRITE_TAC[GSYM HAS_GMEASURE; GSYM HAS_GMEASURE_MEASURE] THEN
  ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[_VEC; REAL_POS; REAL_LE_REFL]) THEN
  ASM SET_TAC[]);; *)

lemma has_gmeasure_inner_outer: True .. (*
 "!s:real^N->bool m.
        s has_gmeasure m \<longleftrightarrow>
                (!e. 0 < e ==> ?t. t \<subseteq> s \<and> gmeasurable t \<and>
                                    m - e < gmeasure t) \<and>
                (!e. 0 < e ==> ?u. s \<subseteq> u \<and> gmeasurable u \<and>
                                    gmeasure u < m + e)"
qed   REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_GMEASURE_MEASURABLE_MEASURE] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "t") (LABEL_TAC "u")) THEN
  MATCH_MP_TAC(TAUT `a \<and> (a ==> b) ==> a \<and> b`) THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [MEASURABLE_INNER_OUTER] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "u" (MP_TAC o SPEC `e / 2`) THEN
    REMOVE_THEN "t" (MP_TAC o SPEC `e / 2`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[IMP_IMP; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `0 < e \<and> t <= u \<and> m - e / 2 < t \<and> u < m + e / 2
                          ==> abs(t - u) < e`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `~(0 < x - y) \<and> ~(0 < y - x) ==> x = y`) THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [REMOVE_THEN "u" (MP_TAC o SPEC `measure(s:real^N->bool) - m`) THEN
      ASM_REWRITE_TAC[REAL_SUB_ADD2; GSYM REAL_NOT_LE];
      REMOVE_THEN "t" (MP_TAC o SPEC `m - measure(s:real^N->bool)`) THEN
      ASM_REWRITE_TAC[REAL_SUB_SUB2; GSYM REAL_NOT_LE]] THEN
    ASM_MESON_TAC[MEASURE_SUBSET]]);; *)

lemma has_gmeasure_inner_outer_le: True .. (*
 "!s:real^N->bool m.
        s has_gmeasure m \<longleftrightarrow>
                (!e. 0 < e ==> ?t. t \<subseteq> s \<and> gmeasurable t \<and>
                                    m - e <= gmeasure t) \<and>
                (!e. 0 < e ==> ?u. s \<subseteq> u \<and> gmeasurable u \<and>
                                    gmeasure u <= m + e)"
qed   REWRITE_TAC[HAS_GMEASURE_INNER_OUTER] THEN
  MESON_TAC[REAL_ARITH `0 < e \<and> m - e / 2 <= t ==> m - e < t`;
            REAL_ARITH `0 < e \<and> u <= m + e / 2 ==> u < m + e`;
            REAL_ARITH `0 < e \<longleftrightarrow> 0 < e / 2`; REAL_LT_IMP_LE]);; *)

lemma has_gmeasure_limit: True .. (*
 "!s. s has_gmeasure m \<longleftrightarrow>
        !e. 0 < e
            ==> ?B. 0 < B \<and>
                    !a b. ball(0,B) \<subseteq> {a..b}
                          ==> ?z. (s \<inter> {a..b}) has_gmeasure z \<and>
                                  abs(z - m) < e"
qed   GEN_TAC THEN REWRITE_TAC[HAS_GMEASURE] THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL] THEN
  REWRITE_TAC[IN_UNIV] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[MESON[IN_INTER]
        `(if x \<in> k \<inter> s then a else b) =
         (if x \<in> s then if x \<in> k then a else b else b)`] THEN
  REWRITE_TAC[EXISTS_LIFT; GSYM LIFT_SUB; NORM_LIFT]);; *)

(* ------------------------------------------------------------------------- *)
(* properties of gmeasure under simple affine transformations.                *)
(* ------------------------------------------------------------------------- *)

lemma has_gmeasure_affinity: True .. (*
 "!s m c y. s has_gmeasure y
             ==> (IMAGE (\<lambda>x:real^N. m % x + c) s)
                 has_gmeasure abs(m) pow (dimindex(:N)) * y"
qed   REPEAT GEN_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[REAL_ABS_NUM; VECTOR_ADD_LID; VECTOR_MUL_LZERO] THEN
    ONCE_REWRITE_TAC[MATCH_MP (ARITH_RULE `~(x = 0) ==> x = SUC(x - 1)`)
     (SPEC_ALL DIMINDEX_NONZERO)] THEN DISCH_TAC THEN
    REWRITE_TAC[real_pow; REAL_MUL_LZERO; HAS_GMEASURE_0] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{c:real^N}` THEN
    SIMP_TAC[NEGLIGIBLE_FINITE; FINITE_RULES] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_GMEASURE] THEN
  ONCE_REWRITE_TAC[HAS_INTEGRAL] THEN REWRITE_TAC[IN_UNIV] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real / abs(m) pow dimindex(:N)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; GSYM REAL_ABS_NZ; REAL_POW_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `abs(m) * B + norm(c:real^N)` THEN
  ASM_SIMP_TAC[REAL_ARITH `0 < B \<and> 0 <= x ==> 0 < B + x`;
               NORM_POS_LE; REAL_LT_MUL; GSYM REAL_ABS_NZ; REAL_POW_LT] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
  REWRITE_TAC[IN_IMAGE] THEN
  ASM_SIMP_TAC[VECTOR_EQ_AFFINITY; UNWIND_THM1] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`if 0 <= m then inv m % u + --(inv m % c):real^N
                 else inv m % v + --(inv m % c)`;
     `if 0 <= m then inv m % v + --(inv m % c):real^N
                 else inv m % u + --(inv m % c)`]) THEN
  MATCH_MP_TAC(TAUT `a \<and> (a ==> b ==> c) ==> (a ==> b) ==> c`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPEC `m % x + c:real^N`) THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[IN_BALL; IN_INTERVAL] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NORM_ARITH `dist(0,x) = norm(x:real^N)`] THEN
      DISCH_TAC THEN MATCH_MP_TAC(NORM_ARITH
       `norm(x:real^N) < a ==> norm(x + y) < a + norm(y)`) THEN
      ASM_SIMP_TAC[NORM_MUL; REAL_LT_LMUL; GSYM REAL_ABS_NZ];
      ALL_TAC] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT;
             COND_COMPONENT] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC[REAL_ARITH `m * u + --(m * c):real = (u - c) * m`] THEN
    SUBST1_TAC(REAL_ARITH
      `inv(m) = if 0 <= inv(m) then abs(inv m) else --(abs(inv m))`) THEN
    SIMP_TAC[REAL_LE_INV_EQ] THEN
    REWRITE_TAC[REAL_ARITH `(x - y:real) * --z = (y - x) * z`] THEN
    REWRITE_TAC[REAL_ABS_INV; GSYM real_div] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; GSYM REAL_ABS_NZ] THEN
    ASM_REWRITE_TAC[real_abs] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `0:real^N`) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^1`
   (fun th -> EXISTS_TAC `(abs m pow dimindex (:N)) % z:real^1` THEN
              MP_TAC th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP(REAL_FIELD `~(x = 0) ==> ~(inv x = 0)`)) THEN
  REWRITE_TAC[TAUT `a ==> b ==> c \<longleftrightarrow> b \<and> a ==> c`] THEN
  DISCH_THEN(MP_TAC o SPEC `--(inv m % c):real^N` o
    MATCH_MP HAS_INTEGRAL_AFFINITY) THEN
  ASM_REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; REAL_INV_INV] THEN
  SIMP_TAC[COND_ID] THEN COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC;
               VECTOR_MUL_LNEG; VECTOR_MUL_RNEG] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID; VECTOR_NEG_NEG] THEN
  REWRITE_TAC[VECTOR_ARITH `(u + --c) + c:real^N = u`] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_INV_INV; GSYM REAL_POW_INV] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[LIFT_CMUL; GSYM VECTOR_SUB_LDISTRIB] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_POW; REAL_ABS_ABS] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_POW_LT; GSYM REAL_ABS_NZ]);; *)

lemma stretch_galois: True .. (*
 "!x:real^N y:real^N m.
        (!k. 1 <= k \<and> k <= dimindex(:N) ==>  ~(m k = 0))
        ==> ((y = (lambda k. m k * x$k)) \<longleftrightarrow> (lambda k. inv(m k) * y$k) = x)"
qed   REPEAT GEN_TAC THEN SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
  MATCH_MP_TAC(MESON[]
   `(!x. p x ==> (q x \<longleftrightarrow> r x))
    ==> (!x. p x) ==> ((!x. q x) \<longleftrightarrow> (!x. r x))`) THEN
  GEN_TAC THEN ASM_CASES_TAC `1 <= k \<and> k <= dimindex(:N)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD);; *)

lemma has_gmeasure_stretch: True .. (*
 "!s m y. s has_gmeasure y
           ==> (IMAGE (\<lambda>x:real^N. lambda k. m k * x$k) s :real^N->bool)
               has_gmeasure abs(product (1..dimindex(:N)) m) * y"
qed   REPEAT STRIP_TAC THEN ASM_CASES_TAC
   `!k. 1 <= k \<and> k <= dimindex(:N) ==> ~(m k = 0)`
  THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `product(1..dimindex (:N)) m = 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[PRODUCT_EQ_0_NUMSEG]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LZERO; HAS_GMEASURE_0] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x:real^N | x$k = 0}` THEN
    ASM_SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE; SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA; REAL_MUL_LZERO]] THEN
  UNDISCH_TAC `(s:real^N->bool) has_gmeasure y` THEN
  REWRITE_TAC[HAS_GMEASURE] THEN
  ONCE_REWRITE_TAC[HAS_INTEGRAL] THEN REWRITE_TAC[IN_UNIV] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `0 < abs(product(1..dimindex(:N)) m)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_NZ; REAL_LT_DIV; PRODUCT_EQ_0_NUMSEG];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real / abs(product(1..dimindex(:N)) m)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sup(IMAGE (\<lambda>k. abs(m k) * B) (1..dimindex(:N)))` THEN
  MATCH_MP_TAC(TAUT `a \<and> (a ==> b) ==> a \<and> b`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_SUP_FINITE; FINITE_IMAGE; NUMSEG_EMPTY; FINITE_NUMSEG;
                 IN_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1; IMAGE_EQ_EMPTY;
                 EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[IN_NUMSEG; DIMINDEX_GE_1; LE_REFL; REAL_LT_MUL; REAL_ABS_NZ];
    DISCH_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[IN_IMAGE; STRETCH_GALOIS; UNWIND_THM1] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`(lambda k. min (inv(m k) * (u:real^N)$k)
                     (inv(m k) * (v:real^N)$k)):real^N`;
     `(lambda k. max (inv(m k) * (u:real^N)$k)
                 (inv(m k) * (v:real^N)$k)):real^N`]) THEN
  MATCH_MP_TAC(TAUT `a \<and> (b ==> a ==> c) ==> (a ==> b) ==> c`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `z:real^1` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `!k. 1 <= k \<and> k <= dimindex (:N) ==> ~(inv(m k) = 0)`
    MP_TAC THENL [ASM_SIMP_TAC[REAL_INV_EQ_0]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_STRETCH)] THEN
  (MP_TAC(ISPECL [`u:real^N`; `v:real^N`; `\i:num. inv(m i)`]
    IMAGE_STRETCH_INTERVAL) THEN
   SUBGOAL_THEN `~(interval[u:real^N,v] = {})` ASSUME_TAC THENL
    [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
      `s \<subseteq> t ==> ~(s = {}) ==> ~(t = {})`)) THEN
     ASM_REWRITE_TAC[BALL_EQ_EMPTY; GSYM REAL_NOT_LT];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM))
  THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `b \<subseteq> s ==> b' \<subseteq> IMAGE f b ==> b' \<subseteq> IMAGE f s`)) THEN
    REWRITE_TAC[IN_BALL; SUBSET; NORM_ARITH `dist(0,x) = norm x`;
                IN_IMAGE] THEN
    ASM_SIMP_TAC[STRETCH_GALOIS; REAL_INV_EQ_0; UNWIND_THM1; REAL_INV_INV] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC
     `norm(sup(IMAGE(\<lambda>k. abs(m k)) (1..dimindex(:N))) % x:real^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
      SIMP_TAC[LAMBDA_BETA; VECTOR_MUL_COMPONENT; REAL_ABS_MUL] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y`) THEN
      ASM_SIMP_TAC[REAL_LE_SUP_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
                  NUMSEG_EMPTY; FINITE_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; IN_NUMSEG] THEN ASM_MESON_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `abs(sup(IMAGE(\<lambda>k. abs(m k)) (1..dimindex(:N)))) * B` THEN
    SUBGOAL_THEN `0 < sup(IMAGE(\<lambda>k. abs(m k)) (1..dimindex(:N)))`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_SUP_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
                  NUMSEG_EMPTY; FINITE_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; GSYM REAL_ABS_NZ; IN_NUMSEG] THEN
      ASM_MESON_TAC[DIMINDEX_GE_1; LE_REFL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_ARITH `0 < x ==> 0 < abs x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sup(IMAGE(\<lambda>k. abs(m k)) (1..dimindex(:N))) * B` THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_ARITH `0 < x ==> abs x <= x`] THEN
    ASM_SIMP_TAC[REAL_LE_SUP_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
                  NUMSEG_EMPTY; FINITE_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1] THEN
    ASM_SIMP_TAC[EXISTS_IN_IMAGE; REAL_LE_RMUL_EQ] THEN
    ASM_SIMP_TAC[REAL_SUP_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
                 NUMSEG_EMPTY; FINITE_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1] THEN
    MP_TAC(ISPEC `IMAGE (\<lambda>k. abs (m k)) (1..dimindex(:N))` SUP_FINITE) THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMAGE_EQ_EMPTY; NUMSEG_EMPTY;
                 GSYM NOT_LE; DIMINDEX_GE_1] THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];

    MATCH_MP_TAC(MESON[]
     `s = t \<and> P z ==> (f has_integral z) s ==> Q
                       ==> ?w. (f has_integral w) t \<and> P w`) THEN
    SIMP_TAC[GSYM PRODUCT_INV; FINITE_NUMSEG; GSYM REAL_ABS_INV] THEN
    REWRITE_TAC[REAL_INV_INV] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC(SET_RULE
       `(!x. f x = x) ==> IMAGE f s = s`) THEN
      SIMP_TAC[o_THM; LAMBDA_BETA; CART_EQ] THEN
      ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_MUL_LID];
      REWRITE_TAC[ABS_; _SUB; LIFT_; _CMUL] THEN
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; ETA_AX] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_ABS] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
      ASM_MESON_TAC[ABS_; _SUB; LIFT_]]]);; *)

lemma has_gmeasure_translation: True .. (*
 "!s m a. s has_gmeasure m ==> (IMAGE (\<lambda>x:real^N. a + x) s) has_gmeasure m"
qed   REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `1`; `a:real^N`; `m:real`]
                HAS_GMEASURE_AFFINITY) THEN
  REWRITE_TAC[VECTOR_MUL_LID; REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID] THEN
  REWRITE_TAC[VECTOR_ADD_SYM]);; *)

lemma negligible_translation: True .. (*
 "!s a. negligible s ==> negligible (IMAGE (\<lambda>x:real^N. a + x) s)"
qed   SIMP_TAC[GSYM HAS_GMEASURE_0; HAS_GMEASURE_TRANSLATION]);; *)

lemma has_gmeasure_translation_eq: True .. (*
 "!s m. (IMAGE (\<lambda>x:real^N. a + x) s) has_gmeasure m \<longleftrightarrow> s has_gmeasure m"
qed   REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[HAS_GMEASURE_TRANSLATION] THEN
  DISCH_THEN(MP_TAC o SPEC `--a:real^N` o
    MATCH_MP HAS_GMEASURE_TRANSLATION) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `--a + a + b:real^N = b`] THEN
  SET_TAC[]);; *)

lemma negligible_translation_rev: True .. (*
 "!s a. negligible (IMAGE (\<lambda>x:real^N. a + x) s) ==> negligible s"
qed   SIMP_TAC[GSYM HAS_GMEASURE_0; HAS_GMEASURE_TRANSLATION_EQ]);; *)

lemma negligible_translation_eq: True .. (*
 "!s a. negligible (IMAGE (\<lambda>x:real^N. a + x) s) \<longleftrightarrow> negligible s"
qed   SIMP_TAC[GSYM HAS_GMEASURE_0; HAS_GMEASURE_TRANSLATION_EQ]);; *)

lemma gmeasurable_translation: True .. (*
 "!s. gmeasurable (IMAGE (\<lambda>x. a + x) s) \<longleftrightarrow> gmeasurable s"
qed   REWRITE_TAC[measurable; HAS_GMEASURE_TRANSLATION_EQ]);; *)

lemma measure_translation: True .. (*
 "!s. gmeasurable s ==> measure(IMAGE (\<lambda>x. a + x) s) = gmeasure s"
qed   REWRITE_TAC[HAS_GMEASURE_MEASURE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_REWRITE_TAC[HAS_GMEASURE_TRANSLATION_EQ]);; *)

lemma has_gmeasure_scaling: True .. (*
 "!s m c. s has_gmeasure m
           ==> (IMAGE (\<lambda>x:real^N. c % x) s) has_gmeasure
               (abs(c) pow dimindex(:N)) * m"
qed   REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c:real`; `0:real^N`; `m:real`]
                HAS_GMEASURE_AFFINITY) THEN
  REWRITE_TAC[VECTOR_ADD_RID]);; *)

lemma has_gmeasure_scaling_eq: True .. (*
 "!s m c. ~(c = 0)
           ==> (IMAGE (\<lambda>x:real^N. c % x) s
                  has_gmeasure (abs(c) pow dimindex(:N)) * m \<longleftrightarrow>
                s has_gmeasure m)"
qed   REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[HAS_GMEASURE_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(c)` o MATCH_MP HAS_GMEASURE_SCALING) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; GSYM REAL_ABS_MUL] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL; VECTOR_MUL_ASSOC; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_MUL; REAL_MUL_LINV] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_ABS_NUM; REAL_MUL_LID; VECTOR_MUL_LID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);; *)

lemma gmeasurable_scaling: True .. (*
 "!s c. gmeasurable s ==> gmeasurable (IMAGE (\<lambda>x. c % x) s)"
qed   REWRITE_TAC[measurable] THEN MESON_TAC[HAS_GMEASURE_SCALING]);; *)

lemma gmeasurable_scaling_eq: True .. (*
 "!s c. ~(c = 0) ==> (measurable (IMAGE (\<lambda>x. c % x) s) \<longleftrightarrow> gmeasurable s)"
qed   REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[MEASURABLE_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv c` o MATCH_MP GMEASURABLE_SCALING) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; GSYM REAL_ABS_MUL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
  SET_TAC[]);; *)

lemma measure_scaling: True .. (*
 "!s. gmeasurable s
       ==> measure(IMAGE (\<lambda>x:real^N. c % x) s) =
              (abs(c) pow dimindex(:N)) * gmeasure s"
qed   REWRITE_TAC[HAS_GMEASURE_MEASURE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURE_UNIQUE THEN ASM_SIMP_TAC[HAS_GMEASURE_SCALING]);; *)

(* ------------------------------------------------------------------------- *)
(* Measurability of countable unions and intersections of various kinds.     *)
(* ------------------------------------------------------------------------- *)

lemma has_gmeasure_nested_unions:
  assumes "\<And>n. gmeasurable(s n)" "\<And>n. gmeasure(s n) \<le> B" "\<And>n. s(n) \<subseteq> s(Suc n)"
  shows "gmeasurable(\<Union> { s n | n. n \<in> UNIV }) \<and>
  (\<lambda>n. gmeasure(s n)) ----> gmeasure(\<Union> { s(n) | n. n \<in> UNIV })"
proof- let ?g = "\<lambda>x. if x \<in> \<Union>{s n |n. n \<in> UNIV} then 1 else (0::real)"
  have "?g integrable_on UNIV \<and> (\<lambda>k. integral UNIV (\<lambda>x. if x \<in> s k then 1 else 0)) ----> integral UNIV ?g"
  proof(rule monotone_convergence_increasing)
    case goal1 show ?case using assms(1) unfolding gmeasurable_integrable by auto
    case goal2 show ?case using assms(3) by auto
    have "\<forall>m n. m\<le>n \<longrightarrow> s m \<subseteq> s n" apply(subst transitive_stepwise_le_eq)
      using assms(3) by auto note * = this[rule_format]
    have **:"\<And>x e n. \<lbrakk>x \<in> s n; 0 < e\<rbrakk> \<Longrightarrow> \<exists>N. \<forall>n. x \<notin> s n \<longrightarrow> N \<le> n \<longrightarrow> dist 0 1 < e"
      apply(rule_tac x=n in exI) using * by auto 
    case goal3 show ?case unfolding Lim_sequentially by(auto intro!: **) 
    case goal4 show ?case unfolding bounded_def apply(rule_tac x=0 in exI)
      apply(rule_tac x=B in exI) unfolding dist_real_def apply safe
      unfolding measure_integral_univ[OF assms(1),THEN sym]
      apply(subst abs_of_nonpos) using assms(1,2) by auto
  qed note conjunctD2[OF this]
  thus ?thesis unfolding gmeasurable_integrable[THEN sym] measure_integral_univ[OF assms(1)]
    apply- unfolding measure_integral_univ by auto
qed

lemmas gmeasurable_nested_unions = has_gmeasure_nested_unions(1)

lemma sums_alt:"f sums s = (\<lambda>n. setsum f {0..n}) ----> s"
proof- have *:"\<And>n. {0..<Suc n} = {0..n}" by auto
  show ?thesis unfolding sums_def apply(subst LIMSEQ_Suc_iff[THEN sym]) unfolding * ..
qed

lemma has_gmeasure_countable_negligible_unions: 
  assumes "\<And>n. gmeasurable(s n)" "\<And>m n. m \<noteq> n \<Longrightarrow> negligible(s m \<inter> s n)"
  "\<And>n. setsum (\<lambda>k. gmeasure(s k)) {0..n}  <= B"
  shows "gmeasurable(\<Union> { s(n) |n. n \<in> UNIV })" (is ?m)
  "((\<lambda>n. gmeasure(s n)) sums (gmeasure(\<Union> { s(n) |n. n \<in> UNIV })))" (is ?s)
proof- have *:"\<And>n. (\<Union> (s ` {0..n})) has_gmeasure (setsum (\<lambda>k. gmeasure(s k)) {0..n})"
    apply(rule has_gmeasure_negligible_unions_image) using assms by auto
  have **:"(\<Union>{\<Union>s ` {0..n} |n. n \<in> UNIV}) = (\<Union>{s n |n. n \<in> UNIV})" unfolding simple_image by fastsimp
  have "gmeasurable (\<Union>{\<Union>s ` {0..n} |n. n \<in> UNIV}) \<and>
    (\<lambda>n. gmeasure (\<Union>(s ` {0..n}))) ----> gmeasure (\<Union>{\<Union>s ` {0..n} |n. n \<in> UNIV})"
    apply(rule has_gmeasure_nested_unions) apply(rule gmeasurableI,rule *)
    unfolding measure_unique[OF *] defer apply(rule Union_mono,rule image_mono) using assms(3) by auto
  note lem = conjunctD2[OF this,unfolded **]
  show ?m using lem(1) .
  show ?s using lem(2) unfolding sums_alt measure_unique[OF *] .
qed     

lemma negligible_countable_unions: True .. (*
 "!s:num->real^N->bool.
        (!n. negligible(s n)) ==> negligible(UNIONS {s(n) | n \<in> (:num)})"
qed   REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:num->real^N->bool`; `0`]
    HAS_GMEASURE_COUNTABLE_NEGLIGIBLE_UNIONS) THEN
  ASM_SIMP_TAC[MEASURE_EQ_0; SUM_0; REAL_LE_REFL; LIFT_NUM] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[HAS_GMEASURE_0; gmeasurable; INTER_SUBSET; NEGLIGIBLE_SUBSET];
    ALL_TAC] THEN
  SIMP_TAC[GSYM GMEASURABLE_MEASURE_EQ_0] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM LIFT_EQ] THEN
  MATCH_MP_TAC SERIES_UNIQUE THEN REWRITE_TAC[LIFT_NUM] THEN
  MAP_EVERY EXISTS_TAC [`(\<lambda>k. 0):num->real^1`; `from 0`] THEN
  ASM_REWRITE_TAC[SERIES_0]);; *)

lemma gmeasurable_countable_unions_strong:
  assumes "\<And>n. gmeasurable(s n)" "\<And>n::nat. gmeasure(\<Union>{s k |k. k \<le> n}) \<le> B"
  shows "gmeasurable(\<Union>{ s(n) |n. n \<in> UNIV })"
proof- have *:"\<Union>{\<Union>s ` {0..n} |n. n \<in> UNIV} = \<Union>range s" unfolding simple_image by fastsimp
  show ?thesis unfolding simple_image
    apply(rule gmeasurable_nested_unions[of "\<lambda>n. \<Union>(s ` {0..n})", THEN conjunct1,unfolded *])
  proof- fix n::nat show "gmeasurable (\<Union>s ` {0..n})"
      apply(rule gmeasurable_finite_unions) using assms(1) by auto
    show "gmeasure (\<Union>s ` {0..n}) \<le> B"
      using assms(2)[of n] unfolding simple_image[THEN sym] by auto
    show "\<Union>s ` {0..n} \<subseteq> \<Union>s ` {0..Suc n}" apply(rule Union_mono) by auto
  qed
qed

lemma has_gmeasure_countable_negligible_unions_bounded: True .. (*
 "!s:num->real^N->bool.
        (!n. gmeasurable(s n)) \<and>
        (!m n. ~(m = n) ==> negligible(s m \<inter> s n)) \<and>
        bounded(\<Union>{ s(n) | n \<in> (:num) })
        ==> gmeasurable(\<Union>{ s(n) | n \<in> (:num) }) \<and>
            ((\<lambda>n. lift(measure(s n))) sums
             lift(measure(\<Union>{ s(n) | n \<in> (:num) }))) (from 0)"
qed   REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_GMEASURE_COUNTABLE_NEGLIGIBLE_UNIONS THEN
  EXISTS_TAC `measure(interval[a:real^N,b])` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(UNIONS (IMAGE (s:num->real^N->bool) (0..n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS_IMAGE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG];
    MATCH_MP_TAC MEASURE_SUBSET THEN REWRITE_TAC[MEASURABLE_INTERVAL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GMEASURABLE_UNIONS THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE];
      ASM SET_TAC[]]]);; *)

lemma gmeasurable_countable_negligible_unions_bounded: True .. (*
 "!s:num->real^N->bool.
        (!n. gmeasurable(s n)) \<and>
        (!m n. ~(m = n) ==> negligible(s m \<inter> s n)) \<and>
        bounded(\<Union>{ s(n) | n \<in> (:num) })
        ==> gmeasurable(\<Union>{ s(n) | n \<in> (:num) })"
qed   SIMP_TAC[HAS_GMEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED]);; *)

lemma gmeasurable_countable_unions: True .. (*
 "!s:num->real^N->bool B.
        (!n. gmeasurable(s n)) \<and>
        (!n. sum (0..n) (\<lambda>k. measure(s k)) \<le> B)
        ==> gmeasurable(\<Union>{ s(n) | n \<in> (:num) })"
qed   REPEAT STRIP_TAC THEN MATCH_MP_TAC GMEASURABLE_COUNTABLE_UNIONS_STRONG THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..n) (\<lambda>k. measure(s k:real^N->bool))` THEN
  ASM_REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (rand o rand) MEASURE_UNIONS_LE_IMAGE o
       rand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
  REWRITE_TAC[IN_NUMSEG; LE_0]);; *)

lemma gmeasurable_countable_inters: True .. (*
 "!s:num->real^N->bool.
        (!n. gmeasurable(s n))
        ==> gmeasurable(INTERS { s(n) | n \<in> (:num) })"
qed   REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `INTERS { s(n):real^N->bool | n \<in> (:num) } =
                s 0 DIFF (\<Union>{s 0 DIFF s n | n \<in> (:num)})`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTERS; IN_DIFF; IN_UNIONS] THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC GMEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GMEASURABLE_COUNTABLE_UNIONS_STRONG THEN
  EXISTS_TAC `measure(s 0:real^N->bool)` THEN
  ASM_SIMP_TAC[MEASURABLE_DIFF; LE_0] THEN
  GEN_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; IN_ELIM_THM; IN_DIFF] THEN
    MESON_TAC[IN_DIFF]] THEN
  ONCE_REWRITE_TAC[GSYM IN_NUMSEG_0] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
               GMEASURABLE_DIFF; GMEASURABLE_UNIONS]);; *)

(* ------------------------------------------------------------------------- *)
(* measurability of compact and bounded open sets.                           *)
(* ------------------------------------------------------------------------- *)

lemma gmeasurable_compact: True .. (*
 "!s:real^N->bool. compact s ==> gmeasurable s"
qed   lemma lemma = prove
   (`!f s:real^N->bool.
          (!n. FINITE(f n)) \<and>
          (!n. s \<subseteq> UNIONS(f n)) \<and>
          (!x. ~(x \<in> s) ==> ?n. ~(x \<in> UNIONS(f n))) \<and>
          (!n a. a \<in> f(SUC n) ==> ?b. b \<in> f(n) \<and> a \<subseteq> b) \<and>
          (!n a. a \<in> f(n) ==> gmeasurable a)
          ==> gmeasurable s"
qed     REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `!n. UNIONS(f(SUC n):(real^N->bool)->bool) \<subseteq> UNIONS(f n)`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `s = INTERS { UNIONS(f n) | n \<in> (:num) }:real^N->bool`
    SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
      REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_IMAGE; IN_UNIV] THEN
      REWRITE_TAC[IN_IMAGE] THEN ASM SET_TAC[];
      MATCH_MP_TAC GMEASURABLE_COUNTABLE_INTERS THEN
      ASM_REWRITE_TAC[] THEN GEN_TAC THEN
      MATCH_MP_TAC GMEASURABLE_UNIONS THEN
      ASM_MESON_TAC[]]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
  EXISTS_TAC
   `\n. { k | ?u:real^N. (!i. 1 \<le> i \<and> i \<le> dimindex(:N)
                              ==> integer(u$i)) \<and>
                  k = { x:real^N | !i. 1 \<le> i \<and> i \<le> dimindex(:N)
                                       ==> u$i / 2 pow n \<le> x$i \<and>
                                           x$i < (u$i + 1) / 2 pow n } \<and>
                  ~(s \<inter> k = {})}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
    SUBGOAL_THEN
     `?N. !x:real^N i. x \<in> s \<and> 1 \<le> i \<and> i \<le> dimindex(:N)
                       ==> abs(x$i * 2 pow n) < N`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
      REWRITE_TAC[BOUNDED_POS; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `B:real` THEN STRIP_TAC THEN
      MP_TAC(SPEC `B * 2 pow n` (MATCH_MP REAL_ARCH REAL_LT_01)) THEN
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[REAL_MUL_RID] THEN
      X_GEN_TAC `N:num` THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM] THEN
      SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS; REAL_LET_TRANS];
      ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `IMAGE (\<lambda>u. {x | !i. 1 \<le> i \<and> i \<le> dimindex(:N)
                          ==> (u:real^N)$i \<le> (x:real^N)$i * 2 pow n \<and>
                              x$i * 2 pow n < u$i + 1})
            {u | !i. 1 \<le> i \<and> i \<le> dimindex(:N) ==> integer (u$i) \<and>
                                                     abs(u$i) \<le> N}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_CART THEN
      REWRITE_TAC[GSYM REAL_BOUNDS_LE; FINITE_INTSEG];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `l:real^N->bool` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N` THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_REVERSE_INTEGERS THEN
      ASM_SIMP_TAC[INTEGER_CLOSED] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` MP_TAC) THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `k:num`)) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `k:num`]) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    EXISTS_TAC `(lambda i. floor(2 pow n * (x:real^N)$i)):real^N` THEN
    ONCE_REWRITE_TAC[TAUT `(a \<and> b \<and> c) \<and> d \<longleftrightarrow> b \<and> a \<and> c \<and> d`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN SIMP_TAC[LAMBDA_BETA; FLOOR] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
    REWRITE_TAC[REAL_MUL_SYM; FLOOR];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_CLOSED) THEN
    REWRITE_TAC[closed; open_def] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`inv(2)`; `e / (dimindex(:N))`] REAL_ARCH_POW_INV) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_RDIV_EQ; REAL_OF_NUM_LT;
                 DIMINDEX_GE_1; ARITH_RULE `0 < x \<longleftrightarrow> 1 \<le> x`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a \<and> b \<and> c) \<and> d \<longleftrightarrow> b \<and> a \<and> c \<and> d`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    X_GEN_TAC `u:real^N` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC o CONJUNCT2) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N`
     (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `d < e ==> x \<le> d ==> x < e`)) THEN
    REWRITE_TAC[dist] THEN
    W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC(REAL_ARITH `a \<le> b ==> x \<le> a ==> x \<le> b`) THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC SUM_BOUND THEN
    SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; VECTOR_SUB_COMPONENT] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `k:num`)) THEN
    ASM_REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
    REWRITE_TAC[REAL_MUL_LID; GSYM REAL_POW_INV] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`n:num`; `a:real^N->bool`] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N`
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a \<and> b \<and> c) \<and> d \<longleftrightarrow> b \<and> a \<and> c \<and> d`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN
    EXISTS_TAC `(lambda i. floor((u:real^N)$i / 2)):real^N` THEN
    ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; LAMBDA_BETA; FLOOR] THEN
    MATCH_MP_TAC(SET_RULE `~(s \<inter> a = {}) \<and> a \<subseteq> b
                           ==> ~(s \<inter> b = {}) \<and> a \<subseteq> b`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "a" THEN REWRITE_TAC[SUBSET] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_pow; real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
    MP_TAC(SPEC `(u:real^N)$k / 2` FLOOR) THEN
    REWRITE_TAC[REAL_ARITH `u / 2 < floor(u / 2) + 1 \<longleftrightarrow>
                            u < 2 * floor(u / 2) + 2`] THEN
    ASM_SIMP_TAC[REAL_LT_INTEGERS; INTEGER_CLOSED; FLOOR_FRAC] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `a:real^N->bool`; `u:real^N`] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ONCE_REWRITE_TAC[MEASURABLE_INNER_OUTER] THEN
    GEN_TAC THEN DISCH_TAC THEN
    EXISTS_TAC `interval(inv(2 pow n) % u:real^N,
                         inv(2 pow n) % (u + 1))` THEN
    EXISTS_TAC `interval[inv(2 pow n) % u:real^N,
                         inv(2 pow n) % (u + 1)]` THEN
    REWRITE_TAC[MEASURABLE_INTERVAL; MEASURE_INTERVAL] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `y:real^N` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT;
                 VEC_COMPONENT] THEN
    REAL_ARITH_TAC]);; *)

lemma gmeasurable_open: True .. (*
 "!s:real^N->bool. bounded s \<and> open s ==> gmeasurable s"
qed   REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `s \<subseteq> t ==> s = t DIFF (t DIFF s)`)) THEN
  MATCH_MP_TAC GMEASURABLE_DIFF THEN
  REWRITE_TAC[MEASURABLE_INTERVAL] THEN
  MATCH_MP_TAC GMEASURABLE_COMPACT THEN
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_DIFF; BOUNDED_INTERVAL] THEN
  MATCH_MP_TAC CLOSED_DIFF THEN ASM_REWRITE_TAC[CLOSED_INTERVAL]);; *)

lemma gmeasurable_closure: True .. (*
 "!s. bounded s ==> gmeasurable(closure s)"
qed   SIMP_TAC[MEASURABLE_COMPACT; COMPACT_EQ_BOUNDED_CLOSED; CLOSED_CLOSURE;
           BOUNDED_CLOSURE]);; *)

lemma gmeasurable_interior: True .. (*
 "!s. bounded s ==> gmeasurable(interior s)"
qed   SIMP_TAC[MEASURABLE_OPEN; OPEN_INTERIOR; BOUNDED_INTERIOR]);; *)

lemma gmeasurable_frontier: True .. (*
 "!s:real^N->bool. bounded s ==> gmeasurable(frontier s)"
qed   REPEAT STRIP_TAC THEN REWRITE_TAC[frontier] THEN
  MATCH_MP_TAC GMEASURABLE_DIFF THEN
  ASM_SIMP_TAC[MEASURABLE_CLOSURE; GMEASURABLE_INTERIOR] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
  REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET]);; *)

lemma measure_frontier: True .. (*
 "!s:real^N->bool.
        bounded s
        ==> measure(frontier s) = measure(closure s) - measure(interior s)"
qed   REPEAT STRIP_TAC THEN REWRITE_TAC[frontier] THEN
  MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN
  ASM_SIMP_TAC[MEASURABLE_CLOSURE; GMEASURABLE_INTERIOR] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
  REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET]);; *)

lemma gmeasurable_jordan: True .. (*
 "!s:real^N->bool. bounded s \<and> negligible(frontier s) ==> gmeasurable s"
qed   REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MEASURABLE_INNER_OUTER] THEN
  GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `interior(s):real^N->bool` THEN
  EXISTS_TAC `closure(s):real^N->bool` THEN
  ASM_SIMP_TAC[MEASURABLE_INTERIOR; GMEASURABLE_CLOSURE] THEN
  REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET] THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
  ASM_SIMP_TAC[GSYM MEASURE_FRONTIER; REAL_ABS_NUM; MEASURE_EQ_0]);; *)

lemma has_gmeasure_elementary: True .. (*
 "!d s. d division_of s ==> s has_gmeasure (sum d content)"
qed   REPEAT STRIP_TAC THEN REWRITE_TAC[has_gmeasure] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[LIFT_SUM] THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_DIVISION THEN
  ASM_REWRITE_TAC[o_THM] THEN REWRITE_TAC[GSYM has_gmeasure] THEN
  ASM_MESON_TAC[HAS_GMEASURE_INTERVAL; division_of]);; *)

lemma gmeasurable_elementary: True .. (*
 "!d s. d division_of s ==> gmeasurable s"
qed   REWRITE_TAC[measurable] THEN MESON_TAC[HAS_GMEASURE_ELEMENTARY]);; *)

lemma measure_elementary: True .. (*
 "!d s. d division_of s ==> gmeasure s = sum d content"
qed   MESON_TAC[HAS_GMEASURE_ELEMENTARY; MEASURE_UNIQUE]);; *)

lemma gmeasurable_inter_interval: True .. (*
 "!s a b:real^N. gmeasurable s ==> gmeasurable (s \<inter> {a..b})"
qed   SIMP_TAC[MEASURABLE_INTER; GMEASURABLE_INTERVAL]);; *)

(* ------------------------------------------------------------------------- *)
(* A nice lemma for negligibility proofs.                                    *)
(* ------------------------------------------------------------------------- *)

lemma STARLIKE_NEGLIGIBLE_BOUNDED_MEASURABLE: True .. (*
 "!s. gmeasurable s \<and> bounded s \<and>
       (!c x:real^N. 0 \<le> c \<and> x \<in> s \<and> (c % x) \<in> s ==> c = 1)
       ==> negligible s"
qed   REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(0 < measure(s:real^N->bool))`
   (fun th -> ASM_MESON_TAC[th; GMEASURABLE_MEASURE_POS_LT]) THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `(0:real^N) INSERT s`
      BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC) THEN
  ASM_SIMP_TAC[BOUNDED_INSERT; COMPACT_IMP_BOUNDED; NOT_EXISTS_THM] THEN
  X_GEN_TAC `a:real^N` THEN REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?N. EVEN N \<and> 0 < N \<and>
        measure(interval[--a:real^N,a])
         < (N * measure(s:real^N->bool)) / 4 pow dimindex (:N)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC
     `measure(interval[--a:real^N,a]) * 4 pow (dimindex(:N))` o
     MATCH_MP REAL_ARCH) THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    SIMP_TAC[GSYM REAL_LT_LDIV_EQ; ASSUME `0 < measure(s:real^N->bool)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `2 * (N DIV 2 + 1)` THEN REWRITE_TAC[EVEN_MULT; ARITH] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < a ==> a \<le> b ==> x < b`)) THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\<Union>(IMAGE (\<lambda>m. IMAGE (\<lambda>x:real^N. (m / N) % x) s)
                                (1..N))`;
                  `interval[--a:real^N,a]`] MEASURE_SUBSET) THEN
  MP_TAC(ISPECL [`measure:(real^N->bool)->real`;
                 `IMAGE (\<lambda>m. IMAGE (\<lambda>x:real^N. (m / N) % x) s) (1..N)`]
                HAS_GMEASURE_DISJOINT_UNIONS) THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM HAS_GMEASURE_MEASURE] THEN
    MATCH_MP_TAC GMEASURABLE_SCALING THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  ONCE_REWRITE_TAC[TAUT `(a \<and> b) \<and> ~c ==> d \<longleftrightarrow> a \<and> b \<and> ~d ==> c`] THEN
  SUBGOAL_THEN
   `!m n. m \<in> 1..N \<and> n \<in> 1..N \<and>
          ~(DISJOINT (IMAGE (\<lambda>x:real^N. m / N % x) s)
                     (IMAGE (\<lambda>x. n / N % x) s))
          ==> m = n`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N`
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N`
     (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN(MP_TAC o AP_TERM `(%) (N / m) :real^N->real^N`) THEN
    SUBGOAL_THEN `~(N = 0) \<and> ~(m = 0)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_NUMSEG])) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE (BINDER_CONV o BINDER_CONV)
     [GSYM CONTRAPOS_THM]) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_FIELD
     `~(x = 0) \<and> ~(y = 0) ==> x / y * y / x = 1`] THEN
    ASM_SIMP_TAC[REAL_FIELD
     `~(x = 0) \<and> ~(y = 0) ==> x / y * z / x = z / y`] THEN
    REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n / m`; `y:real^N`]) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_FIELD
     `~(y = 0) ==> (x / y = 1 \<longleftrightarrow> x = y)`] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; EQ_SYM_EQ];
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[measurable] THEN ASM_MESON_TAC[];
    REWRITE_TAC[MEASURABLE_INTERVAL];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`--a:real^N`; `a:real^N`] CONVEX_INTERVAL) THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[CONVEX_ALT] o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPECL [`0:real^N`; `x:real^N`; `n / N`]) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[REAL_LE_DIV; REAL_POS] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_NUMSEG]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `1 \<le> n \<and> n \<le> N ==> 0 < N \<and> n \<le> N`)) THEN
    SIMP_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_LT; REAL_LE_LDIV_EQ] THEN
    SIMP_TAC[REAL_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP MEASURE_UNIQUE) THEN
  ASM_SIMP_TAC[MEASURE_SCALING; REAL_NOT_LE] THEN
  FIRST_X_ASSUM(K ALL_TAC o SPEC `0`) THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC
   `sum (1..N) (measure o (\<lambda>m. IMAGE (\<lambda>x:real^N. m / N % x) s))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_IMAGE THEN REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SET_RULE `DISJOINT s s \<longleftrightarrow> s = {}`; IMAGE_EQ_EMPTY] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[REAL_LT_REFL; MEASURE_EMPTY]] THEN
  FIRST_X_ASSUM(K ALL_TAC o SPEC `0`) THEN
  ASM_SIMP_TAC[o_DEF; MEASURE_SCALING; SUM_RMUL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x < a ==> a \<le> b ==> x < b`)) THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = (a * c) * b`] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `M:num` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_MUL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ARITH `0 < 2 * x \<longleftrightarrow> 0 < x`]) THEN
  ASM_SIMP_TAC[REAL_FIELD `0 < y ==> x / (2 * y) * 4 = x * 2 / y`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(M..(2*M)) (\<lambda>i. (i * 2 / M) pow dimindex (:N))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; REAL_LE_DIV; REAL_POS] THEN
    REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG; SUBSET] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_OF_NUM_LT]) THEN
    ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(M..(2*M)) (\<lambda>i. 2)` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_CONST_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `(2 * M + 1) - M = M + 1`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `2 pow (dimindex(:N))` THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[DIMINDEX_GE_1] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  REWRITE_TAC[REAL_POS; ARITH; real_div; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `M:num \<le> n` THEN ARITH_TAC);; *)

lemma STARLIKE_NEGLIGIBLE_LEMMA: True .. (*
 "!s. compact s \<and>
       (!c x:real^N. 0 \<le> c \<and> x \<in> s \<and> (c % x) \<in> s ==> c = 1)
       ==> negligible s"
qed   REPEAT STRIP_TAC THEN
  MATCH_MP_TAC STARLIKE_NEGLIGIBLE_BOUNDED_MEASURABLE THEN
  ASM_MESON_TAC[MEASURABLE_COMPACT; COMPACT_IMP_BOUNDED]);; *)

lemma STARLIKE_NEGLIGIBLE: True .. (*
 "!s a. closed s \<and>
         (!c x:real^N. 0 \<le> c \<and> (a + x) \<in> s \<and> (a + c % x) \<in> s ==> c = 1)
         ==> negligible s"
qed   REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_TRANSLATION_REV THEN
  EXISTS_TAC `--a:real^N` THEN ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
  MATCH_MP_TAC STARLIKE_NEGLIGIBLE_LEMMA THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_INTER_COMPACT THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    ASM_SIMP_TAC[CLOSED_TRANSLATION];
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `x:real^N = --a + y \<longleftrightarrow> y = a + x`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN ASM MESON_TAC[]]);; *)

lemma STARLIKE_NEGLIGIBLE_STRONG: True .. (*
 "!s a. closed s \<and>
         (!c x:real^N. 0 \<le> c \<and> c < 1 \<and> (a + x) \<in> s
                       ==> ~((a + c % x) \<in> s))
         ==> negligible s"
qed   REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC STARLIKE_NEGLIGIBLE THEN
  EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `~(x < y) \<and> ~(y < x) ==> x = y`) THEN
  STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`inv c`; `c % x:real^N`]) THEN
  ASM_REWRITE_TAC[REAL_LE_INV_EQ; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ARITH `1 < c ==> ~(c = 0)`] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_1] THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_LT_01]);; *)

(* ------------------------------------------------------------------------- *)
(* In particular.                                                            *)
(* ------------------------------------------------------------------------- *)

lemma NEGLIGIBLE_HYPERPLANE: True .. (*
 "!a b. ~(a = 0 \<and> b = 0) ==> negligible {x:real^N | a dot x = b}"
qed   REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = 0` THEN
  ASM_SIMP_TAC[DOT_LZERO; SET_RULE `{x | F} = {}`; NEGLIGIBLE_EMPTY] THEN
  MATCH_MP_TAC STARLIKE_NEGLIGIBLE THEN
  SUBGOAL_THEN `?x:real^N. ~(a dot x = b)` MP_TAC THENL
   [MATCH_MP_TAC(MESON[] `!a:real^N. P a \/ P(--a) ==> ?x. P x`) THEN
    EXISTS_TAC `a:real^N` THEN REWRITE_TAC[DOT_RNEG] THEN
    MATCH_MP_TAC(REAL_ARITH `~(a = 0) ==> ~(a = b) \/ ~(--a = b)`) THEN
    ASM_REWRITE_TAC[DOT_EQ_0];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[CLOSED_HYPERPLANE; IN_ELIM_THM; DOT_RADD; DOT_RMUL] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `0 \<le> t \<and> ac + ay = b \<and> ac + t * ay = b
    ==> ((ay = 0 ==> ac = b) \<and> (t - 1) * ay = 0)`)) THEN
  ASM_SIMP_TAC[REAL_ENTIRE; REAL_SUB_0] THEN CONV_TAC TAUT);; *)

lemma NEGLIGIBLE_LOWDIM: True .. (*
 "!s:real^N->bool. dim(s) < dimindex(:N) ==> negligible s"
qed   GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LOWDIM_SUBSET_HYPERPLANE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `span(s):real^N->bool` THEN REWRITE_TAC[SPAN_INC] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x:real^N | a dot x = 0}` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_HYPERPLANE]);; *)

(* ------------------------------------------------------------------------- *)
(* Measurability of bounded convex sets.                                     *)
(* ------------------------------------------------------------------------- *)

lemma NEGLIGIBLE_CONVEX_FRONTIER: True .. (*
 "!s:real^N->bool. convex s ==> negligible(frontier s)"
qed   SUBGOAL_THEN
   `!s:real^N->bool. convex s \<and> (0) \<in> s ==> negligible(frontier s)`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[FRONTIER_EMPTY; NEGLIGIBLE_EMPTY] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (\<lambda>x:real^N. --a + x) s`) THEN
    ASM_SIMP_TAC[CONVEX_TRANSLATION; IN_IMAGE] THEN
    ASM_REWRITE_TAC[UNWIND_THM2;
                    VECTOR_ARITH `0:real^N = --a + x \<longleftrightarrow> x = a`] THEN
    REWRITE_TAC[FRONTIER_TRANSLATION; NEGLIGIBLE_TRANSLATION_EQ]] THEN
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `s:real^N->bool` DIM_SUBSET_UNIV) THEN
  REWRITE_TAC[ARITH_RULE `d:num \<le> e \<longleftrightarrow> d < e \/ d = e`] THEN STRIP_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `closure s:real^N->bool` THEN
    REWRITE_TAC[frontier; SUBSET_DIFF] THEN
    MATCH_MP_TAC NEGLIGIBLE_LOWDIM THEN ASM_REWRITE_TAC[DIM_CLOSURE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. a \<in> interior s` CHOOSE_TAC THENL
   [X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC
     (ISPEC `s:real^N->bool` BASIS_EXISTS) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPEC `b:real^N->bool` INTERIOR_SIMPLEX_NONEMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_REWRITE_TAC[INSERT_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC STARLIKE_NEGLIGIBLE_STRONG THEN
  EXISTS_TAC `a:real^N` THEN REWRITE_TAC[FRONTIER_CLOSED] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[frontier; IN_DIFF; DE_MORGAN_THM] THEN DISJ2_TAC THEN
  SIMP_TAC[VECTOR_ARITH
   `a + c % x:real^N = (a + x) - (1 - c) % ((a + x) - a)`] THEN
  MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
  RULE_ASSUM_TAC(REWRITE_RULE[frontier; IN_DIFF]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);; *)

lemma GMEASURABLE_CONVEX: True .. (*
 "!s:real^N->bool. convex s \<and> bounded s ==> gmeasurable s"
qed   REPEAT STRIP_TAC THEN MATCH_MP_TAC GMEASURABLE_JORDAN THEN
  ASM_SIMP_TAC[NEGLIGIBLE_CONVEX_FRONTIER]);; *)

(* ------------------------------------------------------------------------- *)
(* Various special cases.                                                    *)
(* ------------------------------------------------------------------------- *)

lemma NEGLIGIBLE_SPHERE: True .. (*
 "!a r. negligible {x:real^N | dist(a,x) = r}"
qed   REWRITE_TAC[GSYM FRONTIER_CBALL] THEN
  SIMP_TAC[NEGLIGIBLE_CONVEX_FRONTIER; CONVEX_CBALL]);; *)

lemma GMEASURABLE_BALL: True .. (*
 "!a r. gmeasurable(ball(a,r))"
qed   SIMP_TAC[MEASURABLE_OPEN; BOUNDED_BALL; OPEN_BALL]);; *)

lemma GMEASURABLE_CBALL: True .. (*
 "!a r. gmeasurable(cball(a,r))"
qed   SIMP_TAC[MEASURABLE_COMPACT; COMPACT_CBALL]);; *)

(* ------------------------------------------------------------------------- *)
(* Negligibility of image under non-injective linear map.                    *)
(* ------------------------------------------------------------------------- *)

lemma NEGLIGIBLE_LINEAR_SINGULAR_IMAGE: True .. (*
 "!f:real^N->real^N s.
        linear f \<and> ~(!x y. f(x) = f(y) ==> x = y)
        ==> negligible(IMAGE f s)"
qed   REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP LINEAR_SINGULAR_IMAGE_HYPERPLANE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x:real^N | a dot x = 0}` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_HYPERPLANE]);; *)

(* ------------------------------------------------------------------------- *)
(* Approximation of gmeasurable set by union of intervals.                    *)
(* ------------------------------------------------------------------------- *)

lemma COVERING_LEMMA: True .. (*
 "!a b:real^N s g.
        s \<subseteq> {a..b} \<and> ~({a<..<b} = {}) \<and> gauge g
        ==> ?d. COUNTABLE d \<and>
                (!k. k \<in> d ==> k \<subseteq> {a..b} \<and> ~(k = {}) \<and>
                                (\<exists>c d. k = {c..d})) \<and>
                (!k1 k2. k1 \<in> d \<and> k2 \<in> d \<and> ~(k1 = k2)
                         ==> interior k1 \<inter> interior k2 = {}) \<and>
                (!k. k \<in> d ==> ?x. x \<in> (s \<inter> k) \<and> k \<subseteq> g(x)) \<and>
                s \<subseteq> \<Union>d"
qed   REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. COUNTABLE d \<and>
        (!k. k \<in> d ==> k \<subseteq> {a..b} \<and> ~(k = {}) \<and>
                        (\<exists>c d:real^N. k = {c..d})) \<and>
        (!k1 k2. k1 \<in> d \<and> k2 \<in> d
                 ==> k1 \<subseteq> k2 \/ k2 \<subseteq> k1 \/
                     interior k1 \<inter> interior k2 = {}) \<and>
        (!x. x \<in> s ==> ?k. k \<in> d \<and> x \<in> k \<and> k \<subseteq> g(x)) \<and>
        (!k. k \<in> d ==> FINITE {l | l \<in> d \<and> k \<subseteq> l})`
  ASSUME_TAC THENL
   [EXISTS_TAC
     `IMAGE (\<lambda>(n,v).
             interval[(lambda i. a$i + (v$i) / 2 pow n *
                                       ((b:real^N)$i - (a:real^N)$i)):real^N,
                      (lambda i. a$i + ((v$i) + 1) / 2 pow n * (b$i - a$i))])
            {n,v | n \<in> (:num) \<and>
                   v \<in> {v:num^N | !i. 1 \<le> i \<and> i \<le> dimindex(:N)
                                       ==> v$i < 2 EXP n}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_IMAGE THEN
      MATCH_MP_TAC COUNTABLE_PRODUCT_DEPENDENT THEN
      REWRITE_TAC[NUM_COUNTABLE; IN_UNIV] THEN
      GEN_TAC THEN MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN
      MATCH_MP_TAC FINITE_CART THEN REWRITE_TAC[FINITE_NUMSEG_LT];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `v:num^N`] THEN
      REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN DISCH_TAC THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
      SIMP_TAC[INTERVAL_NE_EMPTY; SUBSET_INTERVAL; LAMBDA_BETA] THEN
      REWRITE_TAC[REAL_LE_LADD; REAL_LE_ADDR; REAL_ARITH
        `a + x * (b - a) \<le> b \<longleftrightarrow> 0 \<le> (1 - x) * (b - a)`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
      REPEAT STRIP_TAC THEN
      (MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LE_RMUL) THEN
      ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_DIV2_EQ; REAL_LT_POW2] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_POW2] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_POS; REAL_MUL_LID; REAL_LE_ADDR] THEN
      SIMP_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
      ASM_SIMP_TAC[ARITH_RULE `x + 1 \<le> y \<longleftrightarrow> x < y`; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[IMP_CONJ] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[IN_ELIM_PAIR_THM; IN_UNIV] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
      GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
      MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
       [REPEAT GEN_TAC THEN
        GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM] THEN
        REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN SET_TAC[];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`v:num^N`; `w:num^N`] THEN REPEAT DISCH_TAC THEN
      REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; SUBSET_INTERVAL] THEN
      SIMP_TAC[DISJOINT_INTERVAL; LAMBDA_BETA] THEN
      MATCH_MP_TAC(TAUT `p \/ q \/ r ==> (a ==> p) \/ (b ==> q) \/ r`) THEN
      ONCE_REWRITE_TAC[TAUT `a \<and> b \<and> c \<longleftrightarrow> ~(a \<and> b ==> ~c)`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
      ASM_SIMP_TAC[REAL_LE_LADD; REAL_LE_RMUL_EQ; REAL_SUB_LT; LAMBDA_BETA] THEN
      REWRITE_TAC[NOT_IMP; REAL_LE_LADD] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_POW2] THEN
      REWRITE_TAC[REAL_ARITH `~(x + 1 \<le> x)`] THEN DISJ2_TAC THEN
      MATCH_MP_TAC(MESON[]
       `(!i. ~P i ==> Q i) ==> (!i. Q i) \/ (\<exists>i. P i)`) THEN
      X_GEN_TAC `i:num` THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LE] THEN
      UNDISCH_TAC `m:num \<le> n` THEN REWRITE_TAC[LE_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_POW2; REAL_LT_DIV2_EQ] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_POW2;
                   REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
      SIMP_TAC[REAL_LT_INTEGERS; INTEGER_CLOSED] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN
        `?e. 0 < e \<and> !y. (!i. 1 \<le> i \<and> i \<le> dimindex(:N)
                                ==> abs((x:real^N)$i - (y:real^N)$i) \<le> e)
                           ==> y \<in> g(x)`
      STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I [gauge]) THEN
        STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `e / 2 / (dimindex(:N))` THEN
        ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1;
                     ARITH] THEN
        X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
        MATCH_MP_TAC(SET_RULE `!s. s \<subseteq> t \<and> x \<in> s ==> x \<in> t`) THEN
        EXISTS_TAC `ball(x:real^N,e)` THEN ASM_REWRITE_TAC[IN_BALL] THEN
        MATCH_MP_TAC(REAL_ARITH `0 < e \<and> x \<le> e / 2 ==> x < e`) THEN
        ASM_REWRITE_TAC[dist] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `sum(1..dimindex(:N)) (\<lambda>i. abs((x - y:real^N)$i))` THEN
        REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_BOUND_GEN THEN
        ASM_SIMP_TAC[IN_NUMSEG; FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT;
                     DIMINDEX_GE_1; VECTOR_SUB_COMPONENT; CARD_NUMSEG_1];
        ALL_TAC] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
      MP_TAC(SPECL [`1 / 2`; `e / norm(b - a:real^N)`]
        REAL_ARCH_POW_INV) THEN
      SUBGOAL_THEN `0 < norm(b - a:real^N)` ASSUME_TAC THENL
       [ASM_MESON_TAC[VECTOR_SUB_EQ; NORM_POS_LT; INTERVAL_SING]; ALL_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
      REWRITE_TAC[real_div; REAL_MUL_LID; REAL_POW_INV] THEN DISCH_TAC THEN
      SIMP_TAC[IN_ELIM_THM; IN_INTERVAL; SUBSET; LAMBDA_BETA] THEN
      MATCH_MP_TAC(MESON[]
       `(!x. Q x ==> R x) \<and> (\<exists>x. P x \<and> Q x) ==> ?x. P x \<and> Q x \<and> R x`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
        MAP_EVERY X_GEN_TAC [`w:num^N`; `y:real^N`] THEN
        REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
        DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
         `(a + n \<le> x \<and> x \<le> a + m) \<and>
          (a + n \<le> y \<and> y \<le> a + m) ==> abs(x - y) \<le> m - n`)) THEN
        MATCH_MP_TAC(REAL_ARITH
         `y * z \<le> e
          ==> a \<le> ((x + 1) * y) * z - ((x * y) * z) ==> a \<le> e`) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
        (REAL_ARITH `n < e * x ==> 0 \<le> e * (inv y - x) ==> n \<le> e / y`)) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_SIMP_TAC[REAL_SUB_LT] THEN
        MP_TAC(SPECL [`b - a:real^N`; `i:num`] COMPONENT_LE_NORM) THEN
        ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIV; AND_FORALL_THM] THEN
      REWRITE_TAC[TAUT `(a ==> c) \<and> (a ==> b) \<longleftrightarrow> a ==> b \<and> c`] THEN
      REWRITE_TAC[GSYM LAMBDA_SKOLEM] THEN X_GEN_TAC `i:num` THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^N) \<in> {a..b}` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN REWRITE_TAC[IN_INTERVAL] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN STRIP_TAC THEN
      DISJ_CASES_TAC(MATCH_MP (REAL_ARITH `x \<le> y ==> x = y \/ x < y`)
       (ASSUME `(x:real^N)$i \<le> (b:real^N)$i`))
      THENL
       [EXISTS_TAC `2 EXP n - 1` THEN
        SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_LT;
                 EXP_LT_0; LE_1; ARITH] THEN
        ASM_REWRITE_TAC[REAL_SUB_ADD; REAL_ARITH `a - 1 < a`] THEN
        MATCH_MP_TAC(REAL_ARITH
         `1 * (b - a) = x \<and> y \<le> x ==> a + y \<le> b \<and> b \<le> a + x`) THEN
        ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL; REAL_LT_IMP_NZ; REAL_LE_RMUL_EQ;
                     REAL_SUB_LT; REAL_LT_INV_EQ; REAL_LT_POW2] THEN
        SIMP_TAC[GSYM REAL_OF_NUM_POW; REAL_MUL_RINV; REAL_POW_EQ_0;
                 REAL_OF_NUM_EQ; ARITH_EQ] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPEC `2 pow n * ((x:real^N)$i - (a:real^N)$i) /
                              ((b:real^N)$i - (a:real^N)$i)` FLOOR_POS) THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[REAL_LE_MUL; REAL_LE_MUL; REAL_POW_LE; REAL_POS;
                      REAL_SUB_LE; REAL_LT_IMP_LE; REAL_LE_DIV];
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_POW] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      REWRITE_TAC[REAL_ARITH `a + b * c \<le> x \<and> x \<le> a + b' * c \<longleftrightarrow>
                              b * c \<le> x - a \<and> x - a \<le> b' * c`] THEN
      ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; GSYM REAL_LE_RDIV_EQ;
                   REAL_SUB_LT; GSYM real_div] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_POW2] THEN
      SIMP_TAC[FLOOR; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `((x:real^N)$i - (a:real^N)$i) /
                  ((b:real^N)$i - (a:real^N)$i) *
                  2 pow n` THEN
      REWRITE_TAC[FLOOR] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LT_POW2] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID; REAL_SUB_LT] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `v:num^N`] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     `IMAGE (\<lambda>(n,v).
            interval[(lambda i. a$i + (v$i) / 2 pow n *
                                      ((b:real^N)$i - (a:real^N)$i)):real^N,
                     (lambda i. a$i + ((v$i) + 1) / 2 pow n * (b$i - a$i))])
            {m,v | m \<in> 0..n \<and>
                   v \<in> {v:num^N | !i. 1 \<le> i \<and> i \<le> dimindex(:N)
                                       ==> v$i < 2 EXP m}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC FINITE_CART THEN REWRITE_TAC[FINITE_NUMSEG_LT];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `w:num^N`] THEN DISCH_TAC THEN
    DISCH_TAC THEN SIMP_TAC[IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY EXISTS_TAC [`m:num`; `w:num^N`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_NUMSEG; GSYM NOT_LT; LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_INTERVAL]) THEN
    SIMP_TAC[NOT_IMP; LAMBDA_BETA] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
    ASM_SIMP_TAC[REAL_LE_LADD; REAL_LE_RMUL_EQ; REAL_SUB_LT] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_POW2] THEN
    REWRITE_TAC[REAL_ARITH `x \<le> x + 1`] THEN
    DISCH_THEN(MP_TAC o SPEC `1`) THEN
    REWRITE_TAC[LE_REFL; DIMINDEX_GE_1] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `w / m \<le> v / n \<and> (v + 1) / n \<le> (w + 1) / m
      ==> inv n \<le> inv m`)) THEN
    REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_REWRITE_TAC[REAL_LT_POW2] THEN MATCH_MP_TAC REAL_POW_MONO_LT THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. COUNTABLE d \<and>
        (!k. k \<in> d ==> k \<subseteq> {a..b} \<and> ~(k = {}) \<and>
                        (\<exists>c d:real^N. k = {c..d})) \<and>
        (!k1 k2. k1 \<in> d \<and> k2 \<in> d
                 ==> k1 \<subseteq> k2 \/ k2 \<subseteq> k1 \/
                     interior k1 \<inter> interior k2 = {}) \<and>
        (!k. k \<in> d ==> (\<exists>x. x \<in> s \<inter> k \<and> k \<subseteq> g x)) \<and>
        (!k. k \<in> d ==> FINITE {l | l \<in> d \<and> k \<subseteq> l}) \<and>
        s \<subseteq> \<Union>d`
  MP_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC
     `{k:real^N->bool | k \<in> d \<and> ?x. x \<in> (s \<inter> k) \<and> k \<subseteq> g x}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_SUBSET THEN
      EXISTS_TAC `d:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      X_GEN_TAC `k:real^N->bool` THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{l:real^N->bool | l \<in> d \<and> k \<subseteq> l}` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `{k:real^N->bool | k \<in> d \<and> !k'. k' \<in> d \<and> ~(k = k')
                                     ==> ~(k \<subseteq> k')}` THEN
  ASM_SIMP_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC `d:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_UNIONS] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `x:real^N`] THEN DISCH_TAC THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  MP_TAC(ISPEC `\k l:real^N->bool. k \<in> d \<and> l \<in> d \<and> l \<subseteq> k \<and> ~(k = l)`
     WF_FINITE) THEN
  REWRITE_TAC[WF] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN X_GEN_TAC `l:real^N->bool` THEN
    ASM_CASES_TAC `(l:real^N->bool) \<in> d` THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; FINITE_RULES] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{m:real^N->bool | m \<in> d \<and> l \<subseteq> m}` THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\l:real^N->bool. l \<in> d \<and> x \<in> l`) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);; *)

lemma GMEASURABLE_OUTER_INTERVALS_BOUNDED: True .. (*
 "!s a b:real^N e.
        gmeasurable s \<and> s \<subseteq> {a..b} \<and> 0 < e
        ==> ?d. COUNTABLE d \<and>
                (!k. k \<in> d ==> k \<subseteq> {a..b} \<and> ~(k = {}) \<and>
                                (\<exists>c d. k = {c..d})) \<and>
                (!k1 k2. k1 \<in> d \<and> k2 \<in> d \<and> ~(k1 = k2)
                         ==> interior k1 \<inter> interior k2 = {}) \<and>
                s \<subseteq> \<Union>d \<and>
                gmeasurable (\<Union>d) \<and>
                gmeasure (\<Union>d) \<le> gmeasure s + e"
qed   lemma lemma = prove
   (`(!x y. (x,y) \<in> IMAGE (\<lambda>z. f z,g z) s ==> P x y) \<longleftrightarrow>
     (!z. z \<in> s ==> P (f z) (g z))"
qed   REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN MESON_TAC[]) in
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
   [ASM_REWRITE_TAC[SUBSET_EMPTY] THEN STRIP_TAC THEN
    EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; UNIONS_0; MEASURE_EMPTY; REAL_ADD_LID;
                    SUBSET_REFL; COUNTABLE_EMPTY; GMEASURABLE_EMPTY] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_CASES_TAC `interval(a:real^N,b) = {}` THENL
   [EXISTS_TAC `{interval[a:real^N,b]}` THEN
    REWRITE_TAC[UNIONS_1; COUNTABLE_SING] THEN
    ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT;
                    NOT_IN_EMPTY; SUBSET_REFL; GMEASURABLE_INTERVAL] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `measure(interval[a:real^N,b]) = 0 \<and> measure(s:real^N->bool) = 0`
     (fun th -> ASM_SIMP_TAC[th; REAL_LT_IMP_LE; REAL_ADD_LID]) THEN
    SUBGOAL_THEN
      `interval[a:real^N,b] has_gmeasure 0 \<and> (s:real^N->bool) has_gmeasure 0`
      (fun th -> MESON_TAC[th; MEASURE_UNIQUE]) THEN
    REWRITE_TAC[HAS_GMEASURE_0] THEN
    MATCH_MP_TAC(TAUT `a \<and> (a ==> b) ==> a \<and> b`) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[NEGLIGIBLE_INTERVAL];
      ASM_MESON_TAC[NEGLIGIBLE_SUBSET]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [measurable]) THEN
  DISCH_THEN(X_CHOOSE_TAC `m:real`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MEASURE_UNIQUE) THEN
  SUBGOAL_THEN
   `((\<lambda>x:real^N. if x \<in> s then 1 else 0) has_integral (lift m))
    {a..b}`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_GMEASURE]) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_EQ) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HAS_INTEGRAL_INTEGRABLE) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_integral]) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:real^N`; `b:real^N`; `s:real^N->bool`;
                `g:real^N->real^N->bool`] COVERING_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:(real^N->bool)->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(\<lambda>x. if x \<in> s then 1 else 0):real^N->real^1`;
                 `a:real^N`; `b:real^N`; `g:real^N->real^N->bool`;
                 `e:real`]
                HENSTOCK_LEMMA_PART1) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "*") THEN
  SUBGOAL_THEN
   `!k l:real^N->bool. k \<in> d \<and> l \<in> d \<and> ~(k = l)
                       ==> negligible(k \<inter> l)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:real^N->bool`; `l:real^N->bool`]) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN
     `?x y:real^N u v:real^N. k = {x..y} \<and> l = {u..v}`
    MP_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
    REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN DISCH_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `(interval[x:real^N,y] DIFF {x<..<y}) UNION
                (interval[u:real^N,v] DIFF {u<..<v}) UNION
                (interval (x,y) \<inter> interval (u,v))` THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    ASM_REWRITE_TAC[UNION_EMPTY] THEN
    SIMP_TAC[NEGLIGIBLE_UNION; NEGLIGIBLE_FRONTIER_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!D. FINITE D \<and> D \<subseteq> d
         ==> gmeasurable(\<Union>D :real^N->bool) \<and> measure(\<Union>D) \<le> m + e`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?t:(real^N->bool)->real^N. !k. k \<in> D ==> t(k) \<in> (s \<inter> k) \<and>
                                                k \<subseteq> (g(t k))`
    (CHOOSE_THEN (LABEL_TAC "+")) THENL
     [REWRITE_TAC[GSYM SKOLEM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC
     `IMAGE (\<lambda>k. (t:(real^N->bool)->real^N) k,k) D`) THEN
    ASM_SIMP_TAC[VSUM_IMAGE; PAIR_EQ] THEN REWRITE_TAC[o_DEF] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[tagged_partial_division_of; fine] THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[lemma; RIGHT_FORALL_IMP_THM; IMP_CONJ; PAIR_EQ] THEN
      ASM_SIMP_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET]];
      ALL_TAC] THEN
    USE_THEN "+" (MP_TAC o REWRITE_RULE[IN_INTER]) THEN
    SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_SIMP_TAC[VSUM_SUB] THEN
    SUBGOAL_THEN `D division_of (\<Union>D:real^N->bool)` ASSUME_TAC THENL
     [REWRITE_TAC[division_of] THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP GMEASURABLE_ELEMENTARY) THEN
    SUBGOAL_THEN `vsum D (\<lambda>k:real^N->bool. content k % 1) =
                  lift(measure(\<Union>D))`
    SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[GSYM _EQ] THEN
      ASM_SIMP_TAC[LIFT_; _VSUM; o_DEF; _CMUL; _VEC] THEN
      SIMP_TAC[REAL_MUL_RID; ETA_AX] THEN ASM_MESON_TAC[MEASURE_ELEMENTARY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `vsum D (\<lambda>k. integral k (\<lambda>x:real^N. if x \<in> s then 1 else 0)) =
      lift(sum D (\<lambda>k. measure(k \<inter> s)))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC VSUM_EQ THEN
      X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `measurable(k:real^N->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET; GMEASURABLE_INTERVAL]; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM INTEGRAL_MEASURE_UNIV; GMEASURABLE_INTER] THEN
      REWRITE_TAC[MESON[IN_INTER]
        `(if x \<in> k \<inter> s then a else b) =
         (if x \<in> k then if x \<in> s then a else b else b)`] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_RESTRICT_UNIV THEN
      ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN
      REWRITE_TAC[MESON[IN_INTER]
       `(if x \<in> k then if x \<in> s then a else b else b) =
        (if x \<in> k \<inter> s then a else b)`] THEN
      ASM_SIMP_TAC[GSYM GMEASURABLE_INTEGRABLE; GMEASURABLE_INTER];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
    MATCH_MP_TAC(REAL_ARITH `y \<le> m ==> abs(x - y) \<le> e ==> x \<le> m + e`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `measure(\<Union>D \<inter> s:real^N->bool)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "m" THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC GMEASURABLE_INTER THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[INTER_UNIONS] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG THEN
    ASM_SIMP_TAC[FINITE_RESTRICT] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET; GMEASURABLE_INTERVAL; GMEASURABLE_INTER];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `l:real^N->bool`] THEN
    STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `k \<inter> l:real^N->bool` THEN ASM_SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `FINITE(d:(real^N->bool)->bool)` THENL
   [ASM_MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  MP_TAC(ISPEC `d:(real^N->bool)->bool` COUNTABLE_AS_INJECTIVE_IMAGE) THEN
  ASM_REWRITE_TAC[INFINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->real^N->bool`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:num->real^N->bool`; `m + e:real`]
    HAS_GMEASURE_COUNTABLE_NEGLIGIBLE_UNIONS) THEN
  MATCH_MP_TAC(TAUT `a \<and> (a \<and> b ==> c) ==> (a ==> b) ==> c`) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM;
                              FORALL_IN_IMAGE; IN_UNIV]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MEASURABLE_INTERVAL; GMEASURABLE_INTER];
    ASM_MESON_TAC[];
    X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (s:num->real^N->bool) (0..n)`) THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMAGE_SUBSET; SUBSET_UNIV] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x \<le> e ==> y \<le> e`) THEN
    MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS_IMAGE THEN
    ASM_MESON_TAC[FINITE_NUMSEG; GMEASURABLE_INTERVAL];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT2 LIFT_)] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_COMPONENT_UBOUND) THEN
  EXISTS_TAC
   `\n. vsum(from 0 \<inter> (0..n)) (\<lambda>n. lift(measure(s n:real^N->bool)))` THEN
  ASM_REWRITE_TAC[GSYM sums; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  REWRITE_TAC[DIMINDEX_1; ARITH; EVENTUALLY_SEQUENTIALLY] THEN
  SIMP_TAC[VSUM_COMPONENT; ARITH; DIMINDEX_1] THEN
  ASM_REWRITE_TAC[GSYM ; LIFT_; FROM_INTER_NUMSEG]);; *)

(* ------------------------------------------------------------------------- *)
(* Hence for linear transformation, suffices to check compact intervals.     *)
(* ------------------------------------------------------------------------- *)

lemma GMEASURABLE_LINEAR_IMAGE_INTERVAL: True .. (*
 "!f a b. linear f ==> gmeasurable(IMAGE f {a..b})"
qed   REPEAT STRIP_TAC THEN MATCH_MP_TAC GMEASURABLE_CONVEX THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_LINEAR_IMAGE THEN
    ASM_MESON_TAC[CONVEX_INTERVAL];
    MATCH_MP_TAC BOUNDED_LINEAR_IMAGE THEN
    ASM_MESON_TAC[BOUNDED_INTERVAL]]);; *)

lemma HAS_GMEASURE_LINEAR_SUFFICIENT: True .. (*
 "!f:real^N->real^N m.
        linear f \<and>
        (!a b. IMAGE f {a..b} has_gmeasure
               (m * measure{a..b}))
        ==> !s. gmeasurable s ==> (IMAGE f s) has_gmeasure (m * gmeasure s)"
qed   REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `m < 0 \/ 0 \<le> m`) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`0:real^N`; `1:real^N`]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_GMEASURE_POS_LE) THEN
    MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN
    MATCH_MP_TAC(REAL_ARITH `0 < --m * x ==> ~(0 \<le> m * x)`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_NEG_GT0] THEN
    REWRITE_TAC[MEASURE_INTERVAL] THEN MATCH_MP_TAC CONTENT_POS_LT THEN
    SIMP_TAC[VEC_COMPONENT; REAL_LT_01];
    ALL_TAC] THEN
  ASM_CASES_TAC `!x y. (f:real^N->real^N) x = f y ==> x = y` THENL
   [ALL_TAC;
    SUBGOAL_THEN `!s. negligible(IMAGE (f:real^N->real^N) s)` ASSUME_TAC THENL
     [ASM_MESON_TAC[NEGLIGIBLE_LINEAR_SINGULAR_IMAGE]; ALL_TAC] THEN
    SUBGOAL_THEN `m * measure(interval[0:real^N,1]) = 0` MP_TAC THENL
     [MATCH_MP_TAC(ISPEC `IMAGE (f:real^N->real^N) {0..1}`
        HAS_GMEASURE_UNIQUE) THEN
      ASM_REWRITE_TAC[HAS_GMEASURE_0];
      REWRITE_TAC[REAL_ENTIRE; MEASURE_INTERVAL] THEN
      MATCH_MP_TAC(TAUT `~b \<and> (a ==> c) ==> a \/ b ==> c`) THEN CONJ_TAC THENL
       [SIMP_TAC[CONTENT_EQ_0_INTERIOR; INTERIOR_CLOSED_INTERVAL;
                 INTERVAL_NE_EMPTY; VEC_COMPONENT; REAL_LT_01];
        ASM_SIMP_TAC[REAL_MUL_LZERO; HAS_GMEASURE_0]]]] THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_INJECTIVE_ISOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN `!x y. (f:real^N->real^N) x = f y ==> x = y` (K ALL_TAC) THEN
  SUBGOAL_THEN
   `!s. bounded s \<and> gmeasurable s
        ==> (IMAGE (f:real^N->real^N) s) has_gmeasure (m * gmeasure s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!d. COUNTABLE d \<and>
          (!k. k \<in> d ==> k \<subseteq> {a..b} \<and> ~(k = {}) \<and>
                          (\<exists>c d. k = {c..d})) \<and>
          (!k1 k2. k1 \<in> d \<and> k2 \<in> d \<and> ~(k1 = k2)
                   ==> interior k1 \<inter> interior k2 = {})
          ==> IMAGE (f:real^N->real^N) (\<Union>d) has_gmeasure
                    (m * measure(\<Union>d))`
    ASSUME_TAC THENL
     [REWRITE_TAC[IMAGE_UNIONS] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `!g:real^N->real^N.
          linear g
          ==> !k l. k \<in> d \<and> l \<in> d \<and> ~(k = l)
                    ==> negligible((IMAGE g k) \<inter> (IMAGE g l))`
      MP_TAC THENL
       [REPEAT STRIP_TAC THEN
        ASM_CASES_TAC `!x y. (g:real^N->real^N) x = g y ==> x = y` THENL
         [ALL_TAC;
          ASM_MESON_TAC[NEGLIGIBLE_LINEAR_SINGULAR_IMAGE;
                        NEGLIGIBLE_INTER]] THEN
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `frontier(IMAGE (g:real^N->real^N) k \<inter> IMAGE g l) UNION
                    interior(IMAGE g k \<inter> IMAGE g l)` THEN
        CONJ_TAC THENL
         [ALL_TAC;
          REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
           `s \<subseteq> t ==> s \<subseteq> (t DIFF u) \<union> u`) THEN
          REWRITE_TAC[CLOSURE_SUBSET]] THEN
        MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC THENL
         [MATCH_MP_TAC NEGLIGIBLE_CONVEX_FRONTIER THEN
          MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC THEN
          MATCH_MP_TAC CONVEX_LINEAR_IMAGE THEN ASM_MESON_TAC[CONVEX_INTERVAL];
          ALL_TAC] THEN
        REWRITE_TAC[INTERIOR_INTER] THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `IMAGE (g:real^N->real^N) (interior k) INTER
                    IMAGE g (interior l)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
          EXISTS_TAC
           `IMAGE (g:real^N->real^N) (interior k \<inter> interior l)` THEN
          CONJ_TAC THENL
           [ASM_SIMP_TAC[IMAGE_CLAUSES; NEGLIGIBLE_EMPTY]; SET_TAC[]];
          MATCH_MP_TAC(SET_RULE
           `s \<subseteq> u \<and> t \<subseteq> v ==> (s \<inter> t) \<subseteq> (u \<inter> v)`) THEN
          CONJ_TAC THEN MATCH_MP_TAC INTERIOR_IMAGE_SUBSET THEN
          ASM_MESON_TAC[LINEAR_CONTINUOUS_AT]];
        ALL_TAC] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `f:real^N->real^N` th) THEN
          MP_TAC(SPEC `\x:real^N. x` th)) THEN
      ASM_REWRITE_TAC[LINEAR_ID; SET_RULE `IMAGE (\<lambda>x. x) s = s`] THEN
      REPEAT STRIP_TAC THEN ASM_CASES_TAC `FINITE(d:(real^N->bool)->bool)` THENL
       [MP_TAC(ISPECL [`IMAGE (f:real^N->real^N)`; `d:(real^N->bool)->bool`]
                  HAS_GMEASURE_NEGLIGIBLE_UNIONS_IMAGE) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[measurable]; ALL_TAC] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `sum d (\<lambda>k:real^N->bool. m * gmeasure k)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[MEASURE_UNIQUE]; ALL_TAC] THEN
        REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS THEN
        ASM_REWRITE_TAC[GSYM HAS_GMEASURE_MEASURE] THEN
        ASM_MESON_TAC[MEASURABLE_INTERVAL];
        ALL_TAC] THEN
      MP_TAC(ISPEC `d:(real^N->bool)->bool` COUNTABLE_AS_INJECTIVE_IMAGE) THEN
      ASM_REWRITE_TAC[INFINITE] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:num->real^N->bool`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      MP_TAC(ISPEC `s:num->real^N->bool`
        HAS_GMEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED) THEN
      MP_TAC(ISPEC `\n:num. IMAGE (f:real^N->real^N) (s n)`
        HAS_GMEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM;
                                  FORALL_IN_IMAGE; IN_UNIV]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]) THEN
      ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[MEASURABLE_LINEAR_IMAGE_INTERVAL];
          ASM_MESON_TAC[];
          ONCE_REWRITE_TAC[GSYM o_DEF] THEN
          REWRITE_TAC[GSYM IMAGE_UNIONS; IMAGE_o] THEN
          MATCH_MP_TAC BOUNDED_LINEAR_IMAGE THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC BOUNDED_SUBSET THEN REWRITE_TAC[UNIONS_SUBSET] THEN
          EXISTS_TAC `interval[a:real^N,b]` THEN
          REWRITE_TAC[BOUNDED_INTERVAL] THEN ASM SET_TAC[]];
        ALL_TAC] THEN
      STRIP_TAC THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[MEASURABLE_INTERVAL];
          ASM_MESON_TAC[];
          MATCH_MP_TAC BOUNDED_SUBSET THEN REWRITE_TAC[UNIONS_SUBSET] THEN
          EXISTS_TAC `interval[a:real^N,b]` THEN
          REWRITE_TAC[BOUNDED_INTERVAL] THEN ASM SET_TAC[]];
        ALL_TAC] THEN
      STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      SUBGOAL_THEN `m * gmeasure (\<Union>(IMAGE s (:num)):real^N->bool) =
             measure(\<Union>(IMAGE (\<lambda>x. IMAGE f (s x)) (:num)):real^N->bool)`
       (fun th -> ASM_REWRITE_TAC[GSYM HAS_GMEASURE_MEASURE; th]) THEN
      ONCE_REWRITE_TAC[GSYM LIFT_EQ] THEN
      MATCH_MP_TAC SERIES_UNIQUE THEN
      EXISTS_TAC `\n:num. lift(measure(IMAGE (f:real^N->real^N) (s n)))` THEN
      EXISTS_TAC `from 0` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUMS_EQ THEN
      EXISTS_TAC `\n:num. m % lift(measure(s n:real^N->bool))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN
        ASM_MESON_TAC[MEASURE_UNIQUE];
        REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SERIES_CMUL THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[HAS_GMEASURE_INNER_OUTER_LE] THEN CONJ_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`{a..b} DIFF s:real^N->bool`; `a:real^N`;
       `b:real^N`; `e / (1 + abs m)`] GMEASURABLE_OUTER_INTERVALS_BOUNDED) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[MEASURABLE_DIFF; GMEASURABLE_INTERVAL] THEN
        ASM_SIMP_TAC[REAL_ARITH `0 < 1 + abs x`; REAL_LT_DIV] THEN SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE f {a..b} DIFF
                  IMAGE (f:real^N->real^N) (\<Union>d)` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `d:(real^N->bool)->bool`) THEN
      ASM_SIMP_TAC[IMAGE_SUBSET] THEN DISCH_TAC THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MEASURABLE_DIFF; gmeasurable]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `measure(IMAGE f {a..b}) -
                  measure(IMAGE (f:real^N->real^N) (\<Union>d))` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN
        REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[measurable]; ALL_TAC]) THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_SIMP_TAC[UNIONS_SUBSET]] THEN
      FIRST_ASSUM(ASSUME_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
      REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP MEASURE_UNIQUE)) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `m * measure(s:real^N->bool) - m * e / (1 + abs m)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_ARITH `a - x \<le> a - y \<longleftrightarrow> y \<le> x`] THEN
        REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
        REWRITE_TAC[GSYM real_div] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `0 < 1 + abs x`] THEN
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
        `d \<le> a + e ==> a = i - s ==> s - e \<le> i - d`)) THEN
      MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN
      ASM_REWRITE_TAC[MEASURABLE_INTERVAL];
      MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`; `b:real^N`;
                `e / (1 + abs m)`] GMEASURABLE_OUTER_INTERVALS_BOUNDED) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `0 < 1 + abs x`] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE (f:real^N->real^N) (\<Union>d)` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `d:(real^N->bool)->bool`) THEN
      ASM_SIMP_TAC[IMAGE_SUBSET] THEN
      SIMP_TAC[HAS_GMEASURE_MEASURABLE_MEASURE] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `m * measure(s:real^N->bool) + m * e / (1 + abs m)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ASM_SIMP_TAC[REAL_LE_LMUL];
        REWRITE_TAC[REAL_LE_LADD] THEN
        REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
        REWRITE_TAC[GSYM real_div] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `0 < 1 + abs x`] THEN
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HAS_GMEASURE_LIMIT] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_GMEASURE_MEASURE]) THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_GMEASURE_LIMIT] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (1 + abs m)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `0 < 1 + abs x`] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))) THEN
  MP_TAC(ISPEC `ball(0:real^N,B)` BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[BOUNDED_BALL; LEFT_IMP_EXISTS_THM] THEN
  REMOVE_THEN "*" MP_TAC THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `c:real^N` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `d:real^N` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`interval[c:real^N,d]`; `0:real^N`]
    BOUNDED_SUBSET_BALL) THEN
  REWRITE_TAC[BOUNDED_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_BOUNDED_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN

  EXISTS_TAC `D * C` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `s \<inter> (IMAGE (h:real^N->real^N) {a..b})`) THEN
  SUBGOAL_THEN
   `IMAGE (f:real^N->real^N) (s \<inter> IMAGE h (interval [a,b])) =
    (IMAGE f s) \<inter> {a..b}`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[BOUNDED_INTER; BOUNDED_LINEAR_IMAGE; BOUNDED_INTERVAL] THEN
    ASM_SIMP_TAC[MEASURABLE_INTER; GMEASURABLE_LINEAR_IMAGE_INTERVAL];
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC
   `m * measure(s \<inter> (IMAGE (h:real^N->real^N) {a..b}))` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `m * e / (1 + abs m)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `0 < 1 + abs x`] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN REAL_ARITH_TAC] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [real_abs] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `abs(z - m) < e ==> z \<le> w \<and> w \<le> m ==> abs(w - m) \<le> e`)) THEN
  SUBST1_TAC(SYM(MATCH_MP MEASURE_UNIQUE
   (ASSUME `s \<inter> interval [c:real^N,d] has_gmeasure z`))) THEN
  CONJ_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
  ASM_SIMP_TAC[MEASURABLE_INTER; GMEASURABLE_LINEAR_IMAGE_INTERVAL;
               GMEASURABLE_INTERVAL; INTER_SUBSET] THEN
  MATCH_MP_TAC(SET_RULE
   `!v. t \<subseteq> v \<and> v \<subseteq> u ==> s \<inter> t \<subseteq> s \<inter> u`) THEN
  EXISTS_TAC `ball(0:real^N,D)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE
   `!f. (!x. h(f x) = x) \<and> IMAGE f s \<subseteq> t ==> s \<subseteq> IMAGE h t`) THEN
  EXISTS_TAC `f:real^N->real^N` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(0:real^N,D * C)` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `C * norm(x:real^N)` THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ]);; *)

(* ------------------------------------------------------------------------- *)
(* Some inductions by expressing mapping in terms of elementary matrices.    *)
(* ------------------------------------------------------------------------- *)

lemma INDUCT_MATRIX_ROW_OPERATIONS: True .. (*
 "!P:real^N^N->bool.
        (!A i. 1 \<le> i \<and> i \<le> dimindex(:N) \<and> row i A = 0 ==> P A) \<and>
        (!A. (!i j. 1 \<le> i \<and> i \<le> dimindex(:N) \<and>
                    1 \<le> j \<and> j \<le> dimindex(:N) \<and> ~(i = j)
                    ==> A$i$j = 0) ==> P A) \<and>
        (!A m n. P A \<and> 1 \<le> m \<and> m \<le> dimindex(:N) \<and>
                 1 \<le> n \<and> n \<le> dimindex(:N) \<and> ~(m = n)
                 ==> P(lambda i j. A$i$(swap(m,n) j))) \<and>
        (!A m n c. P A \<and> 1 \<le> m \<and> m \<le> dimindex(:N) \<and>
                   1 \<le> n \<and> n \<le> dimindex(:N) \<and> ~(m = n)
                   ==> P(lambda i. if i = m then row m A + c % row n A
                                   else row i A))
        ==> !A. P A"
qed   GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "zero_row") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "diagonal") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "swap_cols") (LABEL_TAC "row_op")) THEN
  SUBGOAL_THEN
   `!k A:real^N^N.
        (!i j. 1 \<le> i \<and> i \<le> dimindex(:N) \<and>
               k \<le> j \<and> j \<le> dimindex(:N) \<and> ~(i = j)
               ==> A$i$j = 0)
        ==> P A`
   (fun th -> GEN_TAC THEN MATCH_MP_TAC th THEN
              EXISTS_TAC `dimindex(:N) + 1` THEN ARITH_TAC) THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "diagonal" MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_THEN(LABEL_TAC "ind_hyp") THEN
  DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC (ARITH_RULE `k = 0 \/ 1 \<le> k`) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  ASM_CASES_TAC `k \<le> dimindex(:N)` THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN REMOVE_THEN "ind_hyp" MATCH_MP_TAC THEN
    ASM_ARITH_TAC] THEN
  SUBGOAL_THEN
   `!A:real^N^N.
        ~(A$k$k = 0) \<and>
        (!i j. 1 \<le> i \<and> i \<le> dimindex (:N) \<and>
               SUC k \<le> j \<and> j \<le> dimindex (:N) \<and> ~(i = j)
               ==> A$i$j = 0)
        ==> P A`
  (LABEL_TAC "nonzero_hyp") THENL
   [ALL_TAC;
    X_GEN_TAC `A:real^N^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `row k (A:real^N^N) = 0` THENL
     [REMOVE_THEN "zero_row" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
    SIMP_TAC[VEC_COMPONENT; row; LAMBDA_BETA] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `l:num = k` THENL
     [REMOVE_THEN "nonzero_hyp" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "swap_cols" (MP_TAC o SPECL
     [`(lambda i j. (A:real^N^N)$i$swap(k,l) j):real^N^N`;
      `k:num`; `l:num`]) THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[swap] THEN
      REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA])] THEN
    REMOVE_THEN "nonzero_hyp" MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `SUC k \<le> i \<longleftrightarrow> 1 \<le> i \<and> SUC k \<le> i`] THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    ASM_REWRITE_TAC[swap] THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    STRIP_TAC THEN SUBGOAL_THEN `l:num \<le> k` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `l:num`]) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC] THEN
   SUBGOAL_THEN
   `!l A:real^N^N.
        ~(A$k$k = 0) \<and>
        (!i j. 1 \<le> i \<and> i \<le> dimindex (:N) \<and>
               SUC k \<le> j \<and> j \<le> dimindex (:N) \<and> ~(i = j)
               ==> A$i$j = 0) \<and>
        (!i. l \<le> i \<and> i \<le> dimindex(:N) \<and> ~(i = k) ==> A$i$k = 0)
        ==> P A`
   MP_TAC THENL
    [ALL_TAC;
     DISCH_THEN(MP_TAC o SPEC `dimindex(:N) + 1`) THEN
     REWRITE_TAC[CONJ_ASSOC; ARITH_RULE `~(n + 1 \<le> i \<and> i \<le> n)`]] THEN
   MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
    [GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
     DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "main") (LABEL_TAC "aux")) THEN
     USE_THEN "ind_hyp" MATCH_MP_TAC THEN
     MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
     ASM_CASES_TAC `j:num = k` THENL
      [ASM_REWRITE_TAC[] THEN USE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC;
       REMOVE_THEN "main" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `l:num` THEN DISCH_THEN(LABEL_TAC "inner_hyp") THEN
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "main") (LABEL_TAC "aux")) THEN
  ASM_CASES_TAC `l:num = k` THENL
   [REMOVE_THEN "inner_hyp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REMOVE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISJ_CASES_TAC(ARITH_RULE `l = 0 \/ 1 \<le> l`) THENL
   [REMOVE_THEN "ind_hyp" MATCH_MP_TAC THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `j:num = k` THENL
     [ASM_REWRITE_TAC[] THEN REMOVE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REMOVE_THEN "main" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `l \<le> dimindex(:N)` THENL
   [ALL_TAC;
    REMOVE_THEN "inner_hyp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC] THEN
  REMOVE_THEN "inner_hyp" (MP_TAC o SPECL
   [`(lambda i. if i = l then row l (A:real^N^N) + --(A$l$k/A$k$k) % row k A
                else row i A):real^N^N`]) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `!i. l \<le> i ==> 1 \<le> i` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `SUC k \<le> j \<longleftrightarrow> 1 \<le> j \<and> SUC k \<le> j`] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; row; COND_COMPONENT;
                 VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(y = 0) ==> x + --(x / y) * y = 0`] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i:num = l` THEN ASM_REWRITE_TAC[] THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_RING `x = 0 \<and> y = 0 ==> x + z * y = 0`) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN REMOVE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN REMOVE_THEN "row_op" (MP_TAC o SPECL
   [`(lambda i. if i = l then row l A + --(A$l$k / A$k$k) % row k A
                else row i (A:real^N^N)):real^N^N`;
    `l:num`; `k:num`; `(A:real^N^N)$l$k / A$k$k`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT; row; COND_COMPONENT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);; *)

lemma INDUCT_MATRIX_ELEMENTARY: True .. (*
 "!P:real^N^N->bool.
        (!A B. P A \<and> P B ==> P(A ** B)) \<and>
        (!A i. 1 \<le> i \<and> i \<le> dimindex(:N) \<and> row i A = 0 ==> P A) \<and>
        (!A. (!i j. 1 \<le> i \<and> i \<le> dimindex(:N) \<and>
                    1 \<le> j \<and> j \<le> dimindex(:N) \<and> ~(i = j)
                    ==> A$i$j = 0) ==> P A) \<and>
        (!m n. 1 \<le> m \<and> m \<le> dimindex(:N) \<and>
               1 \<le> n \<and> n \<le> dimindex(:N) \<and> ~(m = n)
               ==> P(lambda i j. (mat 1:real^N^N)$i$(swap(m,n) j))) \<and>
        (!m n c. 1 \<le> m \<and> m \<le> dimindex(:N) \<and>
                 1 \<le> n \<and> n \<le> dimindex(:N) \<and> ~(m = n)
                 ==> P(lambda i j. if i = m \<and> j = n then c
                                   else if i = j then 1 else 0))
        ==> !A. P A"
qed   GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th ->
    MATCH_MP_TAC INDUCT_MATRIX_ROW_OPERATIONS THEN MP_TAC th) THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `A:real^N^N` THEN MP_TAC th) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(P:real^N^N->bool) A` THENL
   [REWRITE_TAC[GSYM IMP_CONJ]; REWRITE_TAC[GSYM IMP_CONJ_ALT]] THEN
  DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN REWRITE_TAC[CART_EQ] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; matrix_mul; row] THENL
   [ASM_SIMP_TAC[mat; IN_DIMINDEX_SWAP; LAMBDA_BETA] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[SUM_DELTA; REAL_MUL_RZERO; REAL_MUL_RID] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[swap; IN_NUMSEG]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[SUM_DELTA; LAMBDA_BETA; IN_NUMSEG; REAL_MUL_LID]] THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; LAMBDA_BETA] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `sum {m,n} (\<lambda>k. (if k = n then c else if m = k then 1 else 0) *
                    (A:real^N^N)$k$j)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN
    ASM_SIMP_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM;
                 IN_NUMSEG; REAL_MUL_LZERO] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[SUM_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC]);; *)

lemma INDUCT_MATRIX_ELEMENTARY_ALT: True .. (*
 "!P:real^N^N->bool.
        (!A B. P A \<and> P B ==> P(A ** B)) \<and>
        (!A i. 1 \<le> i \<and> i \<le> dimindex(:N) \<and> row i A = 0 ==> P A) \<and>
        (!A. (!i j. 1 \<le> i \<and> i \<le> dimindex(:N) \<and>
                    1 \<le> j \<and> j \<le> dimindex(:N) \<and> ~(i = j)
                    ==> A$i$j = 0) ==> P A) \<and>
        (!m n. 1 \<le> m \<and> m \<le> dimindex(:N) \<and>
               1 \<le> n \<and> n \<le> dimindex(:N) \<and> ~(m = n)
               ==> P(lambda i j. (mat 1:real^N^N)$i$(swap(m,n) j))) \<and>
        (!m n. 1 \<le> m \<and> m \<le> dimindex(:N) \<and>
               1 \<le> n \<and> n \<le> dimindex(:N) \<and> ~(m = n)
               ==> P(lambda i j. if i = m \<and> j = n \/ i = j then 1 else 0))
        ==> !A. P A"
qed   GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC INDUCT_MATRIX_ELEMENTARY THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `c = 0` THENL
   [FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`]) THEN
    ASM_SIMP_TAC[LAMBDA_BETA; COND_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(lambda i j. if i = m \<and> j = n then c else if i = j then 1 else 0) =
  ((lambda i j. if i = j then if j = n then inv c else 1 else 0):real^N^N) **
    ((lambda i j. if i = m \<and> j = n \/ i = j then 1 else 0):real^N^N) **
    ((lambda i j. if i = j then if j = n then c else 1 else 0):real^N^N)`
  SUBST1_TAC THENL
   [ALL_TAC;
    REPEAT(MATCH_MP_TAC(ASSUME `!A B:real^N^N. P A \<and> P B ==> P(A ** B)`) THEN
           CONJ_TAC) THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`]) THEN
    ASM_SIMP_TAC[LAMBDA_BETA]] THEN
  SIMP_TAC[CART_EQ; matrix_mul; LAMBDA_BETA] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG; REAL_ARITH
       `(if p then 1 else 0) * (if q then c else 0) =
        if q then if p then c else 0 else 0`] THEN
  REWRITE_TAC[REAL_ARITH
   `(if p then x else 0) * y = (if p then x * y else 0)`] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG] THEN
  ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `j:num = n` THEN ASM_REWRITE_TAC[REAL_MUL_LID; EQ_SYM_EQ] THEN
  ASM_CASES_TAC `i:num = n` THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_LID; REAL_MUL_RZERO]);; *)

(* ------------------------------------------------------------------------- *)
(* The same thing in mapping form (might have been easier all along).        *)
(* ------------------------------------------------------------------------- *)

lemma INDUCT_LINEAR_ELEMENTARY: True .. (*
 "!P. (!f g. linear f \<and> linear g \<and> P f \<and> P g ==> P(f o g)) \<and>
       (!f i. linear f \<and> 1 \<le> i \<and> i \<le> dimindex(:N) \<and> (!x. (f x)$i = 0)
              ==> P f) \<and>
       (!c. P(\<lambda>x. lambda i. c i * x$i)) \<and>
       (!m n. 1 \<le> m \<and> m \<le> dimindex(:N) \<and>
              1 \<le> n \<and> n \<le> dimindex(:N) \<and> ~(m = n)
              ==> P(\<lambda>x. lambda i. x$swap(m,n) i)) \<and>
       (!m n. 1 \<le> m \<and> m \<le> dimindex(:N) \<and>
              1 \<le> n \<and> n \<le> dimindex(:N) \<and> ~(m = n)
              ==> P(\<lambda>x. lambda i. if i = m then x$m + x$n else x$i))
       ==> !f:real^N->real^N. linear f ==> P f"
qed   GEN_TAC THEN
  MP_TAC(ISPEC `\A:real^N^N. P(\<lambda>x:real^N. A ** x):bool`
    INDUCT_MATRIX_ELEMENTARY_ALT) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN X_GEN_TAC `f:real^N->real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `matrix(f:real^N->real^N)`) THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN REWRITE_TAC[ETA_AX]] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`A:real^N^N`; `B:real^N^N`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`\x:real^N. (A:real^N^N) ** x`; `\x:real^N. (B:real^N^N) ** x`]) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; o_DEF] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`A:real^N^N`; `m:num`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`\x:real^N. (A:real^N^N) ** x`; `m:num`]) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `row m (A:real^N^N) = 0` THEN
    ASM_SIMP_TAC[CART_EQ; row; LAMBDA_BETA; VEC_COMPONENT; matrix_vector_mul;
                 REAL_MUL_LZERO; SUM_0];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `A:real^N^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\i. (A:real^N^N)$i$i`) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CART_EQ; matrix_vector_mul; FUN_EQ_THM; LAMBDA_BETA] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `i:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `sum(1..dimindex(:N)) (\<lambda>j. if j = i then (A:real^N^N)$i$j * (x:real^N)$j
                                else 0)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `m:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[CART_EQ; matrix_vector_mul; FUN_EQ_THM; LAMBDA_BETA;
               mat; IN_DIMINDEX_SWAP]
  THENL
   [ONCE_REWRITE_TAC[SWAP_GALOIS] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
    ONCE_REWRITE_TAC[COND_RATOR] THEN
    SIMP_TAC[SUM_DELTA; REAL_MUL_LID; REAL_MUL_LZERO; IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[swap] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^N`; `i:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[SUM_DELTA; REAL_MUL_LZERO; REAL_MUL_LID; IN_NUMSEG] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `sum {m,n} (\<lambda>j. if n = j \/ j = m then (x:real^N)$j else 0)` THEN
    CONJ_TAC THENL
     [SIMP_TAC[SUM_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[REAL_ADD_RID];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
      ASM_SIMP_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM;
                   IN_NUMSEG; REAL_MUL_LZERO] THEN
      ASM_ARITH_TAC]]);; *)

(* ------------------------------------------------------------------------- *)
(* Hence the effect of an arbitrary linear map on a gmeasurable set.          *)
(* ------------------------------------------------------------------------- *)

lemma LAMBDA_SWAP_GALOIS: True .. (*
 "!x:real^N y:real^N.
        1 \<le> m \<and> m \<le> dimindex(:N) \<and> 1 \<le> n \<and> n \<le> dimindex(:N)
        ==> (x = (lambda i. y$swap(m,n) i) \<longleftrightarrow>
             (lambda i. x$swap(m,n) i) = y)"
qed   SIMP_TAC[CART_EQ; LAMBDA_BETA; IN_DIMINDEX_SWAP] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `swap(m,n) (i:num)`) THEN
  ASM_SIMP_TAC[IN_DIMINDEX_SWAP] THEN
  ASM_MESON_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] SWAP_IDEMPOTENT]);; *)

lemma LAMBDA_ADD_GALOIS: True .. (*
 "!x:real^N y:real^N.
        1 \<le> m \<and> m \<le> dimindex(:N) \<and> 1 \<le> n \<and> n \<le> dimindex(:N) \<and>
        ~(m = n)
        ==> (x = (lambda i. if i = m then y$m + y$n else y$i) \<longleftrightarrow>
             (lambda i. if i = m then x$m - x$n else x$i) = y)"
qed   SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);; *)

lemma HAS_GMEASURE_SHEAR_INTERVAL: True .. (*
 "!a b:real^N m n.
        1 \<le> m \<and> m \<le> dimindex(:N) \<and>
        1 \<le> n \<and> n \<le> dimindex(:N) \<and>
        ~(m = n) \<and> ~({a..b} = {}) \<and>
        0 \<le> a$n
        ==> (IMAGE (\<lambda>x. (lambda i. if i = m then x$m + x$n else x$i))
                   {a..b}:real^N->bool)
            has_gmeasure gmeasure (interval [a,b])"
qed   lemma lemma = prove
   (`!s t u v:real^N->bool.
          gmeasurable s \<and> gmeasurable t \<and> gmeasurable u \<and>
          negligible(s \<inter> t) \<and> negligible(s \<inter> u) \<and>
          negligible(t \<inter> u) \<and>
          s \<union> t \<union> u = v
          ==> v has_gmeasure (measure s) + (measure t) + (measure u)"
qed     REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[HAS_GMEASURE_MEASURABLE_MEASURE; GMEASURABLE_UNION] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[MEASURE_UNION; GMEASURABLE_UNION] THEN
    ASM_SIMP_TAC[MEASURE_EQ_0; UNION_OVER_INTER; MEASURE_UNION;
                 GMEASURABLE_UNION; NEGLIGIBLE_INTER; GMEASURABLE_INTER] THEN
    REAL_ARITH_TAC)
  and lemma' = prove
   (`!s t u a.
          gmeasurable s \<and> gmeasurable t \<and>
          s \<union> (IMAGE (\<lambda>x. a + x) t) = u \<and>
          negligible(s \<inter> (IMAGE (\<lambda>x. a + x) t))
          ==> gmeasure s + gmeasure t = gmeasure u"
qed     REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC[MEASURE_NEGLIGIBLE_UNION; GMEASURABLE_TRANSLATION;
                 MEASURE_TRANSLATION]) in
  REWRITE_TAC[INTERVAL_NE_EMPTY] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `linear((\<lambda>x. lambda i. if i = m then x$m + x$n else x$i):real^N->real^N)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[linear; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT; CART_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (\<lambda>x. lambda i. if i = m then x$m + x$n else x$i)
            (interval[a:real^N,b]):real^N->bool`;
    `interval[a,(lambda i. if i = m then (b:real^N)$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x \<le> a$m}`;
    `interval[a,(lambda i. if i = m then b$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x >= (b:real^N)$m}`;
    `interval[a:real^N,
              (lambda i. if i = m then (b:real^N)$m + b$n else b$i)]`]
     lemma) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONVEX_LINEAR_IMAGE; CONVEX_INTERVAL;
                 CONVEX_HALFSPACE_LE; CONVEX_HALFSPACE_GE;
                 CONVEX_INTER; GMEASURABLE_CONVEX; BOUNDED_INTER;
                 BOUNDED_LINEAR_IMAGE; BOUNDED_INTERVAL] THEN
    REWRITE_TAC[INTER] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_IMAGE] THEN
    ASM_SIMP_TAC[LAMBDA_ADD_GALOIS; UNWIND_THM1] THEN
    ASM_SIMP_TAC[IN_INTERVAL; IN_ELIM_THM; LAMBDA_BETA;
                 DOT_BASIS; DOT_LSUB] THEN
    ONCE_REWRITE_TAC[MESON[]
       `(!i:num. P i) \<longleftrightarrow> P m \<and> (!i. ~(i = m) ==> P i)`] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[TAUT `(p \<and> x) \<and> (q \<and> x) \<and> r \<longleftrightarrow> x \<and> p \<and> q \<and> r`;
                TAUT `(p \<and> x) \<and> q \<and> (r \<and> x) \<longleftrightarrow> x \<and> p \<and> q \<and> r`;
                TAUT `((p \<and> x) \<and> q) \<and> (r \<and> x) \<and> s \<longleftrightarrow>
                            x \<and> p \<and> q \<and> r \<and> s`;
            TAUT `(a \<and> x \/ (b \<and> x) \<and> c \/ (d \<and> x) \<and> e \<longleftrightarrow> f \<and> x) \<longleftrightarrow>
                  x ==> (a \/ b \<and> c \/ d \<and> e \<longleftrightarrow> f)`] THEN
    ONCE_REWRITE_TAC[SET_RULE
     `{x | P x \<and> Q x} = {x | P x} \<inter> {x | Q x}`] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [ALL_TAC;
      GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_INTER THEN DISJ2_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THENL
     [EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (a:real^N)$m}`;
      EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (b:real^N)$m}`;
      EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (b:real^N)$m}`]
    THEN (CONJ_TAC THENL
      [MATCH_MP_TAC NEGLIGIBLE_HYPERPLANE THEN
       REWRITE_TAC[VECTOR_SUB_EQ] THEN
       ASM_MESON_TAC[BASIS_INJ];
       ASM_SIMP_TAC[DOT_LSUB; DOT_BASIS; SUBSET; IN_ELIM_THM;
                    NOT_IN_EMPTY] THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
       ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  ASM_SIMP_TAC[HAS_GMEASURE_MEASURABLE_MEASURE;
               GMEASURABLE_LINEAR_IMAGE_INTERVAL;
               GMEASURABLE_INTERVAL] THEN
  MP_TAC(ISPECL
   [`interval[a,(lambda i. if i = m then (b:real^N)$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x \<le> a$m}`;
    `interval[a,(lambda i. if i = m then b$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x >= (b:real^N)$m}`;
    `interval[a:real^N,
              (lambda i. if i = m then (a:real^N)$m + b$n
                         else (b:real^N)$i)]`;
    `(lambda i. if i = m then (a:real^N)$m - (b:real^N)$m
                else 0):real^N`]
     lemma') THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONVEX_LINEAR_IMAGE; CONVEX_INTERVAL;
                 CONVEX_HALFSPACE_LE; CONVEX_HALFSPACE_GE;
                 CONVEX_INTER; GMEASURABLE_CONVEX; BOUNDED_INTER;
                 BOUNDED_LINEAR_IMAGE; BOUNDED_INTERVAL] THEN
    REWRITE_TAC[INTER] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_IMAGE] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `x:real^N = (lambda i. p i) + y \<longleftrightarrow>
                                   x - (lambda i. p i) = y`] THEN
    ASM_SIMP_TAC[IN_INTERVAL; IN_ELIM_THM; LAMBDA_BETA;
                 DOT_BASIS; DOT_LSUB; UNWIND_THM1;
                 VECTOR_SUB_COMPONENT] THEN
    ONCE_REWRITE_TAC[MESON[]
       `(!i:num. P i) \<longleftrightarrow> P m \<and> (!i. ~(i = m) ==> P i)`] THEN
    ASM_SIMP_TAC[REAL_SUB_RZERO] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN
      FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC
       `!i. ~(i = m)
            ==> 1 \<le> i \<and> i \<le> dimindex (:N)
                ==> (a:real^N)$i \<le> (x:real^N)$i \<and>
                    x$i \<le> (b:real^N)$i` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[TAUT `((a \<and> b) \<and> c) \<and> (d \<and> e) \<and> f \<longleftrightarrow>
                             (b \<and> e) \<and> a \<and> c \<and> d \<and> f`] THEN
      ONCE_REWRITE_TAC[SET_RULE
       `{x | P x \<and> Q x} = {x | P x} \<inter> {x | Q x}`] THEN
      MATCH_MP_TAC NEGLIGIBLE_INTER THEN DISJ2_TAC THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (a:real^N)$m}`
      THEN CONJ_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_HYPERPLANE THEN
        REWRITE_TAC[VECTOR_SUB_EQ] THEN
        ASM_MESON_TAC[BASIS_INJ];
        ASM_SIMP_TAC[DOT_LSUB; DOT_BASIS; SUBSET; IN_ELIM_THM;
                     NOT_IN_EMPTY] THEN
        FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `a = b + c ==> a = x + b ==> x = c`) THEN
  ASM_SIMP_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES;
               LAMBDA_BETA] THEN
  REPEAT(COND_CASES_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]) THEN
  SUBGOAL_THEN `1..dimindex(:N) = m INSERT ((1..dimindex(:N)) DELETE m)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE; IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[IN_DELETE] THEN
  MATCH_MP_TAC(REAL_RING
   `s1 = s3 \<and> s2 = s3
    ==> ((bm + bn) - am) * s1 =
        ((am + bn) - am) * s2 + (bm - am) * s3`) THEN
  CONJ_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
  SIMP_TAC[IN_DELETE] THEN REAL_ARITH_TAC);; *)

lemma HAS_GMEASURE_LINEAR_IMAGE: True .. (*
 "!f:real^N->real^N s.
        linear f \<and> gmeasurable s
        ==> (IMAGE f s) has_gmeasure (abs(det(matrix f)) * gmeasure s)"
qed   REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC INDUCT_LINEAR_ELEMENTARY THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
    REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC o SPEC `IMAGE (g:real^N->real^N) s`)
     (MP_TAC o SPEC `s:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [HAS_GMEASURE_MEASURABLE_MEASURE] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_COMPOSE; DET_MUL; REAL_ABS_MUL] THEN
    REWRITE_TAC[IMAGE_o; GSYM REAL_MUL_ASSOC];

    MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `m:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(!x y. (f:real^N->real^N) x = f y ==> x = y)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[LINEAR_SINGULAR_INTO_HYPERPLANE] THEN
      EXISTS_TAC `basis m:real^N` THEN
      ASM_SIMP_TAC[BASIS_NONZERO; DOT_BASIS];
      ALL_TAC] THEN
    MP_TAC(ISPEC `matrix f:real^N^N` INVERTIBLE_DET_NZ) THEN
    ASM_SIMP_TAC[INVERTIBLE_LEFT_INVERSE; MATRIX_LEFT_INVERTIBLE_INJECTIVE;
                 MATRIX_WORKS; REAL_ABS_NUM; REAL_MUL_LZERO] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[HAS_GMEASURE_0] THEN
    ASM_SIMP_TAC[NEGLIGIBLE_LINEAR_SINGULAR_IMAGE];

    MAP_EVERY X_GEN_TAC [`c:num->real`; `s:real^N->bool`] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[HAS_GMEASURE_MEASURE]) THEN
    FIRST_ASSUM(MP_TAC o SPEC `c:num->real` o
     MATCH_MP HAS_GMEASURE_STRETCH) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[matrix; LAMBDA_BETA] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) DET_DIAGONAL o rand o snd) THEN
    SIMP_TAC[LAMBDA_BETA; BASIS_COMPONENT; REAL_MUL_RZERO] THEN
    DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
    REWRITE_TAC[REAL_MUL_RID];

    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_GMEASURE_LINEAR_SUFFICIENT THEN
    ASM_SIMP_TAC[linear; LAMBDA_BETA; IN_DIMINDEX_SWAP; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT; CART_EQ] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
    SUBGOAL_THEN `matrix (\<lambda>x:real^N. lambda i. x$swap (m,n) i):real^N^N =
                  transp(lambda i j. (mat 1:real^N^N)$i$swap (m,n) j)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[MATRIX_EQ; LAMBDA_BETA; IN_DIMINDEX_SWAP;
                    matrix_vector_mul; CART_EQ; matrix; mat; basis;
                    COND_COMPONENT; transp] THEN
      REWRITE_TAC[EQ_SYM_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[DET_TRANSP] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) DET_PERMUTE_COLUMNS o
        rand o lhand o rand o snd) THEN
    ASM_SIMP_TAC[PERMUTES_SWAP; IN_NUMSEG; ETA_AX] THEN
    DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[DET_I; REAL_ABS_SIGN; REAL_MUL_RID; REAL_MUL_LID] THEN
    ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
     [ASM_SIMP_TAC[IMAGE_CLAUSES; HAS_GMEASURE_EMPTY; MEASURE_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(IMAGE (\<lambda>x:real^N. lambda i. x$swap (m,n) i)
              {a..b}:real^N->bool = {})`
    MP_TAC THENL [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (\<lambda>x:real^N. lambda i. x$swap (m,n) i)
              {a..b}:real^N->bool =
      interval[(lambda i. a$swap (m,n) i),
               (lambda i. b$swap (m,n) i)]`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTERVAL; IN_IMAGE] THEN
      ASM_SIMP_TAC[LAMBDA_SWAP_GALOIS; UNWIND_THM1] THEN
      SIMP_TAC[LAMBDA_BETA] THEN GEN_TAC THEN EQ_TAC THEN
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `swap(m,n) (i:num)`) THEN
      ASM_SIMP_TAC[IN_DIMINDEX_SWAP] THEN
      ASM_MESON_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] SWAP_IDEMPOTENT];
      ALL_TAC] THEN
    REWRITE_TAC[HAS_GMEASURE_MEASURABLE_MEASURE; GMEASURABLE_INTERVAL] THEN
    REWRITE_TAC[MEASURE_INTERVAL] THEN
    ASM_SIMP_TAC[CONTENT_CLOSED_INTERVAL; GSYM INTERVAL_NE_EMPTY] THEN
    DISCH_THEN(K ALL_TAC) THEN SIMP_TAC[LAMBDA_BETA] THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; IN_DIMINDEX_SWAP] THEN
    MP_TAC(ISPECL [`\i. (b - a:real^N)$i`; `swap(m:num,n)`; `1..dimindex(:N)`]
                (GSYM PRODUCT_PERMUTE)) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PERMUTES_SWAP; IN_NUMSEG];

    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_GMEASURE_LINEAR_SUFFICIENT THEN
    MATCH_MP_TAC(TAUT `a \<and> (a ==> b) ==> a \<and> b`) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[linear; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                   VECTOR_MUL_COMPONENT; CART_EQ] THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
    SUBGOAL_THEN
      `det(matrix(\<lambda>x. lambda i. if i = m then (x:real^N)$m + x$n
                                else x$i):real^N^N) = 1`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[matrix; basis; COND_COMPONENT; LAMBDA_BETA] THEN
      FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
       `~(m:num = n) ==> m < n \/ n < m`))
      THENL
       [W(MP_TAC o PART_MATCH (lhs o rand) DET_UPPERTRIANGULAR o lhs o snd);
        W(MP_TAC o PART_MATCH (lhs o rand) DET_LOWERTRIANGULAR o lhs o snd)]
      THEN ASM_SIMP_TAC[LAMBDA_BETA; BASIS_COMPONENT; COND_COMPONENT;
                        matrix; REAL_ADD_RID; COND_ID;
                        PRODUCT_CONST_NUMSEG; REAL_POW_ONE] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REPEAT GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LID] THEN
    ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
     [ASM_SIMP_TAC[IMAGE_CLAUSES; HAS_GMEASURE_EMPTY; MEASURE_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (\<lambda>x. lambda i. if i = m then x$m + x$n else x$i) (interval [a,b]) =
      IMAGE (\<lambda>x:real^N. (lambda i. if i = m \/ i = n then a$n else 0) +
                        x)
            (IMAGE (\<lambda>x:real^N. lambda i. if i = m then x$m + x$n else x$i)
                   (IMAGE (\<lambda>x. (lambda i. if i = n then --(a$n) else 0) + x)
                          {a..b}))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[FUN_EQ_THM; o_THM; VECTOR_ADD_COMPONENT; LAMBDA_BETA;
                   CART_EQ] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `i:num`] THEN
      STRIP_TAC THEN ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i:num = n` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_GMEASURE_TRANSLATION THEN
    SUBGOAL_THEN
     `measure{a..b} =
      measure(IMAGE (\<lambda>x:real^N. (lambda i. if i = n then --(a$n) else 0) + x)
                    {a..b}:real^N->bool)`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_TRANSLATION THEN
      REWRITE_TAC[MEASURABLE_INTERVAL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(IMAGE (\<lambda>x:real^N. (lambda i. if i = n then --(a$n) else 0) + x)
                    {a..b}:real^N->bool = {})`
    MP_TAC THENL [ASM_SIMP_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `c + x = 1 % x + c`] THEN
    ASM_REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; REAL_POS] THEN
    DISCH_TAC THEN MATCH_MP_TAC HAS_GMEASURE_SHEAR_INTERVAL THEN
    ASM_SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC]);; *)

lemma GMEASURABLE_LINEAR_IMAGE: True .. (*
 "!f:real^N->real^N s.
        linear f \<and> gmeasurable s ==> gmeasurable(IMAGE f s)"
qed   REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_GMEASURE_LINEAR_IMAGE) THEN
  SIMP_TAC[HAS_GMEASURE_MEASURABLE_MEASURE]);; *)

lemma MEASURE_LINEAR_IMAGE: True .. (*
 "!f:real^N->real^N s.
        linear f \<and> gmeasurable s
        ==> measure(IMAGE f s) = abs(det(matrix f)) * gmeasure s"
qed   REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_GMEASURE_LINEAR_IMAGE) THEN
  SIMP_TAC[HAS_GMEASURE_MEASURABLE_MEASURE]);; *)

lemma HAS_GMEASURE_LINEAR_IMAGE_SAME: True .. (*
 "!f s. linear f \<and> gmeasurable s \<and> abs(det(matrix f)) = 1
         ==> (IMAGE f s) has_gmeasure (measure s)"
qed   MESON_TAC[HAS_GMEASURE_LINEAR_IMAGE; REAL_MUL_LID]);; *)

lemma MEASURE_LINEAR_IMAGE_SAME: True .. (*
 "!f:real^N->real^N s.
        linear f \<and> gmeasurable s \<and> abs(det(matrix f)) = 1
        ==> measure(IMAGE f s) = gmeasure s"
qed   REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_GMEASURE_LINEAR_IMAGE_SAME) THEN
  SIMP_TAC[HAS_GMEASURE_MEASURABLE_MEASURE]);; *)

(* ------------------------------------------------------------------------- *)
(* gmeasure of a standard simplex.                                            *)
(* ------------------------------------------------------------------------- *)

lemma CONGRUENT_IMAGE_STD_SIMPLEX: True .. (*
 "!p. p permutes 1..dimindex(:N)
       ==> {x:real^N | 0 \<le> x$(p 1) \<and> x$(p(dimindex(:N))) \<le> 1 \<and>
                       (!i. 1 \<le> i \<and> i < dimindex(:N)
                            ==> x$(p i) \<le> x$(p(i + 1)))} =
           IMAGE (\<lambda>x:real^N. lambda i. sum(1..inverse p(i)) (\<lambda>j. x$j))
                 {x | (!i. 1 \<le> i \<and> i \<le> dimindex (:N) ==> 0 \<le> x$i) \<and>
                      sum (1..dimindex (:N)) (\<lambda>i. x$i) \<le> 1}"
qed   REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA; LAMBDA_BETA_PERM; LE_REFL;
                 ARITH_RULE `i < n ==> i \<le> n \<and> i + 1 \<le> n`;
                 ARITH_RULE `1 \<le> n + 1`; DIMINDEX_GE_1] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PERMUTES_INVERSES th]) THEN
    ASM_SIMP_TAC[SUM_SING_NUMSEG; DIMINDEX_GE_1; LE_REFL] THEN
    REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 \<le> SUC n`] THEN
    ASM_SIMP_TAC[REAL_LE_ADDR] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  STRIP_TAC THEN
  EXISTS_TAC `(lambda i. if i = 1 then x$(p 1)
                         else (x:real^N)$p(i) - x$p(i - 1)):real^N` THEN
  ASM_SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA; LAMBDA_BETA_PERM; LE_REFL;
               ARITH_RULE `i < n ==> i \<le> n \<and> i + 1 \<le> n`;
               ARITH_RULE `1 \<le> n + 1`; DIMINDEX_GE_1; CART_EQ] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `1 \<le> inverse (p:num->num) i \<and>
                  !x. x \<le> inverse p i ==> x \<le> dimindex(:N)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_INVERSE; IN_NUMSEG; LE_TRANS; PERMUTES_IN_IMAGE];
      ASM_SIMP_TAC[LAMBDA_BETA] THEN ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH]] THEN
    SIMP_TAC[ARITH_RULE `2 \<le> n ==> ~(n = 1)`] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o BINDER_CONV)
                [GSYM REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[SUM_PARTIAL_PRE] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; SUM_0; COND_ID] THEN
    REWRITE_TAC[REAL_MUL_LID; ARITH; REAL_SUB_RZERO] THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
     `1 \<le> p ==> p = 1 \/ 2 \<le> p`) o CONJUNCT1) THEN
    ASM_SIMP_TAC[ARITH] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PERMUTES_INVERSES th]) THEN
    REWRITE_TAC[REAL_ADD_RID] THEN TRY REAL_ARITH_TAC THEN
    ASM_MESON_TAC[PERMUTES_INVERSE_EQ; PERMUTES_INVERSE];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
    ASM_SIMP_TAC[SUB_ADD] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;

    SIMP_TAC[SUM_CLAUSES_LEFT; DIMINDEX_GE_1; ARITH;
             ARITH_RULE `2 \<le> n ==> ~(n = 1)`] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o BINDER_CONV)
                [GSYM REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[SUM_PARTIAL_PRE] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; SUM_0; COND_ID] THEN
    REWRITE_TAC[REAL_MUL_LID; ARITH; REAL_SUB_RZERO] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_ADD_RID] THEN
    ASM_REWRITE_TAC[REAL_ARITH `x + y - x:real = y`] THEN
    ASM_MESON_TAC[DIMINDEX_GE_1;
                  ARITH_RULE `1 \<le> n \<and> ~(2 \<le> n) ==> n = 1`]]);; *)

lemma HAS_GMEASURE_IMAGE_STD_SIMPLEX: True .. (*
 "!p. p permutes 1..dimindex(:N)
       ==> {x:real^N | 0 \<le> x$(p 1) \<and> x$(p(dimindex(:N))) \<le> 1 \<and>
                       (!i. 1 \<le> i \<and> i < dimindex(:N)
                            ==> x$(p i) \<le> x$(p(i + 1)))}
           has_gmeasure
           (measure (convex hull
             (0 INSERT {basis i:real^N | 1 \<le> i \<and> i \<le> dimindex(:N)})))"
qed   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONGRUENT_IMAGE_STD_SIMPLEX] THEN
  ASM_SIMP_TAC[GSYM STD_SIMPLEX] THEN
  MATCH_MP_TAC HAS_GMEASURE_LINEAR_IMAGE_SAME THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[linear; CART_EQ] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                 GSYM SUM_ADD_NUMSEG; GSYM SUM_LMUL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THENL
     [MATCH_MP_TAC VECTOR_ADD_COMPONENT;
      MATCH_MP_TAC VECTOR_MUL_COMPONENT] THEN
    ASM_MESON_TAC[PERMUTES_INVERSE; IN_NUMSEG; LE_TRANS; PERMUTES_IN_IMAGE];
    MATCH_MP_TAC GMEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN REWRITE_TAC[BOUNDED_INSERT] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC FINITE_IMP_BOUNDED THEN MATCH_MP_TAC FINITE_IMAGE THEN
    REWRITE_TAC[GSYM numseg; FINITE_NUMSEG];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `abs(det
       ((lambda i. ((lambda i j. if j \<le> i then 1 else 0):real^N^N)
                   $inverse p i)
        :real^N^N))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[CART_EQ] THEN
      ASM_SIMP_TAC[matrix; LAMBDA_BETA; BASIS_COMPONENT; COND_COMPONENT;
                   LAMBDA_BETA_PERM; PERMUTES_INVERSE] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `sum (1..inverse (p:num->num) i)
                      (\<lambda>k. if k = j then 1 else 0)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN
        ASM_SIMP_TAC[IN_NUMSEG; PERMUTES_IN_IMAGE; basis] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC LAMBDA_BETA THEN
        ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; LE_TRANS;
                      PERMUTES_INVERSE];
        ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PERMUTES_INVERSE; DET_PERMUTE_ROWS; ETA_AX] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_SIGN; REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `x = 1 ==> abs x = 1`) THEN
    ASM_SIMP_TAC[DET_LOWERTRIANGULAR; GSYM NOT_LT; LAMBDA_BETA] THEN
    REWRITE_TAC[LT_REFL; PRODUCT_CONST_NUMSEG; REAL_POW_ONE]]);; *)

lemma HAS_GMEASURE_STD_SIMPLEX: True .. (*
 "(convex hull (0:real^N INSERT {basis i | 1 \<le> i \<and> i \<le> dimindex(:N)}))
   has_gmeasure inv((FACT(dimindex(:N))))"
qed   lemma lemma = prove
   (`!f:num->real. (!i. 1 \<le> i \<and> i < n ==> f i \<le> f(i + 1)) \<longleftrightarrow>
                   (!i j. 1 \<le> i \<and> i \<le> j \<and> j \<le> n ==> f i \<le> f j)"
qed     GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [GEN_TAC THEN INDUCT_TAC THEN
      SIMP_TAC[LE; REAL_LE_REFL] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->real) j` THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC x \<le> y ==> x \<le> y`] THEN
      REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]) in
  MP_TAC(ISPECL
   [`\p. {x:real^N | 0 \<le> x$(p 1) \<and> x$(p(dimindex(:N))) \<le> 1 \<and>
                     (!i. 1 \<le> i \<and> i < dimindex(:N)
                          ==> x$(p i) \<le> x$(p(i + 1)))}`;
    `{p | p permutes 1..dimindex(:N)}`]
    HAS_GMEASURE_NEGLIGIBLE_UNIONS_IMAGE) THEN
  ASM_SIMP_TAC[REWRITE_RULE[HAS_GMEASURE_MEASURABLE_MEASURE]
                            HAS_GMEASURE_IMAGE_STD_SIMPLEX; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_PERMUTATIONS; FINITE_NUMSEG;
               CARD_PERMUTATIONS; CARD_NUMSEG_1] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:num->num`; `q:num->num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?i. i \<in> 1..dimindex(:N) \<and> ~(p i:num = q i)` MP_TAC THENL
     [ASM_MESON_TAC[permutes; FUN_EQ_THM]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    REWRITE_TAC[TAUT `a ==> ~(b \<and> ~c) \<longleftrightarrow> a \<and> b ==> c`] THEN
    REWRITE_TAC[IN_NUMSEG] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x:real^N | (basis(p(k:num)) - basis(q k)) dot x = 0}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_HYPERPLANE THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN
      MATCH_MP_TAC BASIS_NE THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; DOT_LSUB; VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[DOT_BASIS; GSYM IN_NUMSEG; PERMUTES_IN_IMAGE] THEN
    SUBGOAL_THEN `?l. (q:num->num) l = p(k:num)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[permutes]; ALL_TAC] THEN
    SUBGOAL_THEN `1 \<le> l \<and> l \<le> dimindex(:N)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
    SUBGOAL_THEN `k:num < l` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LE] THEN REWRITE_TAC[LE_LT] THEN
      ASM_MESON_TAC[PERMUTES_INJECTIVE; IN_NUMSEG];
      ALL_TAC] THEN
    SUBGOAL_THEN `?m. (p:num->num) m = q(k:num)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[permutes]; ALL_TAC] THEN
    SUBGOAL_THEN `1 \<le> m \<and> m \<le> dimindex(:N)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
    SUBGOAL_THEN `k:num < m` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LE] THEN REWRITE_TAC[LE_LT] THEN
      ASM_MESON_TAC[PERMUTES_INJECTIVE; IN_NUMSEG];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[lemma] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `l:num`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `m:num`]) THEN
    ASM_SIMP_TAC[LT_IMP_LE; IMP_IMP; REAL_LE_ANTISYM; REAL_SUB_0] THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; DOT_BASIS];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_GMEASURE_MEASURABLE_MEASURE] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN CONJ_TAC THENL
   [MATCH_MP_TAC GMEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN REWRITE_TAC[BOUNDED_INSERT] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC FINITE_IMP_BOUNDED THEN MATCH_MP_TAC FINITE_IMAGE THEN
    REWRITE_TAC[GSYM numseg; FINITE_NUMSEG];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(y = 0) ==> (x = inv y \<longleftrightarrow> y * x = 1)`;
               REAL_OF_NUM_EQ; FACT_NZ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `measure(interval[0:real^N,1])` THEN CONJ_TAC THENL
   [AP_TERM_TAC; REWRITE_TAC[MEASURE_INTERVAL; CONTENT_UNIT]] THEN
  REWRITE_TAC[lemma] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; FORALL_IN_IMAGE; IMP_CONJ;
                RIGHT_FORALL_IMP_THM; IN_ELIM_THM] THEN
    SIMP_TAC[IMP_IMP; IN_INTERVAL; LAMBDA_BETA; VEC_COMPONENT] THEN
    X_GEN_TAC `p:num->num` THEN STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN
    STRIP_TAC THEN X_GEN_TAC `i:num` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `(x:real^N)$(p 1)`;
      EXISTS_TAC `(x:real^N)$(p(dimindex(:N)))`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP PERMUTES_SURJECTIVE) THEN
    ASM_MESON_TAC[LE_REFL; PERMUTES_IN_IMAGE; IN_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `s \<subseteq> UNIONS(IMAGE f t) \<longleftrightarrow>
                        !x. x \<in> s ==> ?y. y \<in> t \<and> x \<in> f y`] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTERVAL; IN_ELIM_THM] THEN
  SIMP_TAC[VEC_COMPONENT] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\i j. ~((x:real^N)$j \<le> x$i)` TOPOLOGICAL_SORT) THEN
  REWRITE_TAC[REAL_NOT_LE; REAL_NOT_LT] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`dimindex(:N)`; `1..dimindex(:N)`]) THEN
  REWRITE_TAC[HAS_SIZE_NUMSEG_1; EXTENSION; IN_IMAGE; IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num` (CONJUNCTS_THEN2
   (ASSUME_TAC o GSYM) ASSUME_TAC)) THEN
  EXISTS_TAC `\i. if i \<in> 1..dimindex(:N) then f(i) else i` THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ARITH_RULE
    `1 \<le> i \<and> i \<le> j \<and> j \<le> n \<longleftrightarrow>
     1 \<le> i \<and> 1 \<le> j \<and> i \<le> n \<and> j \<le> n \<and> i \<le> j`] THEN
  ASM_SIMP_TAC[IN_NUMSEG; LE_REFL; DIMINDEX_GE_1] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[LE_REFL; DIMINDEX_GE_1; LE_LT; REAL_LE_LT]] THEN
  SIMP_TAC[PERMUTES_FINITE_SURJECTIVE; FINITE_NUMSEG] THEN
  SIMP_TAC[IN_NUMSEG] THEN ASM_MESON_TAC[]);; *)

(* ------------------------------------------------------------------------- *)
(* Hence the gmeasure of a general simplex.                                   *)
(* ------------------------------------------------------------------------- *)

lemma HAS_GMEASURE_SIMPLEX_0: True .. (*
 "!l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> (convex hull (0 INSERT set_of_list l)) has_gmeasure
            abs(det(vector l)) / (FACT(dimindex(:N)))"
qed   REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `0 INSERT (set_of_list l) =
        IMAGE (\<lambda>x:real^N. transp(vector l:real^N^N) ** x)
              (0 INSERT {basis i:real^N | 1 \<le> i \<and> i \<le> dimindex(:N)})`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[IMAGE_CLAUSES; GSYM IMAGE_o; o_DEF] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN AP_TERM_TAC THEN
    SIMP_TAC[matrix_vector_mul; vector; transp; LAMBDA_BETA; basis] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[REAL_MUL_RZERO; SUM_DELTA] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    ONCE_REWRITE_TAC[TAUT `a \<and> b \<and> c \<longleftrightarrow> ~(b \<and> c ==> ~a)`] THEN
    X_GEN_TAC `y:real^N` THEN SIMP_TAC[LAMBDA_BETA; REAL_MUL_RID] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
    REWRITE_TAC[NOT_IMP; REAL_MUL_RID; GSYM CART_EQ] THEN
    ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM_EXISTS_EL] THEN
    EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC `SUC i`; EXISTS_TAC `i - 1`] THEN
    ASM_REWRITE_TAC[SUC_SUB1] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CONVEX_HULL_LINEAR_IMAGE; MATRIX_VECTOR_MUL_LINEAR] THEN
  SUBGOAL_THEN
   `det(vector l:real^N^N) = det(matrix(\<lambda>x:real^N. transp(vector l) ** x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; DET_TRANSP]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  ASM_SIMP_TAC[GSYM(REWRITE_RULE[HAS_GMEASURE_MEASURABLE_MEASURE]
                 HAS_GMEASURE_STD_SIMPLEX)] THEN
  MATCH_MP_TAC HAS_GMEASURE_LINEAR_IMAGE THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
  MATCH_MP_TAC GMEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN REWRITE_TAC[BOUNDED_INSERT] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  MATCH_MP_TAC FINITE_IMP_BOUNDED THEN MATCH_MP_TAC FINITE_IMAGE THEN
  REWRITE_TAC[GSYM numseg; FINITE_NUMSEG]);; *)

lemma HAS_GMEASURE_SIMPLEX: True .. (*
 "!a l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> (convex hull (set_of_list(CONS a l))) has_gmeasure
            abs(det(vector(MAP (\<lambda>x. x - a) l))) / (FACT(dimindex(:N)))"
qed   REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `MAP (\<lambda>x:real^N. x - a) l` HAS_GMEASURE_SIMPLEX_0) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; set_of_list] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N` o MATCH_MP HAS_GMEASURE_TRANSLATION) THEN
  REWRITE_TAC[GSYM CONVEX_HULL_TRANSLATION] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[IMAGE_CLAUSES; VECTOR_ADD_RID; SET_OF_LIST_MAP] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `a + x - a:real^N = x`;
              SET_RULE `IMAGE (\<lambda>x. x) s = s`]);; *)

lemma GMEASURABLE_SIMPLEX: True .. (*
 "!l. gmeasurable(convex hull (set_of_list l))"
qed   GEN_TAC THEN
  MATCH_MP_TAC GMEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN
  MATCH_MP_TAC FINITE_IMP_BOUNDED THEN REWRITE_TAC[FINITE_SET_OF_LIST]);; *)

lemma MEASURE_SIMPLEX: True .. (*
 "!a l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> measure(convex hull (set_of_list(CONS a l))) =
            abs(det(vector(MAP (\<lambda>x. x - a) l))) / (FACT(dimindex(:N)))"
qed   MESON_TAC[HAS_GMEASURE_SIMPLEX; HAS_GMEASURE_MEASURABLE_MEASURE]);; *)

(* ------------------------------------------------------------------------- *)
(* Area of a triangle.                                                       *)
(* ------------------------------------------------------------------------- *)

lemma HAS_GMEASURE_TRIANGLE: True .. (*
 "!a b c:real^2.
        convex hull {a,b,c} has_gmeasure
        abs((b$1 - a$1) * (c$2 - a$2) - (b$2 - a$2) * (c$1 - a$1)) / 2"
qed   REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `[b;c]:(real^2)list`] HAS_GMEASURE_SIMPLEX) THEN
  REWRITE_TAC[LENGTH; DIMINDEX_2; ARITH; set_of_list; MAP] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DET_2; VECTOR_2] THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_2; ARITH]);; *)

lemma GMEASURABLE_TRIANGLE: True .. (*
 "!a b c:real^N. gmeasurable(convex hull {a,b,c})"
qed   REPEAT GEN_TAC THEN
  MATCH_MP_TAC GMEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_BOUNDED THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_RULES]);; *)

lemma MEASURE_TRIANGLE: True .. (*
 "!a b c:real^2.
        measure(convex hull {a,b,c}) =
        abs((b$1 - a$1) * (c$2 - a$2) - (b$2 - a$2) * (c$1 - a$1)) / 2"
qed   REWRITE_TAC[REWRITE_RULE[HAS_GMEASURE_MEASURABLE_MEASURE]
               HAS_GMEASURE_TRIANGLE]);; *)

(* ------------------------------------------------------------------------- *)
(* Volume of a tetrahedron.                                                  *)
(* ------------------------------------------------------------------------- *)

lemma HAS_GMEASURE_TETRAHEDRON: True .. (*
 "!a b c d:real^3.
        convex hull {a,b,c,d} has_gmeasure
        abs((b$1 - a$1) * (c$2 - a$2) * (d$3 - a$3) +
            (b$2 - a$2) * (c$3 - a$3) * (d$1 - a$1) +
            (b$3 - a$3) * (c$1 - a$1) * (d$2 - a$2) -
            (b$1 - a$1) * (c$3 - a$3) * (d$2 - a$2) -
            (b$2 - a$2) * (c$1 - a$1) * (d$3 - a$3) -
            (b$3 - a$3) * (c$2 - a$2) * (d$1 - a$1)) /
           6"
qed   REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `[b;c;d]:(real^3)list`] HAS_GMEASURE_SIMPLEX) THEN
  REWRITE_TAC[LENGTH; DIMINDEX_3; ARITH; set_of_list; MAP] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DET_3; VECTOR_3] THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_3; ARITH]);; *)

lemma GMEASURABLE_TETRAHEDRON: True .. (*
 "!a b c d:real^N. gmeasurable(convex hull {a,b,c,d})"
qed   REPEAT GEN_TAC THEN
  MATCH_MP_TAC GMEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_BOUNDED THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_RULES]);; *)

lemma MEASURE_TETRAHEDRON: True .. (*
 "!a b c d:real^3.
        measure(convex hull {a,b,c,d}) =
        abs((b$1 - a$1) * (c$2 - a$2) * (d$3 - a$3) +
            (b$2 - a$2) * (c$3 - a$3) * (d$1 - a$1) +
            (b$3 - a$3) * (c$1 - a$1) * (d$2 - a$2) -
            (b$1 - a$1) * (c$3 - a$3) * (d$2 - a$2) -
            (b$2 - a$2) * (c$1 - a$1) * (d$3 - a$3) -
            (b$3 - a$3) * (c$2 - a$2) * (d$1 - a$1)) / 6"
qed   REWRITE_TAC[REWRITE_RULE[HAS_GMEASURE_MEASURABLE_MEASURE]
               HAS_GMEASURE_TETRAHEDRON]);; *)

end
