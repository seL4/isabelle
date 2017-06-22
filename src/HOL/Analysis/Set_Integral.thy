(*  Title:      HOL/Analysis/Set_Integral.thy
    Author:     Jeremy Avigad (CMU), Johannes Hölzl (TUM), Luke Serafin (CMU)
    Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr

Notation and useful facts for working with integrals over a set.

TODO: keep all these? Need unicode translations as well.
*)

theory Set_Integral
  imports Radon_Nikodym
begin

lemma bij_inv_eq_iff: "bij p \<Longrightarrow> x = inv p y \<longleftrightarrow> p x = y" (* COPIED FROM Permutations *)
  using surj_f_inv_f[of p] by (auto simp add: bij_def)

subsection \<open>Fun.thy\<close>

lemma inj_fn:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "inj f"
  shows "inj (f^^n)"
proof (induction n)
  case (Suc n)
  have "inj (f o (f^^n))"
    using inj_comp[OF assms Suc.IH] by simp
  then show "inj (f^^(Suc n))"
    by auto
qed (auto)

lemma surj_fn:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "surj f"
  shows "surj (f^^n)"
proof (induction n)
  case (Suc n)
  have "surj (f o (f^^n))"
    using assms Suc.IH by (simp add: comp_surj)
  then show "surj (f^^(Suc n))"
    by auto
qed (auto)

lemma bij_fn:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "bij f"
  shows "bij (f^^n)"
by (rule bijI[OF inj_fn[OF bij_is_inj[OF assms]] surj_fn[OF bij_is_surj[OF assms]]])

lemma inv_fn_o_fn_is_id:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "bij f"
  shows "((inv f)^^n) o (f^^n) = (\<lambda>x. x)"
proof -
  have "((inv f)^^n)((f^^n) x) = x" for x n
  proof (induction n)
    case (Suc n)
    have *: "(inv f) (f y) = y" for y
      by (simp add: assms bij_is_inj)
    have "(inv f ^^ Suc n) ((f ^^ Suc n) x) = (inv f^^n) (inv f (f ((f^^n) x)))"
      by (simp add: funpow_swap1)
    also have "... = (inv f^^n) ((f^^n) x)"
      using * by auto
    also have "... = x" using Suc.IH by auto
    finally show ?case by simp
  qed (auto)
  then show ?thesis unfolding o_def by blast
qed

lemma fn_o_inv_fn_is_id:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "bij f"
  shows "(f^^n) o ((inv f)^^n) = (\<lambda>x. x)"
proof -
  have "(f^^n) (((inv f)^^n) x) = x" for x n
  proof (induction n)
    case (Suc n)
    have *: "f(inv f y) = y" for y
      using assms by (meson bij_inv_eq_iff)
    have "(f ^^ Suc n) ((inv f ^^ Suc n) x) = (f^^n) (f (inv f ((inv f^^n) x)))"
      by (simp add: funpow_swap1)
    also have "... = (f^^n) ((inv f^^n) x)"
      using * by auto
    also have "... = x" using Suc.IH by auto
    finally show ?case by simp
  qed (auto)
  then show ?thesis unfolding o_def by blast
qed

lemma inv_fn:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "bij f"
  shows "inv (f^^n) = ((inv f)^^n)"
proof -
  have "inv (f^^n) x = ((inv f)^^n) x" for x
  apply (rule inv_into_f_eq, auto simp add: inj_fn[OF bij_is_inj[OF assms]])
  using fn_o_inv_fn_is_id[OF assms, of n] by (metis comp_apply)
  then show ?thesis by auto
qed


lemma mono_inv:
  fixes f::"'a::linorder \<Rightarrow> 'b::linorder"
  assumes "mono f" "bij f"
  shows "mono (inv f)"
proof
  fix x y::'b assume "x \<le> y"
  then show "inv f x \<le> inv f y"
    by (metis (no_types, lifting) assms bij_is_surj eq_iff le_cases mono_def surj_f_inv_f)
qed

lemma mono_bij_Inf:
  fixes f :: "'a::complete_linorder \<Rightarrow> 'b::complete_linorder"
  assumes "mono f" "bij f"
  shows "f (Inf A) = Inf (f`A)"
proof -
  have "(inv f) (Inf (f`A)) \<le> Inf ((inv f)`(f`A))"
    using mono_Inf[OF mono_inv[OF assms], of "f`A"] by simp
  then have "Inf (f`A) \<le> f (Inf ((inv f)`(f`A)))"
    by (metis (no_types, lifting) assms mono_def bij_inv_eq_iff)
  also have "... = f(Inf A)"
    using assms by (simp add: bij_is_inj)
  finally show ?thesis using mono_Inf[OF assms(1), of A] by auto
qed


lemma Inf_nat_def1:
  fixes K::"nat set"
  assumes "K \<noteq> {}"
  shows "Inf K \<in> K"
by (auto simp add: Min_def Inf_nat_def) (meson LeastI assms bot.extremum_unique subsetI)

subsection \<open>Liminf-Limsup.thy\<close>

lemma limsup_shift:
  "limsup (\<lambda>n. u (n+1)) = limsup u"
proof -
  have "(SUP m:{n+1..}. u m) = (SUP m:{n..}. u (m + 1))" for n
    apply (rule SUP_eq) using Suc_le_D by auto
  then have a: "(INF n. SUP m:{n..}. u (m + 1)) = (INF n. (SUP m:{n+1..}. u m))" by auto
  have b: "(INF n. (SUP m:{n+1..}. u m)) = (INF n:{1..}. (SUP m:{n..}. u m))"
    apply (rule INF_eq) using Suc_le_D by auto
  have "(INF n:{1..}. v n) = (INF n. v n)" if "decseq v" for v::"nat \<Rightarrow> 'a"
    apply (rule INF_eq) using \<open>decseq v\<close> decseq_Suc_iff by auto
  moreover have "decseq (\<lambda>n. (SUP m:{n..}. u m))" by (simp add: SUP_subset_mono decseq_def)
  ultimately have c: "(INF n:{1..}. (SUP m:{n..}. u m)) = (INF n. (SUP m:{n..}. u m))" by simp
  have "(INF n. SUPREMUM {n..} u) = (INF n. SUP m:{n..}. u (m + 1))" using a b c by simp
  then show ?thesis by (auto cong: limsup_INF_SUP)
qed

lemma limsup_shift_k:
  "limsup (\<lambda>n. u (n+k)) = limsup u"
proof (induction k)
  case (Suc k)
  have "limsup (\<lambda>n. u (n+k+1)) = limsup (\<lambda>n. u (n+k))" using limsup_shift[where ?u="\<lambda>n. u(n+k)"] by simp
  then show ?case using Suc.IH by simp
qed (auto)

lemma liminf_shift:
  "liminf (\<lambda>n. u (n+1)) = liminf u"
proof -
  have "(INF m:{n+1..}. u m) = (INF m:{n..}. u (m + 1))" for n
    apply (rule INF_eq) using Suc_le_D by (auto)
  then have a: "(SUP n. INF m:{n..}. u (m + 1)) = (SUP n. (INF m:{n+1..}. u m))" by auto
  have b: "(SUP n. (INF m:{n+1..}. u m)) = (SUP n:{1..}. (INF m:{n..}. u m))"
    apply (rule SUP_eq) using Suc_le_D by (auto)
  have "(SUP n:{1..}. v n) = (SUP n. v n)" if "incseq v" for v::"nat \<Rightarrow> 'a"
    apply (rule SUP_eq) using \<open>incseq v\<close> incseq_Suc_iff by auto
  moreover have "incseq (\<lambda>n. (INF m:{n..}. u m))" by (simp add: INF_superset_mono mono_def)
  ultimately have c: "(SUP n:{1..}. (INF m:{n..}. u m)) = (SUP n. (INF m:{n..}. u m))" by simp
  have "(SUP n. INFIMUM {n..} u) = (SUP n. INF m:{n..}. u (m + 1))" using a b c by simp
  then show ?thesis by (auto cong: liminf_SUP_INF)
qed

lemma liminf_shift_k:
  "liminf (\<lambda>n. u (n+k)) = liminf u"
proof (induction k)
  case (Suc k)
  have "liminf (\<lambda>n. u (n+k+1)) = liminf (\<lambda>n. u (n+k))" using liminf_shift[where ?u="\<lambda>n. u(n+k)"] by simp
  then show ?case using Suc.IH by simp
qed (auto)

lemma Limsup_obtain:
  fixes u::"_ \<Rightarrow> 'a :: complete_linorder"
  assumes "Limsup F u > c"
  shows "\<exists>i. u i > c"
proof -
  have "(INF P:{P. eventually P F}. SUP x:{x. P x}. u x) > c" using assms by (simp add: Limsup_def)
  then show ?thesis by (metis eventually_True mem_Collect_eq less_INF_D less_SUP_iff)
qed

text \<open>The next lemma is extremely useful, as it often makes it possible to reduce statements
about limsups to statements about limits.\<close>

lemma limsup_subseq_lim:
  fixes u::"nat \<Rightarrow> 'a :: {complete_linorder, linorder_topology}"
  shows "\<exists>r. subseq r \<and> (u o r) \<longlonglongrightarrow> limsup u"
proof (cases)
  assume "\<forall>n. \<exists>p>n. \<forall>m\<ge>p. u m \<le> u p"
  then have "\<exists>r. \<forall>n. (\<forall>m\<ge>r n. u m \<le> u (r n)) \<and> r n < r (Suc n)"
    by (intro dependent_nat_choice) (auto simp: conj_commute)
  then obtain r where "subseq r" and mono: "\<And>n m. r n \<le> m \<Longrightarrow> u m \<le> u (r n)"
    by (auto simp: subseq_Suc_iff)
  define umax where "umax = (\<lambda>n. (SUP m:{n..}. u m))"
  have "decseq umax" unfolding umax_def by (simp add: SUP_subset_mono antimono_def)
  then have "umax \<longlonglongrightarrow> limsup u" unfolding umax_def by (metis LIMSEQ_INF limsup_INF_SUP)
  then have *: "(umax o r) \<longlonglongrightarrow> limsup u" by (simp add: LIMSEQ_subseq_LIMSEQ \<open>subseq r\<close>)
  have "\<And>n. umax(r n) = u(r n)" unfolding umax_def using mono
    by (metis SUP_le_iff antisym atLeast_def mem_Collect_eq order_refl)
  then have "umax o r = u o r" unfolding o_def by simp
  then have "(u o r) \<longlonglongrightarrow> limsup u" using * by simp
  then show ?thesis using \<open>subseq r\<close> by blast
next
  assume "\<not> (\<forall>n. \<exists>p>n. (\<forall>m\<ge>p. u m \<le> u p))"
  then obtain N where N: "\<And>p. p > N \<Longrightarrow> \<exists>m>p. u p < u m" by (force simp: not_le le_less)
  have "\<exists>r. \<forall>n. N < r n \<and> r n < r (Suc n) \<and> (\<forall>i\<in> {N<..r (Suc n)}. u i \<le> u (r (Suc n)))"
  proof (rule dependent_nat_choice)
    fix x assume "N < x"
    then have a: "finite {N<..x}" "{N<..x} \<noteq> {}" by simp_all
    have "Max {u i |i. i \<in> {N<..x}} \<in> {u i |i. i \<in> {N<..x}}" apply (rule Max_in) using a by (auto)
    then obtain p where "p \<in> {N<..x}" and upmax: "u p = Max{u i |i. i \<in> {N<..x}}" by auto
    define U where "U = {m. m > p \<and> u p < u m}"
    have "U \<noteq> {}" unfolding U_def using N[of p] \<open>p \<in> {N<..x}\<close> by auto
    define y where "y = Inf U"
    then have "y \<in> U" using \<open>U \<noteq> {}\<close> by (simp add: Inf_nat_def1)
    have a: "\<And>i. i \<in> {N<..x} \<Longrightarrow> u i \<le> u p"
    proof -
      fix i assume "i \<in> {N<..x}"
      then have "u i \<in> {u i |i. i \<in> {N<..x}}" by blast
      then show "u i \<le> u p" using upmax by simp
    qed
    moreover have "u p < u y" using \<open>y \<in> U\<close> U_def by auto
    ultimately have "y \<notin> {N<..x}" using not_le by blast
    moreover have "y > N" using \<open>y \<in> U\<close> U_def \<open>p \<in> {N<..x}\<close> by auto
    ultimately have "y > x" by auto

    have "\<And>i. i \<in> {N<..y} \<Longrightarrow> u i \<le> u y"
    proof -
      fix i assume "i \<in> {N<..y}" show "u i \<le> u y"
      proof (cases)
        assume "i = y"
        then show ?thesis by simp
      next
        assume "\<not>(i=y)"
        then have i:"i \<in> {N<..<y}" using \<open>i \<in> {N<..y}\<close> by simp
        have "u i \<le> u p"
        proof (cases)
          assume "i \<le> x"
          then have "i \<in> {N<..x}" using i by simp
          then show ?thesis using a by simp
        next
          assume "\<not>(i \<le> x)"
          then have "i > x" by simp
          then have *: "i > p" using \<open>p \<in> {N<..x}\<close> by simp
          have "i < Inf U" using i y_def by simp
          then have "i \<notin> U" using Inf_nat_def not_less_Least by auto
          then show ?thesis using U_def * by auto
        qed
        then show "u i \<le> u y" using \<open>u p < u y\<close> by auto
      qed
    qed
    then have "N < y \<and> x < y \<and> (\<forall>i\<in>{N<..y}. u i \<le> u y)" using \<open>y > x\<close> \<open>y > N\<close> by auto
    then show "\<exists>y>N. x < y \<and> (\<forall>i\<in>{N<..y}. u i \<le> u y)" by auto
  qed (auto)
  then obtain r where r: "\<forall>n. N < r n \<and> r n < r (Suc n) \<and> (\<forall>i\<in> {N<..r (Suc n)}. u i \<le> u (r (Suc n)))" by auto
  have "subseq r" using r by (auto simp: subseq_Suc_iff)
  have "incseq (u o r)" unfolding o_def using r by (simp add: incseq_SucI order.strict_implies_order)
  then have "(u o r) \<longlonglongrightarrow> (SUP n. (u o r) n)" using LIMSEQ_SUP by blast
  then have "limsup (u o r) = (SUP n. (u o r) n)" by (simp add: lim_imp_Limsup)
  moreover have "limsup (u o r) \<le> limsup u" using \<open>subseq r\<close> by (simp add: limsup_subseq_mono)
  ultimately have "(SUP n. (u o r) n) \<le> limsup u" by simp

  {
    fix i assume i: "i \<in> {N<..}"
    obtain n where "i < r (Suc n)" using \<open>subseq r\<close> using Suc_le_eq seq_suble by blast
    then have "i \<in> {N<..r(Suc n)}" using i by simp
    then have "u i \<le> u (r(Suc n))" using r by simp
    then have "u i \<le> (SUP n. (u o r) n)" unfolding o_def by (meson SUP_upper2 UNIV_I)
  }
  then have "(SUP i:{N<..}. u i) \<le> (SUP n. (u o r) n)" using SUP_least by blast
  then have "limsup u \<le> (SUP n. (u o r) n)" unfolding Limsup_def
    by (metis (mono_tags, lifting) INF_lower2 atLeast_Suc_greaterThan atLeast_def eventually_ge_at_top mem_Collect_eq)
  then have "limsup u = (SUP n. (u o r) n)" using \<open>(SUP n. (u o r) n) \<le> limsup u\<close> by simp
  then have "(u o r) \<longlonglongrightarrow> limsup u" using \<open>(u o r) \<longlonglongrightarrow> (SUP n. (u o r) n)\<close> by simp
  then show ?thesis using \<open>subseq r\<close> by auto
qed

lemma liminf_subseq_lim:
  fixes u::"nat \<Rightarrow> 'a :: {complete_linorder, linorder_topology}"
  shows "\<exists>r. subseq r \<and> (u o r) \<longlonglongrightarrow> liminf u"
proof (cases)
  assume "\<forall>n. \<exists>p>n. \<forall>m\<ge>p. u m \<ge> u p"
  then have "\<exists>r. \<forall>n. (\<forall>m\<ge>r n. u m \<ge> u (r n)) \<and> r n < r (Suc n)"
    by (intro dependent_nat_choice) (auto simp: conj_commute)
  then obtain r where "subseq r" and mono: "\<And>n m. r n \<le> m \<Longrightarrow> u m \<ge> u (r n)"
    by (auto simp: subseq_Suc_iff)
  define umin where "umin = (\<lambda>n. (INF m:{n..}. u m))"
  have "incseq umin" unfolding umin_def by (simp add: INF_superset_mono incseq_def)
  then have "umin \<longlonglongrightarrow> liminf u" unfolding umin_def by (metis LIMSEQ_SUP liminf_SUP_INF)
  then have *: "(umin o r) \<longlonglongrightarrow> liminf u" by (simp add: LIMSEQ_subseq_LIMSEQ \<open>subseq r\<close>)
  have "\<And>n. umin(r n) = u(r n)" unfolding umin_def using mono
    by (metis le_INF_iff antisym atLeast_def mem_Collect_eq order_refl)
  then have "umin o r = u o r" unfolding o_def by simp
  then have "(u o r) \<longlonglongrightarrow> liminf u" using * by simp
  then show ?thesis using \<open>subseq r\<close> by blast
next
  assume "\<not> (\<forall>n. \<exists>p>n. (\<forall>m\<ge>p. u m \<ge> u p))"
  then obtain N where N: "\<And>p. p > N \<Longrightarrow> \<exists>m>p. u p > u m" by (force simp: not_le le_less)
  have "\<exists>r. \<forall>n. N < r n \<and> r n < r (Suc n) \<and> (\<forall>i\<in> {N<..r (Suc n)}. u i \<ge> u (r (Suc n)))"
  proof (rule dependent_nat_choice)
    fix x assume "N < x"
    then have a: "finite {N<..x}" "{N<..x} \<noteq> {}" by simp_all
    have "Min {u i |i. i \<in> {N<..x}} \<in> {u i |i. i \<in> {N<..x}}" apply (rule Min_in) using a by (auto)
    then obtain p where "p \<in> {N<..x}" and upmin: "u p = Min{u i |i. i \<in> {N<..x}}" by auto
    define U where "U = {m. m > p \<and> u p > u m}"
    have "U \<noteq> {}" unfolding U_def using N[of p] \<open>p \<in> {N<..x}\<close> by auto
    define y where "y = Inf U"
    then have "y \<in> U" using \<open>U \<noteq> {}\<close> by (simp add: Inf_nat_def1)
    have a: "\<And>i. i \<in> {N<..x} \<Longrightarrow> u i \<ge> u p"
    proof -
      fix i assume "i \<in> {N<..x}"
      then have "u i \<in> {u i |i. i \<in> {N<..x}}" by blast
      then show "u i \<ge> u p" using upmin by simp
    qed
    moreover have "u p > u y" using \<open>y \<in> U\<close> U_def by auto
    ultimately have "y \<notin> {N<..x}" using not_le by blast
    moreover have "y > N" using \<open>y \<in> U\<close> U_def \<open>p \<in> {N<..x}\<close> by auto
    ultimately have "y > x" by auto

    have "\<And>i. i \<in> {N<..y} \<Longrightarrow> u i \<ge> u y"
    proof -
      fix i assume "i \<in> {N<..y}" show "u i \<ge> u y"
      proof (cases)
        assume "i = y"
        then show ?thesis by simp
      next
        assume "\<not>(i=y)"
        then have i:"i \<in> {N<..<y}" using \<open>i \<in> {N<..y}\<close> by simp
        have "u i \<ge> u p"
        proof (cases)
          assume "i \<le> x"
          then have "i \<in> {N<..x}" using i by simp
          then show ?thesis using a by simp
        next
          assume "\<not>(i \<le> x)"
          then have "i > x" by simp
          then have *: "i > p" using \<open>p \<in> {N<..x}\<close> by simp
          have "i < Inf U" using i y_def by simp
          then have "i \<notin> U" using Inf_nat_def not_less_Least by auto
          then show ?thesis using U_def * by auto
        qed
        then show "u i \<ge> u y" using \<open>u p > u y\<close> by auto
      qed
    qed
    then have "N < y \<and> x < y \<and> (\<forall>i\<in>{N<..y}. u i \<ge> u y)" using \<open>y > x\<close> \<open>y > N\<close> by auto
    then show "\<exists>y>N. x < y \<and> (\<forall>i\<in>{N<..y}. u i \<ge> u y)" by auto
  qed (auto)
  then obtain r where r: "\<forall>n. N < r n \<and> r n < r (Suc n) \<and> (\<forall>i\<in> {N<..r (Suc n)}. u i \<ge> u (r (Suc n)))" by auto
  have "subseq r" using r by (auto simp: subseq_Suc_iff)
  have "decseq (u o r)" unfolding o_def using r by (simp add: decseq_SucI order.strict_implies_order)
  then have "(u o r) \<longlonglongrightarrow> (INF n. (u o r) n)" using LIMSEQ_INF by blast
  then have "liminf (u o r) = (INF n. (u o r) n)" by (simp add: lim_imp_Liminf)
  moreover have "liminf (u o r) \<ge> liminf u" using \<open>subseq r\<close> by (simp add: liminf_subseq_mono)
  ultimately have "(INF n. (u o r) n) \<ge> liminf u" by simp

  {
    fix i assume i: "i \<in> {N<..}"
    obtain n where "i < r (Suc n)" using \<open>subseq r\<close> using Suc_le_eq seq_suble by blast
    then have "i \<in> {N<..r(Suc n)}" using i by simp
    then have "u i \<ge> u (r(Suc n))" using r by simp
    then have "u i \<ge> (INF n. (u o r) n)" unfolding o_def by (meson INF_lower2 UNIV_I)
  }
  then have "(INF i:{N<..}. u i) \<ge> (INF n. (u o r) n)" using INF_greatest by blast
  then have "liminf u \<ge> (INF n. (u o r) n)" unfolding Liminf_def
    by (metis (mono_tags, lifting) SUP_upper2 atLeast_Suc_greaterThan atLeast_def eventually_ge_at_top mem_Collect_eq)
  then have "liminf u = (INF n. (u o r) n)" using \<open>(INF n. (u o r) n) \<ge> liminf u\<close> by simp
  then have "(u o r) \<longlonglongrightarrow> liminf u" using \<open>(u o r) \<longlonglongrightarrow> (INF n. (u o r) n)\<close> by simp
  then show ?thesis using \<open>subseq r\<close> by auto
qed


subsection \<open>Extended-Real.thy\<close>

text\<open>The proof of this one is copied from \verb+ereal_add_mono+.\<close>
lemma ereal_add_strict_mono2:
  fixes a b c d :: ereal
  assumes "a < b"
    and "c < d"
  shows "a + c < b + d"
using assms
apply (cases a)
apply (cases rule: ereal3_cases[of b c d], auto)
apply (cases rule: ereal3_cases[of b c d], auto)
done

text \<open>The next ones are analogues of \verb+mult_mono+ and \verb+mult_mono'+ in ereal.\<close>

lemma ereal_mult_mono:
  fixes a b c d::ereal
  assumes "b \<ge> 0" "c \<ge> 0" "a \<le> b" "c \<le> d"
  shows "a * c \<le> b * d"
by (metis ereal_mult_right_mono mult.commute order_trans assms)

lemma ereal_mult_mono':
  fixes a b c d::ereal
  assumes "a \<ge> 0" "c \<ge> 0" "a \<le> b" "c \<le> d"
  shows "a * c \<le> b * d"
by (metis ereal_mult_right_mono mult.commute order_trans assms)

lemma ereal_mult_mono_strict:
  fixes a b c d::ereal
  assumes "b > 0" "c > 0" "a < b" "c < d"
  shows "a * c < b * d"
proof -
  have "c < \<infinity>" using \<open>c < d\<close> by auto
  then have "a * c < b * c" by (metis ereal_mult_strict_left_mono[OF assms(3) assms(2)] mult.commute)
  moreover have "b * c \<le> b * d" using assms(2) assms(4) by (simp add: assms(1) ereal_mult_left_mono less_imp_le)
  ultimately show ?thesis by simp
qed

lemma ereal_mult_mono_strict':
  fixes a b c d::ereal
  assumes "a > 0" "c > 0" "a < b" "c < d"
  shows "a * c < b * d"
apply (rule ereal_mult_mono_strict, auto simp add: assms) using assms by auto

lemma ereal_abs_add:
  fixes a b::ereal
  shows "abs(a+b) \<le> abs a + abs b"
by (cases rule: ereal2_cases[of a b]) (auto)

lemma ereal_abs_diff:
  fixes a b::ereal
  shows "abs(a-b) \<le> abs a + abs b"
by (cases rule: ereal2_cases[of a b]) (auto)

lemma sum_constant_ereal:
  fixes a::ereal
  shows "(\<Sum>i\<in>I. a) = a * card I"
apply (cases "finite I", induct set: finite, simp_all)
apply (cases a, auto, metis (no_types, hide_lams) add.commute mult.commute semiring_normalization_rules(3))
done

lemma real_lim_then_eventually_real:
  assumes "(u \<longlongrightarrow> ereal l) F"
  shows "eventually (\<lambda>n. u n = ereal(real_of_ereal(u n))) F"
proof -
  have "ereal l \<in> {-\<infinity><..<(\<infinity>::ereal)}" by simp
  moreover have "open {-\<infinity><..<(\<infinity>::ereal)}" by simp
  ultimately have "eventually (\<lambda>n. u n \<in> {-\<infinity><..<(\<infinity>::ereal)}) F" using assms tendsto_def by blast
  moreover have "\<And>x. x \<in> {-\<infinity><..<(\<infinity>::ereal)} \<Longrightarrow> x = ereal(real_of_ereal x)" using ereal_real by auto
  ultimately show ?thesis by (metis (mono_tags, lifting) eventually_mono)
qed

lemma ereal_Inf_cmult:
  assumes "c>(0::real)"
  shows "Inf {ereal c * x |x. P x} = ereal c * Inf {x. P x}"
proof -
  have "(\<lambda>x::ereal. c * x) (Inf {x::ereal. P x}) = Inf ((\<lambda>x::ereal. c * x)`{x::ereal. P x})"
    apply (rule mono_bij_Inf)
    apply (simp add: assms ereal_mult_left_mono less_imp_le mono_def)
    apply (rule bij_betw_byWitness[of _ "\<lambda>x. (x::ereal) / c"], auto simp add: assms ereal_mult_divide)
    using assms ereal_divide_eq apply auto
    done
  then show ?thesis by (simp only: setcompr_eq_image[symmetric])
qed


subsubsection \<open>Continuity of addition\<close>

text \<open>The next few lemmas remove an unnecessary assumption in \verb+tendsto_add_ereal+, culminating
in \verb+tendsto_add_ereal_general+ which essentially says that the addition
is continuous on ereal times ereal, except at $(-\infty, \infty)$ and $(\infty, -\infty)$.
It is much more convenient in many situations, see for instance the proof of
\verb+tendsto_sum_ereal+ below.\<close>

lemma tendsto_add_ereal_PInf:
  fixes y :: ereal
  assumes y: "y \<noteq> -\<infinity>"
  assumes f: "(f \<longlongrightarrow> \<infinity>) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> \<infinity>) F"
proof -
  have "\<exists>C. eventually (\<lambda>x. g x > ereal C) F"
  proof (cases y)
    case (real r)
    have "y > y-1" using y real by (simp add: ereal_between(1))
    then have "eventually (\<lambda>x. g x > y - 1) F" using g y order_tendsto_iff by auto
    moreover have "y-1 = ereal(real_of_ereal(y-1))"
      by (metis real ereal_eq_1(1) ereal_minus(1) real_of_ereal.simps(1))
    ultimately have "eventually (\<lambda>x. g x > ereal(real_of_ereal(y - 1))) F" by simp
    then show ?thesis by auto
  next
    case (PInf)
    have "eventually (\<lambda>x. g x > ereal 0) F" using g PInf by (simp add: tendsto_PInfty)
    then show ?thesis by auto
  qed (simp add: y)
  then obtain C::real where ge: "eventually (\<lambda>x. g x > ereal C) F" by auto

  {
    fix M::real
    have "eventually (\<lambda>x. f x > ereal(M - C)) F" using f by (simp add: tendsto_PInfty)
    then have "eventually (\<lambda>x. (f x > ereal (M-C)) \<and> (g x > ereal C)) F"
      by (auto simp add: ge eventually_conj_iff)
    moreover have "\<And>x. ((f x > ereal (M-C)) \<and> (g x > ereal C)) \<Longrightarrow> (f x + g x > ereal M)"
      using ereal_add_strict_mono2 by fastforce
    ultimately have "eventually (\<lambda>x. f x + g x > ereal M) F" using eventually_mono by force
  }
  then show ?thesis by (simp add: tendsto_PInfty)
qed

text\<open>One would like to deduce the next lemma from the previous one, but the fact
that $-(x+y)$ is in general different from $(-x) + (-y)$ in ereal creates difficulties,
so it is more efficient to copy the previous proof.\<close>

lemma tendsto_add_ereal_MInf:
  fixes y :: ereal
  assumes y: "y \<noteq> \<infinity>"
  assumes f: "(f \<longlongrightarrow> -\<infinity>) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> -\<infinity>) F"
proof -
  have "\<exists>C. eventually (\<lambda>x. g x < ereal C) F"
  proof (cases y)
    case (real r)
    have "y < y+1" using y real by (simp add: ereal_between(1))
    then have "eventually (\<lambda>x. g x < y + 1) F" using g y order_tendsto_iff by force
    moreover have "y+1 = ereal(real_of_ereal (y+1))" by (simp add: real)
    ultimately have "eventually (\<lambda>x. g x < ereal(real_of_ereal(y + 1))) F" by simp
    then show ?thesis by auto
  next
    case (MInf)
    have "eventually (\<lambda>x. g x < ereal 0) F" using g MInf by (simp add: tendsto_MInfty)
    then show ?thesis by auto
  qed (simp add: y)
  then obtain C::real where ge: "eventually (\<lambda>x. g x < ereal C) F" by auto

  {
    fix M::real
    have "eventually (\<lambda>x. f x < ereal(M - C)) F" using f by (simp add: tendsto_MInfty)
    then have "eventually (\<lambda>x. (f x < ereal (M- C)) \<and> (g x < ereal C)) F"
      by (auto simp add: ge eventually_conj_iff)
    moreover have "\<And>x. ((f x < ereal (M-C)) \<and> (g x < ereal C)) \<Longrightarrow> (f x + g x < ereal M)"
      using ereal_add_strict_mono2 by fastforce
    ultimately have "eventually (\<lambda>x. f x + g x < ereal M) F" using eventually_mono by force
  }
  then show ?thesis by (simp add: tendsto_MInfty)
qed

lemma tendsto_add_ereal_general1:
  fixes x y :: ereal
  assumes y: "\<bar>y\<bar> \<noteq> \<infinity>"
  assumes f: "(f \<longlongrightarrow> x) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> x + y) F"
proof (cases x)
  case (real r)
  have a: "\<bar>x\<bar> \<noteq> \<infinity>" by (simp add: real)
  show ?thesis by (rule tendsto_add_ereal[OF a, OF y, OF f, OF g])
next
  case PInf
  then show ?thesis using tendsto_add_ereal_PInf assms by force
next
  case MInf
  then show ?thesis using tendsto_add_ereal_MInf assms
    by (metis abs_ereal.simps(3) ereal_MInfty_eq_plus)
qed

lemma tendsto_add_ereal_general2:
  fixes x y :: ereal
  assumes x: "\<bar>x\<bar> \<noteq> \<infinity>"
      and f: "(f \<longlongrightarrow> x) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> x + y) F"
proof -
  have "((\<lambda>x. g x + f x) \<longlongrightarrow> x + y) F"
    using tendsto_add_ereal_general1[OF x, OF g, OF f] add.commute[of "y", of "x"] by simp
  moreover have "\<And>x. g x + f x = f x + g x" using add.commute by auto
  ultimately show ?thesis by simp
qed

text \<open>The next lemma says that the addition is continuous on ereal, except at
the pairs $(-\infty, \infty)$ and $(\infty, -\infty)$.\<close>

lemma tendsto_add_ereal_general [tendsto_intros]:
  fixes x y :: ereal
  assumes "\<not>((x=\<infinity> \<and> y=-\<infinity>) \<or> (x=-\<infinity> \<and> y=\<infinity>))"
      and f: "(f \<longlongrightarrow> x) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> x + y) F"
proof (cases x)
  case (real r)
  show ?thesis
    apply (rule tendsto_add_ereal_general2) using real assms by auto
next
  case (PInf)
  then have "y \<noteq> -\<infinity>" using assms by simp
  then show ?thesis using tendsto_add_ereal_PInf PInf assms by auto
next
  case (MInf)
  then have "y \<noteq> \<infinity>" using assms by simp
  then show ?thesis using tendsto_add_ereal_MInf MInf f g by (metis ereal_MInfty_eq_plus)
qed

subsubsection \<open>Continuity of multiplication\<close>

text \<open>In the same way as for addition, we prove that the multiplication is continuous on
ereal times ereal, except at $(\infty, 0)$ and $(-\infty, 0)$ and $(0, \infty)$ and $(0, -\infty)$,
starting with specific situations.\<close>

lemma tendsto_mult_real_ereal:
  assumes "(u \<longlongrightarrow> ereal l) F" "(v \<longlongrightarrow> ereal m) F"
  shows "((\<lambda>n. u n * v n) \<longlongrightarrow> ereal l * ereal m) F"
proof -
  have ureal: "eventually (\<lambda>n. u n = ereal(real_of_ereal(u n))) F" by (rule real_lim_then_eventually_real[OF assms(1)])
  then have "((\<lambda>n. ereal(real_of_ereal(u n))) \<longlongrightarrow> ereal l) F" using assms by auto
  then have limu: "((\<lambda>n. real_of_ereal(u n)) \<longlongrightarrow> l) F" by auto
  have vreal: "eventually (\<lambda>n. v n = ereal(real_of_ereal(v n))) F" by (rule real_lim_then_eventually_real[OF assms(2)])
  then have "((\<lambda>n. ereal(real_of_ereal(v n))) \<longlongrightarrow> ereal m) F" using assms by auto
  then have limv: "((\<lambda>n. real_of_ereal(v n)) \<longlongrightarrow> m) F" by auto

  {
    fix n assume "u n = ereal(real_of_ereal(u n))" "v n = ereal(real_of_ereal(v n))"
    then have "ereal(real_of_ereal(u n) * real_of_ereal(v n)) = u n * v n" by (metis times_ereal.simps(1))
  }
  then have *: "eventually (\<lambda>n. ereal(real_of_ereal(u n) * real_of_ereal(v n)) = u n * v n) F"
    using eventually_elim2[OF ureal vreal] by auto

  have "((\<lambda>n. real_of_ereal(u n) * real_of_ereal(v n)) \<longlongrightarrow> l * m) F" using tendsto_mult[OF limu limv] by auto
  then have "((\<lambda>n. ereal(real_of_ereal(u n)) * real_of_ereal(v n)) \<longlongrightarrow> ereal(l * m)) F" by auto
  then show ?thesis using * filterlim_cong by fastforce
qed

lemma tendsto_mult_ereal_PInf:
  fixes f g::"_ \<Rightarrow> ereal"
  assumes "(f \<longlongrightarrow> l) F" "l>0" "(g \<longlongrightarrow> \<infinity>) F"
  shows "((\<lambda>x. f x * g x) \<longlongrightarrow> \<infinity>) F"
proof -
  obtain a::real where "0 < ereal a" "a < l" using assms(2) using ereal_dense2 by blast
  have *: "eventually (\<lambda>x. f x > a) F" using \<open>a < l\<close> assms(1) by (simp add: order_tendsto_iff)
  {
    fix K::real
    define M where "M = max K 1"
    then have "M > 0" by simp
    then have "ereal(M/a) > 0" using \<open>ereal a > 0\<close> by simp
    then have "\<And>x. ((f x > a) \<and> (g x > M/a)) \<Longrightarrow> (f x * g x > ereal a * ereal(M/a))"
      using ereal_mult_mono_strict'[where ?c = "M/a", OF \<open>0 < ereal a\<close>] by auto
    moreover have "ereal a * ereal(M/a) = M" using \<open>ereal a > 0\<close> by simp
    ultimately have "\<And>x. ((f x > a) \<and> (g x > M/a)) \<Longrightarrow> (f x * g x > M)" by simp
    moreover have "M \<ge> K" unfolding M_def by simp
    ultimately have Imp: "\<And>x. ((f x > a) \<and> (g x > M/a)) \<Longrightarrow> (f x * g x > K)"
      using ereal_less_eq(3) le_less_trans by blast

    have "eventually (\<lambda>x. g x > M/a) F" using assms(3) by (simp add: tendsto_PInfty)
    then have "eventually (\<lambda>x. (f x > a) \<and> (g x > M/a)) F"
      using * by (auto simp add: eventually_conj_iff)
    then have "eventually (\<lambda>x. f x * g x > K) F" using eventually_mono Imp by force
  }
  then show ?thesis by (auto simp add: tendsto_PInfty)
qed

lemma tendsto_mult_ereal_pos:
  fixes f g::"_ \<Rightarrow> ereal"
  assumes "(f \<longlongrightarrow> l) F" "(g \<longlongrightarrow> m) F" "l>0" "m>0"
  shows "((\<lambda>x. f x * g x) \<longlongrightarrow> l * m) F"
proof (cases)
  assume *: "l = \<infinity> \<or> m = \<infinity>"
  then show ?thesis
  proof (cases)
    assume "m = \<infinity>"
    then show ?thesis using tendsto_mult_ereal_PInf assms by auto
  next
    assume "\<not>(m = \<infinity>)"
    then have "l = \<infinity>" using * by simp
    then have "((\<lambda>x. g x * f x) \<longlongrightarrow> l * m) F" using tendsto_mult_ereal_PInf assms by auto
    moreover have "\<And>x. g x * f x = f x * g x" using mult.commute by auto
    ultimately show ?thesis by simp
  qed
next
  assume "\<not>(l = \<infinity> \<or> m = \<infinity>)"
  then have "l < \<infinity>" "m < \<infinity>" by auto
  then obtain lr mr where "l = ereal lr" "m = ereal mr"
    using \<open>l>0\<close> \<open>m>0\<close> by (metis ereal_cases ereal_less(6) not_less_iff_gr_or_eq)
  then show ?thesis using tendsto_mult_real_ereal assms by auto
qed

text \<open>We reduce the general situation to the positive case by multiplying by suitable signs.
Unfortunately, as ereal is not a ring, all the neat sign lemmas are not available there. We
give the bare minimum we need.\<close>

lemma ereal_sgn_abs:
  fixes l::ereal
  shows "sgn(l) * l = abs(l)"
apply (cases l) by (auto simp add: sgn_if ereal_less_uminus_reorder)

lemma sgn_squared_ereal:
  assumes "l \<noteq> (0::ereal)"
  shows "sgn(l) * sgn(l) = 1"
apply (cases l) using assms by (auto simp add: one_ereal_def sgn_if)

lemma tendsto_mult_ereal [tendsto_intros]:
  fixes f g::"_ \<Rightarrow> ereal"
  assumes "(f \<longlongrightarrow> l) F" "(g \<longlongrightarrow> m) F" "\<not>((l=0 \<and> abs(m) = \<infinity>) \<or> (m=0 \<and> abs(l) = \<infinity>))"
  shows "((\<lambda>x. f x * g x) \<longlongrightarrow> l * m) F"
proof (cases)
  assume "l=0 \<or> m=0"
  then have "abs(l) \<noteq> \<infinity>" "abs(m) \<noteq> \<infinity>" using assms(3) by auto
  then obtain lr mr where "l = ereal lr" "m = ereal mr" by auto
  then show ?thesis using tendsto_mult_real_ereal assms by auto
next
  have sgn_finite: "\<And>a::ereal. abs(sgn a) \<noteq> \<infinity>"
    by (metis MInfty_neq_ereal(2) PInfty_neq_ereal(2) abs_eq_infinity_cases ereal_times(1) ereal_times(3) ereal_uminus_eq_reorder sgn_ereal.elims)
  then have sgn_finite2: "\<And>a b::ereal. abs(sgn a * sgn b) \<noteq> \<infinity>"
    by (metis abs_eq_infinity_cases abs_ereal.simps(2) abs_ereal.simps(3) ereal_mult_eq_MInfty ereal_mult_eq_PInfty)
  assume "\<not>(l=0 \<or> m=0)"
  then have "l \<noteq> 0" "m \<noteq> 0" by auto
  then have "abs(l) > 0" "abs(m) > 0"
    by (metis abs_ereal_ge0 abs_ereal_less0 abs_ereal_pos ereal_uminus_uminus ereal_uminus_zero less_le not_less)+
  then have "sgn(l) * l > 0" "sgn(m) * m > 0" using ereal_sgn_abs by auto
  moreover have "((\<lambda>x. sgn(l) * f x) \<longlongrightarrow> (sgn(l) * l)) F"
    by (rule tendsto_cmult_ereal, auto simp add: sgn_finite assms(1))
  moreover have "((\<lambda>x. sgn(m) * g x) \<longlongrightarrow> (sgn(m) * m)) F"
    by (rule tendsto_cmult_ereal, auto simp add: sgn_finite assms(2))
  ultimately have *: "((\<lambda>x. (sgn(l) * f x) * (sgn(m) * g x)) \<longlongrightarrow> (sgn(l) * l) * (sgn(m) * m)) F"
    using tendsto_mult_ereal_pos by force
  have "((\<lambda>x. (sgn(l) * sgn(m)) * ((sgn(l) * f x) * (sgn(m) * g x))) \<longlongrightarrow> (sgn(l) * sgn(m)) * ((sgn(l) * l) * (sgn(m) * m))) F"
    by (rule tendsto_cmult_ereal, auto simp add: sgn_finite2 *)
  moreover have "\<And>x. (sgn(l) * sgn(m)) * ((sgn(l) * f x) * (sgn(m) * g x)) = f x * g x"
    by (metis mult.left_neutral sgn_squared_ereal[OF \<open>l \<noteq> 0\<close>] sgn_squared_ereal[OF \<open>m \<noteq> 0\<close>] mult.assoc mult.commute)
  moreover have "(sgn(l) * sgn(m)) * ((sgn(l) * l) * (sgn(m) * m)) = l * m"
    by (metis mult.left_neutral sgn_squared_ereal[OF \<open>l \<noteq> 0\<close>] sgn_squared_ereal[OF \<open>m \<noteq> 0\<close>] mult.assoc mult.commute)
  ultimately show ?thesis by auto
qed

lemma tendsto_cmult_ereal_general [tendsto_intros]:
  fixes f::"_ \<Rightarrow> ereal" and c::ereal
  assumes "(f \<longlongrightarrow> l) F" "\<not> (l=0 \<and> abs(c) = \<infinity>)"
  shows "((\<lambda>x. c * f x) \<longlongrightarrow> c * l) F"
by (cases "c = 0", auto simp add: assms tendsto_mult_ereal)


subsubsection \<open>Continuity of division\<close>

lemma tendsto_inverse_ereal_PInf:
  fixes u::"_ \<Rightarrow> ereal"
  assumes "(u \<longlongrightarrow> \<infinity>) F"
  shows "((\<lambda>x. 1/ u x) \<longlongrightarrow> 0) F"
proof -
  {
    fix e::real assume "e>0"
    have "1/e < \<infinity>" by auto
    then have "eventually (\<lambda>n. u n > 1/e) F" using assms(1) by (simp add: tendsto_PInfty)
    moreover
    {
      fix z::ereal assume "z>1/e"
      then have "z>0" using \<open>e>0\<close> using less_le_trans not_le by fastforce
      then have "1/z \<ge> 0" by auto
      moreover have "1/z < e" using \<open>e>0\<close> \<open>z>1/e\<close>
        apply (cases z) apply auto
        by (metis (mono_tags, hide_lams) less_ereal.simps(2) less_ereal.simps(4) divide_less_eq ereal_divide_less_pos ereal_less(4)
            ereal_less_eq(4) less_le_trans mult_eq_0_iff not_le not_one_less_zero times_ereal.simps(1))
      ultimately have "1/z \<ge> 0" "1/z < e" by auto
    }
    ultimately have "eventually (\<lambda>n. 1/u n<e) F" "eventually (\<lambda>n. 1/u n\<ge>0) F" by (auto simp add: eventually_mono)
  } note * = this
  show ?thesis
  proof (subst order_tendsto_iff, auto)
    fix a::ereal assume "a<0"
    then show "eventually (\<lambda>n. 1/u n > a) F" using *(2) eventually_mono less_le_trans linordered_field_no_ub by fastforce
  next
    fix a::ereal assume "a>0"
    then obtain e::real where "e>0" "a>e" using ereal_dense2 ereal_less(2) by blast
    then have "eventually (\<lambda>n. 1/u n < e) F" using *(1) by auto
    then show "eventually (\<lambda>n. 1/u n < a) F" using \<open>a>e\<close> by (metis (mono_tags, lifting) eventually_mono less_trans)
  qed
qed

text \<open>The next lemma deserves to exist by itself, as it is so common and useful.\<close>

lemma tendsto_inverse_real [tendsto_intros]:
  fixes u::"_ \<Rightarrow> real"
  shows "(u \<longlongrightarrow> l) F \<Longrightarrow> l \<noteq> 0 \<Longrightarrow> ((\<lambda>x. 1/ u x) \<longlongrightarrow> 1/l) F"
  using tendsto_inverse unfolding inverse_eq_divide .

lemma tendsto_inverse_ereal [tendsto_intros]:
  fixes u::"_ \<Rightarrow> ereal"
  assumes "(u \<longlongrightarrow> l) F" "l \<noteq> 0"
  shows "((\<lambda>x. 1/ u x) \<longlongrightarrow> 1/l) F"
proof (cases l)
  case (real r)
  then have "r \<noteq> 0" using assms(2) by auto
  then have "1/l = ereal(1/r)" using real by (simp add: one_ereal_def)
  define v where "v = (\<lambda>n. real_of_ereal(u n))"
  have ureal: "eventually (\<lambda>n. u n = ereal(v n)) F" unfolding v_def using real_lim_then_eventually_real assms(1) real by auto
  then have "((\<lambda>n. ereal(v n)) \<longlongrightarrow> ereal r) F" using assms real v_def by auto
  then have *: "((\<lambda>n. v n) \<longlongrightarrow> r) F" by auto
  then have "((\<lambda>n. 1/v n) \<longlongrightarrow> 1/r) F" using \<open>r \<noteq> 0\<close> tendsto_inverse_real by auto
  then have lim: "((\<lambda>n. ereal(1/v n)) \<longlongrightarrow> 1/l) F" using \<open>1/l = ereal(1/r)\<close> by auto

  have "r \<in> -{0}" "open (-{(0::real)})" using \<open>r \<noteq> 0\<close> by auto
  then have "eventually (\<lambda>n. v n \<in> -{0}) F" using * using topological_tendstoD by blast
  then have "eventually (\<lambda>n. v n \<noteq> 0) F" by auto
  moreover
  {
    fix n assume H: "v n \<noteq> 0" "u n = ereal(v n)"
    then have "ereal(1/v n) = 1/ereal(v n)" by (simp add: one_ereal_def)
    then have "ereal(1/v n) = 1/u n" using H(2) by simp
  }
  ultimately have "eventually (\<lambda>n. ereal(1/v n) = 1/u n) F" using ureal eventually_elim2 by force
  with Lim_transform_eventually[OF this lim] show ?thesis by simp
next
  case (PInf)
  then have "1/l = 0" by auto
  then show ?thesis using tendsto_inverse_ereal_PInf assms PInf by auto
next
  case (MInf)
  then have "1/l = 0" by auto
  have "1/z = -1/ -z" if "z < 0" for z::ereal
    apply (cases z) using divide_ereal_def \<open> z < 0 \<close> by auto
  moreover have "eventually (\<lambda>n. u n < 0) F" by (metis (no_types) MInf assms(1) tendsto_MInfty zero_ereal_def)
  ultimately have *: "eventually (\<lambda>n. -1/-u n = 1/u n) F" by (simp add: eventually_mono)

  define v where "v = (\<lambda>n. - u n)"
  have "(v \<longlongrightarrow> \<infinity>) F" unfolding v_def using MInf assms(1) tendsto_uminus_ereal by fastforce
  then have "((\<lambda>n. 1/v n) \<longlongrightarrow> 0) F" using tendsto_inverse_ereal_PInf by auto
  then have "((\<lambda>n. -1/v n) \<longlongrightarrow> 0) F" using tendsto_uminus_ereal by fastforce
  then show ?thesis unfolding v_def using Lim_transform_eventually[OF *] \<open> 1/l = 0 \<close> by auto
qed

lemma tendsto_divide_ereal [tendsto_intros]:
  fixes f g::"_ \<Rightarrow> ereal"
  assumes "(f \<longlongrightarrow> l) F" "(g \<longlongrightarrow> m) F" "m \<noteq> 0" "\<not>(abs(l) = \<infinity> \<and> abs(m) = \<infinity>)"
  shows "((\<lambda>x. f x / g x) \<longlongrightarrow> l / m) F"
proof -
  define h where "h = (\<lambda>x. 1/ g x)"
  have *: "(h \<longlongrightarrow> 1/m) F" unfolding h_def using assms(2) assms(3) tendsto_inverse_ereal by auto
  have "((\<lambda>x. f x * h x) \<longlongrightarrow> l * (1/m)) F"
    apply (rule tendsto_mult_ereal[OF assms(1) *]) using assms(3) assms(4) by (auto simp add: divide_ereal_def)
  moreover have "f x * h x = f x / g x" for x unfolding h_def by (simp add: divide_ereal_def)
  moreover have "l * (1/m) = l/m" by (simp add: divide_ereal_def)
  ultimately show ?thesis unfolding h_def using Lim_transform_eventually by auto
qed


subsubsection \<open>Further limits\<close>

lemma id_nat_ereal_tendsto_PInf [tendsto_intros]:
  "(\<lambda> n::nat. real n) \<longlonglongrightarrow> \<infinity>"
by (simp add: filterlim_real_sequentially tendsto_PInfty_eq_at_top)

lemma tendsto_at_top_pseudo_inverse [tendsto_intros]:
  fixes u::"nat \<Rightarrow> nat"
  assumes "LIM n sequentially. u n :> at_top"
  shows "LIM n sequentially. Inf {N. u N \<ge> n} :> at_top"
proof -
  {
    fix C::nat
    define M where "M = Max {u n| n. n \<le> C}+1"
    {
      fix n assume "n \<ge> M"
      have "eventually (\<lambda>N. u N \<ge> n) sequentially" using assms
        by (simp add: filterlim_at_top)
      then have *: "{N. u N \<ge> n} \<noteq> {}" by force

      have "N > C" if "u N \<ge> n" for N
      proof (rule ccontr)
        assume "\<not>(N > C)"
        have "u N \<le> Max {u n| n. n \<le> C}"
          apply (rule Max_ge) using \<open>\<not>(N > C)\<close> by auto
        then show False using \<open>u N \<ge> n\<close> \<open>n \<ge> M\<close> unfolding M_def by auto
      qed
      then have **: "{N. u N \<ge> n} \<subseteq> {C..}" by fastforce
      have "Inf {N. u N \<ge> n} \<ge> C"
        by (metis "*" "**" Inf_nat_def1 atLeast_iff subset_eq)
    }
    then have "eventually (\<lambda>n. Inf {N. u N \<ge> n} \<ge> C) sequentially"
      using eventually_sequentially by auto
  }
  then show ?thesis using filterlim_at_top by auto
qed

lemma pseudo_inverse_finite_set:
  fixes u::"nat \<Rightarrow> nat"
  assumes "LIM n sequentially. u n :> at_top"
  shows "finite {N. u N \<le> n}"
proof -
  fix n
  have "eventually (\<lambda>N. u N \<ge> n+1) sequentially" using assms
    by (simp add: filterlim_at_top)
  then obtain N1 where N1: "\<And>N. N \<ge> N1 \<Longrightarrow> u N \<ge> n + 1"
    using eventually_sequentially by auto
  have "{N. u N \<le> n} \<subseteq> {..<N1}"
    apply auto using N1 by (metis Suc_eq_plus1 not_less not_less_eq_eq)
  then show "finite {N. u N \<le> n}" by (simp add: finite_subset)
qed

lemma tendsto_at_top_pseudo_inverse2 [tendsto_intros]:
  fixes u::"nat \<Rightarrow> nat"
  assumes "LIM n sequentially. u n :> at_top"
  shows "LIM n sequentially. Max {N. u N \<le> n} :> at_top"
proof -
  {
    fix N0::nat
    have "N0 \<le> Max {N. u N \<le> n}" if "n \<ge> u N0" for n
      apply (rule Max.coboundedI) using pseudo_inverse_finite_set[OF assms] that by auto
    then have "eventually (\<lambda>n. N0 \<le> Max {N. u N \<le> n}) sequentially"
      using eventually_sequentially by blast
  }
  then show ?thesis using filterlim_at_top by auto
qed

lemma ereal_truncation_top [tendsto_intros]:
  fixes x::ereal
  shows "(\<lambda>n::nat. min x n) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using reals_Archimedean2 gr0I by auto
  then have "min x n = x" if "n \<ge> K" for n apply (subst real, subst real, auto) using that eq_iff by fastforce
  then have "eventually (\<lambda>n. min x n = x) sequentially" using eventually_at_top_linorder by blast
  then show ?thesis by (simp add: Lim_eventually)
next
  case (PInf)
  then have "min x n = n" for n::nat by (auto simp add: min_def)
  then show ?thesis using id_nat_ereal_tendsto_PInf PInf by auto
next
  case (MInf)
  then have "min x n = x" for n::nat by (auto simp add: min_def)
  then show ?thesis by auto
qed

lemma ereal_truncation_real_top [tendsto_intros]:
  fixes x::ereal
  assumes "x \<noteq> - \<infinity>"
  shows "(\<lambda>n::nat. real_of_ereal(min x n)) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using reals_Archimedean2 gr0I by auto
  then have "min x n = x" if "n \<ge> K" for n apply (subst real, subst real, auto) using that eq_iff by fastforce
  then have "real_of_ereal(min x n) = r" if "n \<ge> K" for n using real that by auto
  then have "eventually (\<lambda>n. real_of_ereal(min x n) = r) sequentially" using eventually_at_top_linorder by blast
  then have "(\<lambda>n. real_of_ereal(min x n)) \<longlonglongrightarrow> r" by (simp add: Lim_eventually)
  then show ?thesis using real by auto
next
  case (PInf)
  then have "real_of_ereal(min x n) = n" for n::nat by (auto simp add: min_def)
  then show ?thesis using id_nat_ereal_tendsto_PInf PInf by auto
qed (simp add: assms)

lemma ereal_truncation_bottom [tendsto_intros]:
  fixes x::ereal
  shows "(\<lambda>n::nat. max x (- real n)) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using reals_Archimedean2 gr0I by auto
  then have "max x (-real n) = x" if "n \<ge> K" for n apply (subst real, subst real, auto) using that eq_iff by fastforce
  then have "eventually (\<lambda>n. max x (-real n) = x) sequentially" using eventually_at_top_linorder by blast
  then show ?thesis by (simp add: Lim_eventually)
next
  case (MInf)
  then have "max x (-real n) = (-1)* ereal(real n)" for n::nat by (auto simp add: max_def)
  moreover have "(\<lambda>n. (-1)* ereal(real n)) \<longlonglongrightarrow> -\<infinity>"
    using tendsto_cmult_ereal[of "-1", OF _ id_nat_ereal_tendsto_PInf] by (simp add: one_ereal_def)
  ultimately show ?thesis using MInf by auto
next
  case (PInf)
  then have "max x (-real n) = x" for n::nat by (auto simp add: max_def)
  then show ?thesis by auto
qed

lemma ereal_truncation_real_bottom [tendsto_intros]:
  fixes x::ereal
  assumes "x \<noteq> \<infinity>"
  shows "(\<lambda>n::nat. real_of_ereal(max x (- real n))) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using reals_Archimedean2 gr0I by auto
  then have "max x (-real n) = x" if "n \<ge> K" for n apply (subst real, subst real, auto) using that eq_iff by fastforce
  then have "real_of_ereal(max x (-real n)) = r" if "n \<ge> K" for n using real that by auto
  then have "eventually (\<lambda>n. real_of_ereal(max x (-real n)) = r) sequentially" using eventually_at_top_linorder by blast
  then have "(\<lambda>n. real_of_ereal(max x (-real n))) \<longlonglongrightarrow> r" by (simp add: Lim_eventually)
  then show ?thesis using real by auto
next
  case (MInf)
  then have "real_of_ereal(max x (-real n)) = (-1)* ereal(real n)" for n::nat by (auto simp add: max_def)
  moreover have "(\<lambda>n. (-1)* ereal(real n)) \<longlonglongrightarrow> -\<infinity>"
    using tendsto_cmult_ereal[of "-1", OF _ id_nat_ereal_tendsto_PInf] by (simp add: one_ereal_def)
  ultimately show ?thesis using MInf by auto
qed (simp add: assms)

text \<open>the next one is copied from \verb+tendsto_sum+.\<close>
lemma tendsto_sum_ereal [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> (f i \<longlongrightarrow> a i) F"
          "\<And>i. abs(a i) \<noteq> \<infinity>"
  shows "((\<lambda>x. \<Sum>i\<in>S. f i x) \<longlongrightarrow> (\<Sum>i\<in>S. a i)) F"
proof (cases "finite S")
  assume "finite S" then show ?thesis using assms
    by (induct, simp, simp add: tendsto_add_ereal_general2 assms)
qed(simp)

subsubsection \<open>Limsups and liminfs\<close>

lemma limsup_finite_then_bounded:
  fixes u::"nat \<Rightarrow> real"
  assumes "limsup u < \<infinity>"
  shows "\<exists>C. \<forall>n. u n \<le> C"
proof -
  obtain C where C: "limsup u < C" "C < \<infinity>" using assms ereal_dense2 by blast
  then have "C = ereal(real_of_ereal C)" using ereal_real by force
  have "eventually (\<lambda>n. u n < C) sequentially" using C(1) unfolding Limsup_def
    apply (auto simp add: INF_less_iff)
    using SUP_lessD eventually_mono by fastforce
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> u n < C" using eventually_sequentially by auto
  define D where "D = max (real_of_ereal C) (Max {u n |n. n \<le> N})"
  have "\<And>n. u n \<le> D"
  proof -
    fix n show "u n \<le> D"
    proof (cases)
      assume *: "n \<le> N"
      have "u n \<le> Max {u n |n. n \<le> N}" by (rule Max_ge, auto simp add: *)
      then show "u n \<le> D" unfolding D_def by linarith
    next
      assume "\<not>(n \<le> N)"
      then have "n \<ge> N" by simp
      then have "u n < C" using N by auto
      then have "u n < real_of_ereal C" using \<open>C = ereal(real_of_ereal C)\<close> less_ereal.simps(1) by fastforce
      then show "u n \<le> D" unfolding D_def by linarith
    qed
  qed
  then show ?thesis by blast
qed

lemma liminf_finite_then_bounded_below:
  fixes u::"nat \<Rightarrow> real"
  assumes "liminf u > -\<infinity>"
  shows "\<exists>C. \<forall>n. u n \<ge> C"
proof -
  obtain C where C: "liminf u > C" "C > -\<infinity>" using assms using ereal_dense2 by blast
  then have "C = ereal(real_of_ereal C)" using ereal_real by force
  have "eventually (\<lambda>n. u n > C) sequentially" using C(1) unfolding Liminf_def
    apply (auto simp add: less_SUP_iff)
    using eventually_elim2 less_INF_D by fastforce
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> u n > C" using eventually_sequentially by auto
  define D where "D = min (real_of_ereal C) (Min {u n |n. n \<le> N})"
  have "\<And>n. u n \<ge> D"
  proof -
    fix n show "u n \<ge> D"
    proof (cases)
      assume *: "n \<le> N"
      have "u n \<ge> Min {u n |n. n \<le> N}" by (rule Min_le, auto simp add: *)
      then show "u n \<ge> D" unfolding D_def by linarith
    next
      assume "\<not>(n \<le> N)"
      then have "n \<ge> N" by simp
      then have "u n > C" using N by auto
      then have "u n > real_of_ereal C" using \<open>C = ereal(real_of_ereal C)\<close> less_ereal.simps(1) by fastforce
      then show "u n \<ge> D" unfolding D_def by linarith
    qed
  qed
  then show ?thesis by blast
qed

lemma liminf_upper_bound:
  fixes u:: "nat \<Rightarrow> ereal"
  assumes "liminf u < l"
  shows "\<exists>N>k. u N < l"
by (metis assms gt_ex less_le_trans liminf_bounded_iff not_less)

text \<open>The following statement about limsups is reduced to a statement about limits using
subsequences thanks to \verb+limsup_subseq_lim+. The statement for limits follows for instance from
\verb+tendsto_add_ereal_general+.\<close>

lemma ereal_limsup_add_mono:
  fixes u v::"nat \<Rightarrow> ereal"
  shows "limsup (\<lambda>n. u n + v n) \<le> limsup u + limsup v"
proof (cases)
  assume "(limsup u = \<infinity>) \<or> (limsup v = \<infinity>)"
  then have "limsup u + limsup v = \<infinity>" by simp
  then show ?thesis by auto
next
  assume "\<not>((limsup u = \<infinity>) \<or> (limsup v = \<infinity>))"
  then have "limsup u < \<infinity>" "limsup v < \<infinity>" by auto

  define w where "w = (\<lambda>n. u n + v n)"
  obtain r where r: "subseq r" "(w o r) \<longlonglongrightarrow> limsup w" using limsup_subseq_lim by auto
  obtain s where s: "subseq s" "(u o r o s) \<longlonglongrightarrow> limsup (u o r)" using limsup_subseq_lim by auto
  obtain t where t: "subseq t" "(v o r o s o t) \<longlonglongrightarrow> limsup (v o r o s)" using limsup_subseq_lim by auto

  define a where "a = r o s o t"
  have "subseq a" using r s t by (simp add: a_def subseq_o)
  have l:"(w o a) \<longlonglongrightarrow> limsup w"
         "(u o a) \<longlonglongrightarrow> limsup (u o r)"
         "(v o a) \<longlonglongrightarrow> limsup (v o r o s)"
  apply (metis (no_types, lifting) r(2) s(1) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) s(2) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) t(2) a_def comp_assoc)
  done

  have "limsup (u o r) \<le> limsup u" by (simp add: limsup_subseq_mono r(1))
  then have a: "limsup (u o r) \<noteq> \<infinity>" using \<open>limsup u < \<infinity>\<close> by auto
  have "limsup (v o r o s) \<le> limsup v" by (simp add: comp_assoc limsup_subseq_mono r(1) s(1) subseq_o)
  then have b: "limsup (v o r o s) \<noteq> \<infinity>" using \<open>limsup v < \<infinity>\<close> by auto

  have "(\<lambda>n. (u o a) n + (v o a) n) \<longlonglongrightarrow> limsup (u o r) + limsup (v o r o s)"
    using l tendsto_add_ereal_general a b by fastforce
  moreover have "(\<lambda>n. (u o a) n + (v o a) n) = (w o a)" unfolding w_def by auto
  ultimately have "(w o a) \<longlonglongrightarrow> limsup (u o r) + limsup (v o r o s)" by simp
  then have "limsup w = limsup (u o r) + limsup (v o r o s)" using l(1) LIMSEQ_unique by blast
  then have "limsup w \<le> limsup u + limsup v"
    using \<open>limsup (u o r) \<le> limsup u\<close> \<open>limsup (v o r o s) \<le> limsup v\<close> ereal_add_mono by simp
  then show ?thesis unfolding w_def by simp
qed

text \<open>There is an asymmetry between liminfs and limsups in ereal, as $\infty + (-\infty) = \infty$.
This explains why there are more assumptions in the next lemma dealing with liminfs that in the
previous one about limsups.\<close>

lemma ereal_liminf_add_mono:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "\<not>((liminf u = \<infinity> \<and> liminf v = -\<infinity>) \<or> (liminf u = -\<infinity> \<and> liminf v = \<infinity>))"
  shows "liminf (\<lambda>n. u n + v n) \<ge> liminf u + liminf v"
proof (cases)
  assume "(liminf u = -\<infinity>) \<or> (liminf v = -\<infinity>)"
  then have *: "liminf u + liminf v = -\<infinity>" using assms by auto
  show ?thesis by (simp add: *)
next
  assume "\<not>((liminf u = -\<infinity>) \<or> (liminf v = -\<infinity>))"
  then have "liminf u > -\<infinity>" "liminf v > -\<infinity>" by auto

  define w where "w = (\<lambda>n. u n + v n)"
  obtain r where r: "subseq r" "(w o r) \<longlonglongrightarrow> liminf w" using liminf_subseq_lim by auto
  obtain s where s: "subseq s" "(u o r o s) \<longlonglongrightarrow> liminf (u o r)" using liminf_subseq_lim by auto
  obtain t where t: "subseq t" "(v o r o s o t) \<longlonglongrightarrow> liminf (v o r o s)" using liminf_subseq_lim by auto

  define a where "a = r o s o t"
  have "subseq a" using r s t by (simp add: a_def subseq_o)
  have l:"(w o a) \<longlonglongrightarrow> liminf w"
         "(u o a) \<longlonglongrightarrow> liminf (u o r)"
         "(v o a) \<longlonglongrightarrow> liminf (v o r o s)"
  apply (metis (no_types, lifting) r(2) s(1) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) s(2) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) t(2) a_def comp_assoc)
  done

  have "liminf (u o r) \<ge> liminf u" by (simp add: liminf_subseq_mono r(1))
  then have a: "liminf (u o r) \<noteq> -\<infinity>" using \<open>liminf u > -\<infinity>\<close> by auto
  have "liminf (v o r o s) \<ge> liminf v" by (simp add: comp_assoc liminf_subseq_mono r(1) s(1) subseq_o)
  then have b: "liminf (v o r o s) \<noteq> -\<infinity>" using \<open>liminf v > -\<infinity>\<close> by auto

  have "(\<lambda>n. (u o a) n + (v o a) n) \<longlonglongrightarrow> liminf (u o r) + liminf (v o r o s)"
    using l tendsto_add_ereal_general a b by fastforce
  moreover have "(\<lambda>n. (u o a) n + (v o a) n) = (w o a)" unfolding w_def by auto
  ultimately have "(w o a) \<longlonglongrightarrow> liminf (u o r) + liminf (v o r o s)" by simp
  then have "liminf w = liminf (u o r) + liminf (v o r o s)" using l(1) LIMSEQ_unique by blast
  then have "liminf w \<ge> liminf u + liminf v"
    using \<open>liminf (u o r) \<ge> liminf u\<close> \<open>liminf (v o r o s) \<ge> liminf v\<close> ereal_add_mono by simp
  then show ?thesis unfolding w_def by simp
qed

lemma ereal_limsup_lim_add:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "abs(a) \<noteq> \<infinity>"
  shows "limsup (\<lambda>n. u n + v n) = a + limsup v"
proof -
  have "limsup u = a" using assms(1) using tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by blast
  have "(\<lambda>n. -u n) \<longlonglongrightarrow> -a" using assms(1) by auto
  then have "limsup (\<lambda>n. -u n) = -a" using tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by blast

  have "limsup (\<lambda>n. u n + v n) \<le> limsup u + limsup v"
    by (rule ereal_limsup_add_mono)
  then have up: "limsup (\<lambda>n. u n + v n) \<le> a + limsup v" using \<open>limsup u = a\<close> by simp

  have a: "limsup (\<lambda>n. (u n + v n) + (-u n)) \<le> limsup (\<lambda>n. u n + v n) + limsup (\<lambda>n. -u n)"
    by (rule ereal_limsup_add_mono)
  have "eventually (\<lambda>n. u n = ereal(real_of_ereal(u n))) sequentially" using assms
    real_lim_then_eventually_real by auto
  moreover have "\<And>x. x = ereal(real_of_ereal(x)) \<Longrightarrow> x + (-x) = 0"
    by (metis plus_ereal.simps(1) right_minus uminus_ereal.simps(1) zero_ereal_def)
  ultimately have "eventually (\<lambda>n. u n + (-u n) = 0) sequentially"
    by (metis (mono_tags, lifting) eventually_mono)
  moreover have "\<And>n. u n + (-u n) = 0 \<Longrightarrow> u n + v n + (-u n) = v n"
    by (metis add.commute add.left_commute add.left_neutral)
  ultimately have "eventually (\<lambda>n. u n + v n + (-u n) = v n) sequentially"
    using eventually_mono by force
  then have "limsup v = limsup (\<lambda>n. u n + v n + (-u n))" using Limsup_eq by force
  then have "limsup v \<le> limsup (\<lambda>n. u n + v n) -a" using a \<open>limsup (\<lambda>n. -u n) = -a\<close> by (simp add: minus_ereal_def)
  then have "limsup (\<lambda>n. u n + v n) \<ge> a + limsup v" using assms(2) by (metis add.commute ereal_le_minus)
  then show ?thesis using up by simp
qed

lemma ereal_limsup_lim_mult:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "a>0" "a \<noteq> \<infinity>"
  shows "limsup (\<lambda>n. u n * v n) = a * limsup v"
proof -
  define w where "w = (\<lambda>n. u n * v n)"
  obtain r where r: "subseq r" "(v o r) \<longlonglongrightarrow> limsup v" using limsup_subseq_lim by auto
  have "(u o r) \<longlonglongrightarrow> a" using assms(1) LIMSEQ_subseq_LIMSEQ r by auto
  with tendsto_mult_ereal[OF this r(2)] have "(\<lambda>n. (u o r) n * (v o r) n) \<longlonglongrightarrow> a * limsup v" using assms(2) assms(3) by auto
  moreover have "\<And>n. (w o r) n = (u o r) n * (v o r) n" unfolding w_def by auto
  ultimately have "(w o r) \<longlonglongrightarrow> a * limsup v" unfolding w_def by presburger
  then have "limsup (w o r) = a * limsup v" by (simp add: tendsto_iff_Liminf_eq_Limsup)
  then have I: "limsup w \<ge> a * limsup v" by (metis limsup_subseq_mono r(1))

  obtain s where s: "subseq s" "(w o s) \<longlonglongrightarrow> limsup w" using limsup_subseq_lim by auto
  have *: "(u o s) \<longlonglongrightarrow> a" using assms(1) LIMSEQ_subseq_LIMSEQ s by auto
  have "eventually (\<lambda>n. (u o s) n > 0) sequentially" using assms(2) * order_tendsto_iff by blast
  moreover have "eventually (\<lambda>n. (u o s) n < \<infinity>) sequentially" using assms(3) * order_tendsto_iff by blast
  moreover have "(w o s) n / (u o s) n = (v o s) n" if "(u o s) n > 0" "(u o s) n < \<infinity>" for n
    unfolding w_def using that by (auto simp add: ereal_divide_eq)
  ultimately have "eventually (\<lambda>n. (w o s) n / (u o s) n = (v o s) n) sequentially" using eventually_elim2 by force
  moreover have "(\<lambda>n. (w o s) n / (u o s) n) \<longlonglongrightarrow> (limsup w) / a"
    apply (rule tendsto_divide_ereal[OF s(2) *]) using assms(2) assms(3) by auto
  ultimately have "(v o s) \<longlonglongrightarrow> (limsup w) / a" using Lim_transform_eventually by fastforce
  then have "limsup (v o s) = (limsup w) / a" by (simp add: tendsto_iff_Liminf_eq_Limsup)
  then have "limsup v \<ge> (limsup w) / a" by (metis limsup_subseq_mono s(1))
  then have "a * limsup v \<ge> limsup w" using assms(2) assms(3) by (simp add: ereal_divide_le_pos)
  then show ?thesis using I unfolding w_def by auto
qed

lemma ereal_liminf_lim_mult:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "a>0" "a \<noteq> \<infinity>"
  shows "liminf (\<lambda>n. u n * v n) = a * liminf v"
proof -
  define w where "w = (\<lambda>n. u n * v n)"
  obtain r where r: "subseq r" "(v o r) \<longlonglongrightarrow> liminf v" using liminf_subseq_lim by auto
  have "(u o r) \<longlonglongrightarrow> a" using assms(1) LIMSEQ_subseq_LIMSEQ r by auto
  with tendsto_mult_ereal[OF this r(2)] have "(\<lambda>n. (u o r) n * (v o r) n) \<longlonglongrightarrow> a * liminf v" using assms(2) assms(3) by auto
  moreover have "\<And>n. (w o r) n = (u o r) n * (v o r) n" unfolding w_def by auto
  ultimately have "(w o r) \<longlonglongrightarrow> a * liminf v" unfolding w_def by presburger
  then have "liminf (w o r) = a * liminf v" by (simp add: tendsto_iff_Liminf_eq_Limsup)
  then have I: "liminf w \<le> a * liminf v" by (metis liminf_subseq_mono r(1))

  obtain s where s: "subseq s" "(w o s) \<longlonglongrightarrow> liminf w" using liminf_subseq_lim by auto
  have *: "(u o s) \<longlonglongrightarrow> a" using assms(1) LIMSEQ_subseq_LIMSEQ s by auto
  have "eventually (\<lambda>n. (u o s) n > 0) sequentially" using assms(2) * order_tendsto_iff by blast
  moreover have "eventually (\<lambda>n. (u o s) n < \<infinity>) sequentially" using assms(3) * order_tendsto_iff by blast
  moreover have "(w o s) n / (u o s) n = (v o s) n" if "(u o s) n > 0" "(u o s) n < \<infinity>" for n
    unfolding w_def using that by (auto simp add: ereal_divide_eq)
  ultimately have "eventually (\<lambda>n. (w o s) n / (u o s) n = (v o s) n) sequentially" using eventually_elim2 by force
  moreover have "(\<lambda>n. (w o s) n / (u o s) n) \<longlonglongrightarrow> (liminf w) / a"
    apply (rule tendsto_divide_ereal[OF s(2) *]) using assms(2) assms(3) by auto
  ultimately have "(v o s) \<longlonglongrightarrow> (liminf w) / a" using Lim_transform_eventually by fastforce
  then have "liminf (v o s) = (liminf w) / a" by (simp add: tendsto_iff_Liminf_eq_Limsup)
  then have "liminf v \<le> (liminf w) / a" by (metis liminf_subseq_mono s(1))
  then have "a * liminf v \<le> liminf w" using assms(2) assms(3) by (simp add: ereal_le_divide_pos)
  then show ?thesis using I unfolding w_def by auto
qed

lemma ereal_liminf_lim_add:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "abs(a) \<noteq> \<infinity>"
  shows "liminf (\<lambda>n. u n + v n) = a + liminf v"
proof -
  have "liminf u = a" using assms(1) tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by blast
  then have *: "abs(liminf u) \<noteq> \<infinity>" using assms(2) by auto
  have "(\<lambda>n. -u n) \<longlonglongrightarrow> -a" using assms(1) by auto
  then have "liminf (\<lambda>n. -u n) = -a" using tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by blast
  then have **: "abs(liminf (\<lambda>n. -u n)) \<noteq> \<infinity>" using assms(2) by auto

  have "liminf (\<lambda>n. u n + v n) \<ge> liminf u + liminf v"
    apply (rule ereal_liminf_add_mono) using * by auto
  then have up: "liminf (\<lambda>n. u n + v n) \<ge> a + liminf v" using \<open>liminf u = a\<close> by simp

  have a: "liminf (\<lambda>n. (u n + v n) + (-u n)) \<ge> liminf (\<lambda>n. u n + v n) + liminf (\<lambda>n. -u n)"
    apply (rule ereal_liminf_add_mono) using ** by auto
  have "eventually (\<lambda>n. u n = ereal(real_of_ereal(u n))) sequentially" using assms
    real_lim_then_eventually_real by auto
  moreover have "\<And>x. x = ereal(real_of_ereal(x)) \<Longrightarrow> x + (-x) = 0"
    by (metis plus_ereal.simps(1) right_minus uminus_ereal.simps(1) zero_ereal_def)
  ultimately have "eventually (\<lambda>n. u n + (-u n) = 0) sequentially"
    by (metis (mono_tags, lifting) eventually_mono)
  moreover have "\<And>n. u n + (-u n) = 0 \<Longrightarrow> u n + v n + (-u n) = v n"
    by (metis add.commute add.left_commute add.left_neutral)
  ultimately have "eventually (\<lambda>n. u n + v n + (-u n) = v n) sequentially"
    using eventually_mono by force
  then have "liminf v = liminf (\<lambda>n. u n + v n + (-u n))" using Liminf_eq by force
  then have "liminf v \<ge> liminf (\<lambda>n. u n + v n) -a" using a \<open>liminf (\<lambda>n. -u n) = -a\<close> by (simp add: minus_ereal_def)
  then have "liminf (\<lambda>n. u n + v n) \<le> a + liminf v" using assms(2) by (metis add.commute ereal_minus_le)
  then show ?thesis using up by simp
qed

lemma ereal_liminf_limsup_add:
  fixes u v::"nat \<Rightarrow> ereal"
  shows "liminf (\<lambda>n. u n + v n) \<le> liminf u + limsup v"
proof (cases)
  assume "limsup v = \<infinity> \<or> liminf u = \<infinity>"
  then show ?thesis by auto
next
  assume "\<not>(limsup v = \<infinity> \<or> liminf u = \<infinity>)"
  then have "limsup v < \<infinity>" "liminf u < \<infinity>" by auto

  define w where "w = (\<lambda>n. u n + v n)"
  obtain r where r: "subseq r" "(u o r) \<longlonglongrightarrow> liminf u" using liminf_subseq_lim by auto
  obtain s where s: "subseq s" "(w o r o s) \<longlonglongrightarrow> liminf (w o r)" using liminf_subseq_lim by auto
  obtain t where t: "subseq t" "(v o r o s o t) \<longlonglongrightarrow> limsup (v o r o s)" using limsup_subseq_lim by auto

  define a where "a = r o s o t"
  have "subseq a" using r s t by (simp add: a_def subseq_o)
  have l:"(u o a) \<longlonglongrightarrow> liminf u"
         "(w o a) \<longlonglongrightarrow> liminf (w o r)"
         "(v o a) \<longlonglongrightarrow> limsup (v o r o s)"
  apply (metis (no_types, lifting) r(2) s(1) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) s(2) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) t(2) a_def comp_assoc)
  done

  have "liminf (w o r) \<ge> liminf w" by (simp add: liminf_subseq_mono r(1))
  have "limsup (v o r o s) \<le> limsup v" by (simp add: comp_assoc limsup_subseq_mono r(1) s(1) subseq_o)
  then have b: "limsup (v o r o s) < \<infinity>" using \<open>limsup v < \<infinity>\<close> by auto

  have "(\<lambda>n. (u o a) n + (v o a) n) \<longlonglongrightarrow> liminf u + limsup (v o r o s)"
    apply (rule tendsto_add_ereal_general) using b \<open>liminf u < \<infinity>\<close> l(1) l(3) by force+
  moreover have "(\<lambda>n. (u o a) n + (v o a) n) = (w o a)" unfolding w_def by auto
  ultimately have "(w o a) \<longlonglongrightarrow> liminf u + limsup (v o r o s)" by simp
  then have "liminf (w o r) = liminf u + limsup (v o r o s)" using l(2) using LIMSEQ_unique by blast
  then have "liminf w \<le> liminf u + limsup v"
    using \<open>liminf (w o r) \<ge> liminf w\<close> \<open>limsup (v o r o s) \<le> limsup v\<close>
    by (metis add_mono_thms_linordered_semiring(2) le_less_trans not_less)
  then show ?thesis unfolding w_def by simp
qed

lemma ereal_liminf_limsup_minus:
  fixes u v::"nat \<Rightarrow> ereal"
  shows "liminf (\<lambda>n. u n - v n) \<le> limsup u - limsup v"
  unfolding minus_ereal_def
  apply (subst add.commute)
  apply (rule order_trans[OF ereal_liminf_limsup_add])
  using ereal_Limsup_uminus[of sequentially "\<lambda>n. - v n"]
  apply (simp add: add.commute)
  done


lemma liminf_minus_ennreal:
  fixes u v::"nat \<Rightarrow> ennreal"
  shows "(\<And>n. v n \<le> u n) \<Longrightarrow> liminf (\<lambda>n. u n - v n) \<le> limsup u - limsup v"
  unfolding liminf_SUP_INF limsup_INF_SUP
  including ennreal.lifting
proof (transfer, clarsimp)
  fix v u :: "nat \<Rightarrow> ereal" assume *: "\<forall>x. 0 \<le> v x" "\<forall>x. 0 \<le> u x" "\<And>n. v n \<le> u n"
  moreover have "0 \<le> limsup u - limsup v"
    using * by (intro ereal_diff_positive Limsup_mono always_eventually) simp
  moreover have "0 \<le> (SUPREMUM {x..} v)" for x
    using * by (intro SUP_upper2[of x]) auto
  moreover have "0 \<le> (SUPREMUM {x..} u)" for x
    using * by (intro SUP_upper2[of x]) auto
  ultimately show "(SUP n. INF n:{n..}. max 0 (u n - v n))
            \<le> max 0 ((INF x. max 0 (SUPREMUM {x..} u)) - (INF x. max 0 (SUPREMUM {x..} v)))"
    by (auto simp: * ereal_diff_positive max.absorb2 liminf_SUP_INF[symmetric] limsup_INF_SUP[symmetric] ereal_liminf_limsup_minus)
qed

(*
    Notation
*)

abbreviation "set_borel_measurable M A f \<equiv> (\<lambda>x. indicator A x *\<^sub>R f x) \<in> borel_measurable M"

abbreviation "set_integrable M A f \<equiv> integrable M (\<lambda>x. indicator A x *\<^sub>R f x)"

abbreviation "set_lebesgue_integral M A f \<equiv> lebesgue_integral M (\<lambda>x. indicator A x *\<^sub>R f x)"

syntax
"_ascii_set_lebesgue_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(4LINT (_):(_)/|(_)./ _)" [0,60,110,61] 60)

translations
"LINT x:A|M. f" == "CONST set_lebesgue_integral M A (\<lambda>x. f)"

(*
    Notation for integration wrt lebesgue measure on the reals:

      LBINT x. f
      LBINT x : A. f

    TODO: keep all these? Need unicode.
*)

syntax
"_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real"
("(2LBINT _./ _)" [0,60] 60)

syntax
"_set_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real"
("(3LBINT _:_./ _)" [0,60,61] 60)

(*
    Basic properties
*)

(*
lemma indicator_abs_eq: "\<And>A x. \<bar>indicator A x\<bar> = ((indicator A x) :: real)"
  by (auto simp add: indicator_def)
*)

lemma set_borel_measurable_sets:
  fixes f :: "_ \<Rightarrow> _::real_normed_vector"
  assumes "set_borel_measurable M X f" "B \<in> sets borel" "X \<in> sets M"
  shows "f -` B \<inter> X \<in> sets M"
proof -
  have "f \<in> borel_measurable (restrict_space M X)"
    using assms by (subst borel_measurable_restrict_space_iff) auto
  then have "f -` B \<inter> space (restrict_space M X) \<in> sets (restrict_space M X)"
    by (rule measurable_sets) fact
  with \<open>X \<in> sets M\<close> show ?thesis
    by (subst (asm) sets_restrict_space_iff) (auto simp: space_restrict_space)
qed

lemma set_lebesgue_integral_cong:
  assumes "A \<in> sets M" and "\<forall>x. x \<in> A \<longrightarrow> f x = g x"
  shows "(LINT x:A|M. f x) = (LINT x:A|M. g x)"
  using assms by (auto intro!: Bochner_Integration.integral_cong split: split_indicator simp add: sets.sets_into_space)

lemma set_lebesgue_integral_cong_AE:
  assumes [measurable]: "A \<in> sets M" "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes "AE x \<in> A in M. f x = g x"
  shows "LINT x:A|M. f x = LINT x:A|M. g x"
proof-
  have "AE x in M. indicator A x *\<^sub>R f x = indicator A x *\<^sub>R g x"
    using assms by auto
  thus ?thesis by (intro integral_cong_AE) auto
qed

lemma set_integrable_cong_AE:
    "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow>
    AE x \<in> A in M. f x = g x \<Longrightarrow> A \<in> sets M \<Longrightarrow>
    set_integrable M A f = set_integrable M A g"
  by (rule integrable_cong_AE) auto

lemma set_integrable_subset:
  fixes M A B and f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "set_integrable M A f" "B \<in> sets M" "B \<subseteq> A"
  shows "set_integrable M B f"
proof -
  have "set_integrable M B (\<lambda>x. indicator A x *\<^sub>R f x)"
    by (rule integrable_mult_indicator) fact+
  with \<open>B \<subseteq> A\<close> show ?thesis
    by (simp add: indicator_inter_arith[symmetric] Int_absorb2)
qed

(* TODO: integral_cmul_indicator should be named set_integral_const *)
(* TODO: borel_integrable_atLeastAtMost should be named something like set_integrable_Icc_isCont *)

lemma set_integral_scaleR_right [simp]: "LINT t:A|M. a *\<^sub>R f t = a *\<^sub>R (LINT t:A|M. f t)"
  by (subst integral_scaleR_right[symmetric]) (auto intro!: Bochner_Integration.integral_cong)

lemma set_integral_mult_right [simp]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "LINT t:A|M. a * f t = a * (LINT t:A|M. f t)"
  by (subst integral_mult_right_zero[symmetric]) auto

lemma set_integral_mult_left [simp]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "LINT t:A|M. f t * a = (LINT t:A|M. f t) * a"
  by (subst integral_mult_left_zero[symmetric]) auto

lemma set_integral_divide_zero [simp]:
  fixes a :: "'a::{real_normed_field, field, second_countable_topology}"
  shows "LINT t:A|M. f t / a = (LINT t:A|M. f t) / a"
  by (subst integral_divide_zero[symmetric], intro Bochner_Integration.integral_cong)
     (auto split: split_indicator)

lemma set_integrable_scaleR_right [simp, intro]:
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. a *\<^sub>R f t)"
  unfolding scaleR_left_commute by (rule integrable_scaleR_right)

lemma set_integrable_scaleR_left [simp, intro]:
  fixes a :: "_ :: {banach, second_countable_topology}"
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. f t *\<^sub>R a)"
  using integrable_scaleR_left[of a M "\<lambda>x. indicator A x *\<^sub>R f x"] by simp

lemma set_integrable_mult_right [simp, intro]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. a * f t)"
  using integrable_mult_right[of a M "\<lambda>x. indicator A x *\<^sub>R f x"] by simp

lemma set_integrable_mult_left [simp, intro]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. f t * a)"
  using integrable_mult_left[of a M "\<lambda>x. indicator A x *\<^sub>R f x"] by simp

lemma set_integrable_divide [simp, intro]:
  fixes a :: "'a::{real_normed_field, field, second_countable_topology}"
  assumes "a \<noteq> 0 \<Longrightarrow> set_integrable M A f"
  shows "set_integrable M A (\<lambda>t. f t / a)"
proof -
  have "integrable M (\<lambda>x. indicator A x *\<^sub>R f x / a)"
    using assms by (rule integrable_divide_zero)
  also have "(\<lambda>x. indicator A x *\<^sub>R f x / a) = (\<lambda>x. indicator A x *\<^sub>R (f x / a))"
    by (auto split: split_indicator)
  finally show ?thesis .
qed

lemma set_integral_add [simp, intro]:
  fixes f g :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "set_integrable M A f" "set_integrable M A g"
  shows "set_integrable M A (\<lambda>x. f x + g x)"
    and "LINT x:A|M. f x + g x = (LINT x:A|M. f x) + (LINT x:A|M. g x)"
  using assms by (simp_all add: scaleR_add_right)

lemma set_integral_diff [simp, intro]:
  assumes "set_integrable M A f" "set_integrable M A g"
  shows "set_integrable M A (\<lambda>x. f x - g x)" and "LINT x:A|M. f x - g x =
    (LINT x:A|M. f x) - (LINT x:A|M. g x)"
  using assms by (simp_all add: scaleR_diff_right)

(* question: why do we have this for negation, but multiplication by a constant
   requires an integrability assumption? *)
lemma set_integral_uminus: "set_integrable M A f \<Longrightarrow> LINT x:A|M. - f x = - (LINT x:A|M. f x)"
  by (subst integral_minus[symmetric]) simp_all

lemma set_integral_complex_of_real:
  "LINT x:A|M. complex_of_real (f x) = of_real (LINT x:A|M. f x)"
  by (subst integral_complex_of_real[symmetric])
     (auto intro!: Bochner_Integration.integral_cong split: split_indicator)

lemma set_integral_mono:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "set_integrable M A f" "set_integrable M A g"
    "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows "(LINT x:A|M. f x) \<le> (LINT x:A|M. g x)"
using assms by (auto intro: integral_mono split: split_indicator)

lemma set_integral_mono_AE:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "set_integrable M A f" "set_integrable M A g"
    "AE x \<in> A in M. f x \<le> g x"
  shows "(LINT x:A|M. f x) \<le> (LINT x:A|M. g x)"
using assms by (auto intro: integral_mono_AE split: split_indicator)

lemma set_integrable_abs: "set_integrable M A f \<Longrightarrow> set_integrable M A (\<lambda>x. \<bar>f x\<bar> :: real)"
  using integrable_abs[of M "\<lambda>x. f x * indicator A x"] by (simp add: abs_mult ac_simps)

lemma set_integrable_abs_iff:
  fixes f :: "_ \<Rightarrow> real"
  shows "set_borel_measurable M A f \<Longrightarrow> set_integrable M A (\<lambda>x. \<bar>f x\<bar>) = set_integrable M A f"
  by (subst (2) integrable_abs_iff[symmetric]) (simp_all add: abs_mult ac_simps)

lemma set_integrable_abs_iff':
  fixes f :: "_ \<Rightarrow> real"
  shows "f \<in> borel_measurable M \<Longrightarrow> A \<in> sets M \<Longrightarrow>
    set_integrable M A (\<lambda>x. \<bar>f x\<bar>) = set_integrable M A f"
by (intro set_integrable_abs_iff) auto

lemma set_integrable_discrete_difference:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "countable X"
  assumes diff: "(A - B) \<union> (B - A) \<subseteq> X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> emeasure M {x} = 0" "\<And>x. x \<in> X \<Longrightarrow> {x} \<in> sets M"
  shows "set_integrable M A f \<longleftrightarrow> set_integrable M B f"
proof (rule integrable_discrete_difference[where X=X])
  show "\<And>x. x \<in> space M \<Longrightarrow> x \<notin> X \<Longrightarrow> indicator A x *\<^sub>R f x = indicator B x *\<^sub>R f x"
    using diff by (auto split: split_indicator)
qed fact+

lemma set_integral_discrete_difference:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "countable X"
  assumes diff: "(A - B) \<union> (B - A) \<subseteq> X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> emeasure M {x} = 0" "\<And>x. x \<in> X \<Longrightarrow> {x} \<in> sets M"
  shows "set_lebesgue_integral M A f = set_lebesgue_integral M B f"
proof (rule integral_discrete_difference[where X=X])
  show "\<And>x. x \<in> space M \<Longrightarrow> x \<notin> X \<Longrightarrow> indicator A x *\<^sub>R f x = indicator B x *\<^sub>R f x"
    using diff by (auto split: split_indicator)
qed fact+

lemma set_integrable_Un:
  fixes f g :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes f_A: "set_integrable M A f" and f_B:  "set_integrable M B f"
    and [measurable]: "A \<in> sets M" "B \<in> sets M"
  shows "set_integrable M (A \<union> B) f"
proof -
  have "set_integrable M (A - B) f"
    using f_A by (rule set_integrable_subset) auto
  from Bochner_Integration.integrable_add[OF this f_B] show ?thesis
    by (rule integrable_cong[THEN iffD1, rotated 2]) (auto split: split_indicator)
qed

lemma set_integrable_UN:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "finite I" "\<And>i. i\<in>I \<Longrightarrow> set_integrable M (A i) f"
    "\<And>i. i\<in>I \<Longrightarrow> A i \<in> sets M"
  shows "set_integrable M (\<Union>i\<in>I. A i) f"
using assms by (induct I) (auto intro!: set_integrable_Un)

lemma set_integral_Un:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "A \<inter> B = {}"
  and "set_integrable M A f"
  and "set_integrable M B f"
  shows "LINT x:A\<union>B|M. f x = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
by (auto simp add: indicator_union_arith indicator_inter_arith[symmetric]
      scaleR_add_left assms)

lemma set_integral_cong_set:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes [measurable]: "set_borel_measurable M A f" "set_borel_measurable M B f"
    and ae: "AE x in M. x \<in> A \<longleftrightarrow> x \<in> B"
  shows "LINT x:B|M. f x = LINT x:A|M. f x"
proof (rule integral_cong_AE)
  show "AE x in M. indicator B x *\<^sub>R f x = indicator A x *\<^sub>R f x"
    using ae by (auto simp: subset_eq split: split_indicator)
qed fact+

lemma set_borel_measurable_subset:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes [measurable]: "set_borel_measurable M A f" "B \<in> sets M" and "B \<subseteq> A"
  shows "set_borel_measurable M B f"
proof -
  have "set_borel_measurable M B (\<lambda>x. indicator A x *\<^sub>R f x)"
    by measurable
  also have "(\<lambda>x. indicator B x *\<^sub>R indicator A x *\<^sub>R f x) = (\<lambda>x. indicator B x *\<^sub>R f x)"
    using \<open>B \<subseteq> A\<close> by (auto simp: fun_eq_iff split: split_indicator)
  finally show ?thesis .
qed

lemma set_integral_Un_AE:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes ae: "AE x in M. \<not> (x \<in> A \<and> x \<in> B)" and [measurable]: "A \<in> sets M" "B \<in> sets M"
  and "set_integrable M A f"
  and "set_integrable M B f"
  shows "LINT x:A\<union>B|M. f x = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
proof -
  have f: "set_integrable M (A \<union> B) f"
    by (intro set_integrable_Un assms)
  then have f': "set_borel_measurable M (A \<union> B) f"
    by (rule borel_measurable_integrable)
  have "LINT x:A\<union>B|M. f x = LINT x:(A - A \<inter> B) \<union> (B - A \<inter> B)|M. f x"
  proof (rule set_integral_cong_set)
    show "AE x in M. (x \<in> A - A \<inter> B \<union> (B - A \<inter> B)) = (x \<in> A \<union> B)"
      using ae by auto
    show "set_borel_measurable M (A - A \<inter> B \<union> (B - A \<inter> B)) f"
      using f' by (rule set_borel_measurable_subset) auto
  qed fact
  also have "\<dots> = (LINT x:(A - A \<inter> B)|M. f x) + (LINT x:(B - A \<inter> B)|M. f x)"
    by (auto intro!: set_integral_Un set_integrable_subset[OF f])
  also have "\<dots> = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
    using ae
    by (intro arg_cong2[where f="op+"] set_integral_cong_set)
       (auto intro!: set_borel_measurable_subset[OF f'])
  finally show ?thesis .
qed

lemma set_integral_finite_Union:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "finite I" "disjoint_family_on A I"
    and "\<And>i. i \<in> I \<Longrightarrow> set_integrable M (A i) f" "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M"
  shows "(LINT x:(\<Union>i\<in>I. A i)|M. f x) = (\<Sum>i\<in>I. LINT x:A i|M. f x)"
  using assms
  apply induct
  apply (auto intro!: set_integral_Un set_integrable_Un set_integrable_UN simp: disjoint_family_on_def)
by (subst set_integral_Un, auto intro: set_integrable_UN)

(* TODO: find a better name? *)
lemma pos_integrable_to_top:
  fixes l::real
  assumes "\<And>i. A i \<in> sets M" "mono A"
  assumes nneg: "\<And>x i. x \<in> A i \<Longrightarrow> 0 \<le> f x"
  and intgbl: "\<And>i::nat. set_integrable M (A i) f"
  and lim: "(\<lambda>i::nat. LINT x:A i|M. f x) \<longlonglongrightarrow> l"
  shows "set_integrable M (\<Union>i. A i) f"
  apply (rule integrable_monotone_convergence[where f = "\<lambda>i::nat. \<lambda>x. indicator (A i) x *\<^sub>R f x" and x = l])
  apply (rule intgbl)
  prefer 3 apply (rule lim)
  apply (rule AE_I2)
  using \<open>mono A\<close> apply (auto simp: mono_def nneg split: split_indicator) []
proof (rule AE_I2)
  { fix x assume "x \<in> space M"
    show "(\<lambda>i. indicator (A i) x *\<^sub>R f x) \<longlonglongrightarrow> indicator (\<Union>i. A i) x *\<^sub>R f x"
    proof cases
      assume "\<exists>i. x \<in> A i"
      then guess i ..
      then have *: "eventually (\<lambda>i. x \<in> A i) sequentially"
        using \<open>x \<in> A i\<close> \<open>mono A\<close> by (auto simp: eventually_sequentially mono_def)
      show ?thesis
        apply (intro Lim_eventually)
        using *
        apply eventually_elim
        apply (auto split: split_indicator)
        done
    qed auto }
  then show "(\<lambda>x. indicator (\<Union>i. A i) x *\<^sub>R f x) \<in> borel_measurable M"
    apply (rule borel_measurable_LIMSEQ_real)
    apply assumption
    apply (intro borel_measurable_integrable intgbl)
    done
qed

(* Proof from Royden Real Analysis, p. 91. *)
lemma lebesgue_integral_countable_add:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes meas[intro]: "\<And>i::nat. A i \<in> sets M"
    and disj: "\<And>i j. i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
    and intgbl: "set_integrable M (\<Union>i. A i) f"
  shows "LINT x:(\<Union>i. A i)|M. f x = (\<Sum>i. (LINT x:(A i)|M. f x))"
proof (subst integral_suminf[symmetric])
  show int_A: "\<And>i. set_integrable M (A i) f"
    using intgbl by (rule set_integrable_subset) auto
  { fix x assume "x \<in> space M"
    have "(\<lambda>i. indicator (A i) x *\<^sub>R f x) sums (indicator (\<Union>i. A i) x *\<^sub>R f x)"
      by (intro sums_scaleR_left indicator_sums) fact }
  note sums = this

  have norm_f: "\<And>i. set_integrable M (A i) (\<lambda>x. norm (f x))"
    using int_A[THEN integrable_norm] by auto

  show "AE x in M. summable (\<lambda>i. norm (indicator (A i) x *\<^sub>R f x))"
    using disj by (intro AE_I2) (auto intro!: summable_mult2 sums_summable[OF indicator_sums])

  show "summable (\<lambda>i. LINT x|M. norm (indicator (A i) x *\<^sub>R f x))"
  proof (rule summableI_nonneg_bounded)
    fix n
    show "0 \<le> LINT x|M. norm (indicator (A n) x *\<^sub>R f x)"
      using norm_f by (auto intro!: integral_nonneg_AE)

    have "(\<Sum>i<n. LINT x|M. norm (indicator (A i) x *\<^sub>R f x)) =
      (\<Sum>i<n. set_lebesgue_integral M (A i) (\<lambda>x. norm (f x)))"
      by (simp add: abs_mult)
    also have "\<dots> = set_lebesgue_integral M (\<Union>i<n. A i) (\<lambda>x. norm (f x))"
      using norm_f
      by (subst set_integral_finite_Union) (auto simp: disjoint_family_on_def disj)
    also have "\<dots> \<le> set_lebesgue_integral M (\<Union>i. A i) (\<lambda>x. norm (f x))"
      using intgbl[THEN integrable_norm]
      by (intro integral_mono set_integrable_UN[of "{..<n}"] norm_f)
         (auto split: split_indicator)
    finally show "(\<Sum>i<n. LINT x|M. norm (indicator (A i) x *\<^sub>R f x)) \<le>
      set_lebesgue_integral M (\<Union>i. A i) (\<lambda>x. norm (f x))"
      by simp
  qed
  show "set_lebesgue_integral M (UNION UNIV A) f = LINT x|M. (\<Sum>i. indicator (A i) x *\<^sub>R f x)"
    apply (rule Bochner_Integration.integral_cong[OF refl])
    apply (subst suminf_scaleR_left[OF sums_summable[OF indicator_sums, OF disj], symmetric])
    using sums_unique[OF indicator_sums[OF disj]]
    apply auto
    done
qed

lemma set_integral_cont_up:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes [measurable]: "\<And>i. A i \<in> sets M" and A: "incseq A"
  and intgbl: "set_integrable M (\<Union>i. A i) f"
  shows "(\<lambda>i. LINT x:(A i)|M. f x) \<longlonglongrightarrow> LINT x:(\<Union>i. A i)|M. f x"
proof (intro integral_dominated_convergence[where w="\<lambda>x. indicator (\<Union>i. A i) x *\<^sub>R norm (f x)"])
  have int_A: "\<And>i. set_integrable M (A i) f"
    using intgbl by (rule set_integrable_subset) auto
  then show "\<And>i. set_borel_measurable M (A i) f" "set_borel_measurable M (\<Union>i. A i) f"
    "set_integrable M (\<Union>i. A i) (\<lambda>x. norm (f x))"
    using intgbl integrable_norm[OF intgbl] by auto

  { fix x i assume "x \<in> A i"
    with A have "(\<lambda>xa. indicator (A xa) x::real) \<longlonglongrightarrow> 1 \<longleftrightarrow> (\<lambda>xa. 1::real) \<longlonglongrightarrow> 1"
      by (intro filterlim_cong refl)
         (fastforce simp: eventually_sequentially incseq_def subset_eq intro!: exI[of _ i]) }
  then show "AE x in M. (\<lambda>i. indicator (A i) x *\<^sub>R f x) \<longlonglongrightarrow> indicator (\<Union>i. A i) x *\<^sub>R f x"
    by (intro AE_I2 tendsto_intros) (auto split: split_indicator)
qed (auto split: split_indicator)

(* Can the int0 hypothesis be dropped? *)
lemma set_integral_cont_down:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes [measurable]: "\<And>i. A i \<in> sets M" and A: "decseq A"
  and int0: "set_integrable M (A 0) f"
  shows "(\<lambda>i::nat. LINT x:(A i)|M. f x) \<longlonglongrightarrow> LINT x:(\<Inter>i. A i)|M. f x"
proof (rule integral_dominated_convergence)
  have int_A: "\<And>i. set_integrable M (A i) f"
    using int0 by (rule set_integrable_subset) (insert A, auto simp: decseq_def)
  show "set_integrable M (A 0) (\<lambda>x. norm (f x))"
    using int0[THEN integrable_norm] by simp
  have "set_integrable M (\<Inter>i. A i) f"
    using int0 by (rule set_integrable_subset) (insert A, auto simp: decseq_def)
  with int_A show "set_borel_measurable M (\<Inter>i. A i) f" "\<And>i. set_borel_measurable M (A i) f"
    by auto
  show "\<And>i. AE x in M. norm (indicator (A i) x *\<^sub>R f x) \<le> indicator (A 0) x *\<^sub>R norm (f x)"
    using A by (auto split: split_indicator simp: decseq_def)
  { fix x i assume "x \<in> space M" "x \<notin> A i"
    with A have "(\<lambda>i. indicator (A i) x::real) \<longlonglongrightarrow> 0 \<longleftrightarrow> (\<lambda>i. 0::real) \<longlonglongrightarrow> 0"
      by (intro filterlim_cong refl)
         (auto split: split_indicator simp: eventually_sequentially decseq_def intro!: exI[of _ i]) }
  then show "AE x in M. (\<lambda>i. indicator (A i) x *\<^sub>R f x) \<longlonglongrightarrow> indicator (\<Inter>i. A i) x *\<^sub>R f x"
    by (intro AE_I2 tendsto_intros) (auto split: split_indicator)
qed

lemma set_integral_at_point:
  fixes a :: real
  assumes "set_integrable M {a} f"
  and [simp]: "{a} \<in> sets M" and "(emeasure M) {a} \<noteq> \<infinity>"
  shows "(LINT x:{a} | M. f x) = f a * measure M {a}"
proof-
  have "set_lebesgue_integral M {a} f = set_lebesgue_integral M {a} (%x. f a)"
    by (intro set_lebesgue_integral_cong) simp_all
  then show ?thesis using assms by simp
qed


abbreviation complex_integrable :: "'a measure \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> bool" where
  "complex_integrable M f \<equiv> integrable M f"

abbreviation complex_lebesgue_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> complex" ("integral\<^sup>C") where
  "integral\<^sup>C M f == integral\<^sup>L M f"

syntax
  "_complex_lebesgue_integral" :: "pttrn \<Rightarrow> complex \<Rightarrow> 'a measure \<Rightarrow> complex"
 ("\<integral>\<^sup>C _. _ \<partial>_" [60,61] 110)

translations
  "\<integral>\<^sup>Cx. f \<partial>M" == "CONST complex_lebesgue_integral M (\<lambda>x. f)"

syntax
  "_ascii_complex_lebesgue_integral" :: "pttrn \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
  ("(3CLINT _|_. _)" [0,110,60] 60)

translations
  "CLINT x|M. f" == "CONST complex_lebesgue_integral M (\<lambda>x. f)"

lemma complex_integrable_cnj [simp]:
  "complex_integrable M (\<lambda>x. cnj (f x)) \<longleftrightarrow> complex_integrable M f"
proof
  assume "complex_integrable M (\<lambda>x. cnj (f x))"
  then have "complex_integrable M (\<lambda>x. cnj (cnj (f x)))"
    by (rule integrable_cnj)
  then show "complex_integrable M f"
    by simp
qed simp

lemma complex_of_real_integrable_eq:
  "complex_integrable M (\<lambda>x. complex_of_real (f x)) \<longleftrightarrow> integrable M f"
proof
  assume "complex_integrable M (\<lambda>x. complex_of_real (f x))"
  then have "integrable M (\<lambda>x. Re (complex_of_real (f x)))"
    by (rule integrable_Re)
  then show "integrable M f"
    by simp
qed simp


abbreviation complex_set_integrable :: "'a measure \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> bool" where
  "complex_set_integrable M A f \<equiv> set_integrable M A f"

abbreviation complex_set_lebesgue_integral :: "'a measure \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> complex" where
  "complex_set_lebesgue_integral M A f \<equiv> set_lebesgue_integral M A f"

syntax
"_ascii_complex_set_lebesgue_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(4CLINT _:_|_. _)" [0,60,110,61] 60)

translations
"CLINT x:A|M. f" == "CONST complex_set_lebesgue_integral M A (\<lambda>x. f)"

lemma set_measurable_continuous_on_ivl:
  assumes "continuous_on {a..b} (f :: real \<Rightarrow> real)"
  shows "set_borel_measurable borel {a..b} f"
  by (rule borel_measurable_continuous_on_indicator[OF _ assms]) simp


text\<open>This notation is from Sébastien Gouëzel: His use is not directly in line with the
notations in this file, they are more in line with sum, and more readable he thinks.\<close>

abbreviation "set_nn_integral M A f \<equiv> nn_integral M (\<lambda>x. f x * indicator A x)"

syntax
"_set_nn_integral" :: "pttrn => 'a set => 'a measure => ereal => ereal"
("(\<integral>\<^sup>+((_)\<in>(_)./ _)/\<partial>_)" [0,60,110,61] 60)

"_set_lebesgue_integral" :: "pttrn => 'a set => 'a measure => ereal => ereal"
("(\<integral>((_)\<in>(_)./ _)/\<partial>_)" [0,60,110,61] 60)

translations
"\<integral>\<^sup>+x \<in> A. f \<partial>M" == "CONST set_nn_integral M A (\<lambda>x. f)"
"\<integral>x \<in> A. f \<partial>M" == "CONST set_lebesgue_integral M A (\<lambda>x. f)"

lemma nn_integral_disjoint_pair:
  assumes [measurable]: "f \<in> borel_measurable M"
          "B \<in> sets M" "C \<in> sets M"
          "B \<inter> C = {}"
  shows "(\<integral>\<^sup>+x \<in> B \<union> C. f x \<partial>M) = (\<integral>\<^sup>+x \<in> B. f x \<partial>M) + (\<integral>\<^sup>+x \<in> C. f x \<partial>M)"
proof -
  have mes: "\<And>D. D \<in> sets M \<Longrightarrow> (\<lambda>x. f x * indicator D x) \<in> borel_measurable M" by simp
  have pos: "\<And>D. AE x in M. f x * indicator D x \<ge> 0" using assms(2) by auto
  have "\<And>x. f x * indicator (B \<union> C) x = f x * indicator B x + f x * indicator C x" using assms(4)
    by (auto split: split_indicator)
  then have "(\<integral>\<^sup>+x. f x * indicator (B \<union> C) x \<partial>M) = (\<integral>\<^sup>+x. f x * indicator B x + f x * indicator C x \<partial>M)"
    by simp
  also have "... = (\<integral>\<^sup>+x. f x * indicator B x \<partial>M) + (\<integral>\<^sup>+x. f x * indicator C x \<partial>M)"
    by (rule nn_integral_add) (auto simp add: assms mes pos)
  finally show ?thesis by simp
qed

lemma nn_integral_disjoint_pair_countspace:
  assumes "B \<inter> C = {}"
  shows "(\<integral>\<^sup>+x \<in> B \<union> C. f x \<partial>count_space UNIV) = (\<integral>\<^sup>+x \<in> B. f x \<partial>count_space UNIV) + (\<integral>\<^sup>+x \<in> C. f x \<partial>count_space UNIV)"
by (rule nn_integral_disjoint_pair) (simp_all add: assms)

lemma nn_integral_null_delta:
  assumes "A \<in> sets M" "B \<in> sets M"
          "(A - B) \<union> (B - A) \<in> null_sets M"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+x \<in> B. f x \<partial>M)"
proof (rule nn_integral_cong_AE, auto simp add: indicator_def)
  have *: "AE a in M. a \<notin> (A - B) \<union> (B - A)"
    using assms(3) AE_not_in by blast
  then show "AE a in M. a \<notin> A \<longrightarrow> a \<in> B \<longrightarrow> f a = 0"
    by auto
  show "AE x\<in>A in M. x \<notin> B \<longrightarrow> f x = 0"
    using * by auto
qed

lemma nn_integral_disjoint_family:
  assumes [measurable]: "f \<in> borel_measurable M" "\<And>(n::nat). B n \<in> sets M"
      and "disjoint_family B"
  shows "(\<integral>\<^sup>+x \<in> (\<Union>n. B n). f x \<partial>M) = (\<Sum>n. (\<integral>\<^sup>+x \<in> B n. f x \<partial>M))"
proof -
  have "(\<integral>\<^sup>+ x. (\<Sum>n. f x * indicator (B n) x) \<partial>M) = (\<Sum>n. (\<integral>\<^sup>+ x. f x * indicator (B n) x \<partial>M))"
    by (rule nn_integral_suminf) simp
  moreover have "(\<Sum>n. f x * indicator (B n) x) = f x * indicator (\<Union>n. B n) x" for x
  proof (cases)
    assume "x \<in> (\<Union>n. B n)"
    then obtain n where "x \<in> B n" by blast
    have a: "finite {n}" by simp
    have "\<And>i. i \<noteq> n \<Longrightarrow> x \<notin> B i" using \<open>x \<in> B n\<close> assms(3) disjoint_family_on_def
      by (metis IntI UNIV_I empty_iff)
    then have "\<And>i. i \<notin> {n} \<Longrightarrow> indicator (B i) x = (0::ennreal)" using indicator_def by simp
    then have b: "\<And>i. i \<notin> {n} \<Longrightarrow> f x * indicator (B i) x = (0::ennreal)" by simp

    define h where "h = (\<lambda>i. f x * indicator (B i) x)"
    then have "\<And>i. i \<notin> {n} \<Longrightarrow> h i = 0" using b by simp
    then have "(\<Sum>i. h i) = (\<Sum>i\<in>{n}. h i)"
      by (metis sums_unique[OF sums_finite[OF a]])
    then have "(\<Sum>i. h i) = h n" by simp
    then have "(\<Sum>n. f x * indicator (B n) x) = f x * indicator (B n) x" using h_def by simp
    then have "(\<Sum>n. f x * indicator (B n) x) = f x" using \<open>x \<in> B n\<close> indicator_def by simp
    then show ?thesis using \<open>x \<in> (\<Union>n. B n)\<close> by auto
  next
    assume "x \<notin> (\<Union>n. B n)"
    then have "\<And>n. f x * indicator (B n) x = 0" by simp
    have "(\<Sum>n. f x * indicator (B n) x) = 0"
      by (simp add: \<open>\<And>n. f x * indicator (B n) x = 0\<close>)
    then show ?thesis using \<open>x \<notin> (\<Union>n. B n)\<close> by auto
  qed
  ultimately show ?thesis by simp
qed

lemma nn_set_integral_add:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
          "A \<in> sets M"
  shows "(\<integral>\<^sup>+x \<in> A. (f x + g x) \<partial>M) = (\<integral>\<^sup>+x \<in> A. f x \<partial>M) + (\<integral>\<^sup>+x \<in> A. g x \<partial>M)"
proof -
  have "(\<integral>\<^sup>+x \<in> A. (f x + g x) \<partial>M) = (\<integral>\<^sup>+x. (f x * indicator A x + g x * indicator A x) \<partial>M)"
    by (auto simp add: indicator_def intro!: nn_integral_cong)
  also have "... = (\<integral>\<^sup>+x. f x * indicator A x \<partial>M) + (\<integral>\<^sup>+x. g x * indicator A x \<partial>M)"
    apply (rule nn_integral_add) using assms(1) assms(2) by auto
  finally show ?thesis by simp
qed

lemma nn_set_integral_cong:
  assumes "AE x in M. f x = g x"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+x \<in> A. g x \<partial>M)"
apply (rule nn_integral_cong_AE) using assms(1) by auto

lemma nn_set_integral_set_mono:
  "A \<subseteq> B \<Longrightarrow> (\<integral>\<^sup>+ x \<in> A. f x \<partial>M) \<le> (\<integral>\<^sup>+ x \<in> B. f x \<partial>M)"
by (auto intro!: nn_integral_mono split: split_indicator)

lemma nn_set_integral_mono:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
          "A \<in> sets M"
      and "AE x\<in>A in M. f x \<le> g x"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) \<le> (\<integral>\<^sup>+x \<in> A. g x \<partial>M)"
by (auto intro!: nn_integral_mono_AE split: split_indicator simp: assms)

lemma nn_set_integral_space [simp]:
  shows "(\<integral>\<^sup>+ x \<in> space M. f x \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M)"
by (metis (mono_tags, lifting) indicator_simps(1) mult.right_neutral nn_integral_cong)

lemma nn_integral_count_compose_inj:
  assumes "inj_on g A"
  shows "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+y \<in> g`A. f y \<partial>count_space UNIV)"
proof -
  have "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+x. f (g x) \<partial>count_space A)"
    by (auto simp add: nn_integral_count_space_indicator[symmetric])
  also have "... = (\<integral>\<^sup>+y. f y \<partial>count_space (g`A))"
    by (simp add: assms nn_integral_bij_count_space inj_on_imp_bij_betw)
  also have "... = (\<integral>\<^sup>+y \<in> g`A. f y \<partial>count_space UNIV)"
    by (auto simp add: nn_integral_count_space_indicator[symmetric])
  finally show ?thesis by simp
qed

lemma nn_integral_count_compose_bij:
  assumes "bij_betw g A B"
  shows "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+y \<in> B. f y \<partial>count_space UNIV)"
proof -
  have "inj_on g A" using assms bij_betw_def by auto
  then have "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+y \<in> g`A. f y \<partial>count_space UNIV)"
    by (rule nn_integral_count_compose_inj)
  then show ?thesis using assms by (simp add: bij_betw_def)
qed

lemma set_integral_null_delta:
  fixes f::"_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes [measurable]: "integrable M f" "A \<in> sets M" "B \<in> sets M"
    and "(A - B) \<union> (B - A) \<in> null_sets M"
  shows "(\<integral>x \<in> A. f x \<partial>M) = (\<integral>x \<in> B. f x \<partial>M)"
proof (rule set_integral_cong_set, auto)
  have *: "AE a in M. a \<notin> (A - B) \<union> (B - A)"
    using assms(4) AE_not_in by blast
  then show "AE x in M. (x \<in> B) = (x \<in> A)"
    by auto
qed

lemma set_integral_space:
  assumes "integrable M f"
  shows "(\<integral>x \<in> space M. f x \<partial>M) = (\<integral>x. f x \<partial>M)"
by (metis (mono_tags, lifting) indicator_simps(1) Bochner_Integration.integral_cong real_vector.scale_one)

lemma null_if_pos_func_has_zero_nn_int:
  fixes f::"'a \<Rightarrow> ennreal"
  assumes [measurable]: "f \<in> borel_measurable M" "A \<in> sets M"
    and "AE x\<in>A in M. f x > 0" "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) = 0"
  shows "A \<in> null_sets M"
proof -
  have "AE x in M. f x * indicator A x = 0"
    by (subst nn_integral_0_iff_AE[symmetric], auto simp add: assms(4))
  then have "AE x\<in>A in M. False" using assms(3) by auto
  then show "A \<in> null_sets M" using assms(2) by (simp add: AE_iff_null_sets)
qed

lemma null_if_pos_func_has_zero_int:
  assumes [measurable]: "integrable M f" "A \<in> sets M"
      and "AE x\<in>A in M. f x > 0" "(\<integral>x\<in>A. f x \<partial>M) = (0::real)"
  shows "A \<in> null_sets M"
proof -
  have "AE x in M. indicator A x * f x = 0"
    apply (subst integral_nonneg_eq_0_iff_AE[symmetric])
    using assms integrable_mult_indicator[OF \<open>A \<in> sets M\<close> assms(1)] by auto
  then have "AE x\<in>A in M. f x = 0" by auto
  then have "AE x\<in>A in M. False" using assms(3) by auto
  then show "A \<in> null_sets M" using assms(2) by (simp add: AE_iff_null_sets)
qed

text\<open>The next lemma is a variant of \<open>density_unique\<close>. Note that it uses the notation
for nonnegative set integrals introduced earlier.\<close>

lemma (in sigma_finite_measure) density_unique2:
  assumes [measurable]: "f \<in> borel_measurable M" "f' \<in> borel_measurable M"
  assumes density_eq: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>\<^sup>+ x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+ x \<in> A. f' x \<partial>M)"
  shows "AE x in M. f x = f' x"
proof (rule density_unique)
  show "density M f = density M f'"
    by (intro measure_eqI) (auto simp: emeasure_density intro!: density_eq)
qed (auto simp add: assms)


text \<open>The next lemma implies the same statement for Banach-space valued functions
using Hahn-Banach theorem and linear forms. Since they are not yet easily available, I
only formulate it for real-valued functions.\<close>

lemma density_unique_real:
  fixes f f'::"_ \<Rightarrow> real"
  assumes [measurable]: "integrable M f" "integrable M f'"
  assumes density_eq: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>x \<in> A. f x \<partial>M) = (\<integral>x \<in> A. f' x \<partial>M)"
  shows "AE x in M. f x = f' x"
proof -
  define A where "A = {x \<in> space M. f x < f' x}"
  then have [measurable]: "A \<in> sets M" by simp
  have "(\<integral>x \<in> A. (f' x - f x) \<partial>M) = (\<integral>x \<in> A. f' x \<partial>M) - (\<integral>x \<in> A. f x \<partial>M)"
    using \<open>A \<in> sets M\<close> assms(1) assms(2) integrable_mult_indicator by blast
  then have "(\<integral>x \<in> A. (f' x - f x) \<partial>M) = 0" using assms(3) by simp
  then have "A \<in> null_sets M"
    using A_def null_if_pos_func_has_zero_int[where ?f = "\<lambda>x. f' x - f x" and ?A = A] assms by auto
  then have "AE x in M. x \<notin> A" by (simp add: AE_not_in)
  then have *: "AE x in M. f' x \<le> f x" unfolding A_def by auto


  define B where "B = {x \<in> space M. f' x < f x}"
  then have [measurable]: "B \<in> sets M" by simp
  have "(\<integral>x \<in> B. (f x - f' x) \<partial>M) = (\<integral>x \<in> B. f x \<partial>M) - (\<integral>x \<in> B. f' x \<partial>M)"
    using \<open>B \<in> sets M\<close> assms(1) assms(2) integrable_mult_indicator by blast
  then have "(\<integral>x \<in> B. (f x - f' x) \<partial>M) = 0" using assms(3) by simp
  then have "B \<in> null_sets M"
    using B_def null_if_pos_func_has_zero_int[where ?f = "\<lambda>x. f x - f' x" and ?A = B] assms by auto
  then have "AE x in M. x \<notin> B" by (simp add: AE_not_in)
  then have "AE x in M. f' x \<ge> f x" unfolding B_def by auto

  then show ?thesis using * by auto
qed

text \<open>The next lemma shows that $L^1$ convergence of a sequence of functions follows from almost
everywhere convergence and the weaker condition of the convergence of the integrated norms (or even
just the nontrivial inequality about them). Useful in a lot of contexts! This statement (or its
variations) are known as Scheffe lemma.

The formalization is more painful as one should jump back and forth between reals and ereals and justify
all the time positivity or integrability (thankfully, measurability is handled more or less automatically).\<close>

lemma Scheffe_lemma1:
  assumes "\<And>n. integrable M (F n)" "integrable M f"
          "AE x in M. (\<lambda>n. F n x) \<longlonglongrightarrow> f x"
          "limsup (\<lambda>n. \<integral>\<^sup>+ x. norm(F n x) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f x) \<partial>M)"
  shows "(\<lambda>n. \<integral>\<^sup>+ x. norm(F n x - f x) \<partial>M) \<longlonglongrightarrow> 0"
proof -
  have [measurable]: "\<And>n. F n \<in> borel_measurable M" "f \<in> borel_measurable M"
    using assms(1) assms(2) by simp_all
  define G where "G = (\<lambda>n x. norm(f x) + norm(F n x) - norm(F n x - f x))"
  have [measurable]: "\<And>n. G n \<in> borel_measurable M" unfolding G_def by simp
  have G_pos[simp]: "\<And>n x. G n x \<ge> 0"
    unfolding G_def by (metis ge_iff_diff_ge_0 norm_minus_commute norm_triangle_ineq4)
  have finint: "(\<integral>\<^sup>+ x. norm(f x) \<partial>M) \<noteq> \<infinity>"
    using has_bochner_integral_implies_finite_norm[OF has_bochner_integral_integrable[OF \<open>integrable M f\<close>]]
    by simp
  then have fin2: "2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M) \<noteq> \<infinity>"
    by (auto simp: ennreal_mult_eq_top_iff)

  {
    fix x assume *: "(\<lambda>n. F n x) \<longlonglongrightarrow> f x"
    then have "(\<lambda>n. norm(F n x)) \<longlonglongrightarrow> norm(f x)" using tendsto_norm by blast
    moreover have "(\<lambda>n. norm(F n x - f x)) \<longlonglongrightarrow> 0" using * Lim_null tendsto_norm_zero_iff by fastforce
    ultimately have a: "(\<lambda>n. norm(F n x) - norm(F n x - f x)) \<longlonglongrightarrow> norm(f x)" using tendsto_diff by fastforce
    have "(\<lambda>n. norm(f x) + (norm(F n x) - norm(F n x - f x))) \<longlonglongrightarrow> norm(f x) + norm(f x)"
      by (rule tendsto_add) (auto simp add: a)
    moreover have "\<And>n. G n x = norm(f x) + (norm(F n x) - norm(F n x - f x))" unfolding G_def by simp
    ultimately have "(\<lambda>n. G n x) \<longlonglongrightarrow> 2 * norm(f x)" by simp
    then have "(\<lambda>n. ennreal(G n x)) \<longlonglongrightarrow> ennreal(2 * norm(f x))" by simp
    then have "liminf (\<lambda>n. ennreal(G n x)) = ennreal(2 * norm(f x))"
      using sequentially_bot tendsto_iff_Liminf_eq_Limsup by blast
  }
  then have "AE x in M. liminf (\<lambda>n. ennreal(G n x)) = ennreal(2 * norm(f x))" using assms(3) by auto
  then have "(\<integral>\<^sup>+ x. liminf (\<lambda>n. ennreal (G n x)) \<partial>M) = (\<integral>\<^sup>+ x. 2 * ennreal(norm(f x)) \<partial>M)"
    by (simp add: nn_integral_cong_AE ennreal_mult)
  also have "... = 2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M)" by (rule nn_integral_cmult) auto
  finally have int_liminf: "(\<integral>\<^sup>+ x. liminf (\<lambda>n. ennreal (G n x)) \<partial>M) = 2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M)"
    by simp

  have "(\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) = (\<integral>\<^sup>+x. norm(f x) \<partial>M) + (\<integral>\<^sup>+x. norm(F n x) \<partial>M)" for n
    by (rule nn_integral_add) (auto simp add: assms)
  then have "limsup (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M)) =
      limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(f x) \<partial>M) + (\<integral>\<^sup>+x. norm(F n x) \<partial>M))"
    by simp
  also have "... = (\<integral>\<^sup>+x. norm(f x) \<partial>M) + limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x) \<partial>M))"
    by (rule Limsup_const_add, auto simp add: finint)
  also have "... \<le> (\<integral>\<^sup>+x. norm(f x) \<partial>M) + (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    using assms(4) by (simp add: add_left_mono)
  also have "... = 2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    unfolding one_add_one[symmetric] distrib_right by simp
  ultimately have a: "limsup (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M)) \<le>
    2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M)" by simp

  have le: "ennreal (norm (F n x - f x)) \<le> ennreal (norm (f x)) + ennreal (norm (F n x))" for n x
    by (simp add: norm_minus_commute norm_triangle_ineq4 ennreal_plus[symmetric] ennreal_minus del: ennreal_plus)
  then have le2: "(\<integral>\<^sup>+ x. ennreal (norm (F n x - f x)) \<partial>M) \<le> (\<integral>\<^sup>+ x. ennreal (norm (f x)) + ennreal (norm (F n x)) \<partial>M)" for n
    by (rule nn_integral_mono)

  have "2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M) = (\<integral>\<^sup>+ x. liminf (\<lambda>n. ennreal (G n x)) \<partial>M)"
    by (simp add: int_liminf)
  also have "\<dots> \<le> liminf (\<lambda>n. (\<integral>\<^sup>+x. G n x \<partial>M))"
    by (rule nn_integral_liminf) auto
  also have "liminf (\<lambda>n. (\<integral>\<^sup>+x. G n x \<partial>M)) =
    liminf (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M))"
  proof (intro arg_cong[where f=liminf] ext)
    fix n
    have "\<And>x. ennreal(G n x) = ennreal(norm(f x)) + ennreal(norm(F n x)) - ennreal(norm(F n x - f x))"
      unfolding G_def by (simp add: ennreal_plus[symmetric] ennreal_minus del: ennreal_plus)
    moreover have "(\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) - ennreal(norm(F n x - f x)) \<partial>M)
            = (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)"
    proof (rule nn_integral_diff)
      from le show "AE x in M. ennreal (norm (F n x - f x)) \<le> ennreal (norm (f x)) + ennreal (norm (F n x))"
        by simp
      from le2 have "(\<integral>\<^sup>+x. ennreal (norm (F n x - f x)) \<partial>M) < \<infinity>" using assms(1) assms(2)
        by (metis has_bochner_integral_implies_finite_norm integrable.simps Bochner_Integration.integrable_diff)
      then show "(\<integral>\<^sup>+x. ennreal (norm (F n x - f x)) \<partial>M) \<noteq> \<infinity>" by simp
    qed (auto simp add: assms)
    ultimately show "(\<integral>\<^sup>+x. G n x \<partial>M) = (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)"
      by simp
  qed
  finally have "2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M) + limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) \<le>
    liminf (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) +
    limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M))"
    by (intro add_mono) auto
  also have "\<dots> \<le> (limsup (\<lambda>n. \<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - limsup (\<lambda>n. \<integral>\<^sup>+x. norm (F n x - f x) \<partial>M)) +
    limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M))"
    by (intro add_mono liminf_minus_ennreal le2) auto
  also have "\<dots> = limsup (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M))"
    by (intro diff_add_cancel_ennreal Limsup_mono always_eventually allI le2)
  also have "\<dots> \<le> 2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    by fact
  finally have "limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) = 0"
    using fin2 by simp
  then show ?thesis
    by (rule tendsto_0_if_Limsup_eq_0_ennreal)
qed

lemma Scheffe_lemma2:
  fixes F::"nat \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "\<And> n::nat. F n \<in> borel_measurable M" "integrable M f"
          "AE x in M. (\<lambda>n. F n x) \<longlonglongrightarrow> f x"
          "\<And>n. (\<integral>\<^sup>+ x. norm(F n x) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f x) \<partial>M)"
  shows "(\<lambda>n. \<integral>\<^sup>+ x. norm(F n x - f x) \<partial>M) \<longlonglongrightarrow> 0"
proof (rule Scheffe_lemma1)
  fix n::nat
  have "(\<integral>\<^sup>+ x. norm(f x) \<partial>M) < \<infinity>" using assms(2) by (metis has_bochner_integral_implies_finite_norm integrable.cases)
  then have "(\<integral>\<^sup>+ x. norm(F n x) \<partial>M) < \<infinity>" using assms(4)[of n] by auto
  then show "integrable M (F n)" by (subst integrable_iff_bounded, simp add: assms(1)[of n])
qed (auto simp add: assms Limsup_bounded)

end
