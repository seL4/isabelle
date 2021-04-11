(*  Author:     Lars Noschinski
*)

section \<open>Permutation orbits\<close>

theory Orbits
imports
  "HOL-Library.FuncSet"
  "HOL-Combinatorics.Permutations"
begin

subsection \<open>Orbits and cyclic permutations\<close>

inductive_set orbit :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a set" for f x where
  base: "f x \<in> orbit f x" |
  step: "y \<in> orbit f x \<Longrightarrow> f y \<in> orbit f x"

definition cyclic_on :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "cyclic_on f S \<longleftrightarrow> (\<exists>s\<in>S. S = orbit f s)"

lemma orbit_altdef: "orbit f x = {(f ^^ n) x | n. 0 < n}" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix y assume "y \<in> ?L" then show "y \<in> ?R"
    by (induct rule: orbit.induct) (auto simp: exI[where x=1] exI[where x="Suc n" for n])
next
  fix y assume "y \<in> ?R"
  then obtain n where "y = (f ^^ n) x" "0 < n" by blast
  then show "y \<in> ?L"
  proof (induction n arbitrary: y)
    case (Suc n) then show ?case by (cases "n = 0") (auto intro: orbit.intros)
  qed simp
qed

lemma orbit_trans:
  assumes "s \<in> orbit f t" "t \<in> orbit f u" shows "s \<in> orbit f u"
  using assms by induct (auto intro: orbit.intros)

lemma orbit_subset:
  assumes "s \<in> orbit f (f t)" shows "s \<in> orbit f t"
  using assms by (induct) (auto intro: orbit.intros)

lemma orbit_sim_step:
  assumes "s \<in> orbit f t" shows "f s \<in> orbit f (f t)"
  using assms by induct (auto intro: orbit.intros)

lemma orbit_step:
  assumes "y \<in> orbit f x" "f x \<noteq> y" shows "y \<in> orbit f (f x)"
  using assms
proof induction
  case (step y) then show ?case by (cases "x = y") (auto intro: orbit.intros)
qed simp

lemma self_in_orbit_trans:
  assumes "s \<in> orbit f s" "t \<in> orbit f s" shows "t \<in> orbit f t"
  using assms(2,1) by induct (auto intro: orbit_sim_step)

lemma orbit_swap:
  assumes "s \<in> orbit f s" "t \<in> orbit f s" shows "s \<in> orbit f t"
  using assms(2,1)
proof induction
  case base then show ?case by (cases "f s = s") (auto intro: orbit_step)
next
  case (step x) then show ?case by (cases "f x = s") (auto intro: orbit_step)
qed

lemma permutation_self_in_orbit:
  assumes "permutation f" shows "s \<in> orbit f s"
  unfolding orbit_altdef using permutation_self[OF assms, of s] by simp metis

lemma orbit_altdef_self_in:
  assumes "s \<in> orbit f s" shows "orbit f s = {(f ^^ n) s | n. True}"
proof (intro set_eqI iffI)
  fix x assume "x \<in> {(f ^^ n) s | n. True}"
  then obtain n where "x = (f ^^ n) s" by auto
  then show "x \<in> orbit f s" using assms by (cases "n = 0") (auto simp: orbit_altdef)
qed (auto simp: orbit_altdef)

lemma orbit_altdef_permutation:
  assumes "permutation f" shows "orbit f s = {(f ^^ n) s | n. True}"
  using assms by (intro orbit_altdef_self_in permutation_self_in_orbit)

lemma orbit_altdef_bounded:
  assumes "(f ^^ n) s = s" "0 < n" shows "orbit f s = {(f ^^ m) s| m. m < n}"
proof -
  from assms have "s \<in> orbit f s"
    by (auto simp add: orbit_altdef) metis 
  then have "orbit f s = {(f ^^ m) s|m. True}" by (rule orbit_altdef_self_in)
  also have "\<dots> = {(f ^^ m) s| m. m < n}"
    using assms
    by (auto simp: funpow_mod_eq intro: exI[where x="m mod n" for m])
  finally show ?thesis .
qed

lemma funpow_in_orbit:
  assumes "s \<in> orbit f t" shows "(f ^^ n) s \<in> orbit f t"
  using assms by (induct n) (auto intro: orbit.intros)

lemma finite_orbit:
  assumes "s \<in> orbit f s" shows "finite (orbit f s)"
proof -
  from assms obtain n where n: "0 < n" "(f ^^ n) s = s"
    by (auto simp: orbit_altdef)
  then show ?thesis by (auto simp: orbit_altdef_bounded)
qed

lemma self_in_orbit_step:
  assumes "s \<in> orbit f s" shows "orbit f (f s) = orbit f s"
proof (intro set_eqI iffI)
  fix t assume "t \<in> orbit f s" then show "t \<in> orbit f (f s)"
    using assms by (auto intro: orbit_step orbit_sim_step)
qed (auto intro: orbit_subset)

lemma permutation_orbit_step:
  assumes "permutation f" shows "orbit f (f s) = orbit f s"
  using assms by (intro self_in_orbit_step permutation_self_in_orbit)

lemma orbit_nonempty:
  "orbit f s \<noteq> {}"
  using orbit.base by fastforce

lemma orbit_inv_eq:
  assumes "permutation f"
  shows "orbit (inv f) x = orbit f x" (is "?L = ?R")
proof -
  { fix g y assume A: "permutation g" "y \<in> orbit (inv g) x"
    have "y \<in> orbit g x"
    proof -
      have inv_g: "\<And>y. x = g y \<Longrightarrow> inv g x = y" "\<And>y. inv g (g y) = y"
        by (metis A(1) bij_inv_eq_iff permutation_bijective)+

      { fix y assume "y \<in> orbit g x"
        then have "inv g y \<in> orbit g x"
          by (cases) (simp_all add: inv_g A(1) permutation_self_in_orbit)
      } note inv_g_in_orb = this

      from A(2) show ?thesis
        by induct (simp_all add: inv_g_in_orb A permutation_self_in_orbit)
    qed
  } note orb_inv_ss = this

  have "inv (inv f) = f"
    by (simp add: assms inv_inv_eq permutation_bijective)
  then show ?thesis
    using orb_inv_ss[OF assms] orb_inv_ss[OF permutation_inverse[OF assms]] by auto
qed

lemma cyclic_on_alldef:
  "cyclic_on f S \<longleftrightarrow> S \<noteq> {} \<and> (\<forall>s\<in>S. S = orbit f s)"
  unfolding cyclic_on_def by (auto intro: orbit.step orbit_swap orbit_trans)

lemma cyclic_on_funpow_in:
  assumes "cyclic_on f S" "s \<in> S" shows "(f^^n) s \<in> S"
  using assms unfolding cyclic_on_def by (auto intro: funpow_in_orbit)

lemma finite_cyclic_on:
  assumes "cyclic_on f S" shows "finite S"
  using assms by (auto simp: cyclic_on_def finite_orbit)

lemma cyclic_on_singleI:
  assumes "s \<in> S" "S = orbit f s" shows "cyclic_on f S"
  using assms unfolding cyclic_on_def by blast

lemma cyclic_on_inI:
  assumes "cyclic_on f S" "s \<in> S" shows "f s \<in> S"
  using assms by (auto simp: cyclic_on_def intro: orbit.intros)

lemma orbit_inverse:
  assumes self: "a \<in> orbit g a"
    and eq: "\<And>x. x \<in> orbit g a \<Longrightarrow> g' (f x) = f (g x)"
  shows "f ` orbit g a = orbit g' (f a)" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix x assume "x \<in> ?L"
  then obtain x0 where "x0 \<in> orbit g a" "x = f x0" by auto
  then show "x \<in> ?R"
  proof (induct arbitrary: x)
    case base then show ?case by (auto simp: self orbit.base eq[symmetric])
  next
    case step then show ?case by cases (auto simp: eq[symmetric] orbit.intros)
  qed
next
  fix x assume "x \<in> ?R"
  then show "x \<in> ?L"
  proof (induct arbitrary: )
    case base then show ?case by (auto simp: self orbit.base eq)
  next
    case step then show ?case by cases (auto simp: eq orbit.intros)
  qed
qed

lemma cyclic_on_image:
  assumes "cyclic_on f S"
  assumes "\<And>x. x \<in> S \<Longrightarrow> g (h x) = h (f x)"
  shows "cyclic_on g (h ` S)"
  using assms by (auto simp: cyclic_on_def) (meson orbit_inverse)

lemma cyclic_on_f_in:
  assumes "f permutes S" "cyclic_on f A" "f x \<in> A"
  shows "x \<in> A"
proof -
  from assms have fx_in_orb: "f x \<in> orbit f (f x)" by (auto simp: cyclic_on_alldef)
  from assms have "A = orbit f (f x)" by (auto simp: cyclic_on_alldef)
  moreover
  then have "\<dots> = orbit f x" using \<open>f x \<in> A\<close> by (auto intro: orbit_step orbit_subset)
  ultimately
    show ?thesis by (metis (no_types) orbit.simps permutes_inverses(2)[OF assms(1)])
qed

lemma orbit_cong0:
  assumes "x \<in> A" "f \<in> A \<rightarrow> A" "\<And>y. y \<in> A \<Longrightarrow> f y = g y" shows "orbit f x = orbit g x"
proof -
  { fix n have "(f ^^ n) x = (g ^^ n) x \<and> (f ^^ n) x \<in> A"
      by (induct n rule: nat.induct) (insert assms, auto)
  } then show ?thesis by (auto simp: orbit_altdef)
qed

lemma orbit_cong:
  assumes self_in: "t \<in> orbit f t" and eq: "\<And>s. s \<in> orbit f t \<Longrightarrow> g s = f s"
  shows "orbit g t = orbit f t"
  using assms(1) _ assms(2) by (rule orbit_cong0) (auto simp: orbit.step eq)

lemma cyclic_cong:
  assumes "\<And>s. s \<in> S \<Longrightarrow> f s = g s" shows "cyclic_on f S = cyclic_on g S"
proof -
  have "(\<exists>s\<in>S. orbit f s = orbit g s) \<Longrightarrow> cyclic_on f S = cyclic_on g S"
    by (metis cyclic_on_alldef cyclic_on_def)
  then show ?thesis by (metis assms orbit_cong cyclic_on_def)
qed

lemma permutes_comp_preserves_cyclic1:
  assumes "g permutes B" "cyclic_on f C"
  assumes "A \<inter> B = {}" "C \<subseteq> A"
  shows "cyclic_on (f o g) C"
proof -
  have *: "\<And>c. c \<in> C \<Longrightarrow> f (g c) = f c"
    using assms by (subst permutes_not_in [of g]) auto
  with assms(2) show ?thesis by (simp cong: cyclic_cong)
qed

lemma permutes_comp_preserves_cyclic2:
  assumes "f permutes A" "cyclic_on g C"
  assumes "A \<inter> B = {}" "C \<subseteq> B"
  shows "cyclic_on (f o g) C"
proof -
  obtain c where c: "c \<in> C" "C = orbit g c" "c \<in> orbit g c"
    using \<open>cyclic_on g C\<close> by (auto simp: cyclic_on_def)
  then have "\<And>c. c \<in> C \<Longrightarrow> f (g c) = g c"
    using assms c by (subst permutes_not_in [of f]) (auto intro: orbit.intros)
  with assms(2) show ?thesis by (simp cong: cyclic_cong)
qed

lemma permutes_orbit_subset:
  assumes "f permutes S" "x \<in> S" shows "orbit f x \<subseteq> S"
proof
  fix y assume "y \<in> orbit f x"
  then show "y \<in> S" by induct (auto simp: permutes_in_image assms)
qed

lemma cyclic_on_orbit':
  assumes "permutation f" shows "cyclic_on f (orbit f x)"
  unfolding cyclic_on_alldef using orbit_nonempty[of f x]
  by (auto intro: assms orbit_swap orbit_trans permutation_self_in_orbit)

lemma cyclic_on_orbit:
  assumes "f permutes S" "finite S" shows "cyclic_on f (orbit f x)"
  using assms by (intro cyclic_on_orbit') (auto simp: permutation_permutes)

lemma orbit_cyclic_eq3:
  assumes "cyclic_on f S" "y \<in> S" shows "orbit f y = S"
  using assms unfolding cyclic_on_alldef by simp

lemma orbit_eq_singleton_iff: "orbit f x = {x} \<longleftrightarrow> f x = x" (is "?L \<longleftrightarrow> ?R")
proof
  assume A: ?R
  { fix y assume "y \<in> orbit f x" then have "y = x"
      by induct (auto simp: A)
  } then show ?L by (metis orbit_nonempty singletonI subsetI subset_singletonD)
next
  assume A: ?L
  then have "\<And>y. y \<in> orbit f x \<Longrightarrow> f x = y"
    by - (erule orbit.cases, simp_all)
  then show ?R using A by blast
qed

lemma eq_on_cyclic_on_iff1:
  assumes "cyclic_on f S" "x \<in> S"
  obtains "f x \<in> S" "f x = x \<longleftrightarrow> card S = 1"
proof
  from assms show "f x \<in> S" by (auto simp: cyclic_on_def intro: orbit.intros)
  from assms have "S = orbit f x" by (auto simp: cyclic_on_alldef)
  then have "f x = x \<longleftrightarrow> S = {x}" by (metis orbit_eq_singleton_iff)
  then show "f x = x \<longleftrightarrow> card S = 1" using \<open>x \<in> S\<close> by (auto simp: card_Suc_eq)
qed

lemma orbit_eqI:
  "y = f x \<Longrightarrow> y \<in> orbit f x"
  "z = f y \<Longrightarrow>y \<in> orbit f x \<Longrightarrow>z \<in> orbit f x"
  by (metis orbit.base) (metis orbit.step)


subsection \<open>Decomposition of arbitrary permutations\<close>

definition perm_restrict :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "perm_restrict f S x \<equiv> if x \<in> S then f x else x"

lemma perm_restrict_comp:
  assumes "A \<inter> B = {}" "cyclic_on f B"
  shows "perm_restrict f A o perm_restrict f B = perm_restrict f (A \<union> B)"
proof -
  have "\<And>x. x \<in> B \<Longrightarrow> f x \<in> B" using \<open>cyclic_on f B\<close> by (rule cyclic_on_inI)
  with assms show ?thesis by (auto simp: perm_restrict_def fun_eq_iff)
qed

lemma perm_restrict_simps:
  "x \<in> S \<Longrightarrow> perm_restrict f S x = f x"
  "x \<notin> S \<Longrightarrow> perm_restrict f S x = x"
  by (auto simp: perm_restrict_def)

lemma perm_restrict_perm_restrict:
  "perm_restrict (perm_restrict f A) B = perm_restrict f (A \<inter> B)"
  by (auto simp: perm_restrict_def)

lemma perm_restrict_union:
  assumes "perm_restrict f A permutes A" "perm_restrict f B permutes B" "A \<inter> B = {}"
  shows "perm_restrict f A o perm_restrict f B = perm_restrict f (A \<union> B)"
  using assms by (auto simp: fun_eq_iff perm_restrict_def permutes_def) (metis Diff_iff Diff_triv)

lemma perm_restrict_id[simp]:
  assumes "f permutes S" shows "perm_restrict f S = f"
  using assms by (auto simp: permutes_def perm_restrict_def)

lemma cyclic_on_perm_restrict:
  "cyclic_on (perm_restrict f S) S \<longleftrightarrow> cyclic_on f S"
  by (simp add: perm_restrict_def cong: cyclic_cong)

lemma perm_restrict_diff_cyclic:
  assumes "f permutes S" "cyclic_on f A"
  shows "perm_restrict f (S - A) permutes (S - A)"
proof -
  { fix y
    have "\<exists>x. perm_restrict f (S - A) x = y"
    proof cases
      assume A: "y \<in> S - A"
      with \<open>f permutes S\<close> obtain x where "f x = y" "x \<in> S"
        unfolding permutes_def by auto metis
      moreover
      with A have "x \<notin> A" by (metis Diff_iff assms(2) cyclic_on_inI)
      ultimately
      have "perm_restrict f (S - A) x = y"  by (simp add: perm_restrict_simps)
      then show ?thesis ..
    next
      assume "y \<notin> S - A"
      then have "perm_restrict f (S - A) y = y" by (simp add: perm_restrict_simps)
      then show ?thesis ..
    qed
  } note X = this

  { fix x y assume "perm_restrict f (S - A) x = perm_restrict f (S - A) y"
    with assms have "x = y"
      by (auto simp: perm_restrict_def permutes_def split: if_splits intro: cyclic_on_f_in)
  } note Y = this

  show ?thesis by (auto simp: permutes_def perm_restrict_simps X intro: Y)
qed

lemma permutes_decompose:
  assumes "f permutes S" "finite S"
  shows "\<exists>C. (\<forall>c \<in> C. cyclic_on f c) \<and> \<Union>C = S \<and> (\<forall>c1 \<in> C. \<forall>c2 \<in> C. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {})"
  using assms(2,1)
proof (induction arbitrary: f rule: finite_psubset_induct)
  case (psubset S)

  show ?case
  proof (cases "S = {}")
    case True then show ?thesis by (intro exI[where x="{}"]) auto
  next
    case False
    then obtain s where "s \<in> S" by auto
    with \<open>f permutes S\<close> have "orbit f s \<subseteq> S"
      by (rule permutes_orbit_subset)
    have cyclic_orbit: "cyclic_on f (orbit f s)"
      using \<open>f permutes S\<close> \<open>finite S\<close> by (rule cyclic_on_orbit)

    let ?f' = "perm_restrict f (S - orbit f s)"

    have "f s \<in> S" using \<open>f permutes S\<close> \<open>s \<in> S\<close> by (auto simp: permutes_in_image)
    then have "S - orbit f s \<subset> S" using orbit.base[of f s] \<open>s \<in> S\<close> by blast
    moreover
    have "?f' permutes (S - orbit f s)"
      using \<open>f permutes S\<close> cyclic_orbit by (rule perm_restrict_diff_cyclic)
    ultimately
    obtain C where C: "\<And>c. c \<in> C \<Longrightarrow> cyclic_on ?f' c" "\<Union>C = S - orbit f s"
        "\<forall>c1 \<in> C. \<forall>c2 \<in> C. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {}"
      using psubset.IH by metis

    { fix c assume "c \<in> C"
      then have *: "\<And>x. x \<in> c \<Longrightarrow> perm_restrict f (S - orbit f s) x = f x"
        using C(2) \<open>f permutes S\<close> by (auto simp add: perm_restrict_def)
      then have "cyclic_on f c" using C(1)[OF \<open>c \<in> C\<close>] by (simp cong: cyclic_cong add: *)
    } note in_C_cyclic = this

    have Un_ins: "\<Union>(insert (orbit f s) C) = S"
      using \<open>\<Union>C = _\<close>  \<open>orbit f s \<subseteq> S\<close> by blast

    have Disj_ins: "(\<forall>c1 \<in> insert (orbit f s) C. \<forall>c2 \<in> insert (orbit f s) C. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {})"
      using C by auto

    show ?thesis
      by (intro conjI Un_ins Disj_ins exI[where x="insert (orbit f s) C"])
        (auto simp: cyclic_orbit in_C_cyclic)
  qed
qed


subsection \<open>Function-power distance between values\<close>

definition funpow_dist :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "funpow_dist f x y \<equiv> LEAST n. (f ^^ n) x = y"

abbreviation funpow_dist1 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "funpow_dist1 f x y \<equiv> Suc (funpow_dist f (f x) y)"

lemma funpow_dist_0:
  assumes "x = y" shows "funpow_dist f x y = 0"
  using assms unfolding funpow_dist_def by (intro Least_eq_0) simp

lemma funpow_dist_least:
  assumes "n < funpow_dist f x y" shows "(f ^^ n) x \<noteq> y"
proof (rule notI)
  assume "(f ^^ n) x = y"
  then have "funpow_dist f x y \<le> n" unfolding funpow_dist_def by (rule Least_le)
  with assms show False by linarith
qed

lemma funpow_dist1_least:
  assumes "0 < n" "n < funpow_dist1 f x y" shows "(f ^^ n) x \<noteq> y"
proof (rule notI)
  assume "(f ^^ n) x = y"
  then have "(f ^^ (n - 1)) (f x) = y"
    using \<open>0 < n\<close> by (cases n) (simp_all add: funpow_swap1)
  then have "funpow_dist f (f x) y \<le> n - 1" unfolding funpow_dist_def by (rule Least_le)
  with assms show False by simp
qed

lemma funpow_dist_prop:
  "y \<in> orbit f x \<Longrightarrow> (f ^^ funpow_dist f x y) x = y"
  unfolding funpow_dist_def by (rule LeastI_ex) (auto simp: orbit_altdef)

lemma funpow_dist_0_eq:
  assumes "y \<in> orbit f x" shows "funpow_dist f x y = 0 \<longleftrightarrow> x = y"
  using assms by (auto simp: funpow_dist_0 dest: funpow_dist_prop)

lemma funpow_dist_step:
  assumes "x \<noteq> y" "y \<in> orbit f x" shows "funpow_dist f x y = Suc (funpow_dist f (f x) y)"
proof -
  from \<open>y \<in> _\<close> obtain n where "(f ^^ n) x = y" by (auto simp: orbit_altdef)
  with \<open>x \<noteq> y\<close> obtain n' where [simp]: "n = Suc n'" by (cases n) auto

  show ?thesis
    unfolding funpow_dist_def
  proof (rule Least_Suc2)
    show "(f ^^ n) x = y" by fact
    then show "(f ^^ n') (f x) = y" by (simp add: funpow_swap1)
    show "(f ^^ 0) x \<noteq> y" using \<open>x \<noteq> y\<close> by simp
    show "\<forall>k. ((f ^^ Suc k) x = y) = ((f ^^ k) (f x) = y)"
      by (simp add: funpow_swap1)
  qed
qed

lemma funpow_dist1_prop:
  assumes "y \<in> orbit f x" shows "(f ^^ funpow_dist1 f x y) x = y"
  by (metis assms funpow_dist_prop funpow_dist_step funpow_simps_right(2) o_apply self_in_orbit_step)

(*XXX simplify? *)
lemma funpow_neq_less_funpow_dist:
  assumes "y \<in> orbit f x" "m \<le> funpow_dist f x y" "n \<le> funpow_dist f x y" "m \<noteq> n"
  shows "(f ^^ m) x \<noteq> (f ^^ n) x"
proof (rule notI)
  assume A: "(f ^^ m) x = (f ^^ n) x"

  define m' n' where "m' = min m n" and "n' = max m n"
  with A assms have A': "m' < n'" "(f ^^ m') x = (f ^^ n') x" "n' \<le> funpow_dist f x y"
    by (auto simp: min_def max_def)

  have "y = (f ^^ funpow_dist f x y) x"
    using \<open>y \<in> _\<close> by (simp only: funpow_dist_prop)
  also have "\<dots> = (f ^^ ((funpow_dist f x y - n') + n')) x"
    using \<open>n' \<le> _\<close> by simp
  also have "\<dots> = (f ^^ ((funpow_dist f x y - n') + m')) x"
    by (simp add: funpow_add \<open>(f ^^ m') x = _\<close>)
  also have "(f ^^ ((funpow_dist f x y - n') + m')) x \<noteq> y"
    using A' by (intro funpow_dist_least) linarith
  finally show "False" by simp
qed

(* XXX reduce to funpow_neq_less_funpow_dist? *)
lemma funpow_neq_less_funpow_dist1:
  assumes "y \<in> orbit f x" "m < funpow_dist1 f x y" "n < funpow_dist1 f x y" "m \<noteq> n"
  shows "(f ^^ m) x \<noteq> (f ^^ n) x"
proof (rule notI)
  assume A: "(f ^^ m) x = (f ^^ n) x"

  define m' n' where "m' = min m n" and "n' = max m n"
  with A assms have A': "m' < n'" "(f ^^ m') x = (f ^^ n') x" "n' < funpow_dist1 f x y"
    by (auto simp: min_def max_def)

  have "y = (f ^^ funpow_dist1 f x y) x"
    using \<open>y \<in> _\<close> by (simp only: funpow_dist1_prop)
  also have "\<dots> = (f ^^ ((funpow_dist1 f x y - n') + n')) x"
    using \<open>n' < _\<close> by simp
  also have "\<dots> = (f ^^ ((funpow_dist1 f x y - n') + m')) x"
    by (simp add: funpow_add \<open>(f ^^ m') x = _\<close>)
  also have "(f ^^ ((funpow_dist1 f x y - n') + m')) x \<noteq> y"
    using A' by (intro funpow_dist1_least) linarith+
  finally show "False" by simp
qed

lemma inj_on_funpow_dist:
  assumes "y \<in> orbit f x" shows "inj_on (\<lambda>n. (f ^^ n) x) {0..funpow_dist f x y}"
  using funpow_neq_less_funpow_dist[OF assms] by (intro inj_onI) auto

lemma inj_on_funpow_dist1:
  assumes "y \<in> orbit f x" shows "inj_on (\<lambda>n. (f ^^ n) x) {0..<funpow_dist1 f x y}"
  using funpow_neq_less_funpow_dist1[OF assms] by (intro inj_onI) auto

lemma orbit_conv_funpow_dist1:
  assumes "x \<in> orbit f x"
  shows "orbit f x = (\<lambda>n. (f ^^ n) x) ` {0..<funpow_dist1 f x x}" (is "?L = ?R")
  using funpow_dist1_prop[OF assms]
  by (auto simp: orbit_altdef_bounded[where n="funpow_dist1 f x x"])

lemma funpow_dist1_prop1:
  assumes "(f ^^ n) x = y" "0 < n" shows "(f ^^ funpow_dist1 f x y) x = y"
proof -
  from assms have "y \<in> orbit f x" by (auto simp: orbit_altdef)
  then show ?thesis by (rule funpow_dist1_prop)
qed

lemma funpow_dist1_dist:
  assumes "funpow_dist1 f x y < funpow_dist1 f x z"
  assumes "{y,z} \<subseteq> orbit f x"
  shows "funpow_dist1 f x z = funpow_dist1 f x y + funpow_dist1 f y z" (is "?L = ?R")
proof -
  define n where \<open>n = funpow_dist1 f x z - funpow_dist1 f x y - 1\<close>
  with assms have *: \<open>funpow_dist1 f x z = Suc (funpow_dist1 f x y + n)\<close>
    by simp
  have x_z: "(f ^^ funpow_dist1 f x z) x = z" using assms by (blast intro: funpow_dist1_prop)
  have x_y: "(f ^^ funpow_dist1 f x y) x = y" using assms by (blast intro: funpow_dist1_prop)

  have "(f ^^ (funpow_dist1 f x z - funpow_dist1 f x y)) y
      = (f ^^ (funpow_dist1 f x z - funpow_dist1 f x y)) ((f ^^ funpow_dist1 f x y) x)"
    using x_y by simp
  also have "\<dots> = z"
    using assms x_z by (simp add: * funpow_add ac_simps funpow_swap1)
  finally have y_z_diff: "(f ^^ (funpow_dist1 f x z - funpow_dist1 f x y)) y = z" .
  then have "(f ^^ funpow_dist1 f y z) y = z"
    using assms by (intro funpow_dist1_prop1) auto
  then have "(f ^^ funpow_dist1 f y z) ((f ^^ funpow_dist1 f x y) x) = z"
    using x_y by simp
  then have "(f ^^ (funpow_dist1 f y z + funpow_dist1 f x y)) x = z"
    by (simp add: * funpow_add funpow_swap1)
  show ?thesis
  proof (rule antisym)
    from y_z_diff have "(f ^^ funpow_dist1 f y z) y = z"
      using assms by (intro funpow_dist1_prop1) auto
    then have "(f ^^ funpow_dist1 f y z) ((f ^^ funpow_dist1 f x y) x) = z"
      using x_y by simp
    then have "(f ^^ (funpow_dist1 f y z + funpow_dist1 f x y)) x = z"
      by (simp add: * funpow_add funpow_swap1)
    then have "funpow_dist1 f x z \<le> funpow_dist1 f y z + funpow_dist1 f x y"
      using funpow_dist1_least not_less by fastforce
    then show "?L \<le> ?R" by presburger
  next
    have "funpow_dist1 f y z \<le> funpow_dist1 f x z - funpow_dist1 f x y"
      using y_z_diff assms(1) by (metis not_less zero_less_diff funpow_dist1_least)
    then show "?R \<le> ?L" by linarith
  qed
qed

lemma funpow_dist1_le_self:
  assumes "(f ^^ m) x = x" "0 < m" "y \<in> orbit f x"
  shows "funpow_dist1 f x y \<le> m"
proof (cases "x = y")
  case True with assms show ?thesis by (auto dest!: funpow_dist1_least)
next
  case False
  have "(f ^^ funpow_dist1 f x y) x = (f ^^ (funpow_dist1 f x y mod m)) x"
    using assms by (simp add: funpow_mod_eq)
  with False \<open>y \<in> orbit f x\<close> have "funpow_dist1 f x y \<le> funpow_dist1 f x y mod m"
    by auto (metis \<open>(f ^^ funpow_dist1 f x y) x = (f ^^ (funpow_dist1 f x y mod m)) x\<close> funpow_dist1_prop funpow_dist_least funpow_dist_step leI)
  with \<open>m > 0\<close> show ?thesis
    by (auto intro: order_trans)
qed

end