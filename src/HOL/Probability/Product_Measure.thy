theory Product_Measure
imports Lebesgue_Integration
begin

definition "dynkin M \<longleftrightarrow>
  space M \<in> sets M \<and>
  (\<forall> A \<in> sets M. A \<subseteq> space M) \<and>
  (\<forall> a \<in> sets M. \<forall> b \<in> sets M. b - a \<in> sets M) \<and>
  (\<forall>A. disjoint_family A \<and> range A \<subseteq> sets M \<longrightarrow> (\<Union>i::nat. A i) \<in> sets M)"

lemma dynkinI:
  assumes "\<And> A. A \<in> sets M \<Longrightarrow> A \<subseteq> space M"
  assumes "space M \<in> sets M" and "\<forall> a \<in> sets M. \<forall> b \<in> sets M. b - a \<in> sets M"
  assumes "\<And> a. (\<And> i j :: nat. i \<noteq> j \<Longrightarrow> a i \<inter> a j = {})
          \<Longrightarrow> (\<And> i :: nat. a i \<in> sets M) \<Longrightarrow> UNION UNIV a \<in> sets M"
  shows "dynkin M"
using assms unfolding dynkin_def sorry

lemma dynkin_subset:
  assumes "dynkin M"
  shows "\<And> A. A \<in> sets M \<Longrightarrow> A \<subseteq> space M"
using assms unfolding dynkin_def by auto

lemma dynkin_space:
  assumes "dynkin M"
  shows "space M \<in> sets M"
using assms unfolding dynkin_def by auto

lemma dynkin_diff:
  assumes "dynkin M"
  shows "\<And> a b. \<lbrakk> a \<in> sets M ; b \<in> sets M \<rbrakk> \<Longrightarrow> b - a \<in> sets M"
using assms unfolding dynkin_def by auto

lemma dynkin_UN:
  assumes "dynkin M"
  assumes "\<And> i j :: nat. i \<noteq> j \<Longrightarrow> a i \<inter> a j = {}"
  assumes "\<forall> i :: nat. a i \<in> sets M"
  shows "UNION UNIV a \<in> sets M"
using assms unfolding dynkin_def sorry

definition "Int_stable M \<longleftrightarrow> (\<forall> a \<in> sets M. \<forall> b \<in> sets M. a \<inter> b \<in> sets M)"

lemma dynkin_trivial:
  shows "dynkin \<lparr> space = A, sets = Pow A \<rparr>"
by (rule dynkinI) auto

lemma
  fixes D :: "'a algebra"
  assumes stab: "Int_stable E"
  and spac: "space E = space D"
  and subsED: "sets E \<subseteq> sets D"
  and subsDE: "sets D \<subseteq> sigma_sets (space E) (sets E)"
  and dyn: "dynkin D"
  shows "sigma (space E) (sets E) = D"
proof -
  def sets_\<delta>E == "\<Inter> {sets d | d :: 'a algebra. dynkin d \<and> space d = space E \<and> sets E \<subseteq> sets d}"
  def \<delta>E == "\<lparr> space = space E, sets = sets_\<delta>E \<rparr>"
  have "\<lparr> space = space E, sets = Pow (space E) \<rparr> \<in> {d | d. dynkin d \<and> space d = space E \<and> sets E \<subseteq> sets d}"
    using dynkin_trivial spac subsED dynkin_subset[OF dyn] by fastsimp
  hence not_empty: "{sets (d :: 'a algebra) | d. dynkin d \<and> space d = space E \<and> sets E \<subseteq> sets d} \<noteq> {}"
    using exI[of "\<lambda> x. space x = space E \<and> dynkin x \<and> sets E \<subseteq> sets x" "\<lparr> space = space E, sets = Pow (space E) \<rparr>", simplified]
    by auto

  have "sets_\<delta>E \<subseteq> sets D"
    unfolding sets_\<delta>E_def using assms by auto

  have \<delta>ynkin: "dynkin \<delta>E"
  proof (rule dynkinI, safe)
    fix A x assume asm: "A \<in> sets \<delta>E" "x \<in> A"
    { fix d :: "('a, 'b) algebra_scheme" assume "A \<in> sets d" "dynkin d \<and> space d = space E"
      hence "A \<subseteq> space d" using dynkin_subset by auto }
    show "x \<in> space \<delta>E" using asm unfolding \<delta>E_def sets_\<delta>E_def using not_empty
      by simp (metis dynkin_subset in_mono mem_def)
  next
    show "space \<delta>E \<in> sets \<delta>E"
      unfolding \<delta>E_def sets_\<delta>E_def
      using dynkin_space by fastsimp
  next
    fix a b assume "a \<in> sets \<delta>E" "b \<in> sets \<delta>E"
    thus "b - a \<in> sets \<delta>E"
      unfolding \<delta>E_def sets_\<delta>E_def by (auto intro:dynkin_diff)
  next
    fix a assume asm: "\<And>i j :: nat. i \<noteq> j \<Longrightarrow> a i \<inter> a j = {}" "\<And>i. a i \<in> sets \<delta>E"
    thus "UNION UNIV a \<in> sets \<delta>E"
      unfolding \<delta>E_def sets_\<delta>E_def apply (auto intro!:dynkin_UN[OF _ asm(1)])
      by blast
  qed

  def Dy == "\<lambda> d. {A | A. A \<in> sets_\<delta>E \<and> A \<inter> d \<in> sets_\<delta>E}"
  { fix d assume dasm: "d \<in> sets_\<delta>E"
    have "dynkin \<lparr> space = space E, sets = Dy d \<rparr>"
    proof (rule dynkinI, safe, simp_all)
      fix A x assume "A \<in> Dy d" "x \<in> A"
      thus "x \<in> space E" unfolding Dy_def sets_\<delta>E_def using not_empty
        by simp (metis dynkin_subset in_mono mem_def)
    next
      show "space E \<in> Dy d"
        unfolding Dy_def \<delta>E_def sets_\<delta>E_def
      proof auto
        fix d assume asm: "dynkin d" "space d = space E" "sets E \<subseteq> sets d"
        hence "space d \<in> sets d" using dynkin_space[OF asm(1)] by auto
        thus "space E \<in> sets d" using asm by auto
      next
        fix da :: "'a algebra" assume asm: "dynkin da" "space da = space E" "sets E \<subseteq> sets da"
        have d: "d = space E \<inter> d"
          using dasm dynkin_subset[OF asm(1)] asm(2) dynkin_subset[OF \<delta>ynkin]
          unfolding \<delta>E_def by auto
        hence "space E \<inter> d \<in> sets \<delta>E" unfolding \<delta>E_def
          using dasm by auto
        have "sets \<delta>E \<subseteq> sets da" unfolding \<delta>E_def sets_\<delta>E_def using asm
          by auto
        thus "space E \<inter> d \<in> sets da" using dasm asm d dynkin_subset[OF \<delta>ynkin]
          unfolding \<delta>E_def by auto
      qed
    next
      fix a b assume absm: "a \<in> Dy d" "b \<in> Dy d"
      hence "a \<in> sets \<delta>E" "b \<in> sets \<delta>E"
        unfolding Dy_def \<delta>E_def by auto
      hence *: "b - a \<in> sets \<delta>E"
        using dynkin_diff[OF \<delta>ynkin] by auto
      have "a \<inter> d \<in> sets \<delta>E" "b \<inter> d \<in> sets \<delta>E"
        using absm unfolding Dy_def \<delta>E_def by auto
      hence "(b \<inter> d) - (a \<inter> d) \<in> sets \<delta>E"
        using dynkin_diff[OF \<delta>ynkin] by auto
      hence **: "(b - a) \<inter> d \<in> sets \<delta>E" by (auto simp add:Diff_Int_distrib2)
      thus "b - a \<in> Dy d"
        using * ** unfolding Dy_def \<delta>E_def by auto
    next
      fix a assume aasm: "\<And>i j :: nat. i \<noteq> j \<Longrightarrow> a i \<inter> a j = {}" "\<And>i. a i \<in> Dy d"
      hence "\<forall> i. a i \<in> sets \<delta>E"
        unfolding Dy_def \<delta>E_def by auto
      from dynkin_UN[OF \<delta>ynkin aasm(1) this]
      have *: "UNION UNIV a \<in> sets \<delta>E" by auto
      from aasm
      have aE: "\<forall> i. a i \<inter> d \<in> sets \<delta>E"
        unfolding Dy_def \<delta>E_def by auto
      from aasm
      have "\<And>i j :: nat. i \<noteq> j \<Longrightarrow> (a i \<inter> d) \<inter> (a j \<inter> d) = {}" by auto
      from dynkin_UN[OF \<delta>ynkin this]
      have "UNION UNIV (\<lambda> i. a i \<inter> d) \<in> sets \<delta>E"
        using aE by auto
      hence **: "UNION UNIV a \<inter> d \<in> sets \<delta>E" by auto
      from * ** show "UNION UNIV a \<in> Dy d" unfolding Dy_def \<delta>E_def by auto
    qed } note Dy_nkin = this
  have E_\<delta>E: "sets E \<subseteq> sets \<delta>E"
    unfolding \<delta>E_def sets_\<delta>E_def by auto
  { fix d assume dasm: "d \<in> sets \<delta>E"
    { fix e assume easm: "e \<in> sets E"
      hence deasm: "e \<in> sets \<delta>E"
        unfolding \<delta>E_def sets_\<delta>E_def by auto
      have subset: "Dy e \<subseteq> sets \<delta>E"
        unfolding Dy_def \<delta>E_def by auto
      { fix e' assume e'asm: "e' \<in> sets E"
        have "e' \<inter> e \<in> sets E"
          using easm e'asm stab unfolding Int_stable_def by auto
        hence "e' \<inter> e \<in> sets \<delta>E"
          unfolding \<delta>E_def sets_\<delta>E_def by auto
        hence "e' \<in> Dy e" using e'asm unfolding Dy_def \<delta>E_def sets_\<delta>E_def by auto }
      hence E_Dy: "sets E \<subseteq> Dy e" by auto
      have "\<lparr> space = space E, sets = Dy e \<rparr> \<in> {d | d. dynkin d \<and> space d = space E \<and> sets E \<subseteq> sets d}"
        using Dy_nkin[OF deasm[unfolded \<delta>E_def, simplified]] E_\<delta>E E_Dy by auto
      hence "sets_\<delta>E \<subseteq> Dy e"
        unfolding sets_\<delta>E_def by auto (metis E_Dy simps(1) simps(2) spac)
      hence "sets \<delta>E = Dy e" using subset unfolding \<delta>E_def by auto
      hence "d \<inter> e \<in> sets \<delta>E"
        using dasm easm deasm unfolding Dy_def \<delta>E_def by auto
      hence "e \<in> Dy d" using deasm
        unfolding Dy_def \<delta>E_def
        by (auto simp add:Int_commute) }
    hence "sets E \<subseteq> Dy d" by auto
    hence "sets \<delta>E \<subseteq> Dy d" using Dy_nkin[OF dasm[unfolded \<delta>E_def, simplified]]
      unfolding \<delta>E_def sets_\<delta>E_def
      by auto (metis `sets E <= Dy d` simps(1) simps(2) spac)
    hence *: "sets \<delta>E = Dy d"
      unfolding Dy_def \<delta>E_def by auto
    fix a assume aasm: "a \<in> sets \<delta>E"
    hence "a \<inter> d \<in> sets \<delta>E"
      using * dasm unfolding Dy_def \<delta>E_def by auto } note \<delta>E_stab = this
  have "sigma_algebra D"
    apply unfold_locales
    using dynkin_subset[OF dyn]
    using dynkin_diff[OF dyn, of _ "space D", OF _ dynkin_space[OF dyn]]
    using dynkin_diff[OF dyn, of "space D" "space D", OF dynkin_space[OF dyn] dynkin_space[OF dyn]]
    using dynkin_space[OF dyn]
    sorry
(*
  proof auto
    fix A :: "nat \<Rightarrow> 'a set" assume Asm: "range A \<subseteq> sets D" "\<And>A. A \<in> sets D \<Longrightarrow> A \<subseteq> space D"
      "\<And>a. a \<in> sets D \<Longrightarrow> space D - a \<in> sets D"
    "{} \<in> sets D" "space D \<in> sets D"
    let "?A i" = "A i - (\<Inter> j \<in> {..< i}. A j)"
    { fix i :: nat assume "i > 0"
      have "(\<Inter> j \<in> {..< i}. A j) \<in> sets \<delta>E" sorry }
      oops
  qed
*)

  show ?thesis sorry
qed

definition prod_sets where
  "prod_sets A B = {z. \<exists>x \<in> A. \<exists>y \<in> B. z = x \<times> y}"

definition
  "prod_measure M \<mu> N \<nu> = (\<lambda>A. measure_space.positive_integral M \<mu> (\<lambda>s0. \<nu> ((\<lambda>s1. (s0, s1)) -` A)))"

definition
  "prod_measure_space M1 M2 = sigma (space M1 \<times> space M2) (prod_sets (sets M1) (sets M2))"

lemma prod_setsI: "x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> (x \<times> y) \<in> prod_sets A B"
  by (auto simp add: prod_sets_def)

lemma sigma_prod_sets_finite:
  assumes "finite A" and "finite B"
  shows "sigma_sets (A \<times> B) (prod_sets (Pow A) (Pow B)) = Pow (A \<times> B)"
proof safe
  have fin: "finite (A \<times> B)" using assms by (rule finite_cartesian_product)

  fix x assume subset: "x \<subseteq> A \<times> B"
  hence "finite x" using fin by (rule finite_subset)
  from this subset show "x \<in> sigma_sets (A\<times>B) (prod_sets (Pow A) (Pow B))"
    (is "x \<in> sigma_sets ?prod ?sets")
  proof (induct x)
    case empty show ?case by (rule sigma_sets.Empty)
  next
    case (insert a x)
    hence "{a} \<in> sigma_sets ?prod ?sets" by (auto simp: prod_sets_def intro!: sigma_sets.Basic)
    moreover have "x \<in> sigma_sets ?prod ?sets" using insert by auto
    ultimately show ?case unfolding insert_is_Un[of a x] by (rule sigma_sets_Un)
  qed
next
  fix x a b
  assume "x \<in> sigma_sets (A\<times>B) (prod_sets (Pow A) (Pow B))" and "(a, b) \<in> x"
  from sigma_sets_into_sp[OF _ this(1)] this(2)
  show "a \<in> A" and "b \<in> B"
    by (auto simp: prod_sets_def)
qed

lemma (in sigma_algebra) measurable_prod_sigma:
  assumes sa1: "sigma_algebra a1" and sa2: "sigma_algebra a2"
  assumes 1: "(fst o f) \<in> measurable M a1" and 2: "(snd o f) \<in> measurable M a2"
  shows "f \<in> measurable M (sigma ((space a1) \<times> (space a2))
                          (prod_sets (sets a1) (sets a2)))"
proof -
  from 1 have fn1: "fst \<circ> f \<in> space M \<rightarrow> space a1"
     and q1: "\<forall>y\<in>sets a1. (fst \<circ> f) -` y \<inter> space M \<in> sets M"
    by (auto simp add: measurable_def)
  from 2 have fn2: "snd \<circ> f \<in> space M \<rightarrow> space a2"
     and q2: "\<forall>y\<in>sets a2. (snd \<circ> f) -` y \<inter> space M \<in> sets M"
    by (auto simp add: measurable_def)
  show ?thesis
    proof (rule measurable_sigma)
      show "prod_sets (sets a1) (sets a2) \<subseteq> Pow (space a1 \<times> space a2)" using sa1 sa2
        by (auto simp add: prod_sets_def sigma_algebra_iff dest: algebra.space_closed)
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

lemma (in sigma_finite_measure) prod_measure_times:
  assumes "sigma_finite_measure N \<nu>"
  and "A1 \<in> sets M" "A2 \<in> sets N"
  shows "prod_measure M \<mu> N \<nu> (A1 \<times> A2) = \<mu> A1 * \<nu> A2"
  oops

lemma (in sigma_finite_measure) sigma_finite_prod_measure_space:
  assumes "sigma_finite_measure N \<nu>"
  shows "sigma_finite_measure (prod_measure_space M N) (prod_measure M \<mu> N \<nu>)"
  oops

lemma (in finite_measure_space) finite_prod_measure_times:
  assumes "finite_measure_space N \<nu>"
  and "A1 \<in> sets M" "A2 \<in> sets N"
  shows "prod_measure M \<mu> N \<nu> (A1 \<times> A2) = \<mu> A1 * \<nu> A2"
proof -
  interpret N: finite_measure_space N \<nu> by fact
  have *: "\<And>x. \<nu> (Pair x -` (A1 \<times> A2)) * \<mu> {x} = (if x \<in> A1 then \<nu> A2 * \<mu> {x} else 0)"
    by (auto simp: vimage_Times comp_def)
  have "finite A1"
    using `A1 \<in> sets M` finite_space by (auto simp: sets_eq_Pow intro: finite_subset)
  then have "\<mu> A1 = (\<Sum>x\<in>A1. \<mu> {x})" using `A1 \<in> sets M`
    by (auto intro!: measure_finite_singleton simp: sets_eq_Pow)
  then show ?thesis using `A1 \<in> sets M`
    unfolding prod_measure_def positive_integral_finite_eq_setsum *
    by (auto simp add: sets_eq_Pow setsum_right_distrib[symmetric] mult_commute setsum_cases[OF finite_space])
qed

lemma (in finite_measure_space) finite_prod_measure_space:
  assumes "finite_measure_space N \<nu>"
  shows "prod_measure_space M N = \<lparr> space = space M \<times> space N, sets = Pow (space M \<times> space N) \<rparr>"
proof -
  interpret N: finite_measure_space N \<nu> by fact
  show ?thesis using finite_space N.finite_space
    by (simp add: sigma_def prod_measure_space_def sigma_prod_sets_finite sets_eq_Pow N.sets_eq_Pow)
qed

lemma (in finite_measure_space) finite_measure_space_finite_prod_measure:
  assumes "finite_measure_space N \<nu>"
  shows "finite_measure_space (prod_measure_space M N) (prod_measure M \<mu> N \<nu>)"
  unfolding finite_prod_measure_space[OF assms]
proof (rule finite_measure_spaceI)
  interpret N: finite_measure_space N \<nu> by fact

  let ?P = "\<lparr>space = space M \<times> space N, sets = Pow (space M \<times> space N)\<rparr>"
  show "measure_space ?P (prod_measure M \<mu> N \<nu>)"
  proof (rule sigma_algebra.finite_additivity_sufficient)
    show "sigma_algebra ?P" by (rule sigma_algebra_Pow)
    show "finite (space ?P)" using finite_space N.finite_space by auto
    from finite_prod_measure_times[OF assms, of "{}" "{}"]
    show "positive (prod_measure M \<mu> N \<nu>)"
      unfolding positive_def by simp

    show "additive ?P (prod_measure M \<mu> N \<nu>)"
      unfolding additive_def
      apply (auto simp add: sets_eq_Pow prod_measure_def positive_integral_add[symmetric]
                  intro!: positive_integral_cong)
      apply (subst N.measure_additive[symmetric])
      by (auto simp: N.sets_eq_Pow sets_eq_Pow)
  qed
  show "finite (space ?P)" using finite_space N.finite_space by auto
  show "sets ?P = Pow (space ?P)" by simp

  fix x assume "x \<in> space ?P"
  with finite_prod_measure_times[OF assms, of "{fst x}" "{snd x}"]
    finite_measure[of "{fst x}"] N.finite_measure[of "{snd x}"]
  show "prod_measure M \<mu> N \<nu> {x} \<noteq> \<omega>"
    by (auto simp add: sets_eq_Pow N.sets_eq_Pow elim!: SigmaE)
qed

lemma (in finite_measure_space) finite_measure_space_finite_prod_measure_alterantive:
  assumes N: "finite_measure_space N \<nu>"
  shows "finite_measure_space \<lparr> space = space M \<times> space N, sets = Pow (space M \<times> space N) \<rparr> (prod_measure M \<mu> N \<nu>)"
    (is "finite_measure_space ?M ?m")
  unfolding finite_prod_measure_space[OF N, symmetric]
  using finite_measure_space_finite_prod_measure[OF N] .

end