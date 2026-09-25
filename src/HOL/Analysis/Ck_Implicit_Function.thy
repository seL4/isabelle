section \<open>The \<open>C\<^sup>1\<close> inverse and implicit function theorems\<close>

text \<open>
  \<open>C\<^sup>1\<close> versions of the inverse and implicit function theorems, and a \<open>C\<^sup>k\<close> implicit
  function theorem.  As in the real-analytic case, the implicit function theorem follows from
  the inverse function theorem, applied to \<open>\<Phi> (x, y) = (x, F (x, y))\<close>.
\<close>

theory Ck_Implicit_Function
  imports Higher_Differentiability_Multi "HOL-Analysis.Determinants"
begin

section \<open>From \<open>C\<^sup>1\<close> to the inverse-function-theorem interface\<close>

text \<open>
  The \<open>C\<^sup>1\<close> inverse function theorem of HOL-Analysis (\<open>inverse_function_theorem\<close>)
  needs a continuous \<open>blinfun\<close>-valued derivative on an open set.  We obtain one from
  \<open>Ck_on (Suc 0)\<close>, upgrading continuity of the directional derivatives to continuity in
  operator norm.
\<close>

text \<open>The Fréchet derivative as a \<open>blinfun\<close>.\<close>

definition Dblinfun :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'b)"
  where "Dblinfun G z = Blinfun (frechet_derivative G (at z))"

lemma blinfun_apply_Dblinfun:
  assumes "G differentiable (at z)"
  shows "blinfun_apply (Dblinfun G z) = frechet_derivative G (at z)"
proof -
  have "bounded_linear (frechet_derivative G (at z))"
    using assms frechet_derivative_works has_derivative_bounded_linear by blast
  thus ?thesis
    unfolding Dblinfun_def by (rule bounded_linear_Blinfun_apply)
qed

text \<open>\<open>C\<^sup>1\<close> at a point: differentiability and continuity of the directional derivatives.\<close>

lemma Ck1_atD:
  assumes "Ck_at (Suc 0) G x"
  shows "G differentiable (at x)"
    and "\<And>v. continuous (at x) (\<lambda>y. frechet_derivative G (at y) v)"
  using assms by auto

text \<open>From \<open>C\<^sup>1\<close> on \<open>W\<close>: \<^const>\<open>Dblinfun\<close> is a derivative of \<open>G\<close> on \<open>W\<close> and is
  continuous there.\<close>

lemma Ck1_on_imp_has_derivative_blinfun:
  fixes G :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "Ck_on (Suc 0) G W"
  shows "\<And>z. z \<in> W \<Longrightarrow> (G has_derivative blinfun_apply (Dblinfun G z)) (at z)"
proof -
  fix z assume z: "z \<in> W"
  have "Ck_at (Suc 0) G z"
    using assms z by (simp add: Ck_on_def)
  hence diff: "G differentiable (at z)" by (rule Ck1_atD)
  show "(G has_derivative blinfun_apply (Dblinfun G z)) (at z)"
    using diff by (simp add: blinfun_apply_Dblinfun frechet_derivative_works)
qed

lemma Ck1_on_imp_continuous_Dblinfun:
  fixes G :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "Ck_on (Suc 0) G W"
  shows "continuous_on W (Dblinfun G)"
proof (rule continuous_on_blinfun_componentwise)
  fix i :: 'a assume i: "i \<in> Basis"
  have W_open: "open W" using assms by (simp add: Ck_on_def)
  \<comment> \<open>per-direction continuity of the Fréchet derivative, on all of \<open>W\<close>\<close>
  have cont_dir: "continuous_on W (\<lambda>z. frechet_derivative G (at z) i)"
  proof (rule continuous_at_imp_continuous_on, rule ballI)
    fix z assume z: "z \<in> W"
    have "Ck_at (Suc 0) G z" using assms z by (simp add: Ck_on_def)
    thus "continuous (at z) (\<lambda>z. frechet_derivative G (at z) i)"
      by (rule Ck1_atD(2))
  qed
  \<comment> \<open>on \<open>W\<close> the blinfun component agrees with that derivative\<close>
  have eq: "\<And>z. z \<in> W \<Longrightarrow> blinfun_apply (Dblinfun G z) i = frechet_derivative G (at z) i"
  proof -
    fix z assume z: "z \<in> W"
    have "Ck_at (Suc 0) G z" using assms z by (simp add: Ck_on_def)
    hence "G differentiable (at z)" by (rule Ck1_atD)
    thus "blinfun_apply (Dblinfun G z) i = frechet_derivative G (at z) i"
      by (simp add: blinfun_apply_Dblinfun)
  qed
  show "continuous_on W (\<lambda>z. blinfun_apply (Dblinfun G z) i)"
    by (rule continuous_on_eq[OF cont_dir]) (simp add: eq)
qed

text \<open>The two halves packaged together.\<close>

theorem Ck1_on_imp_C1_interface:
  fixes G :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "Ck_on (Suc 0) G W"
  shows "(\<forall>z\<in>W. (G has_derivative blinfun_apply (Dblinfun G z)) (at z))
       \<and> continuous_on W (Dblinfun G)"
  using Ck1_on_imp_has_derivative_blinfun[OF assms]
        Ck1_on_imp_continuous_Dblinfun[OF assms]
  by blast

lemma Ck1_on_Pair_fst:
  fixes F :: "('a::euclidean_space \<times> 'b::euclidean_space) \<Rightarrow> 'b"
  assumes C1: "Ck_on (Suc 0) F W"
  shows "Ck_on (Suc 0) (\<lambda>p. (fst p, F p)) W"
  unfolding Ck_on_def
proof (intro conjI ballI)
  show Wopen: "open W" using C1 by (simp add: Ck_on_def)
  fix z assume z: "z \<in> W"
  have Fdiff: "F differentiable (at y)" if "y \<in> W" for y
    using C1 that by (simp add: Ck_on_def Ck1_atD(1))
  have Fcont: "continuous (at y) F" if "y \<in> W" for y
    using Fdiff[OF that] by (rule differentiable_imp_continuous_within)

  show "Ck_at (Suc 0) (\<lambda>p. (fst p, F p)) z"
    unfolding Ck_at.simps(2)
  proof (intro conjI allI)
    \<comment> \<open>continuity on a neighbourhood\<close>
    show "\<exists>A. open A \<and> z \<in> A \<and> (\<forall>y\<in>A. Ck_at 0 (\<lambda>p. (fst p, F p)) y)"
    proof (intro exI[where x = W] conjI ballI)
      fix y assume y: "y \<in> W"
      have "continuous (at y) (\<lambda>p::'a \<times> 'b. (fst p, F p))"
        by (intro continuous_intros Fcont[OF y])
      thus "Ck_at 0 (\<lambda>p. (fst p, F p)) y" by simp
    qed (use Wopen z in auto)
  next
    \<comment> \<open>differentiability at the point\<close>
    have fst_der: "((fst :: ('a \<times> 'b) \<Rightarrow> 'a) has_derivative fst) (at z)"
      by (rule bounded_linear.has_derivative[OF bounded_linear_fst has_derivative_ident])
    have "(F has_derivative frechet_derivative F (at z)) (at z)"
      using Fdiff[OF z] by (rule frechet_derivative_works[THEN iffD1])
    from has_derivative_Pair[OF fst_der this]
    show "(\<lambda>p. (fst p, F p)) differentiable (at z)"
      unfolding differentiable_def by blast
  next
    \<comment> \<open>continuity of each directional derivative\<close>
    fix v :: "'a \<times> 'b"
    have base: "continuous (at z) (\<lambda>y. (fst v, frechet_derivative F (at y) v))"
      using Ck1_atD(2) Ck_on_def assms z by (intro continuous_intros, blast)    
    have eq: "frechet_derivative (\<lambda>p. (fst p, F p)) (at y) v
                = (fst v, frechet_derivative F (at y) v)" if "y \<in> W" for y
      by (simp add: frechet_derivative_Pair_fst[OF Fdiff[OF that]])
    obtain d :: real where dpos: "0 < d" and dball: "ball z d \<subseteq> W"
      using Wopen z by (metis openE)
    have base': "continuous (at z within UNIV)
                   (\<lambda>y. (fst v, frechet_derivative F (at y) v))"
      using base by simp
    have "continuous (at z within UNIV)
            (\<lambda>y. frechet_derivative (\<lambda>p. (fst p, F p)) (at y) v)"
    proof (rule continuous_transform_within [OF base' dpos UNIV_I])
      fix y :: "'a \<times> 'b" assume "y \<in> UNIV" and "dist y z < d"
      hence "y \<in> W"
        by (metis dball dist_commute in_mono mem_ball) 
      thus "(fst v, frechet_derivative F (at y) v)
              = frechet_derivative (\<lambda>p. (fst p, F p)) (at y) v"
        by (simp only: eq)
    qed
    thus "Ck_at 0 (\<lambda>y. frechet_derivative (\<lambda>p. (fst p, F p)) (at y) v) z"
      by simp
  qed
qed


subsection \<open>The \<open>C\<^sup>1\<close> local inverse\<close>

text \<open>
  The inverse function theorem of HOL-Analysis needs a continuous \<open>blinfun\<close>-valued
  derivative (@{thm [source] Ck1_on_imp_C1_interface}) and a left inverse of the derivative at \<open>z\<^sub>0\<close>,
  here \<open>Blinfun (inv B)\<close>.
\<close>

theorem C1_local_inverse:
  fixes G :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes C1: "Ck_on (Suc 0) G W"
      and pW: "z0 \<in> W"
      and reg: "\<exists>B. (G has_derivative B) (at z0) \<and> bij B"
  obtains U' V H where
      "open U'" and "z0 \<in> U'" and "U' \<subseteq> W"
      and "open V" and "G z0 \<in> V"
      and "homeomorphism U' V G H"
      and "\<And>y. y \<in> V \<Longrightarrow> H differentiable (at y)"
proof -
  have Wopen: "open W" using C1 by (simp add: Ck_on_def)
  obtain B where Bder: "(G has_derivative B) (at z0)" and bijB: "bij B"
    using reg by blast

  have derG: "\<And>z. z \<in> W \<Longrightarrow> (G has_derivative blinfun_apply (Dblinfun G z)) (at z)"
    by (rule Ck1_on_imp_has_derivative_blinfun[OF C1])
  have contG: "continuous_on W (Dblinfun G)"
    by (rule Ck1_on_imp_continuous_Dblinfun[OF C1])

  \<comment> \<open>The canonical blinfun derivative at \<open>z\<^sub>0\<close> agrees with the bijective \<open>B\<close>.\<close>
  have Beq: "blinfun_apply (Dblinfun G z0) = B"
    by (rule has_derivative_unique[OF derG[OF pW] Bder])
  have blB: "bounded_linear B" using Bder by (rule has_derivative_bounded_linear)
  have injB: "inj B" using bijB by (simp add: bij_def)
  have blinvB: "bounded_linear (inv B)"
    by (rule inj_linear_imp_inv_bounded_linear[OF blB injB])
  have applyinv: "blinfun_apply (Blinfun (inv B)) = inv B"
    by (rule bounded_linear_Blinfun_apply[OF blinvB])

  have invf: "Blinfun (inv B) o\<^sub>L Dblinfun G z0 = id_blinfun"
  proof (rule blinfun_eqI)
    fix i
    have "blinfun_apply (Blinfun (inv B) o\<^sub>L Dblinfun G z0) i = inv B (B i)"
      by (simp add: applyinv Beq)
    also have "\<dots> = i" using injB by (simp add: inv_f_f)
    finally show "blinfun_apply (Blinfun (inv B) o\<^sub>L Dblinfun G z0) i
                    = blinfun_apply id_blinfun i" by simp
  qed

  obtain U' V H H' where
      U'open: "open U'" and U'sub: "U' \<subseteq> W" and z0U': "z0 \<in> U'"
      and Vopen: "open V" and GzV: "G z0 \<in> V"
      and homeo: "homeomorphism U' V G H"
      and Hder: "\<And>y. y \<in> V \<Longrightarrow> (H has_derivative (H' y)) (at y)"
      and H'eq: "\<And>y. y \<in> V \<Longrightarrow> H' y = inv (blinfun_apply (Dblinfun G (H y)))"
      and Hbij: "\<And>y. y \<in> V \<Longrightarrow> bij (blinfun_apply (Dblinfun G (H y)))"
    by (rule inverse_function_theorem[OF Wopen derG contG pW invf], simp_all)
  have Hdiff: "H differentiable (at y)" if "y \<in> V" for y
    using Hder[OF that] unfolding differentiable_def by blast
  show ?thesis
    by (rule that[OF U'open z0U' U'sub Vopen GzV homeo Hdiff])
qed


subsection \<open>The \<open>C\<^sup>1\<close> implicit function theorem\<close>

text \<open>The implicit function theorem for \<open>C\<^sup>1\<close> data; the solution map is differentiable.\<close>

theorem C1_implicit_function:
  fixes F :: "('a::euclidean_space \<times> 'b::euclidean_space) \<Rightarrow> 'b"
  assumes C1: "Ck_on (Suc 0) F W"
      and pW: "(x0, y0) \<in> W"
      and F0: "F (x0, y0) = 0"
      and reg: "\<exists>L. ((\<lambda>y. F (x0, y)) has_derivative L) (at y0) \<and> bij L"
  obtains U g where
      "open U" and "x0 \<in> U" and "g x0 = y0"
      and "\<And>x. x \<in> U \<Longrightarrow> g differentiable (at x)"
      and "\<forall>x\<in>U. (x, g x) \<in> W \<and> F (x, g x) = 0"
proof -
  have Wopen: "open W" using C1 by (simp add: Ck_on_def)
  let ?Phi = "\<lambda>p::'a \<times> 'b. (fst p, F p)"
  let ?p0 = "(x0, y0)"
  obtain L where Lder: "((\<lambda>y. F (x0, y)) has_derivative L) (at y0)"
      and bijL: "bij L" using reg by blast

  \<comment> \<open>\<open>\<Phi>\<close> is \<open>C\<^sup>1\<close>: the first slot is a projection, the second is \<open>F\<close>.\<close>
  have Phi_C1: "Ck_on (Suc 0) ?Phi W" by (rule Ck1_on_Pair_fst[OF C1])

  have Fdiff: "F differentiable (at ?p0)"
    using C1 pW by (simp add: Ck_on_def Ck1_atD(1))
  then obtain A where Fder: "(F has_derivative A) (at ?p0)"
    unfolding differentiable_def by blast

  \<comment> \<open>The second-slot partial of \<open>F\<close> is the slice of \<open>A\<close>, so \<open>L = (\<lambda>dy. A (0, dy))\<close>.\<close>
  have slice_der: "((\<lambda>y. F (x0, y)) has_derivative (\<lambda>dy. A (0, dy))) (at y0)"
  proof -
    have pair_der: "((\<lambda>y. (x0, y)) has_derivative (\<lambda>dy. (0, dy))) (at y0)"
    proof -
      have cder: "((\<lambda>y::'b. x0) has_derivative (\<lambda>dy. 0)) (at y0)"
        by (rule has_derivative_const)
      have idder: "((\<lambda>y::'b. y) has_derivative (\<lambda>dy. dy)) (at y0)"
        by (rule has_derivative_ident)
      show ?thesis using has_derivative_Pair[OF cder idder] by simp
    qed
    show ?thesis using has_derivative_compose[OF pair_der Fder] by simp
  qed
  have L_eq: "L = (\<lambda>dy. A (0, dy))"
    by (rule has_derivative_unique[OF Lder slice_der])

  let ?B = "\<lambda>h::'a \<times> 'b. (fst h, A h)"
  have Phi_der: "(?Phi has_derivative ?B) (at ?p0)"
  proof -
    have fst_der: "((fst :: ('a \<times> 'b) \<Rightarrow> 'a) has_derivative fst) (at ?p0)"
      by (rule bounded_linear.has_derivative[OF bounded_linear_fst has_derivative_ident])
    show ?thesis using has_derivative_Pair[OF fst_der Fder] by simp
  qed

  have blA: "bounded_linear A" using Fder by (rule has_derivative_bounded_linear)
  interpret A: bounded_linear A by (rule blA)
  have surjL: "surj L" and injL: "inj L" using bijL by (auto simp: bij_def)

  \<comment> \<open>\<open>?B\<close> is block-triangular with invertible diagonal blocks; \<open>?C\<close> is its
      inverse.\<close>
  let ?C = "\<lambda>q::'a \<times> 'b. (fst q, inv L (snd q - A (fst q, 0)))"
  have B_C: "?B (?C q) = q" for q
  proof -
    let ?w = "snd q - A (fst q, 0)"
    have decomp: "(fst q, inv L ?w) = (fst q, 0) + (0, inv L ?w)" by simp
    have Aq: "A (fst q, inv L ?w) = A (fst q, 0) + A (0, inv L ?w)"
      by (subst decomp) (rule A.add)
    have A0_inv: "A (0, inv L ?w) = ?w"
    proof -
      have "A (0, inv L ?w) = L (inv L ?w)" using L_eq by simp
      also have "... = ?w" using surjL by (rule surj_f_inv_f)
      finally show ?thesis .
    qed
    have "A (fst q, inv L ?w) = snd q" using Aq A0_inv by simp
    thus ?thesis by simp
  qed
  have C_B: "?C (?B h) = h" for h
  proof -
    have decomp: "h = (fst h, 0) + (0, snd h)" by simp
    have Ah: "A h = A (fst h, 0) + A (0, snd h)"
      by (subst decomp) (rule A.add)
    have "A h - A (fst h, 0) = L (snd h)" using Ah L_eq by simp
    thus ?thesis using injL by (simp add: inv_f_f)
  qed
  have bijB: "bij ?B"
  proof (rule bijI)
    show "inj ?B"
    proof (rule injI)
      fix u v :: "'a \<times> 'b"
      assume "?B u = ?B v"
      hence "?C (?B u) = ?C (?B v)" by simp
      thus "u = v" using C_B by metis
    qed
    show "surj ?B"
      unfolding surj_def using B_C by metis
  qed

  obtain U' V Psi where U'open: "open U'" and p0U': "?p0 \<in> U'"
      and U'sub: "U' \<subseteq> W" and Vopen: "open V"
      and PhiV: "?Phi ?p0 \<in> V"
      and homeo: "homeomorphism U' V ?Phi Psi"
      and Psi_diff: "\<And>q. q \<in> V \<Longrightarrow> Psi differentiable (at q)"
    by (rule C1_local_inverse[OF Phi_C1 pW]) (use Phi_der bijB in blast)+

  define U where "U = {x. (x, 0::'b) \<in> V}"
  define g where "g = (\<lambda>x. snd (Psi (x, 0::'b)))"

  have Uopen: "open U"
  proof -
    have "continuous_on UNIV (\<lambda>x::'a. (x, 0::'b))" by (intro continuous_intros)
    from continuous_open_preimage[OF this open_UNIV Vopen]
    show ?thesis by (simp add: U_def vimage_def)
  qed
  have x0U: "x0 \<in> U" using PhiV F0 by (simp add: U_def)
  have gx0: "g x0 = y0"
    using homeomorphism_apply1[OF homeo p0U'] F0 by (simp add: g_def)

  \<comment> \<open>\<open>g\<close> is a composite of the affine slice, the differentiable \<open>\<Psi>\<close>, and \<open>snd\<close>.\<close>
  have gdiff: "g differentiable (at x)" if xU: "x \<in> U" for x
  proof -
    have slice: "((\<lambda>x::'a. (x, 0::'b)) has_derivative (\<lambda>dx. (dx, 0::'b))) (at x)"
    proof -
      have idder: "((\<lambda>x::'a. x) has_derivative (\<lambda>dx. dx)) (at x)"
        by (rule has_derivative_ident)
      have cder: "((\<lambda>x::'a. 0::'b) has_derivative (\<lambda>dx. 0)) (at x)"
        by (rule has_derivative_const)
      show ?thesis using has_derivative_Pair[OF idder cder] by simp
    qed
    have inV: "(x, 0::'b) \<in> V" using xU by (simp add: U_def)
    obtain P where P: "(Psi has_derivative P) (at (x, 0::'b))"
      using Psi_diff[OF inV] unfolding differentiable_def by blast
    have "((\<lambda>x::'a. Psi (x, 0::'b)) has_derivative (\<lambda>dx. P (dx, 0))) (at x)"
      using has_derivative_compose[OF slice P] by simp
    from bounded_linear.has_derivative[OF bounded_linear_snd this]
    show ?thesis unfolding g_def differentiable_def by blast
  qed

  have solution: "\<forall>x\<in>U. (x, g x) \<in> W \<and> F (x, g x) = 0"
  proof
    fix x assume xU: "x \<in> U"
    have inV: "(x, 0::'b) \<in> V" using xU by (simp add: U_def)
    have Psi_in: "Psi (x, 0::'b) \<in> U'"
      using homeomorphism_image2[OF homeo] inV by blast
    have PhiPsi: "?Phi (Psi (x, 0::'b)) = (x, 0::'b)"
      by (rule homeomorphism_apply2[OF homeo inV])
    have "(x, g x) = Psi (x, 0::'b)"
      using PhiPsi by (simp add: g_def prod_eq_iff)
    thus "(x, g x) \<in> W \<and> F (x, g x) = 0"
      using Psi_in U'sub PhiPsi by auto
  qed

  show ?thesis by (rule that[OF Uopen x0U gx0 gdiff solution])
qed


subsection \<open>Further \<open>C\<^sup>k\<close> closure properties\<close>

text \<open>
  Closure properties for bootstrapping from \<open>C\<^sup>1\<close> to \<open>C\<^sup>k\<close>: vectors with \<open>C\<^sup>k\<close>
  components, finite products and determinants.
\<close>

lemma Ck_on_scaleR_right:
  fixes s :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "Ck_on k s U"
  shows "Ck_on k (\<lambda>y. s y *\<^sub>R v) U"
  by (rule Ck_on_bounded_linear_compose[OF bounded_linear_scaleR_left assms])

lemma Ck_on_vec:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real^'n::finite"
  assumes oU: "open U" and comps: "\<And>r. Ck_on k (\<lambda>y. f y $ r) U"
  shows "Ck_on k f U"
proof -
  have "Ck_on k (\<lambda>y. \<Sum>r\<in>(UNIV::'n set). (f y $ r) *\<^sub>R axis r 1) U"
    by (rule Ck_on_sum, simp_all, simp only: Ck_on_scaleR_right comps) 
  thus ?thesis
    by (metis (no_types, lifting) ext basis_expansion scalar_mult_eq_scaleR)
qed

text \<open>Finite products, and hence determinants of matrices with \<open>C\<^sup>k\<close> entries.\<close>

lemma Ck_on_prod:
  fixes f :: "'i \<Rightarrow> 'a::real_normed_vector \<Rightarrow> real"
  assumes fin: "finite I" and oU: "open U"
      and Ck: "\<And>i. i \<in> I \<Longrightarrow> Ck_on k (f i) U"
  shows "Ck_on k (\<lambda>y. \<Prod>i\<in>I. f i y) U"
  using fin Ck
proof (induction rule: finite_induct)
  case empty
  show ?case using oU by (simp add: Ck_on_const)
next
  case (insert i I)
  have "Ck_on k (\<lambda>y. f i y * (\<Prod>j\<in>I. f j y)) U"
    by (rule Ck_on_mult[OF insert.prems[of i] insert.IH]) (use insert.prems in auto)
  thus ?case using insert.hyps by simp
qed

lemma Ck_on_det:
  fixes M :: "'a::real_normed_vector \<Rightarrow> real^'n::finite^'n"
  assumes oU: "open U"
      and Ck: "\<And>i j. Ck_on k (\<lambda>y. M y $ i $ j) U"
  shows "Ck_on k (\<lambda>y. det (M y)) U"
proof -
  have finP: "finite {p. p permutes (UNIV::'n set)}" by (simp add: finite_permutations)
  have neP: "{p. p permutes (UNIV::'n set)} \<noteq> {}"
    using permutes_id by blast
  have term_Ck: "Ck_on k (\<lambda>y. of_int (sign p) * (\<Prod>i\<in>UNIV. M y $ i $ p i)) U"
    for p :: "'n \<Rightarrow> 'n"
  proof (rule Ck_on_mult)
    show "Ck_on k (\<lambda>y. of_int (sign p) :: real) U" using oU by (rule Ck_on_const)
    show "Ck_on k (\<lambda>y. \<Prod>i\<in>(UNIV::'n set). M y $ i $ p i) U"
      using assms by (subst Ck_on_prod, simp_all) 
  qed
  have "Ck_on k (\<lambda>y. \<Sum>p | p permutes (UNIV::'n set).
                        of_int (sign p) * (\<Prod>i\<in>UNIV. M y $ i $ p i)) U"
    by (rule Ck_on_sum[OF finP neP]) (use term_Ck in blast)
  thus ?thesis by (simp only: det_def)
qed


subsection \<open>Cramer: a linear system with \<open>C\<^sup>k\<close> data has a \<open>C\<^sup>k\<close> solution\<close>

text \<open>
  If the matrix and right-hand side of a linear system are \<open>C\<^sup>k\<close> in a parameter and the
  matrix stays nonsingular, then the solution is \<open>C\<^sup>k\<close> (by Cramer's rule).
\<close>

lemma Ck_on_solve_linear:
  fixes M :: "'a::real_normed_vector \<Rightarrow> real^'n::finite^'n"
    and b w :: "'a \<Rightarrow> real^'n"
  assumes oU: "open U"
      and MC: "\<And>i j. Ck_on k (\<lambda>y. M y $ i $ j) U"
      and bC: "\<And>i. Ck_on k (\<lambda>y. b y $ i) U"
      and nz: "\<And>y. y \<in> U \<Longrightarrow> det (M y) \<noteq> 0"
      and sol: "\<And>y. y \<in> U \<Longrightarrow> M y *v w y = b y"
  shows "Ck_on k w U"
proof (rule Ck_on_vec[OF oU])
  fix r
  have comp: "w y $ r = det (\<chi> i j. if j = r then b y $ i else M y $ i $ j) / det (M y)"
    if yU: "y \<in> U" for y
  proof -
    have "w y = (\<chi> t. det (\<chi> i j. if j = t then b y $ i else M y $ i $ j) / det (M y))"
      using cramer[OF nz[OF yU]] sol[OF yU] by blast
    thus ?thesis by simp
  qed
  have numC: "Ck_on k (\<lambda>y. det (\<chi> i j. if j = r then b y $ i else M y $ i $ j)) U"
  proof (rule Ck_on_det[OF oU])
    fix i j
    show "Ck_on k (\<lambda>y. (\<chi> i j. if j = r then b y $ i else M y $ i $ j) $ i $ j) U"
      by (cases "j = r") (simp_all add: bC MC)
  qed
  have denC: "Ck_on k (\<lambda>y. det (M y)) U" by (rule Ck_on_det[OF oU MC])
  have "Ck_on k (\<lambda>y. det (\<chi> i j. if j = r then b y $ i else M y $ i $ j) / det (M y)) U"
    by (rule Ck_on_divide[OF numC denC]) (use nz in blast)
  thus "Ck_on k (\<lambda>y. w y $ r) U"
    by (rule Ck_on_congI) (simp add: comp)
qed


subsection \<open>The \<open>C\<^sup>k\<close> implicit function theorem\<close>

text \<open>
  Starting from @{thm [source] C1_implicit_function}, differentiating \<open>F (x, g x) = 0\<close> gives
  a linear system for the derivative of \<open>g\<close>, whose matrix is nonsingular near \<open>x\<^sub>0\<close>.  If
  \<open>g\<close> is \<open>C\<^sup>j\<close>, then so are the data of the system and hence, by
  @{thm [source] Ck_on_solve_linear}, the derivative of \<open>g\<close>; induction on \<open>j\<close> gives \<open>C\<^sup>k\<close>.
  The unknown ranges over \<open>real^'n\<close> so that Cramer's rule applies.
\<close>

theorem Ck_implicit_function:
  fixes F :: "('a::euclidean_space \<times> (real^'n::finite)) \<Rightarrow> real^'n"
  assumes Ck: "Ck_on k F W"
      and k1: "1 \<le> k"
      and pW: "(x0, y0) \<in> W"
      and F0: "F (x0, y0) = 0"
      and reg: "\<exists>L. ((\<lambda>y. F (x0, y)) has_derivative L) (at y0) \<and> bij L"
  obtains U g where
      "open U" and "x0 \<in> U" and "g x0 = y0"
      and "Ck_on k g U"
      and "\<forall>x\<in>U. (x, g x) \<in> W \<and> F (x, g x) = 0"
proof -
  have Wopen: "open W" using Ck by (simp add: Ck_on_def)
  obtain m where km: "k = Suc m" using k1 by (cases k) auto
  have C1: "Ck_on (Suc 0) F W" by (rule Ck_on_mono[OF Ck]) (use k1 in simp)

  text \<open>The \<open>C\<^sup>1\<close> theorem supplies the solution map.\<close>
  obtain U0 g where U0open: "open U0" and x0U0: "x0 \<in> U0" and gx0: "g x0 = y0"
      and gdiff: "\<And>x. x \<in> U0 \<Longrightarrow> g differentiable (at x)"
      and gsol: "\<forall>x\<in>U0. (x, g x) \<in> W \<and> F (x, g x) = 0"
    by (rule C1_implicit_function[OF C1 pW F0 reg]) blast

  text \<open>The derivative of \<open>F\<close> along the graph, and its second-slot matrix.\<close>
  define DF where "DF = (\<lambda>x. frechet_derivative F (at (x, g x)))"
  define M where "M = (\<lambda>x. (\<chi> i j. DF x (0, axis j 1) $ i))"

  have Fdiff: "F differentiable (at q)" if "q \<in> W" for q
  proof -
    have "Ck_at (Suc 0) F q" using C1 that by (simp add: Ck_on_def)
    thus ?thesis by (rule Ck1_atD(1))
  qed
  have blDF: "bounded_linear (DF x)" if "x \<in> U0" for x
  proof -
    have "(x, g x) \<in> W" using gsol that by blast
    from Fdiff[OF this] show ?thesis
      unfolding DF_def
      by (metis frechet_derivative_works has_derivative_bounded_linear)
  qed
  have Mworks: "M x *v w = DF x (0, w)" if xU0: "x \<in> U0" for x w
  proof -
    have lin: "linear (\<lambda>w. DF x (0, w))"
    proof -
      interpret D: bounded_linear "DF x" by (rule blDF[OF xU0])
      show ?thesis
      proof (rule linearI)
        fix u v :: "real^'n"
        show "DF x (0, u + v) = DF x (0, u) + DF x (0, v)"
          using D.add[of "(0, u)" "(0, v)"] by simp
      next
        fix c :: real and u :: "real^'n"
        show "DF x (0, c *\<^sub>R u) = c *\<^sub>R DF x (0, u)"
          using D.scaleR[of c "(0, u)"] by simp
      qed
    qed
    have "M x = matrix (\<lambda>w. DF x (0, w))" by (simp add: M_def matrix_def)
    thus ?thesis using lin by (simp add: matrix_works)
  qed

  text \<open>At \<open>x\<^sub>0\<close> the matrix is the one that \<open>reg\<close> makes invertible.\<close>
  have detx0: "det (M x0) \<noteq> 0"
  proof -
    obtain L where Lder: "((\<lambda>y. F (x0, y)) has_derivative L) (at y0)" and bijL: "bij L"
      using reg by blast
    have slice: "((\<lambda>y. F (x0, y)) has_derivative (\<lambda>dy. DF x0 (0, dy))) (at y0)"
    proof -
      have c: "((\<lambda>y::real^'n. x0) has_derivative (\<lambda>dy. 0)) (at y0)"
        by (rule has_derivative_const)
      have i: "((\<lambda>y::real^'n. y) has_derivative (\<lambda>dy. dy)) (at y0)"
        by (rule has_derivative_ident)
      have pd: "((\<lambda>y. (x0, y)) has_derivative (\<lambda>dy. (0, dy))) (at y0)"
        using has_derivative_Pair[OF c i] by simp
      have "(F has_derivative DF x0) (at (x0, g x0))"
        unfolding DF_def using Fdiff[OF pW] gx0
        by (simp add: frechet_derivative_works)
      hence Fd: "(F has_derivative DF x0) (at (x0, y0))" by (simp add: gx0)
      from has_derivative_compose[OF pd Fd] show ?thesis by simp
    qed
    have Leq: "L = (\<lambda>dy. DF x0 (0, dy))" by (rule has_derivative_unique[OF Lder slice])
    have linL: "linear L" using Lder by (rule has_derivative_linear)
    have "inj L" using bijL by (simp add: bij_def)
    hence "det (matrix L) \<noteq> 0" using linL by (simp add: det_nz_iff_inj)
    moreover have "matrix L = M x0" by (simp add: Leq M_def matrix_def)
    ultimately show ?thesis by simp
  qed

  text \<open>Shrink to the set where the matrix stays nonsingular.\<close>
  have contM: "continuous_on U0 (\<lambda>x. det (M x))"
  proof -
    have ent: "continuous_on U0 (\<lambda>x. M x $ i $ j)" for i j
    proof (rule continuous_at_imp_continuous_on, rule ballI)
      fix x assume x: "x \<in> U0"
      have gc: "isCont g x"
        using gdiff[OF x] by (simp add: differentiable_imp_continuous_within)
      have pair: "isCont (\<lambda>x. (x, g x)) x"
        by (intro continuous_intros gc)
      have inW: "(x, g x) \<in> W" using gsol x by blast
      have "Ck_at (Suc 0) F (x, g x)" using C1 inW by (simp add: Ck_on_def)
      hence cd: "isCont (\<lambda>q. frechet_derivative F (at q) (0, axis j 1)) (x, g x)"
        by (rule Ck1_atD(2))
      have "isCont ((\<lambda>q. frechet_derivative F (at q) (0, axis j 1)) \<circ> (\<lambda>x. (x, g x))) x"
        by (rule continuous_at_compose[OF pair cd])
      hence "isCont (\<lambda>x. DF x (0, axis j 1)) x" by (simp add: o_def DF_def)
      hence "isCont (\<lambda>x. DF x (0, axis j 1) $ i) x"
        by (rule bounded_linear.continuous[OF bounded_linear_vec_nth])
      thus "isCont (\<lambda>x. M x $ i $ j) x" by (simp add: M_def)
    qed
    show ?thesis
      unfolding det_def
      by (intro continuous_on_sum continuous_on_mult continuous_on_const
                continuous_on_prod ent)
  qed
  define U where "U = U0 \<inter> {x. det (M x) \<noteq> 0}"
  have Uopen: "open U"
  proof -
    have "open ((\<lambda>x. det (M x)) -` (- {0}) \<inter> U0)"
      using continuous_on_open_vimage[OF U0open] contM by blast
    moreover have "(\<lambda>x. det (M x)) -` (- {0}) \<inter> U0 = U" by (auto simp: U_def)
    ultimately show ?thesis by simp
  qed
  have x0U: "x0 \<in> U" using x0U0 detx0 by (simp add: U_def)
  have UsubU0: "U \<subseteq> U0" by (simp add: U_def)
  have detU: "det (M x) \<noteq> 0" if "x \<in> U" for x using that by (simp add: U_def)

  text \<open>The linear system satisfied by the derivative of \<open>g\<close>.\<close>
  have gsys: "M x *v (frechet_derivative g (at x) u) = - DF x (u, 0)"
    if xU: "x \<in> U" for x u
  proof -
    have xU0: "x \<in> U0" using xU UsubU0 by blast
    have inW: "(x, g x) \<in> W" using gsol xU0 by blast
    have Fd: "(F has_derivative DF x) (at (x, g x))"
      unfolding DF_def using Fdiff[OF inW] by (simp add: frechet_derivative_works)
    have gd: "(g has_derivative frechet_derivative g (at x)) (at x)"
      using gdiff[OF xU0] by (simp add: frechet_derivative_works)
    have idd: "((\<lambda>x::'a. x) has_derivative (\<lambda>h. h)) (at x)" by (rule has_derivative_ident)
    have graph: "((\<lambda>x. (x, g x)) has_derivative
                    (\<lambda>h. (h, frechet_derivative g (at x) h))) (at x)"
      using has_derivative_Pair[OF idd gd] by simp
    have comp: "((\<lambda>x. F (x, g x)) has_derivative
                   (\<lambda>h. DF x (h, frechet_derivative g (at x) h))) (at x)"
      using has_derivative_compose[OF graph Fd] by simp
    have zero: "((\<lambda>x. F (x, g x)) has_derivative (\<lambda>h. 0)) (at x)"
    proof (rule has_derivative_transform_within_open[where f = "\<lambda>_. 0" and s = U0])
      show "((\<lambda>_::'a. 0::real^'n) has_derivative (\<lambda>h. 0)) (at x)"
        by (rule has_derivative_const)
      show "open U0" by (rule U0open)
      show "x \<in> U0" by (rule xU0)
      show "\<And>y. y \<in> U0 \<Longrightarrow> (0::real^'n) = F (y, g y)" using gsol by auto
    qed
    have vanish: "DF x (u, frechet_derivative g (at x) u) = 0"
      using fun_cong[OF has_derivative_unique[OF comp zero], of u] by simp
    have split: "DF x (u, frechet_derivative g (at x) u)
                   = DF x (u, 0) + DF x (0, frechet_derivative g (at x) u)"
    proof -
      interpret D: bounded_linear "DF x" by (rule blDF[OF xU0])
      have "(u, frechet_derivative g (at x) u)
              = (u, 0) + (0, frechet_derivative g (at x) u)" by simp
      thus ?thesis by (metis D.add)
    qed
    from vanish split have "DF x (0, frechet_derivative g (at x) u) = - DF x (u, 0)"
      by (metis add_eq_0_iff)
    thus ?thesis using Mworks[OF xU0] by simp
  qed

  text \<open>Regularity of the coefficients, given regularity of \<open>g\<close>.\<close>
  have dFCk: "Ck_on j (\<lambda>x. DF x u) U" if gj: "Ck_on j g U" and jm: "j \<le> m" for j u
  proof -
    have innerm: "Ck_on m (\<lambda>q. frechet_derivative F (at q) u) W"
      unfolding Ck_on_def
    proof (intro conjI ballI)
      show "open W" by (rule Wopen)
      fix q assume q: "q \<in> W"
      have "Ck_at (Suc m) F q" using Ck q km by (simp add: Ck_on_def)
      thus "Ck_at m (\<lambda>q'. frechet_derivative F (at q') u) q"
        by (simp only: Ck_at.simps(2))
    qed
    have inner: "Ck_on j (\<lambda>q. frechet_derivative F (at q) u) W"
      by (rule Ck_on_mono[OF innerm jm])
    have graph: "Ck_on j (\<lambda>x. (x, g x)) U"
      by (rule Ck_on_Pair[OF Ck_on_id[OF Uopen] gj])
    have img: "\<And>x. x \<in> U \<Longrightarrow> (x, g x) \<in> W" using gsol UsubU0 by blast
    show ?thesis
      unfolding DF_def by (rule Ck_on_compose[OF inner graph img])
  qed

  text \<open>The bootstrap induction.\<close>
  have boot: "j \<le> k \<Longrightarrow> Ck_on j g U" for j
  proof (induction j)
    case 0
    show ?case
      unfolding Ck_on_def
    proof (intro conjI ballI)
      show "open U" by (rule Uopen)
      fix x assume x: "x \<in> U"
      have "continuous (at x) g"
        using gdiff[OF UsubU0[THEN subsetD, OF x]]
        by (simp add: differentiable_imp_continuous_within)
      thus "Ck_at 0 g x" by simp
    qed
  next
    case (Suc j)
    have jk: "j \<le> k" using Suc.prems by simp
    have jm: "j \<le> m" using Suc.prems km by simp
    have IH: "Ck_on j g U" by (rule Suc.IH[OF jk])
    have derCk: "Ck_on j (\<lambda>x. frechet_derivative g (at x) u) U" for u
    proof (rule Ck_on_solve_linear[OF Uopen])
      fix i jj
      have "Ck_on j (\<lambda>x. DF x (0, axis jj 1) $ i) U"
        by (rule Ck_on_component[OF dFCk[OF IH jm]])
      thus "Ck_on j (\<lambda>x. M x $ i $ jj) U" by (simp add: M_def)
    next
      fix i
      have "Ck_on j (\<lambda>x. DF x (u, 0)) U" by (rule dFCk[OF IH jm])
      hence "Ck_on j (\<lambda>x. - DF x (u, 0)) U" by (rule Ck_on_neg)
      thus "Ck_on j (\<lambda>x. (- DF x (u, 0)) $ i) U" by (rule Ck_on_component)
    next
      show "\<And>x. x \<in> U \<Longrightarrow> det (M x) \<noteq> 0" by (rule detU)
    next
      show "\<And>x. x \<in> U \<Longrightarrow> M x *v frechet_derivative g (at x) u = - DF x (u, 0)"
        by (rule gsys)
    qed
    show ?case
      unfolding Ck_on_def
    proof (intro conjI ballI)
      show "open U" by (rule Uopen)
      fix x assume x: "x \<in> U"
      show "Ck_at (Suc j) g x"
        unfolding Ck_at.simps(2)
      proof (intro conjI allI)
        show "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. Ck_at j g y)"
          using Uopen x IH by (auto simp: Ck_on_def)
        show "g differentiable (at x)" by (rule gdiff[OF UsubU0[THEN subsetD, OF x]])
        fix v
        show "Ck_at j (\<lambda>y. frechet_derivative g (at y) v) x"
          using derCk[of v] x by (simp add: Ck_on_def)
      qed
    qed
  qed
  have solU: "\<forall>x\<in>U. (x, g x) \<in> W \<and> F (x, g x) = 0" using gsol UsubU0 by blast
  show ?thesis
    by (rule that[OF Uopen x0U gx0 boot[OF order_refl] solU])
qed

end
