section \<open>Artin's lemma: a finite automorphism group bounds the degree over its fixed field\<close>

theory Artin
  imports Galois_Correspondence Linear_System Iso_Extension_Tower
begin

text \<open>Let \<open>H\<close> be a \<^emph>\<open>finite\<close> group of automorphisms of a subfield \<open>K\<close> of a field, and let
  @{term "fixed_field K H"} be the subfield it fixes pointwise.  \<^emph>\<open>Artin's lemma\<close> bounds the
  extension \<open>K\<close> over that fixed field by the order of the group: any @{term "card H + 1"} elements
  of \<open>K\<close> are linearly dependent over @{term "fixed_field K H"}.

  The proof is the linear-algebra pigeonhole principle.  Given elements @{text "x\<^sub>1, \<dots>, x\<^sub>n"} of
  \<open>K\<close> with @{text "n > card H"}, consider the homogeneous system

  \<^item> one equation per automorphism @{text "\<sigma> \<in> H"}, namely @{text "\<Sum>\<^sub>j \<sigma>(x\<^sub>j) c\<^sub>j = 0"},
  in the unknowns @{term "c\<^sub>j"}.  There are more unknowns than equations, so
  @{thm [source] Subfield.underdetermined_solution} supplies a nontrivial solution in \<open>K\<close> --- and
  the equation belonging to the identity automorphism is precisely the required dependence
  @{text "\<Sum>\<^sub>j x\<^sub>j c\<^sub>j = 0"}.

  Two things deserve emphasis.  First, the solution produced this way has its coefficients in
  \<^emph>\<open>@{term K}\<close>.  The simultaneous-system descent below, \<open>artin_solution_over_fixed_field\<close>,
  is what puts a nontrivial solution into the fixed field; the vector-space degree assembly and the
  final group equality live in \<open>Artin_Degree\<close>.  Second, the argument never mentions
  separability or normality: finiteness of @{term H} is the only hypothesis, which is what makes this
  lemma the engine of the finite half of the Galois correspondence.\<close>


subsection \<open>Artin's lemma\<close>

text \<open>The system to be solved has one equation per automorphism and one unknown per element, so its
  coefficient matrix is @{term "\<lambda>\<sigma> j. \<sigma> (x j)"}: a genuinely two-index family, indexed by
  \<^emph>\<open>functions\<close> on one side and by the element index on the other.  This is exactly the shape
  @{thm [source] Subfield.underdetermined_solution} was stated for, indices ranging over arbitrary
  finite sets rather than initial segments.\<close>

theorem artin_lemma:
  fixes H :: "('a :: field \<Rightarrow> 'a) set" and x :: "'j \<Rightarrow> 'a"
  assumes K: "Subfield K"
    and finH: "finite H" and HG: "H \<subseteq> field_auto K F"
    and finJ: "finite J" and card: "card H < card J"
    and xK: "\<And>j. j \<in> J \<Longrightarrow> x j \<in> K"
  shows "\<exists>c. (\<forall>j. c j \<in> K) \<and> (\<exists>j \<in> J. c j \<noteq> 0) \<and> (\<forall>\<sigma> \<in> H. (\<Sum>j \<in> J. \<sigma> (x j) * c j) = 0)"
proof -
  interpret K: Subfield K by (rule K)
  \<comment> \<open>The coefficients \<open>\<sigma> (x j)\<close> lie in @{term K}, since an automorphism maps @{term K} onto itself.
    Stated as an explicit @{text \<forall>} rather than with @{text \<And>}: as a rule with schematic variables it
    unifies with the closure premise in more than one way, which @{text OF} rejects outright
    (\<open>OF: multiple unifiers\<close>).\<close>
  have entries: "\<forall>\<sigma> \<in> H. \<forall>j \<in> J. \<sigma> (x j) \<in> K"
    using HG xK by (blast intro: field_auto_closed)
  \<comment> \<open>Every index of the hypothesis is pinned explicitly, or the matrix argument @{term x} comes back
    applied to an unknown index function --- see \<open>Linear_System\<close>.\<close>
  show ?thesis
    using K.underdetermined_solution
        [where A = "\<lambda>\<sigma> j. \<sigma> (x j)" and I = H and J = J, OF finH finJ card]
    using entries by blast
qed

text \<open>The advertised form: more than @{term "card H"} elements of @{term K} admit a nontrivial
  vanishing @{term K}-linear combination against \<^emph>\<open>every\<close> automorphism of @{term H} at once, and in
  particular --- taking the identity, which lies in every Galois group --- against the elements
  themselves.\<close>
corollary artin_lemma_dependence:
  fixes H :: "('a :: field \<Rightarrow> 'a) set" and x :: "'j \<Rightarrow> 'a"
  assumes K: "Subfield K"
    and finH: "finite H" and HG: "H \<subseteq> field_auto K F" and id: "identity K \<in> H"
    and finJ: "finite J" and card: "card H < card J"
    and xJK: "x ` J \<subseteq> K"
  shows "\<exists>c. (\<forall>j. c j \<in> K) \<and> (\<exists>j \<in> J. c j \<noteq> 0) \<and> (\<Sum>j \<in> J. x j * c j) = 0"
proof -
  have xK: "\<And>j. j \<in> J \<Longrightarrow> x j \<in> K" using xJK by blast
  obtain c where cK: "\<forall>j. c j \<in> K" and cnz: "\<exists>j \<in> J. c j \<noteq> 0"
    and ceq: "\<forall>\<sigma> \<in> H. (\<Sum>j \<in> J. \<sigma> (x j) * c j) = 0"
    using artin_lemma[where x = x, OF K finH HG finJ card xK] by blast
  \<comment> \<open>The equation belonging to the identity automorphism is the dependence we want.\<close>
  have "(\<Sum>j \<in> J. identity K (x j) * c j) = 0" using ceq id by blast
  moreover have "\<And>j. j \<in> J \<Longrightarrow> identity K (x j) = x j" using xK by (simp add: identity_apply)
  ultimately have "(\<Sum>j \<in> J. x j * c j) = 0" by simp
  then show ?thesis using cK cnz by blast
qed


text \<open>For a genuine Galois subgroup the identity premise is automatic.  This is the convenient
  interface for the later fixed-field argument, while @{thm [source] artin_lemma} deliberately
  retains the extra generality of an arbitrary finite automorphism family.\<close>
corollary artin_lemma_subgroup_dependence:
  fixes H :: "('a :: field \<Rightarrow> 'a) set" and x :: "'j \<Rightarrow> 'a"
  assumes K: "Subfield K"
    and H: "H \<in> galois_subgroups K F" and finH: "finite H"
    and finJ: "finite J" and card: "card H < card J"
    and xJK: "x ` J \<subseteq> K"
  shows "\<exists>c. (\<forall>j. c j \<in> K) \<and> (\<exists>j \<in> J. c j \<noteq> 0) \<and> (\<Sum>j \<in> J. x j * c j) = 0"
proof -
  interpret H: Subgroup H "field_auto K F" "compose K" "identity K"
    using H by (simp add: galois_subgroups_iff)
  show ?thesis
    by (rule artin_lemma_dependence[OF K finH H.subset H.sub_unit_closed finJ card xJK])
qed

subsection \<open>Transporting a dependence along an automorphism\<close>

text \<open>The step that will drive the descent to the fixed field: an automorphism carries a vanishing
  linear combination to another vanishing linear combination, over the transported coefficients.
  Multiplicativity handles each summand, additivity the sum, and @{thm [source] field_auto_zero} the
  right-hand side.

  This is the mechanism behind the minimality argument sketched at the end.  If @{term c} is a
  dependence among the @{term "x j"} with the fewest nonzero coefficients, normalised so that some
  @{text "c k = 1"}, then @{text "\<lambda>j. \<sigma> (c j)"} is another dependence, also with @{text "\<sigma> (c k) = 1"}
  and supported in the same places.  Their difference is a shorter dependence, so minimality forces it
  to vanish, i.e. @{text "\<sigma> (c j) = c j"} for every @{text "\<sigma> \<in> H"} --- which is exactly to say that
  the coefficients lie in @{term "fixed_field K H"}.\<close>
lemma field_auto_transports_dependence:
  assumes K: "Subfield K" and s: "\<sigma> \<in> field_auto K F"
    and finJ: "finite J"
    and xK: "\<And>j. j \<in> J \<Longrightarrow> x j \<in> K" and cK: "\<And>j. j \<in> J \<Longrightarrow> c j \<in> K"
    and dep: "(\<Sum>j \<in> J. x j * c j) = 0"
  shows "(\<Sum>j \<in> J. \<sigma> (x j) * \<sigma> (c j)) = 0"
proof -
  interpret K: Subfield K by (rule K)
  have "(\<Sum>j \<in> J. \<sigma> (x j) * \<sigma> (c j)) = (\<Sum>j \<in> J. \<sigma> (x j * c j))"
    using xK cK by (intro sum.cong refl) (simp add: field_auto_mult[OF s])
  also have "\<dots> = \<sigma> (\<Sum>j \<in> J. x j * c j)"
    using xK cK by (intro field_auto_sum[OF K s, symmetric]) (blast intro: K.mult_closed)
  also have "\<dots> = 0" using dep field_auto_zero[OF K s] by simp
  finally show ?thesis .
qed


text \<open>Applying one subgroup automorphism to the coefficients preserves the simultaneous system.
  For a target row @{term \<rho>}, apply @{term \<sigma>} to the row indexed by
  \<open>compose K (inverse \<sigma>) \<rho>\<close>; the group laws reduce the transformed row back to
  @{term \<rho>}.\<close>
lemma field_auto_transports_artin_solution:
  fixes H :: "('a :: field \<Rightarrow> 'a) set"
  assumes K: "Subfield K" and H: "H \<in> galois_subgroups K F"
    and s: "\<sigma> \<in> H" and finJ: "finite J"
    and xK: "\<And>j. j \<in> J \<Longrightarrow> x j \<in> K"
    and cK: "\<And>j. j \<in> J \<Longrightarrow> c j \<in> K"
    and equations: "\<forall>\<rho> \<in> H. (\<Sum>j \<in> J. \<rho> (x j) * c j) = 0"
    and "\<rho> \<in> H"
  shows "(\<Sum>j \<in> J. \<rho> (x j) * \<sigma> (c j)) = 0"
proof -
  interpret H: Subgroup H "field_auto K F" "compose K" "identity K"
    using H by (simp add: galois_subgroups_iff)
  let ?\<tau> = "compose K (H.sub.inverse \<sigma>) \<rho>"
  have invH: "H.sub.inverse \<sigma> \<in> H"
    using s by simp
  have t: "?\<tau> \<in> H"
    using invH \<open>\<rho> \<in> H\<close> by (rule H.sub.composition_closed)
  have dep: "(\<Sum>j \<in> J. ?\<tau> (x j) * c j) = 0"
    using equations t by blast
  have txK: "\<And>j. j \<in> J \<Longrightarrow> ?\<tau> (x j) \<in> K"
    using H.subset t xK by (blast intro: field_auto_closed)
  have sAuto: "\<sigma> \<in> field_auto K F"
    using H.subset s by blast
  have transported: "(\<Sum>j \<in> J. \<sigma> (?\<tau> (x j)) * \<sigma> (c j)) = 0"
    using field_auto_transports_dependence[OF K sAuto finJ txK cK dep] .
  have "\<And>j. j \<in> J \<Longrightarrow> \<sigma> (?\<tau> (x j)) = \<rho> (x j)"
    using H.sub.invertible H.sub.invertible_right_inverse2 \<open>\<rho> \<in> H\<close> s xK by (metis compose_eq)
  with transported show "(\<Sum>j \<in> J. \<rho> (x j) * \<sigma> (c j)) = 0"
    by simp
qed


subsection \<open>Descending the coefficients to the fixed field\<close>

text \<open>The coefficients of a dependence can be taken to lie in the fixed field,
  not merely in @{term K}.

  The device is minimality.  Among all nontrivial dependences of the @{term "x j"} choose one whose
  \<^emph>\<open>support\<close> @{term "{j \<in> J. c j \<noteq> 0}"} is smallest, and scale it so that some distinguished
  coefficient equals @{term 1}.  For @{text "\<sigma> \<in> H"} the transported family
  @{text "\<lambda>j. \<sigma> (c j)"} is again a dependence --- this is
  @{thm [source] field_auto_transports_dependence}, and it needs @{term \<sigma>} to fix the @{term "x j"},
  which is why the @{term "x j"} are taken in the fixed field's \<^emph>\<open>ambient\<close> position below.\<close>

lemma dependence_difference:
  fixes c d :: "'j \<Rightarrow> 'a :: field"
  assumes finJ: "finite J"
    and dep_c: "(\<Sum>j \<in> J. x j * c j) = 0" and dep_d: "(\<Sum>j \<in> J. x j * d j) = 0"
  shows "(\<Sum>j \<in> J. x j * (c j - d j)) = 0"
  by (simp add: dep_c dep_d right_diff_distrib' sum_subtractf)

text \<open>The simultaneous system version of the minimal-support descent.  Unlike the specialized
  fixed-vector descent below, this does not assume that the vectors are fixed by
  @{term H}: the equations contain every row @{term "\<rho> \<in> H"}, and
  @{thm [source] field_auto_transports_artin_solution} transports a solution to another solution of
  that same system.  This is the form needed for the genuine Artin bound.\<close>
theorem artin_solution_over_fixed_field:
  fixes H :: "('a :: field \<Rightarrow> 'a) set" and x :: "'j \<Rightarrow> 'a"
  assumes K: "Subfield K" and H: "H \<in> galois_subgroups K F"
    and finJ: "finite J" and xK: "\<And>j. j \<in> J \<Longrightarrow> x j \<in> K"
    and exsol: "\<exists>c. (\<forall>j. c j \<in> K) \<and> (\<exists>j \<in> J. c j \<noteq> 0) \<and> (\<forall>\<rho> \<in> H. (\<Sum>j \<in> J. \<rho> (x j) * c j) = 0)"
  shows "\<exists>c. (\<forall>j \<in> J. c j \<in> fixed_field K H) \<and> (\<exists>j \<in> J. c j \<noteq> 0) \<and> (\<forall>\<rho> \<in> H. (\<Sum>j \<in> J. \<rho> (x j) * c j) = 0)"
proof -
  interpret KS: Subfield K by (rule K)
  define Sol where
    "Sol \<equiv> (\<lambda>c :: 'j \<Rightarrow> 'a. (\<forall>j. c j \<in> K) \<and> (\<exists>j \<in> J. c j \<noteq> 0) \<and> (\<forall>\<rho> \<in> H. (\<Sum>j \<in> J. \<rho> (x j) * c j) = 0))"
  define supp where "supp = (\<lambda>c :: 'j \<Rightarrow> 'a. {j \<in> J. c j \<noteq> 0})"
  define Q where "Q = (\<lambda>n. \<exists>c. Sol c \<and> card (supp c) = n)"
  have "Q (LEAST n. Q n)" using exsol by (metis LeastI Sol_def Q_def)
  then obtain c where solc: "Sol c" and cmin: "card (supp c) = (LEAST n. Q n)"
    unfolding Q_def by blast
  have minimal: "card (supp c) \<le> card (supp d)" if "Sol d" for d
    by (metis Least_le Q_def cmin that)
  from solc have cK: "\<And>j. c j \<in> K" and ceq: "\<And>\<rho>. \<rho> \<in> H \<Longrightarrow> (\<Sum>j \<in> J. \<rho> (x j) * c j) = 0"
    by (simp_all add: Sol_def)
  from solc obtain k where kJ: "k \<in> J" and cknz: "c k \<noteq> 0"
    by (auto simp: Sol_def)
  define e where "e \<equiv> (\<lambda>j. c j / c k)"
  have eK: "\<And>j. e j \<in> K" using cK by (simp add: e_def KS.divide_closed)
  have ek: "e k = 1" using cknz by (simp add: e_def)
  have esupp: "supp e = supp c" using cknz by (auto simp: supp_def e_def)
  have eeq: "(\<Sum>j \<in> J. \<rho> (x j) * e j) = 0" if r: "\<rho> \<in> H" for \<rho>
    using ceq[OF r] by (simp add: e_def divide_simps flip: sum_divide_distrib)
  have depe: "Sol e"
    unfolding Sol_def using eK ek kJ eeq by (intro conjI allI bexI[of _ k]) (simp_all)
  have fixed: "\<sigma> (e j) = e j" if s: "\<sigma> \<in> H" and jJ: "j \<in> J" for \<sigma> j
  proof (rule ccontr)
    assume ne: "\<sigma> (e j) \<noteq> e j"
    have sG: "\<sigma> \<in> field_auto K F"
      using H galois_subgroups_subset s by blast
    define d where "d = (\<lambda>i. e i - \<sigma> (e i))"
    have eqe: "\<forall>\<rho> \<in> H. (\<Sum>i \<in> J. \<rho> (x i) * e i) = 0"
      using depe by (simp add: Sol_def)
    have transported_all:
        "\<forall>\<rho> \<in> H. (\<Sum>i \<in> J. \<rho> (x i) * \<sigma> (e i)) = 0"
      using field_auto_transports_artin_solution[OF K H s finJ xK eK eqe] by blast
    have dep_d: "(\<Sum>i \<in> J. \<rho> (x i) * d i) = 0" if r: "\<rho> \<in> H" for \<rho>
      using r eeq transported_all unfolding d_def
      by (simp add: sum_subtractf right_diff_distrib)
    have dK: "\<And>i. d i \<in> K"
      unfolding d_def using eK sG by (blast intro: KS.diff_closed field_auto_closed)
    have depd: "Sol d"
      using Sol_def dK d_def dep_d jJ ne by force
    have dk: "d k = 0" using ek field_auto_one[OF sG] by (simp add: d_def)
    have sub: "supp d \<subseteq> supp e - {k}"
      using field_auto_zero K d_def dk sG supp_def by fastforce
    have fin_e: "finite (supp e)" using finJ by (simp add: supp_def)
    have k_e: "k \<in> supp e" using kJ ek by (simp add: supp_def)
    have "card (supp d) \<le> card (supp e - {k})" using sub fin_e by (intro card_mono) blast
    also have "\<dots> < card (supp e)"
      using fin_e k_e by (meson card_Diff1_less)
    finally show False using minimal[OF depd] esupp by simp
  qed
  show ?thesis
    using Sol_def depe fixed by (smt (cvc5, dec_internal_enum_inst_sum) fixed_field_memI)
qed

text \<open>Note that the @{term "x j"} are \<^emph>\<open>fixed\<close> by every @{text "\<sigma> \<in> H"}.  This is essential and not a
  technicality: @{thm [source] field_auto_transports_dependence} turns a dependence of the
  @{term "x j"} into a dependence of the images @{term "\<sigma> (x j)"}, and only when those images are the
  @{term "x j"} again is the result a dependence of the \<^emph>\<open>same\<close> family, so that subtracting it from
  the original stays inside the system.  In the intended application the roles are reversed from what
  one might expect: it is the \<^emph>\<open>vectors\<close> that are taken over the fixed field and the
  \<^emph>\<open>coefficients\<close> that are unknown and must be shown to descend.

  Also, @{term H} is closed under composition --- a subgroup of the Galois group --- which is what
  makes @{text "\<sigma> (c j) = c j"} for all @{text "\<sigma> \<in> H"} equivalent to @{term "c j \<in> fixed_field K H"}.
  In fact only membership of @{term "\<sigma> ` H \<subseteq> field_auto K F"} is used below; the group structure is
  what makes the conclusion \<^emph>\<open>mean\<close> what it says.\<close>
theorem dependence_over_fixed_field:
  fixes H :: "('a :: field \<Rightarrow> 'a) set" and x :: "'j \<Rightarrow> 'a"
  assumes K: "Subfield K"
    and HG: "H \<subseteq> field_auto K F"
    and finJ: "finite J"
    and xK: "\<And>j. j \<in> J \<Longrightarrow> x j \<in> K"
    and xfix: "\<And>\<sigma> j. \<lbrakk> \<sigma> \<in> H; j \<in> J \<rbrakk> \<Longrightarrow> \<sigma> (x j) = x j"
    and exdep: "\<exists>c. (\<forall>j. c j \<in> K) \<and> (\<exists>j \<in> J. c j \<noteq> 0) \<and> (\<Sum>j \<in> J. x j * c j) = 0"
  shows "\<exists>c. (\<forall>j \<in> J. c j \<in> fixed_field K H) \<and> (\<exists>j \<in> J. c j \<noteq> 0)
             \<and> (\<Sum>j \<in> J. x j * c j) = 0"
proof -
  interpret K: Subfield K by (rule K)
  \<comment> \<open>The dependences of the @{term "x j"}, and the sizes of their supports.\<close>
  define Dep where
    "Dep \<equiv> (\<lambda>c :: 'j \<Rightarrow> 'a. (\<forall>j. c j \<in> K) \<and> (\<exists>j \<in> J. c j \<noteq> 0) \<and> (\<Sum>j \<in> J. x j * c j) = 0)"
  define supp where "supp \<equiv> (\<lambda>c :: 'j \<Rightarrow> 'a. {j \<in> J. c j \<noteq> 0})"
  define Q where "Q \<equiv> (\<lambda>n. \<exists>c. Dep c \<and> card (supp c) = n)"
  \<comment> \<open>Choose a dependence of least support, exactly as @{text minpoly_exists} chooses an annihilator
    of least degree.\<close>
  have "Q (LEAST n. Q n)" using exdep by (metis LeastI Dep_def Q_def)
  then obtain c where depc: "Dep c" and cmin: "card (supp c) = (LEAST n. Q n)"
    unfolding Q_def by blast
  have minimal: "card (supp c) \<le> card (supp d)" if "Dep d" for d
    by (metis Least_le Q_def cmin that)
  from depc have cK: "\<And>j. c j \<in> K" and ceq: "(\<Sum>j \<in> J. x j * c j) = 0"
    by (simp_all add: Dep_def)
  from depc obtain k where kJ: "k \<in> J" and cknz: "c k \<noteq> 0" by (auto simp: Dep_def)
  \<comment> \<open>Normalise: divide through by @{term "c k"}.  This changes neither the support nor the property
    of being a dependence, and it makes the distinguished coefficient @{term 1}.\<close>
  define e where "e = (\<lambda>j. c j / c k)"
  have eK: "\<And>j. e j \<in> K" using cK by (simp add: e_def K.divide_closed)
  have ek: "e k = 1" using cknz by (simp add: e_def)
  have esupp: "supp e = supp c" using cknz by (auto simp: supp_def e_def)
  have eeq: "(\<Sum>j \<in> J. x j * e j) = 0"
    using ceq e_def
    by (metis (mono_tags, lifting) div_0 sum.cong sum_divide_distrib times_divide_eq_right)
  have depe: "Dep e"
    unfolding Dep_def using eK eeq by (intro conjI allI bexI[of _ k]) (simp_all add: ek kJ)
  \<comment> \<open>The heart of it: every @{term \<sigma>} in @{term H} fixes every coefficient of @{term e}.  Suppose not,
    and let @{term d} be the difference of @{term e} and its transport.  Then @{term d} is a
    dependence, it is nonzero somewhere (where @{term \<sigma>} moved a coefficient), and its support omits
    @{term k} because both families have @{term 1} there.  So @{term d} is a dependence of strictly
    smaller support, contradicting minimality.\<close>
  have fixed: "\<sigma> (e j) = e j" if s: "\<sigma> \<in> H" and jJ: "j \<in> J" for \<sigma> j
  proof (rule ccontr)
    assume ne: "\<not> ?thesis"
    have sG: "\<sigma> \<in> field_auto K F" using s HG by blast
    define d where "d = (\<lambda>i. e i - \<sigma> (e i))"
    \<comment> \<open>The transport is a dependence of the @{term "x i"} themselves, because @{term \<sigma>} fixes them.\<close>
    have "(\<Sum>i \<in> J. \<sigma> (x i) * \<sigma> (e i)) = 0"
      using eeq eK xK by (intro field_auto_transports_dependence[OF K sG finJ]) auto
    then have dep_t: "(\<Sum>i \<in> J. x i * \<sigma> (e i)) = 0" using xfix[OF s] by simp
    have dep_d: "(\<Sum>i \<in> J. x i * d i) = 0"
      unfolding d_def using eeq dep_t by (rule dependence_difference[OF finJ])
    have dK: "\<And>i. d i \<in> K"
      unfolding d_def using eK sG by (blast intro: K.diff_closed field_auto_closed)
    have dnz: "d j \<noteq> 0" using ne by (simp add: d_def)
    have depd: "Dep d" using dK dnz jJ dep_d by (auto simp: Dep_def)
    \<comment> \<open>@{term k} drops out: both families take the value @{term 1} there.\<close>
    have dk: "d k = 0" using ek field_auto_one[OF sG] by (simp add: d_def)
    have sub: "supp d \<subseteq> supp e - {k}"
      using field_auto_zero Diff_iff K d_def dk empty_iff insert_iff mem_Collect_eq right_minus_eq
        sG supp_def by fastforce
    have fin_e: "finite (supp e)" using finJ by (simp add: supp_def)
    have k_e: "k \<in> supp e" using kJ ek by (simp add: supp_def)
    \<comment> \<open>Removing an element of a finite set drops the cardinality; @{term "supp d"} is inside what is
      left.\<close>
    have "card (supp d) \<le> card (supp e - {k})" using sub fin_e by (intro card_mono) blast
    also have "\<dots> < card (supp e)"
      using fin_e k_e by (meson card_Diff1_less_iff)
    finally show False using minimal[OF depd] esupp by simp
  qed
  \<comment> \<open>Fixed by every element of @{term H} and lying in @{term K} is exactly membership of the fixed
    field.\<close>
  show ?thesis
    using Dep_def depe fixed by (metis (lifting) fixed_field_memI)
qed


subsection \<open>Dedekind's lemma: distinct automorphisms are linearly independent\<close>

text \<open>The reverse direction.  Distinct field automorphisms are linearly independent as functions:
  if @{text "\<Sum>\<^sub>\<sigma> a\<^sub>\<sigma> \<sigma>(z) = 0"} for \<^emph>\<open>every\<close> @{term z} in @{term K}, with the @{term \<sigma>} pairwise
  distinct, then all the coefficients @{term "a \<sigma>"} vanish.

  The proof is by induction on the number of automorphisms involved, and the inductive step is a
  small piece of cunning.  Suppose the relation holds for a set @{term "insert \<sigma>\<^sub>0 S"} and, for a
  contradiction, that it is nontrivial.  Pick @{term \<tau>} in @{term S} and, since @{term \<tau>} and
  @{term \<sigma>\<^sub>0} are distinct automorphisms, an element @{term y} of @{term K} with
  @{term "\<sigma>\<^sub>0 y \<noteq> \<tau> y"}.  Now evaluate the relation at @{term "y * z"} rather than at @{term z}: by
  multiplicativity this multiplies the @{term \<sigma>}-th term by @{term "\<sigma> y"}.  Subtracting
  @{term "\<sigma>\<^sub>0 y"} times the original relation annihilates the @{term \<sigma>\<^sub>0} term, leaving a relation on
  @{term S} alone whose @{term \<tau>}-coefficient is @{term "a \<tau> * (\<tau> y - \<sigma>\<^sub>0 y) \<noteq> 0"}.\<close>

lemma character_relation_scaled:
  assumes K: "Subfield K" and finS: "finite S"
    and SG: "S \<subseteq> field_auto K F"
    and rel: "\<And>z. z \<in> K \<Longrightarrow> (\<Sum>\<sigma> \<in> S. a \<sigma> * \<sigma> z) = 0"
    and y: "y \<in> K" and z: "z \<in> K"
  shows "(\<Sum>\<sigma> \<in> S. (a \<sigma> * \<sigma> y) * \<sigma> z) = 0"
proof -
  interpret K: Subfield K by (rule K)
  have mult: "\<sigma> (y * z) = \<sigma> y * \<sigma> z" if "\<sigma> \<in> S" for \<sigma>
    using that SG y z by (blast intro: field_auto_mult)
  have "(\<Sum>\<sigma> \<in> S. (a \<sigma> * \<sigma> y) * \<sigma> z) = (\<Sum>\<sigma> \<in> S. a \<sigma> * \<sigma> (y * z))"
    by (simp add: mult mult.assoc)
  also have "\<dots> = 0" using rel y z by (simp add: K.mult_closed)
  finally show ?thesis .
qed

text \<open>Dedekind's lemma.  The coefficients are arbitrary field elements; no subfield hypothesis on
  them is needed, and none is available in the intended application.\<close>
theorem dedekind_independence:
  fixes S :: "('a :: field \<Rightarrow> 'a) set" and a :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"
  assumes K: "Subfield K"
  shows "\<lbrakk> finite S; S \<subseteq> field_auto K F; \<And>z. z \<in> K \<Longrightarrow> (\<Sum>\<sigma> \<in> S. a \<sigma> * \<sigma> z) = 0 \<rbrakk>
         \<Longrightarrow> \<forall>\<sigma> \<in> S. a \<sigma> = 0"
proof (induction S arbitrary: a rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert \<sigma>\<^sub>0 S)
  interpret K: Subfield K by (rule K)
  \<comment> \<open>@{text finite_induct} consumes the finiteness premise, so the remaining two are the subset and
    the relation.  Named rather than indexed, since the offset is easy to get wrong.\<close>
  note insG = insert.prems(1) and insrel = insert.prems(2)
  have s0G: "\<sigma>\<^sub>0 \<in> field_auto K F" and SG: "S \<subseteq> field_auto K F" using insG by auto
  have rel: "\<And>z. z \<in> K \<Longrightarrow> a \<sigma>\<^sub>0 * \<sigma>\<^sub>0 z + (\<Sum>\<sigma> \<in> S. a \<sigma> * \<sigma> z) = 0"
    using insrel insert.hyps by simp
  \<comment> \<open>Every coefficient indexed by @{term S} vanishes.  Given that, the @{term \<sigma>\<^sub>0} coefficient
    vanishes too, by evaluating the relation at @{term 1}.\<close>
  have S_zero: "a \<tau> = 0" if "\<tau> \<in> S" for \<tau>
  proof (rule ccontr)
    assume atnz: "\<not> ?thesis"
    have tG: "\<tau> \<in> field_auto K F" using \<open>\<tau> \<in> S\<close> SG by blast
    \<comment> \<open>Distinct automorphisms differ at some point of @{term K}: both are extensional on @{term K},
      so agreeing there would make them equal.\<close>
    have tne: "\<tau> \<noteq> \<sigma>\<^sub>0" using \<open>\<tau> \<in> S\<close> insert.hyps by blast
    obtain y where yK: "y \<in> K" and diff: "\<sigma>\<^sub>0 y \<noteq> \<tau> y"
      using s0G tG tne by (metis (no_types, lifting) ext PiE_E field_auto_mem_iff)
    \<comment> \<open>Two relations on @{term "insert \<sigma>\<^sub>0 S"}: the original scaled by @{term "\<sigma>\<^sub>0 y"}, and the one
      obtained by evaluating at @{term "y * z"}.  Both have the same @{term \<sigma>\<^sub>0} term.\<close>
    define b where "b = (\<lambda>\<sigma>. a \<sigma> * (\<sigma> y - \<sigma>\<^sub>0 y))"
    have "(\<Sum>\<sigma> \<in> S. b \<sigma> * \<sigma> z) = 0" if zK: "z \<in> K" for z
    proof -
      have scaled: "(\<Sum>\<sigma> \<in> insert \<sigma>\<^sub>0 S. (a \<sigma> * \<sigma> y) * \<sigma> z) = 0"
        by (rule character_relation_scaled[OF K _ insG insrel yK zK]) (simp add: insert.hyps)
      have orig: "(\<Sum>\<sigma> \<in> insert \<sigma>\<^sub>0 S. (a \<sigma> * \<sigma>\<^sub>0 y) * \<sigma> z) = 0"
      proof -
        have "(\<Sum>\<sigma> \<in> insert \<sigma>\<^sub>0 S. (a \<sigma> * \<sigma>\<^sub>0 y) * \<sigma> z) = \<sigma>\<^sub>0 y * (\<Sum>\<sigma> \<in> insert \<sigma>\<^sub>0 S. a \<sigma> * \<sigma> z)"
          by (simp add: sum_distrib_left mult.commute mult.left_commute)
        also have "\<dots> = 0" using insrel zK by simp
        finally show ?thesis .
      qed
      \<comment> \<open>Subtract.  Splitting the sum of differences into a difference of sums is done as an explicit
        calculation: left to one @{method simp} the goal is a three-way rearrangement of products and
        it does not close.\<close>
      have "(\<Sum>\<sigma> \<in> insert \<sigma>\<^sub>0 S. b \<sigma> * \<sigma> z)
            = (\<Sum>\<sigma> \<in> insert \<sigma>\<^sub>0 S. (a \<sigma> * \<sigma> y) * \<sigma> z) - (\<Sum>\<sigma> \<in> insert \<sigma>\<^sub>0 S. (a \<sigma> * \<sigma>\<^sub>0 y) * \<sigma> z)"
        unfolding b_def by (simp add: sum_subtractf left_diff_distrib right_diff_distrib mult.assoc)
      also have "\<dots> = 0" using scaled orig by simp
      finally have "(\<Sum>\<sigma> \<in> insert \<sigma>\<^sub>0 S. b \<sigma> * \<sigma> z) = 0" .
      moreover have "b \<sigma>\<^sub>0 = 0" by (simp add: b_def)
      ultimately show ?thesis using insert.hyps by simp
    qed
    \<comment> \<open>So the induction hypothesis applies to @{term S} with coefficients @{term b} --- but
      @{term "b \<tau>"} is a product of two nonzero factors.\<close>
    then have "\<forall>\<sigma> \<in> S. b \<sigma> = 0" using insert.IH[where a = b, OF SG] by blast
    then show False using \<open>\<tau> \<in> S\<close> atnz diff by (force simp: b_def)
  qed
  \<comment> \<open>Finally the leading coefficient.\<close>
  have "a \<sigma>\<^sub>0 = 0"
  proof -
    have "a \<sigma>\<^sub>0 * \<sigma>\<^sub>0 1 + (\<Sum>\<sigma> \<in> S. a \<sigma> * \<sigma> 1) = 0" using rel K.one_closed by blast
    moreover have "(\<Sum>\<sigma> \<in> S. a \<sigma> * \<sigma> 1) = 0" using S_zero by simp
    ultimately show ?thesis using field_auto_one[OF s0G] by simp
  qed
  then show ?case using S_zero by blast
qed


text \<open>This theory supplies the two difficult
  ingredients for Artin's theorem: the pigeonhole dependence and the descent of its coefficients
  into the fixed field.  The vector-space degree assembly and the final finite-group equality live
  in \<open>Artin_Degree\<close>.

  The older \<open>dependence_over_fixed_field\<close> remains a useful specialization for a family of
  vectors already fixed by @{term H}.  The corrected simultaneous-system theorem
  \<open>artin_solution_over_fixed_field\<close> is the interface used by the degree layer, so the public
  \<open>artin_theorem\<close> no longer exposes either that fixed-vector premise or an explicit basis
  premise.  This theory remains the reusable dependence layer and does not acquire a second
  vector-space construction.\<close>

end
