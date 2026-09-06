section \<open>Prime and Maximal Ideals\<close>

theory Ideal_Theory
  imports Ring_Theory "HOL.Zorn"
begin

text \<open>Phase B: prime and maximal ideals, and the quotient characterisations.\<close>

context Ideal
begin

text \<open>Prime and maximal ideals: proper ideals with the usual closure / maximality property.\<close>
definition prime_ideal :: bool
  where "prime_ideal \<longleftrightarrow> I \<noteq> R \<and> (\<forall>a\<in>R. \<forall>b\<in>R. a \<cdot> b \<in> I \<longrightarrow> a \<in> I \<or> b \<in> I)"

definition maximal_ideal :: bool
  where "maximal_ideal \<longleftrightarrow> I \<noteq> R \<and> (\<forall>J. Ideal J R (+) (\<cdot>) \<zero> \<one> \<longrightarrow> I \<subseteq> J \<longrightarrow> J = I \<or> J = R)"

text \<open>The coset of an element and the set of all cosets (the quotient @{text "R/I"}), given clean
  names so they can be referred to from interpretations at the top level (the underlying
  @{text additive.Class}/@{text additive.Partition} live behind several sublocale hops and have no
  stable qualified name).\<close>
definition coset :: "'a \<Rightarrow> 'a set"
  where "coset a = additive.Class a"

definition quotient_set :: "'a set set"
  where "quotient_set = additive.Partition"

lemma coset_eq_iff:
  assumes "a \<in> R" "b \<in> R" shows "coset a = coset b \<longleftrightarrow> a + (- b) \<in> I"
proof -
  have "coset a = coset b \<longleftrightarrow> (a, b) \<in> Ring_Congruence"
    unfolding coset_def
    using assms by (simp add: additive.Class_equivalence additive_congruence)
  also have "\<dots> \<longleftrightarrow> a + (- b) \<in> I" using assms by (auto simp: Ring_Congruence_def)
  finally show ?thesis .
qed

lemma coset_in_quotient_set: "a \<in> R \<Longrightarrow> coset a \<in> quotient_set"
  unfolding coset_def quotient_set_def by (rule additive.Class_in_Partition)

lemma quotient_set_repr: "C \<in> quotient_set \<Longrightarrow> \<exists>a\<in>R. C = coset a"
  unfolding coset_def quotient_set_def using additive.representant_exists by blast

text \<open>Membership criterion: a coset is the zero coset iff its representative is in the ideal.\<close>
lemma Class_eq_zero_iff:
  assumes "a \<in> R"
  shows "additive.Class a = additive.Class \<zero> \<longleftrightarrow> a \<in> I"
proof -
  have "additive.Class a = additive.Class \<zero> \<longleftrightarrow> (a, \<zero>) \<in> Ring_Congruence"
    using assms by (simp add: additive.Class_equivalence additive_congruence)
  also have "\<dots> \<longleftrightarrow> a \<in> I"
    using assms by (auto simp: Ring_Congruence_def)
  finally show ?thesis .
qed

end

text \<open>An ideal of a commutative ring: add only the commutativity axiom on top of @{locale Ideal}
  (so the @{text Ring}/@{text multiplicative} structure is shared, avoiding a locale-merge clash).\<close>
locale ideal_in_comm_ring = Ideal + commutative_ring
begin

lemmas comm = multiplicative.commutative

text \<open>The quotient multiplication is commutative.\<close>
lemma quot_mult_comm:
  assumes "a \<in> R" "b \<in> R"
  shows "additive.Class a [\<cdot>] additive.Class b = additive.Class b [\<cdot>] additive.Class a"
proof -
  have "additive.Class a [\<cdot>] additive.Class b = additive.Class (a \<cdot> b)"
    by (rule multiplicative.Class_commutes_with_composition[OF assms])
  also have "\<dots> = additive.Class (b \<cdot> a)" using comm[OF assms] by simp
  also have "\<dots> = additive.Class b [\<cdot>] additive.Class a"
    by (rule multiplicative.Class_commutes_with_composition[OF assms(2,1), symmetric])
  finally show ?thesis .
qed

text \<open>Quotient multiplication in terms of representatives.\<close>
lemma quot_mult_Class:
  assumes "a \<in> R" "b \<in> R"
  shows "additive.Class a [\<cdot>] additive.Class b = additive.Class (a \<cdot> b)"
  by (rule multiplicative.Class_commutes_with_composition[OF assms])

text \<open>B1: the ideal is prime iff the quotient has no zero divisors (is an integral domain,
  given nontriviality @{term "I \<noteq> R"}).\<close>
theorem prime_ideal_iff_quotient_no_zero_divisors:
  "prime_ideal \<longleftrightarrow> I \<noteq> R \<and>
     (\<forall>a\<in>R. \<forall>b\<in>R. additive.Class a [\<cdot>] additive.Class b = additive.Class \<zero>
                  \<longrightarrow> additive.Class a = additive.Class \<zero> \<or> additive.Class b = additive.Class \<zero>)"
proof -
  have "(\<forall>a\<in>R. \<forall>b\<in>R. additive.Class a [\<cdot>] additive.Class b = additive.Class \<zero>
                  \<longrightarrow> additive.Class a = additive.Class \<zero> \<or> additive.Class b = additive.Class \<zero>)
      = (\<forall>a\<in>R. \<forall>b\<in>R. a \<cdot> b \<in> I \<longrightarrow> a \<in> I \<or> b \<in> I)"
  proof (intro ball_cong refl iff_allI)
    fix a b assume ab: "a \<in> R" "b \<in> R"
    have abR: "a \<cdot> b \<in> R" using ab by simp
    show "(additive.Class a [\<cdot>] additive.Class b = additive.Class \<zero>
            \<longrightarrow> additive.Class a = additive.Class \<zero> \<or> additive.Class b = additive.Class \<zero>)
        = (a \<cdot> b \<in> I \<longrightarrow> a \<in> I \<or> b \<in> I)"
      by (simp add: quot_mult_Class[OF ab] Class_eq_zero_iff abR Class_eq_zero_iff[OF ab(1)]
                    Class_eq_zero_iff[OF ab(2)])
  qed
  then show ?thesis unfolding prime_ideal_def by blast
qed

text \<open>The ideal generated by @{term I} together with one element @{term a}, i.e. \<open>I + (a)\<close>.\<close>
definition ext_ideal :: "'a \<Rightarrow> 'a set"
  where "ext_ideal a = {m + r \<cdot> a | m r. m \<in> I \<and> r \<in> R}"

lemma ext_ideal_memI: "\<lbrakk> m \<in> I; r \<in> R \<rbrakk> \<Longrightarrow> m + r \<cdot> a \<in> ext_ideal a"
  unfolding ext_ideal_def by blast

lemma ext_ideal_contains_I:
  assumes "a \<in> R"
  shows "I \<subseteq> ext_ideal a"
proof
  fix m assume m: "m \<in> I"
  then have mR: "m \<in> R" using additive.subset by blast
  have "m + \<zero> \<cdot> a = m" using assms mR by (simp add: additive.right_unit)
  moreover have "m + \<zero> \<cdot> a \<in> ext_ideal a" using m ext_ideal_memI[of m \<zero>] by simp
  ultimately show "m \<in> ext_ideal a" by simp
qed

lemma ext_ideal_contains_elt:
  assumes "a \<in> R"
  shows "a \<in> ext_ideal a"
proof -
  have "\<zero> + \<one> \<cdot> a = a" using assms by (simp add: additive.left_unit)
  moreover have "\<zero> + \<one> \<cdot> a \<in> ext_ideal a" using ext_ideal_memI[of \<zero> \<one>] by simp
  ultimately show ?thesis by simp
qed

text \<open>@{term "ext_ideal a"} is closed under addition and additive inverses, hence an additive
  subgroup of @{term R}.\<close>
lemma ext_ideal_subgroup:
  assumes a: "a \<in> R"
  shows "Subgroup (ext_ideal a) R (+) \<zero>"
proof (rule additive.subgroupI)
  show "ext_ideal a \<subseteq> R"
  proof
    fix x assume "x \<in> ext_ideal a"
    then obtain m r where "m \<in> I" "r \<in> R" "x = m + r \<cdot> a"
      unfolding ext_ideal_def by blast
    then show "x \<in> R" using a additive.subset by auto
  qed
next
  have "\<zero> \<in> I" by (rule additive.sub_unit_closed)
  then have "\<zero> + \<zero> \<cdot> a \<in> ext_ideal a" using a ext_ideal_memI[of \<zero> \<zero>] by blast
  moreover have "\<zero> + \<zero> \<cdot> a = \<zero>" using a by simp
  ultimately show "\<zero> \<in> ext_ideal a" by simp
next
  fix g h assume "g \<in> ext_ideal a" "h \<in> ext_ideal a"
  then obtain m1 r1 m2 r2 where
    g: "m1 \<in> I" "r1 \<in> R" "g = m1 + r1 \<cdot> a" and
    h: "m2 \<in> I" "r2 \<in> R" "h = m2 + r2 \<cdot> a"
    unfolding ext_ideal_def by blast
  have m1R: "m1 \<in> R" and m2R: "m2 \<in> R" using g h additive.subset by auto
  have ra1: "r1 \<cdot> a \<in> R" and ra2: "r2 \<cdot> a \<in> R" using g h a by auto
  \<comment> \<open>Rearrange @{text "(m1 + x) + (m2 + y) = (m1 + m2) + (x + y)"} in the abelian group.\<close>
  have rearr: "(p + x) + (q + y) = (p + q) + (x + y)"
    if "p \<in> R" "x \<in> R" "q \<in> R" "y \<in> R" for p x q y
  proof -
    have "(p + x) + (q + y) = p + (x + (q + y))"
      using that by (simp add: additive.associative)
    also have "\<dots> = p + ((x + q) + y)"
      using that by (simp add: additive.associative)
    also have "\<dots> = p + ((q + x) + y)"
      using that by (simp add: additive.commutative)
    also have "\<dots> = p + (q + (x + y))"
      using that by (simp add: additive.associative)
    also have "\<dots> = (p + q) + (x + y)"
      using that by (simp add: additive.associative)
    finally show ?thesis .
  qed
  have "g + h = (m1 + r1 \<cdot> a) + (m2 + r2 \<cdot> a)" using g h by simp
  also have "\<dots> = (m1 + m2) + (r1 \<cdot> a + r2 \<cdot> a)"
    using rearr[OF m1R ra1 m2R ra2] .
  also have "\<dots> = (m1 + m2) + (r1 + r2) \<cdot> a"
    using g h a by (simp add: distributive)
  finally have "g + h = (m1 + m2) + (r1 + r2) \<cdot> a" .
  moreover have "m1 + m2 \<in> I" using g h by (simp add: additive.sub_composition_closed)
  ultimately show "g + h \<in> ext_ideal a" using g h ext_ideal_memI[of "m1+m2" "r1+r2"] by simp
next
  fix g assume "g \<in> ext_ideal a"
  then obtain m r where "m \<in> I" "r \<in> R" "g = m + r \<cdot> a" unfolding ext_ideal_def by blast
  then have "g \<in> R" using a additive.subset by auto
  then show "additive.invertible g" by simp
next
  fix g assume "g \<in> ext_ideal a"
  then obtain m r where g: "m \<in> I" "r \<in> R" "g = m + r \<cdot> a"
    unfolding ext_ideal_def by blast
  have mR: "m \<in> R" using g additive.subset by auto
  have "additive.inverse g = (additive.inverse m) + (additive.inverse r) \<cdot> a"
    using g mR a by (simp add: additive.inverse_composition_commute additive.commutative left_minus)
  moreover have "additive.inverse m \<in> I" using g by simp
  moreover have "additive.inverse r \<in> R" using g by simp
  ultimately show "additive.inverse g \<in> ext_ideal a"
    using ext_ideal_memI[of "additive.inverse m" "additive.inverse r"] by simp
qed

text \<open>Hence @{term "ext_ideal a"} is an ideal of @{term R}: the absorption laws follow from
  @{term I}'s absorption and commutativity of multiplication.\<close>
lemma ext_ideal_is_ideal:
  assumes a: "a \<in> R"
  shows "Ideal (ext_ideal a) R (+) (\<cdot>) \<zero> \<one>"
proof -
  interpret sub: Subgroup "ext_ideal a" R "(+)" \<zero> by (rule ext_ideal_subgroup[OF a])
  show ?thesis
  proof (unfold_locales)
    fix x y assume x: "x \<in> R" and y: "y \<in> ext_ideal a"
    obtain m r where mr: "m \<in> I" "r \<in> R" "y = m + r \<cdot> a"
      using y unfolding ext_ideal_def by blast
    have mR: "m \<in> R" using mr additive.subset by auto
    show "x \<cdot> y \<in> ext_ideal a"
    proof -
      have "x \<cdot> y = x \<cdot> m + (x \<cdot> r) \<cdot> a"
        using x mr mR a by (simp add: distributive multiplicative.associative)
      moreover have "x \<cdot> m \<in> I" using x mr by (simp add: Ideal)
      moreover have "x \<cdot> r \<in> R" using x mr by simp
      ultimately show ?thesis using ext_ideal_memI[of "x \<cdot> m" "x \<cdot> r"] by simp
    qed
    show "y \<cdot> x \<in> ext_ideal a"
    proof -
      have rax: "(r \<cdot> a) \<cdot> x = (r \<cdot> x) \<cdot> a"
      proof -
        have "(r \<cdot> a) \<cdot> x = r \<cdot> (a \<cdot> x)" using mr a x by (simp add: multiplicative.associative)
        also have "\<dots> = r \<cdot> (x \<cdot> a)" using a x by (simp add: comm)
        also have "\<dots> = (r \<cdot> x) \<cdot> a" using mr a x by (simp add: multiplicative.associative)
        finally show ?thesis .
      qed
      have "y \<cdot> x = m \<cdot> x + (r \<cdot> a) \<cdot> x"
        using x mr mR a by (simp add: distributive)
      also have "\<dots> = m \<cdot> x + (r \<cdot> x) \<cdot> a" using rax by simp
      finally have "y \<cdot> x = m \<cdot> x + (r \<cdot> x) \<cdot> a" .
      moreover have "m \<cdot> x \<in> I" using x mr by (simp add: Ideal)
      moreover have "r \<cdot> x \<in> R" using x mr by simp
      ultimately show ?thesis using ext_ideal_memI[of "m \<cdot> x" "r \<cdot> x"] by simp
    qed
  qed
qed


text \<open>For a maximal ideal, any element outside @{term I} generates (with @{term I}) the whole
  ring, giving a representation @{text "\<one> = m + r \<cdot> a"} with @{term "m \<in> I"}.\<close>
lemma maximal_ext_ideal_eq_whole:
  assumes max: maximal_ideal and a: "a \<in> R" and aI: "a \<notin> I"
  shows "ext_ideal a = R"
proof -
  have "Ideal (ext_ideal a) R (+) (\<cdot>) \<zero> \<one>" by (rule ext_ideal_is_ideal[OF a])
  moreover have "I \<subseteq> ext_ideal a" by (rule ext_ideal_contains_I[OF a])
  moreover have "ext_ideal a \<noteq> I"
    using ext_ideal_contains_elt[OF a] aI by blast
  ultimately show ?thesis using max unfolding maximal_ideal_def by blast
qed

text \<open>\<^emph>\<open>A maximal ideal is prime.\<close>  If \<open>a \<cdot> b \<in> I\<close> but \<open>a \<notin> I\<close>, then adjoining @{term a}
  generates the whole ring, giving \<open>\<one> = m + r \<cdot> a\<close> with \<open>m \<in> I\<close>; hence
  \<open>b = m \<cdot> b + r \<cdot> (a \<cdot> b) \<in> I\<close>.\<close>
theorem maximal_imp_prime_ideal:
  assumes max: maximal_ideal shows "prime_ideal"
proof (unfold prime_ideal_def, intro conjI ballI impI)
  show "I \<noteq> R" using max unfolding maximal_ideal_def by simp
next
  fix a b assume a: "a \<in> R" and b: "b \<in> R" and abI: "a \<cdot> b \<in> I"
  show "a \<in> I \<or> b \<in> I"
  proof (cases "a \<in> I")
    case True then show ?thesis ..
  next
    case False
    \<comment> \<open>@{term a} generates the whole ring together with @{term I}: @{text "\<one> = m + r \<cdot> a"}.\<close>
    have "\<one> \<in> ext_ideal a" using maximal_ext_ideal_eq_whole[OF max a False] by simp
    then obtain m r where m: "m \<in> I" and r: "r \<in> R" and one: "\<one> = m + r \<cdot> a"
      unfolding ext_ideal_def by blast
    have mR: "m \<in> R" using m additive.subset by auto
    \<comment> \<open>Then @{term "b = m \<cdot> b + r \<cdot> (a \<cdot> b)"}, both summands in @{term I}.\<close>
    have "b = \<one> \<cdot> b" using b by simp
    also have "\<dots> = (m + r \<cdot> a) \<cdot> b" using one by simp
    also have "\<dots> = m \<cdot> b + (r \<cdot> a) \<cdot> b" using mR r a b by (simp add: distributive)
    also have "(r \<cdot> a) \<cdot> b = r \<cdot> (a \<cdot> b)" using r a b by (simp add: multiplicative.associative)
    finally have beq: "b = m \<cdot> b + r \<cdot> (a \<cdot> b)" .
    have "m \<cdot> b \<in> I" using Ideal(2)[OF b m] .
    moreover have "r \<cdot> (a \<cdot> b) \<in> I" using Ideal(1)[OF r abI] .
    ultimately have "m \<cdot> b + r \<cdot> (a \<cdot> b) \<in> I" by (rule additive.sub_composition_closed)
    then have "b \<in> I" using beq by simp
    then show ?thesis ..
  qed
qed

lemma maximal_quotient_invertible:
  assumes max: maximal_ideal and a: "a \<in> R" and aI: "a \<notin> I"
  shows "\<exists>r\<in>R. additive.Class r [\<cdot>] additive.Class a = additive.Class \<one>"
proof -
  have "\<one> \<in> ext_ideal a" using maximal_ext_ideal_eq_whole[OF max a aI] by simp
  then obtain m r where m: "m \<in> I" and r: "r \<in> R" and one: "\<one> = m + r \<cdot> a"
    unfolding ext_ideal_def by blast
  have mR: "m \<in> R" using m additive.subset by auto
  have raR: "r \<cdot> a \<in> R" using r a by simp
  have "additive.Class \<one> = additive.Class (m + r \<cdot> a)" using one by simp
  also have "\<dots> = additive.Class m [+] additive.Class (r \<cdot> a)"
    using mR raR by (simp add: additive.Class_commutes_with_composition)
  also have "additive.Class m = additive.Class \<zero>" using m by (simp add: Class_eq_zero_iff mR)
  finally have "additive.Class \<one> = additive.Class \<zero> [+] additive.Class (r \<cdot> a)" .
  also have "\<dots> = additive.Class (r \<cdot> a)"
    using raR by (simp add: additive.Class_commutes_with_composition[symmetric] additive.left_unit)
  also have "additive.Class (r \<cdot> a) = additive.Class r [\<cdot>] additive.Class a"
    using r a by (simp add: quot_mult_Class)
  finally have "additive.Class \<one> = additive.Class r [\<cdot>] additive.Class a" .
  then show ?thesis using r by auto
qed


text \<open>If two ring elements have equal cosets, their difference lies in @{term I}.\<close>
lemma Class_eq_imp_diff_in_I:
  assumes "a \<in> R" "b \<in> R" "additive.Class a = additive.Class b"
  shows "a - b \<in> I"
proof -
  have "(a, b) \<in> Ring_Congruence"
    using assms by (simp add: additive.Class_equivalence additive_congruence)
  then show ?thesis by (rule Ring_CongruenceD)
qed

theorem maximal_ideal_iff_quotient_field:
  "maximal_ideal \<longleftrightarrow> I \<noteq> R \<and>
     (\<forall>a\<in>R. additive.Class a \<noteq> additive.Class \<zero>
            \<longrightarrow> (\<exists>r\<in>R. additive.Class r [\<cdot>] additive.Class a = additive.Class \<one>))"
proof
  assume max: maximal_ideal
  have "I \<noteq> R" using max unfolding maximal_ideal_def by simp
  moreover have "\<exists>r\<in>R. additive.Class r [\<cdot>] additive.Class a = additive.Class \<one>"
    if aR: "a \<in> R" and ane: "additive.Class a \<noteq> additive.Class \<zero>" for a
  proof -
    have "a \<notin> I" using aR ane by (simp add: Class_eq_zero_iff)
    then show ?thesis by (rule maximal_quotient_invertible[OF max aR])
  qed
  ultimately show "I \<noteq> R \<and>
     (\<forall>a\<in>R. additive.Class a \<noteq> additive.Class \<zero>
            \<longrightarrow> (\<exists>r\<in>R. additive.Class r [\<cdot>] additive.Class a = additive.Class \<one>))" by blast
next
  assume rhs: "I \<noteq> R \<and>
     (\<forall>a\<in>R. additive.Class a \<noteq> additive.Class \<zero>
            \<longrightarrow> (\<exists>r\<in>R. additive.Class r [\<cdot>] additive.Class a = additive.Class \<one>))"
  show maximal_ideal
    unfolding maximal_ideal_def
  proof (intro conjI allI impI)
    show "I \<noteq> R" using rhs by simp
    fix J assume J: "Ideal J R (+) (\<cdot>) \<zero> \<one>" and IJ: "I \<subseteq> J"
    show "J = I \<or> J = R"
    proof (rule ccontr)
      assume "\<not> (J = I \<or> J = R)"
      then have JnI: "J \<noteq> I" and JnR: "J \<noteq> R" by auto
      interpret J: Ideal J R "(+)" "(\<cdot>)" \<zero> \<one> by (rule J)
      from JnI IJ obtain a where aJ: "a \<in> J" and aI: "a \<notin> I" by blast
      have aR: "a \<in> R" using aJ J.additive.subset by auto
      have ane: "additive.Class a \<noteq> additive.Class \<zero>" using aR aI by (simp add: Class_eq_zero_iff)
      then obtain r where r: "r \<in> R" and inv: "additive.Class r [\<cdot>] additive.Class a = additive.Class \<one>"
        using rhs aR by blast
      have raJ: "r \<cdot> a \<in> J" using r aJ by (simp add: J.Ideal)
      have raR: "r \<cdot> a \<in> R" using r aR by simp
      have ClassEq: "additive.Class (r \<cdot> a) = additive.Class \<one>"
        using r aR inv by (simp add: quot_mult_Class)
      \<comment> \<open>So @{text "r\<cdot>a - \<one> \<in> I"}, hence @{text "\<one> - r\<cdot>a \<in> I \<subseteq> J"}, giving @{text "\<one> \<in> J"}.\<close>
      have "r \<cdot> a - \<one> \<in> I" using Class_eq_imp_diff_in_I[OF raR _ ClassEq] by simp
      then have negI: "- (r \<cdot> a - \<one>) \<in> I" by simp
      have "- (r \<cdot> a - \<one>) = \<one> - r \<cdot> a"
        using raR by (simp add: additive.inverse_composition_commute additive.commutative)
      then have oneI: "\<one> - r \<cdot> a \<in> I" using negI by simp
      have oneJ: "\<one> - r \<cdot> a \<in> J" using oneI IJ by blast
      have "(\<one> - r \<cdot> a) + r \<cdot> a \<in> J" using oneJ raJ by (simp add: J.additive.sub_composition_closed)
      moreover have "(\<one> - r \<cdot> a) + r \<cdot> a = \<one>"
      proof -
        have "(\<one> - r \<cdot> a) + r \<cdot> a = \<one> + ((- r \<cdot> a) + r \<cdot> a)"
          using raR by (simp add: additive.associative)
        also have "\<dots> = \<one>" using raR by simp
        finally show ?thesis .
      qed
      ultimately have "\<one> \<in> J" by simp
      then have "J = R" using J.additive.subset
        by (metis J.Ideal(1) multiplicative.right_unit subsetI subset_antisym)
      then show False using JnR by simp
    qed
  qed
qed

end


section \<open>Principal Ideals\<close>

text \<open>The principal ideal generated by a single element of a commutative ring: the set of all
  multiples @{text "r \<cdot> a"}.  This is the smallest ideal containing @{term a}, and it is the
  building block for principal ideal domains (e.g. @{text "F[X]"} over a field).\<close>

subsection \<open>Existence of maximal ideals\<close>

text \<open>Every proper ideal is contained in a maximal one.  This is the standard application of
  Zorn's lemma (@{thm [source] Zorn_Lemma2}) to the family of proper ideals containing a given one:
  the union of a chain of such ideals is again one, so the family has a maximal element.

  The only delicate point is \<^emph>\<open>properness\<close> of the union.  An ideal is proper exactly when it omits
  the unit \<open>\<one>\<close>: if \<open>\<one>\<close> lies in an ideal then so does \<open>a \<cdot> \<one> = a\<close> for every \<open>a\<close>, making it the
  whole ring.  Since every member of the chain omits \<open>\<one>\<close>, so does the union --- which is why the
  chain condition can be checked at all, and why the argument needs a ring with a unit.\<close>

context Ring
begin

text \<open>An ideal is proper if and only if it does not contain @{term \<one>}.\<close>
lemma ideal_proper_iff_one_notin:
  assumes I: "Ideal I R (+) (\<cdot>) \<zero> \<one>"
  shows "I \<noteq> R \<longleftrightarrow> \<one> \<notin> I"
proof -
  interpret I: Ideal I R "(+)" "(\<cdot>)" \<zero> \<one> by (rule I)
  show ?thesis
  proof
    assume "I \<noteq> R"
    show "\<one> \<notin> I"
    proof
      assume one: "\<one> \<in> I"
      have "R \<subseteq> I"
      proof
        fix a assume a: "a \<in> R"
        have "a \<cdot> \<one> \<in> I" using a one by (rule I.Ideal(1))
        then show "a \<in> I" using a by simp
      qed
      with I.additive.subset have "I = R" by blast
      with \<open>I \<noteq> R\<close> show False by simp
    qed
  next
    assume "\<one> \<notin> I"
    then show "I \<noteq> R" using multiplicative.unit_closed by blast
  qed
qed

text \<open>The union of a nonempty chain of ideals is an ideal.  Directedness is what makes the additive
  closure work: two elements of the union lie in a common member of the chain.\<close>
lemma ideal_Union_chain:
  assumes ne: "\<C> \<noteq> {}"
    and id: "\<And>I. I \<in> \<C> \<Longrightarrow> Ideal I R (+) (\<cdot>) \<zero> \<one>"
    and chain: "\<And>I J. \<lbrakk> I \<in> \<C>; J \<in> \<C> \<rbrakk> \<Longrightarrow> I \<subseteq> J \<or> J \<subseteq> I"
  shows "Ideal (\<Union> \<C>) R (+) (\<cdot>) \<zero> \<one>"
proof -
  obtain I0 where I0: "I0 \<in> \<C>" using ne by blast
  interpret I0: Ideal I0 R "(+)" "(\<cdot>)" \<zero> \<one> by (rule id[OF I0])
  have sub: "\<Union> \<C> \<subseteq> R"
  proof
    fix x assume "x \<in> \<Union> \<C>"
    then obtain I where I: "I \<in> \<C>" and x: "x \<in> I" by blast
    interpret I: Ideal I R "(+)" "(\<cdot>)" \<zero> \<one> by (rule id[OF I])
    show "x \<in> R" using x I.additive.subset by blast
  qed
  have sg: "Subgroup (\<Union> \<C>) R (+) \<zero>"
  proof (rule additive.subgroupI)
    show "\<Union> \<C> \<subseteq> R" by (rule sub)
    show "\<zero> \<in> \<Union> \<C>" using I0 I0.additive.sub_unit_closed by blast
  next
    \<comment> \<open>Directedness: pick the larger of the two members containing @{term g} and @{term h}.\<close>
    fix g h assume "g \<in> \<Union> \<C>" and "h \<in> \<Union> \<C>"
    then obtain I J where I: "I \<in> \<C>" "g \<in> I" and J: "J \<in> \<C>" "h \<in> J" by blast
    show "g + h \<in> \<Union> \<C>"
    proof (cases "I \<subseteq> J")
      case True
      interpret J: Ideal J R "(+)" "(\<cdot>)" \<zero> \<one> by (rule id[OF J(1)])
      have "g + h \<in> J" using True I(2) J(2) by (blast intro: J.additive.sub_composition_closed)
      then show ?thesis using J(1) by blast
    next
      case False
      then have "J \<subseteq> I" using chain[OF I(1) J(1)] by blast
      interpret I: Ideal I R "(+)" "(\<cdot>)" \<zero> \<one> by (rule id[OF I(1)])
      have "g + h \<in> I" using \<open>J \<subseteq> I\<close> I(2) J(2) by (blast intro: I.additive.sub_composition_closed)
      then show ?thesis using I(1) by blast
    qed
  next
    fix g assume "g \<in> \<Union> \<C>"
    then show "additive.invertible g" using sub by blast
  next
    fix g assume "g \<in> \<Union> \<C>"
    then obtain I where I: "I \<in> \<C>" and g: "g \<in> I" by blast
    interpret I: Ideal I R "(+)" "(\<cdot>)" \<zero> \<one> by (rule id[OF I])
    have "additive.inverse g \<in> I"
      using g I.additive.submonoid_inverse_closed I.additive.sub.invertible by blast
    then show "additive.inverse g \<in> \<Union> \<C>" using I by blast
  qed
  interpret S: Subgroup "\<Union> \<C>" R "(+)" \<zero> by (rule sg)
  show ?thesis
  proof unfold_locales
    fix a b assume a: "a \<in> R" and b: "b \<in> \<Union> \<C>"
    from b obtain I where I: "I \<in> \<C>" and bI: "b \<in> I" by blast
    interpret I: Ideal I R "(+)" "(\<cdot>)" \<zero> \<one> by (rule id[OF I])
    show "a \<cdot> b \<in> \<Union> \<C>" using I a bI by (blast intro: I.Ideal(1))
    show "b \<cdot> a \<in> \<Union> \<C>" using I a bI by (blast intro: I.Ideal(2))
  qed
qed

text \<open>\<^emph>\<open>Krull's theorem.\<close>  Every proper ideal extends to a maximal one.  Apply
  @{thm [source] Zorn_Lemma2} to the family of proper ideals containing @{term I}: a nonempty chain's
  union is an ideal by @{thm [source] ideal_Union_chain}, is proper because no member contains \<open>\<one>\<close>,
  and contains @{term I}; the empty chain is bounded by @{term I} itself.\<close>
theorem maximal_ideal_exists:
  assumes I: "Ideal I R (+) (\<cdot>) \<zero> \<one>" and proper: "I \<noteq> R"
  shows "\<exists>M. Ideal M R (+) (\<cdot>) \<zero> \<one> \<and> I \<subseteq> M \<and> Ideal.maximal_ideal M R (+) (\<cdot>) \<zero> \<one>"
proof -
  interpret I: Ideal I R "(+)" "(\<cdot>)" \<zero> \<one> by (rule I)
  have Ione: "\<one> \<notin> I" using I proper by (simp add: ideal_proper_iff_one_notin)
  \<comment> \<open>The family: proper ideals containing @{term I}.\<close>
  define \<A> where "\<A> = {J. Ideal J R (+) (\<cdot>) \<zero> \<one> \<and> I \<subseteq> J \<and> \<one> \<notin> J}"
  have IA: "I \<in> \<A>" unfolding \<A>_def using I Ione by blast
  \<comment> \<open>Every chain in the family has an upper bound \<^emph>\<open>in\<close> the family.  We use
    @{thm [source] Zorn_Lemma2} rather than @{thm [source] Zorn_Lemma} precisely because of the empty
    chain: the latter would demand \<open>\<Union> {} = {} \<in> \<A>\<close>, which is false, whereas an upper bound for the
    empty chain is supplied by @{term I} itself.\<close>
  have bound: "\<exists>U \<in> \<A>. \<forall>X \<in> \<C>. X \<subseteq> U" if C: "\<C> \<in> chains \<A>" for \<C>
  proof (cases "\<C> = {}")
    case True
    then show ?thesis using IA by blast
  next
    case False
    have sub: "\<C> \<subseteq> \<A>" and ch: "chain\<^sub>\<subseteq> \<C>" using C by (auto simp: chains_def)
    have id: "\<And>J. J \<in> \<C> \<Longrightarrow> Ideal J R (+) (\<cdot>) \<zero> \<one>" using sub by (auto simp: \<A>_def)
    have le: "\<And>J K. \<lbrakk> J \<in> \<C>; K \<in> \<C> \<rbrakk> \<Longrightarrow> J \<subseteq> K \<or> K \<subseteq> J"
      using ch by (auto simp: chain_subset_def)
    have "Ideal (\<Union> \<C>) R (+) (\<cdot>) \<zero> \<one>" using False id le by (rule ideal_Union_chain)
    moreover have "I \<subseteq> \<Union> \<C>" using False sub by (auto simp: \<A>_def)
    moreover have "\<one> \<notin> \<Union> \<C>" using sub by (auto simp: \<A>_def)
    ultimately have "\<Union> \<C> \<in> \<A>" unfolding \<A>_def by blast
    then show ?thesis by blast
  qed
  \<comment> \<open>Zorn gives a maximal member of the family; maximality \<^emph>\<open>among proper ideals over\<close> @{term I}
    upgrades to maximality among all ideals, since a strictly larger ideal either contains \<open>\<one>\<close> ---
    hence is @{term R} --- or would still be in the family.\<close>
  \<comment> \<open>Zorn's premise is discharged as an explicit @{text \<forall>}-statement first: handed to
    @{method blast} as the conditional rule @{text bound}, the set-valued unknown sends it into a
    search that does not terminate.\<close>
  have prem: "\<forall>\<C> \<in> chains \<A>. \<exists>U \<in> \<A>. \<forall>X \<in> \<C>. X \<subseteq> U" using bound by blast
  obtain M where M: "M \<in> \<A>" and max: "\<And>X. X \<in> \<A> \<Longrightarrow> M \<subseteq> X \<Longrightarrow> X = M"
    using Zorn_Lemma2[OF prem] by blast
  from M have Mid: "Ideal M R (+) (\<cdot>) \<zero> \<one>" and IM: "I \<subseteq> M" and Mone: "\<one> \<notin> M"
    by (auto simp: \<A>_def)
  interpret M: Ideal M R "(+)" "(\<cdot>)" \<zero> \<one> by (rule Mid)
  have "Ideal.maximal_ideal M R (+) (\<cdot>) \<zero> \<one>"
    unfolding M.maximal_ideal_def
  proof (intro conjI allI impI)
    show "M \<noteq> R" using Mid Mone by (simp add: ideal_proper_iff_one_notin)
    fix J assume J: "Ideal J R (+) (\<cdot>) \<zero> \<one>" and MJ: "M \<subseteq> J"
    show "J = M \<or> J = R"
    proof (cases "\<one> \<in> J")
        case True
      \<comment> \<open>@{text ideal_proper_iff_one_notin} read contrapositively: containing \<open>\<one>\<close> forces \<open>J = R\<close>.\<close>
      then have "J = R" using ideal_proper_iff_one_notin[OF J] by blast
      then show ?thesis by simp
    next
      case False
      then have "J \<in> \<A>" unfolding \<A>_def using J IM MJ by blast
      then show ?thesis using max MJ by blast
    qed
  qed
  then show ?thesis using Mid IM by blast
qed


end (* Ring *)


context commutative_ring
begin

definition principal_ideal :: "'a \<Rightarrow> 'a set"
  where "principal_ideal a = {r \<cdot> a | r. r \<in> R}"

lemma principal_ideal_memI: "r \<in> R \<Longrightarrow> r \<cdot> a \<in> principal_ideal a"
  unfolding principal_ideal_def by blast

lemma principal_ideal_subset:
  assumes "a \<in> R" shows "principal_ideal a \<subseteq> R"
proof
  fix x assume "x \<in> principal_ideal a"
  then obtain r where "r \<in> R" "x = r \<cdot> a" unfolding principal_ideal_def by blast
  then show "x \<in> R" using assms by auto
qed

text \<open>@{term a} itself lies in @{term "principal_ideal a"} (take @{text "r = \<one>"}).\<close>
lemma principal_ideal_contains:
  assumes "a \<in> R" shows "a \<in> principal_ideal a"
proof -
  have "\<one> \<cdot> a = a" using assms by simp
  moreover have "\<one> \<cdot> a \<in> principal_ideal a" using principal_ideal_memI[of \<one> a] by simp
  ultimately show ?thesis by simp
qed

text \<open>@{term "principal_ideal a"} is an additive subgroup: closed under @{text "+"} via
  distributivity, and under inverses via @{thm [source] left_minus}.\<close>
lemma principal_ideal_subgroup:
  assumes a: "a \<in> R" shows "Subgroup (principal_ideal a) R (+) \<zero>"
proof (rule additive.subgroupI)
  show "principal_ideal a \<subseteq> R" using a by (rule principal_ideal_subset)
next
  have "\<zero> \<cdot> a = \<zero>" using a by simp
  moreover have "\<zero> \<cdot> a \<in> principal_ideal a" using principal_ideal_memI[of \<zero> a] by simp
  ultimately show "\<zero> \<in> principal_ideal a" by simp
next
  fix g h assume "g \<in> principal_ideal a" "h \<in> principal_ideal a"
  then obtain r1 r2 where g: "r1 \<in> R" "g = r1 \<cdot> a" and h: "r2 \<in> R" "h = r2 \<cdot> a"
    unfolding principal_ideal_def by blast
  have "g + h = r1 \<cdot> a + r2 \<cdot> a" using g h by simp
  also have "\<dots> = (r1 + r2) \<cdot> a" using g h a by (simp add: distributive)
  finally have "g + h = (r1 + r2) \<cdot> a" .
  moreover have "r1 + r2 \<in> R" using g h by simp
  ultimately show "g + h \<in> principal_ideal a" using principal_ideal_memI[of "r1 + r2" a] by simp
next
  fix g assume "g \<in> principal_ideal a"
  then obtain r where "r \<in> R" "g = r \<cdot> a" unfolding principal_ideal_def by blast
  then have "g \<in> R" using a by auto
  then show "additive.invertible g" by simp
next
  fix g assume "g \<in> principal_ideal a"
  then obtain r where g: "r \<in> R" "g = r \<cdot> a" unfolding principal_ideal_def by blast
  have "additive.inverse g = (additive.inverse r) \<cdot> a" using g a by (simp add: left_minus)
  moreover have "additive.inverse r \<in> R" using g by simp
  ultimately show "additive.inverse g \<in> principal_ideal a"
    using principal_ideal_memI[of "additive.inverse r" a] by simp
qed

text \<open>Hence @{term "principal_ideal a"} is an ideal: the absorption laws follow from
  associativity and commutativity of multiplication.\<close>
lemma principal_ideal_is_ideal:
  assumes a: "a \<in> R" shows "Ideal (principal_ideal a) R (+) (\<cdot>) \<zero> \<one>"
proof -
  interpret sub: Subgroup "principal_ideal a" R "(+)" \<zero> by (rule principal_ideal_subgroup[OF a])
  show ?thesis
  proof unfold_locales
    fix x y assume x: "x \<in> R" and y: "y \<in> principal_ideal a"
    obtain r where r: "r \<in> R" "y = r \<cdot> a" using y unfolding principal_ideal_def by blast
    have yR: "y \<in> R" using r a by simp
    show "x \<cdot> y \<in> principal_ideal a"
    proof -
      have "x \<cdot> y = (x \<cdot> r) \<cdot> a" using x r a by (simp add: multiplicative.associative)
      moreover have "x \<cdot> r \<in> R" using x r by simp
      ultimately show ?thesis using principal_ideal_memI[of "x \<cdot> r" a] by simp
    qed
    show "y \<cdot> x \<in> principal_ideal a"
    proof -
      have "y \<cdot> x = x \<cdot> y" using multiplicative.commutative[OF yR x] .
      also have "\<dots> = (x \<cdot> r) \<cdot> a" using x r a by (simp add: multiplicative.associative)
      finally have "y \<cdot> x = (x \<cdot> r) \<cdot> a" .
      moreover have "x \<cdot> r \<in> R" using x r by simp
      ultimately show ?thesis using principal_ideal_memI[of "x \<cdot> r" a] by simp
    qed
  qed
qed

end

end
