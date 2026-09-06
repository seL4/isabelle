(*
  Copyright (c) 2015--2019 by Clemens Ballarin
  This file is licensed under the 3-clause BSD license.
*)

theory Ring_Theory
  imports Group_Theory
begin

no_notation plus (infixl \<open>+\<close> 65)
no_notation minus (infixl \<open>-\<close> 65)
unbundle no uminus_syntax
no_notation quotient (infixl \<open>'/'/\<close> 90)


section \<open>Rings\<close>

subsection \<open>Definition and Elementary Properties\<close>

text \<open>Def 2.1\<close>
text \<open>p 86, ll 20--28\<close>
locale Ring = additive: Abelian_Group R "(+)" \<zero> + multiplicative: Monoid R "(\<cdot>)" \<one>
  for R and addition (infixl \<open>+\<close> 65) and multiplication (infixl \<open>\<cdot>\<close> 70) and zero (\<open>\<zero>\<close>) and unit (\<open>\<one>\<close>) +
  assumes distributive: "\<lbrakk> a \<in> R; b \<in> R; c \<in> R \<rbrakk> \<Longrightarrow> a \<cdot> (b + c) = a \<cdot> b + a \<cdot> c"
    "\<lbrakk> a \<in> R; b \<in> R; c \<in> R \<rbrakk> \<Longrightarrow> (b + c) \<cdot> a = b \<cdot> a + c \<cdot> a"
begin

text \<open>p 86, ll 20--28\<close>
notation additive.inverse (\<open>- _\<close> [66] 65)
abbreviation subtraction (infixl \<open>-\<close> 65) where "a - b \<equiv> a + (- b)"  (* or, alternatively, a definition *)

end (* Ring *)

text \<open>Compact version based on the monoid type\<close>
locale Ring' =
  fixes additive multiplicative  
  assumes eq: "mcarrier additive = mcarrier multiplicative"
  assumes Ring: "Ring (mcarrier additive) (mmult additive) (mmult multiplicative) (munit additive) (munit multiplicative)" 

text \<open>p 87, ll 10--12\<close>
locale Subring =
  additive: Subgroup S R "(+)" \<zero> + multiplicative: Submonoid S R "(\<cdot>)" \<one>
  for S and R and addition (infixl \<open>+\<close> 65) and multiplication (infixl \<open>\<cdot>\<close> 70) and zero (\<open>\<zero>\<close>) and unit (\<open>\<one>\<close>)

context Ring begin

text \<open>p 88, ll 26--28\<close>
lemma right_zero [simp]:
  assumes [simp]: "a \<in> R" shows "a \<cdot> \<zero> = \<zero>"
proof -
  have "a \<cdot> \<zero> = a \<cdot> (\<zero> + \<zero>)" by simp
  also have "\<dots> = a \<cdot> \<zero> + a \<cdot> \<zero>" by (simp add: distributive del: additive.left_unit additive.right_unit)
  finally have "a \<cdot> \<zero> - a \<cdot> \<zero> = a \<cdot> \<zero> + a \<cdot> \<zero> - a \<cdot> \<zero>" by simp
  then show ?thesis by (simp add: additive.associative del: additive.invertible_left_cancel)
qed

text \<open>p 88, l 29\<close>
lemma left_zero [simp]:
  assumes [simp]: "a \<in> R" shows "\<zero> \<cdot> a = \<zero>"
proof -
  have "\<zero> \<cdot> a = (\<zero> + \<zero>) \<cdot> a" by simp
  also have "\<dots> = \<zero> \<cdot> a + \<zero> \<cdot> a" by (simp add: distributive del: additive.left_unit additive.right_unit)
  finally have "\<zero> \<cdot> a - \<zero> \<cdot> a = \<zero> \<cdot> a + \<zero> \<cdot> a - \<zero> \<cdot> a" by simp
  then show ?thesis by (simp add: additive.associative del: additive.invertible_left_cancel)
qed

text \<open>p 88, ll 29--30; p 89, ll 1--2\<close>
lemma left_minus:
  assumes [simp]: "a \<in> R" "b \<in> R" shows "(- a) \<cdot> b = - a \<cdot> b"
proof -
  have "\<zero> = \<zero> \<cdot> b" by simp
  also have "\<dots> = (a - a) \<cdot> b" by simp
  also have "\<dots> = a \<cdot> b + (- a) \<cdot> b" by (simp add: distributive del: additive.invertible_right_inverse)
  finally have "- a \<cdot> b + \<zero> = - a \<cdot> b + a \<cdot> b + (- a) \<cdot> b" by (simp add: additive.associative del: additive.invertible_left_inverse)
  then show ?thesis by simp
qed

text \<open>p 89, l 3\<close>
lemma right_minus:
  assumes [simp]: "a \<in> R" "b \<in> R" shows "a \<cdot> (- b) = - a \<cdot> b"
proof -
  have "\<zero> = a \<cdot> \<zero>" by simp
  also have "\<dots> = a \<cdot> (b - b)" by simp
  also have "\<dots> = a \<cdot> b + a \<cdot> (- b)" by (simp add: distributive del: additive.invertible_right_inverse)
  finally have "- a \<cdot> b + \<zero> = - a \<cdot> b + a \<cdot> b + a \<cdot> (- b)" by (simp add: additive.associative del: additive.invertible_left_inverse)
  then show ?thesis by simp
qed

end (* Ring *)


subsection \<open>Commutative rings, integral domains, and fields\<close>

text \<open>A commutative ring is a ring whose multiplication is commutative.  We reuse the
  @{locale commutative_monoid} structure on the multiplicative part, mirroring how
  @{locale Abelian_Group} reuses @{locale commutative_monoid}.\<close>
locale commutative_ring = Ring +
  multiplicative: commutative_monoid R "(\<cdot>)" \<one>
begin

text \<open>Associative-commutative normalisation bundles for the two operations, for on-demand use as
  @{text "simp add: mult_ac"} / @{text "simp add: add_ac"}.  The additive group is abelian, so it too
  supplies the @{text ac} bundle.\<close>
lemmas mult_ac = multiplicative.ac
lemmas add_ac = additive.ac

end

text \<open>A nontrivial ring is one in which the unit and zero differ.  Both integral domains
  and fields require this, so we factor it into a common ancestor: that way the assumption
  is inherited (and named @{text nontrivial}) by a single route, avoiding a duplicate when
  a field is shown to be an integral domain or interpreted.\<close>
locale nontrivial_ring = Ring +
  assumes nontrivial: "\<one> \<noteq> \<zero>"

text \<open>An integral domain is a nontrivial commutative ring without zero divisors.\<close>
locale integral_domain = commutative_ring + nontrivial_ring +
  assumes no_zero_divisors: "\<lbrakk> a \<in> R; b \<in> R; a \<cdot> b = \<zero> \<rbrakk> \<Longrightarrow> a = \<zero> \<or> b = \<zero>"

text \<open>A field is a nontrivial commutative ring in which every nonzero element is
  invertible.  Invertibility is expressed through the multiplicative monoid's
  @{const Monoid.invertible} predicate, so the multiplicative inverse and unit
  machinery is available via the @{text multiplicative} prefix.\<close>
locale Field = commutative_ring + nontrivial_ring +
  assumes field_inverse: "\<lbrakk> a \<in> R; a \<noteq> \<zero> \<rbrakk> \<Longrightarrow> multiplicative.invertible a"
begin

text \<open>Every field is an integral domain.\<close>
sublocale integral_domain
proof unfold_locales
  fix a b assume a: "a \<in> R" and b: "b \<in> R" and ab: "a \<cdot> b = \<zero>"
  show "a = \<zero> \<or> b = \<zero>"
  proof (cases "a = \<zero>")
    case False
    then have inv: "multiplicative.invertible a" using a field_inverse by blast
    then have ia: "multiplicative.inverse a \<in> R" using a by simp
    have "b = multiplicative.inverse a \<cdot> (a \<cdot> b)"
      using a b inv by (simp add: multiplicative.invertible_left_inverse2)
    also have "\<dots> = multiplicative.inverse a \<cdot> \<zero>" using ab by simp
    also have "\<dots> = \<zero>" using ia by (rule right_zero)
    finally have "b = \<zero>" .
    then show ?thesis ..
  qed simp
qed

end (* field *)


subsection \<open>Ideals, Quotient Rings\<close>

text \<open>p 101, ll 2--5\<close>
locale ring_congruence = Ring +
  additive: group_congruence R "(+)" \<zero> E +
  multiplicative: Monoid_congruence R "(\<cdot>)" \<one> E
  for E
begin

text \<open>p 101, ll 2--5\<close>
notation additive.quotient_composition (infixl \<open>[+]\<close> 65)
notation additive.quotient.inverse (\<open>[-] _\<close> [66] 65)
notation multiplicative.quotient_composition (infixl \<open>[\<cdot>]\<close> 70)

text \<open>p 101, ll 5--11\<close>
sublocale quotient: Ring "R / E" "([+])" "([\<cdot>])" "additive.Class \<zero>" "additive.Class \<one>"
  by unfold_locales
    (auto simp: additive.Class_commutes_with_composition additive.associative additive.commutative
     multiplicative.Class_commutes_with_composition distributive elim!: additive.quotient_ClassE)

end (* ring_congruence *)

text \<open>p 101, ll 12--13\<close>
locale subgroup_of_additive_group_of_ring =
  additive: Subgroup I R "(+)" \<zero> + Ring R "(+)" "(\<cdot>)" \<zero> \<one>
  for I and R and addition (infixl \<open>+\<close> 65) and multiplication (infixl \<open>\<cdot>\<close> 70) and zero (\<open>\<zero>\<close>) and unit (\<open>\<one>\<close>)
begin

text \<open>p 101, ll 13--14\<close>
definition "Ring_Congruence = {(a, b). a \<in> R \<and> b \<in> R \<and> a - b \<in> I}"

text \<open>p 101, ll 13--14\<close>
lemma Ring_CongruenceI: "\<lbrakk> a - b \<in> I; a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> (a, b) \<in> Ring_Congruence"
  using Ring_Congruence_def by blast

text \<open>p 101, ll 13--14\<close>
lemma Ring_CongruenceD: "(a, b) \<in> Ring_Congruence \<Longrightarrow> a - b \<in> I"
  using Ring_Congruence_def by blast

text \<open>
  Jacobson's definition of Ring congruence deviates from that of group congruence; this complicates
  the proof.
\<close>
text \<open>p 101, ll 12--14\<close>
sublocale additive: subgroup_of_abelian_group I R "(+)" \<zero>  (* implies normal_subgroup *)
  rewrites additive_congruence: "additive.Congruence = Ring_Congruence"
proof -
  show "subgroup_of_abelian_group I R (+) \<zero>"
    using additive.commutative additive.invertible_right_inverse2 by unfold_locales auto
  then interpret additive: subgroup_of_abelian_group I R "(+)" \<zero> .
  {
    fix a b
    assume [simp]: "a \<in> R" "b \<in> R"
    have "a - b \<in> I \<longleftrightarrow> - (a - b) \<in> I" by auto
    also have "\<dots> \<longleftrightarrow> - a + b \<in> I" by (simp add: additive.commutative additive.inverse_composition_commute)
    finally have "a - b \<in> I \<longleftrightarrow> - a + b \<in> I" .
  }
  then show "additive.Congruence = Ring_Congruence"
    unfolding additive.Congruence_def Ring_Congruence_def by auto
qed

text \<open>p 101, l 14\<close>
notation additive.Left_Coset (infixl \<open>+|\<close> 65)

end (* subgroup_of_additive_group_of_ring *)

text \<open>Def 2.2\<close>
text \<open>p 101, ll 21--22\<close>
locale Ideal = subgroup_of_additive_group_of_ring +
  assumes Ideal: "\<lbrakk> a \<in> R; b \<in> I \<rbrakk> \<Longrightarrow> a \<cdot> b \<in> I" "\<lbrakk> a \<in> R; b \<in> I \<rbrakk> \<Longrightarrow> b \<cdot> a \<in> I"

context subgroup_of_additive_group_of_ring begin

text \<open>p 101, ll 14--17\<close>
theorem multiplicative_congruence_implies_ideal:
  assumes "Monoid_congruence R (\<cdot>) \<one> Ring_Congruence"
  shows "Ideal I R (+) (\<cdot>) \<zero> \<one>"
proof -
  interpret multiplicative: Monoid_congruence R "(\<cdot>)" \<one> Ring_Congruence by fact
  show ?thesis
  proof
    fix a b
    assume [simp]: "a \<in> R" "b \<in> I"
    have congs: "(a, a) \<in> Ring_Congruence" "(b, \<zero>) \<in> Ring_Congruence"
      by (auto simp: additive.ClassD additive.Class_unit_normal_subgroup)
    from congs have "(a \<cdot> b, \<zero>) \<in> Ring_Congruence" using multiplicative.cong by fastforce
    then show "a \<cdot> b \<in> I" using additive.Class_unit_normal_subgroup by blast
    from congs have "(b \<cdot> a, \<zero>) \<in> Ring_Congruence" using multiplicative.cong by fastforce
    then show "b \<cdot> a \<in> I"  using additive.Class_unit_normal_subgroup by blast
  qed
qed

end (* subgroup_of_additive_group_of_ring *)

context Ideal begin

text \<open>p 101, ll 17--20\<close>
theorem multiplicative_congruence [intro]:
  assumes a: "(a, a') \<in> Ring_Congruence" and b: "(b, b') \<in> Ring_Congruence"
  shows "(a \<cdot> b, a' \<cdot> b') \<in> Ring_Congruence"
proof -
  note Ring_CongruenceI [intro] Ring_CongruenceD [dest]
  from a b have [simp]: "a \<in> R" "a' \<in> R" "b \<in> R" "b' \<in> R" by auto
  from a have [simp]: "a - a' \<in> I" ..
  have "a \<cdot> b - a' \<cdot> b = (a - a') \<cdot> b" by (simp add: distributive left_minus)
  also have "\<dots> \<in> I" by (simp add: Ideal)
  finally have ab: "a \<cdot> b - a' \<cdot> b \<in> I" .  \<comment> \<open>ll 18--19\<close>
  from b have [simp]: "b - b' \<in> I" ..
  have "a' \<cdot> b - a' \<cdot> b' = a' \<cdot> (b - b')" by (simp add: distributive right_minus)
  also have "\<dots> \<in> I" by (simp add: Ideal)
  finally have a'b': "a' \<cdot> b - a' \<cdot> b' \<in> I" .  \<comment> \<open>l 19\<close>
  have "a \<cdot> b - a' \<cdot> b' = (a \<cdot> b - a' \<cdot> b) + (a' \<cdot> b - a' \<cdot> b')"
    by (simp add: additive.associative) (simp add: additive.associative [symmetric])
  also have "\<dots> \<in> I" using ab a'b' by simp
  finally show "(a \<cdot> b, a' \<cdot> b') \<in> Ring_Congruence" by auto  \<comment> \<open>ll 19--20\<close>
qed

text \<open>p 101, ll 23--24\<close>
sublocale ring_congruence where E = Ring_Congruence by unfold_locales rule

end (* ideal *)

text \<open>p 101, ll 24--26\<close>
locale quotient_ring = Ideal begin

text \<open>p 101, ll 24--26\<close>
sublocale quotient: Ring "R / (subgroup_of_additive_group_of_ring.Ring_Congruence I R (+) \<zero>)" "([+])" "([\<cdot>])" "additive.Class \<zero>" "additive.Class \<one>" ..

text \<open>p 101, l 26\<close>
lemmas Left_Coset = additive.Left_CosetE

text \<open>Equation 17 (1)\<close>
text \<open>p 101, l 28\<close>
lemmas quotient_addition = additive.factor_composition

text \<open>Equation 17 (2)\<close>
text \<open>p 101, l 29\<close>
theorem quotient_multiplication [simp]:
  "\<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> (a +| I) [\<cdot>] (b +| I) = a \<cdot> b +| I"
  using multiplicative.Class_commutes_with_composition additive.Class_is_Left_Coset by auto

text \<open>p 101, l 30\<close>
lemmas quotient_zero = additive.factor_unit
lemmas quotient_negative = additive.factor_inverse

end (* quotient_ring *)


subsection \<open>Homomorphisms of Rings.  Basic Theorems\<close>

text \<open>Def 2.3\<close>
text \<open>p 106, ll 7--9\<close>
locale ring_homomorphism =
  map \<eta> R R' + source: Ring R "(+)" "(\<cdot>)" \<zero> \<one> + target: Ring R' "(+')" "(\<cdot>')" "\<zero>'" "\<one>'" +
  additive: group_homomorphism \<eta> R "(+)" \<zero> R' "(+')" "\<zero>'" +
  multiplicative: Monoid_homomorphism \<eta> R "(\<cdot>)" \<one> R' "(\<cdot>')" "\<one>'"
  for \<eta>
    and R and addition (infixl \<open>+\<close> 65) and multiplication (infixl \<open>\<cdot>\<close> 70) and zero (\<open>\<zero>\<close>) and unit (\<open>\<one>\<close>)
    and R' and addition' (infixl \<open>+''\<close> 65) and multiplication' (infixl \<open>\<cdot>''\<close> 70) and zero' (\<open>\<zero>''\<close>) and unit' (\<open>\<one>''\<close>)

text \<open>p 106, l 17\<close>
locale ring_epimorphism = ring_homomorphism + surjective_map \<eta> R R'

text \<open>p 106, ll 14--18\<close>
sublocale quotient_ring \<subseteq> natural: ring_epimorphism
  where \<eta> = additive.Class and R' = "R / (subgroup_of_additive_group_of_ring.Ring_Congruence I R (+) \<zero>)" and addition' = "([+])" and multiplication' =  "([\<cdot>])"
    and zero' = "additive.Class \<zero>" and unit' = "additive.Class \<one>"
  ..

context ring_homomorphism begin

text \<open>
  Jacobson reasons via @{term "a - b \<in> additive.Ker"} being a congruence; we prefer the direct proof,
  since it is very simple.
\<close>
text \<open>p 106, ll 19--21\<close>
sublocale kernel: Ideal where I = additive.Ker
  by unfold_locales (auto simp: additive.Ker_image multiplicative.commutes_with_composition)

end (* ring_homomorphism *)

text \<open>p 106, l 22\<close>
locale ring_monomorphism = ring_homomorphism + injective_map \<eta> R R'

context ring_homomorphism begin

text \<open>p 106, ll 21--23\<close>
theorem ring_monomorphism_iff_kernel_unit:
  "ring_monomorphism \<eta> R (+) (\<cdot>) \<zero> \<one> R' (+') (\<cdot>') \<zero>' \<one>' \<longleftrightarrow> additive.Ker = {\<zero>}" (is "?monom \<longleftrightarrow> ?ker")
proof
  assume ?monom then interpret ring_monomorphism . show ?ker by (simp add: additive.injective_iff_kernel_unit [symmetric])
next
  assume ?ker then show ?monom by unfold_locales (simp add: additive.injective_iff_kernel_unit)
qed
  
end (* ring_homomorphism *)

text \<open>p 106, ll 23--25\<close>
sublocale ring_homomorphism \<subseteq> image: Subring "\<eta> ` R" R' "(+')" "(\<cdot>')" "\<zero>'" "\<one>'" ..

text \<open>p 106, ll 26--27\<close>
locale ideal_in_kernel =
  ring_homomorphism + contained: Ideal I R "(+)" "(\<cdot>)" \<zero> \<one> for I +
  assumes subset: "I \<subseteq> additive.Ker"
begin

text \<open>p 106, ll 26--27\<close>
notation contained.additive.quotient_composition (infixl \<open>[+]\<close> 65)
notation contained.multiplicative.quotient_composition (infixl \<open>[\<cdot>]\<close> 70)

text \<open>Provides @{text additive.induced}, which Jacobson calls $\bar{\eta}$.\<close>
text \<open>p 106, l 30\<close>
sublocale additive: normal_subgroup_in_kernel \<eta> R "(+)" \<zero> R' "(+')" "\<zero>'" I
  rewrites "normal_subgroup.Congruence I R addition zero = contained.Ring_Congruence"
  by unfold_locales (rule subset contained.additive_congruence)+

text \<open>Only the multiplicative part needs some work.\<close>
text \<open>p 106, ll 27--30\<close>
sublocale induced: ring_homomorphism additive.induced "R / (subgroup_of_additive_group_of_ring.Ring_Congruence I R (+) \<zero>)" "([+])" "([\<cdot>])" "contained.additive.Class \<zero>" "contained.additive.Class \<one>"
  using contained.multiplicative.Class_commutes_with_composition
  by unfold_locales
    (auto elim!: contained.additive.Left_CosetE simp: contained.additive.Class_is_Left_Coset multiplicative.commutes_with_composition multiplicative.commutes_with_unit)

text \<open>p 106, l 30; p 107, ll 1--3\<close>
text \<open>
  @{term additive.induced} denotes Jacobson's $\bar{\eta}$.  We have the commutativity of the diagram, where
  @{term additive.induced} is unique: @{thm [display] additive.factorization} @{thm [display] additive.uniqueness}
\<close>

end (* ideal_in_kernel *)

text \<open>Fundamental Theorem of Homomorphisms of Rings\<close>

text \<open>p 107, l 6\<close>
locale ring_homomorphism_fundamental = ring_homomorphism begin

text \<open>p 107, l 6\<close>
notation kernel.additive.quotient_composition (infixl \<open>[+]\<close> 65)
notation kernel.multiplicative.quotient_composition (infixl \<open>[\<cdot>]\<close> 70)

text \<open>p 107, l 6\<close>
sublocale ideal_in_kernel where I = additive.Ker by unfold_locales rule

text \<open>p 107, ll 8--9\<close>
sublocale natural: ring_epimorphism
  where \<eta> = kernel.additive.Class and R' = "R / (subgroup_of_additive_group_of_ring.Ring_Congruence additive.Ker R (+) \<zero>)"
    and addition' = "kernel.additive.quotient_composition"
    and multiplication' = "kernel.multiplicative.quotient_composition"
    and zero' = "kernel.additive.Class \<zero>" and unit' = "kernel.additive.Class \<one>"
  ..

text \<open>p 107, l 9\<close>
sublocale induced: ring_monomorphism
  where \<eta> = additive.induced and R = "R / (subgroup_of_additive_group_of_ring.Ring_Congruence additive.Ker R (+) \<zero>)"
    and addition = "kernel.additive.quotient_composition"
    and multiplication = "kernel.multiplicative.quotient_composition"
    and zero = "kernel.additive.Class \<zero>" and unit = "kernel.additive.Class \<one>"
  by unfold_locales (simp add: additive.induced_inj_on)

end (* ring_homomorphism_fundamental *)

text \<open>p 107, l 11\<close>
locale ring_isomorphism = ring_homomorphism + bijective_map \<eta> R R' begin

text \<open>p 107, l 11\<close>
sublocale ring_monomorphism ..
sublocale ring_epimorphism ..

text \<open>p 107, l 11\<close>
lemma inverse_ring_isomorphism:
  "ring_isomorphism (restrict (inv_into R \<eta>) R') R' (+') (\<cdot>') \<zero>' \<one>' R (+) (\<cdot>) \<zero> \<one>"
proof
  fix x y
  assume "x \<in> R'" and "y \<in> R'"
  then obtain u v where *: "\<eta> u = x" "\<eta> v = y" "u \<in> R" "v \<in> R"
    using surjective by blast
  then show "restrict (inv_into R \<eta>) R' (x +' y) = restrict (inv_into R \<eta>) R' x + restrict (inv_into R \<eta>) R' y"
    by (auto simp flip: additive.commutes_with_composition)
  show "restrict (inv_into R \<eta>) R' (x \<cdot>' y) = restrict (inv_into R \<eta>) R' x \<cdot> restrict (inv_into R \<eta>) R' y"
    using * by (auto simp: inv_into_f_eq multiplicative.commutes_with_composition)
next
  show "restrict (inv_into R \<eta>) R' \<zero>' = \<zero>"
    using additive.commutes_with_unit by force
  show "restrict (inv_into R \<eta>) R' \<one>' = \<one>"
    using multiplicative.commutes_with_unit by auto
  show "bij_betw (restrict (inv_into R \<eta>) R') R' R"
    using bij_betw_inverse by blast
qed

end (* ring_isomorphsim *)

text \<open>p 107, l 11\<close>
definition isomorphic_as_rings (infixl \<open>\<cong>\<^sub>R\<close> 50)
  where "\<R> \<cong>\<^sub>R \<R>' \<longleftrightarrow> (let (R, addition, multiplication, zero, unit) = \<R>; (R', addition', multiplication', zero', unit') = \<R>' in
  (\<exists>\<eta>. ring_isomorphism \<eta> R addition multiplication zero unit R' addition' multiplication' zero' unit'))"

text \<open>p 107, l 11\<close>
lemma isomorphic_as_rings_symmetric:
  "(R, addition, multiplication, zero, unit) \<cong>\<^sub>R (R', addition', multiplication', zero', unit') \<Longrightarrow>
   (R', addition', multiplication', zero', unit') \<cong>\<^sub>R (R, addition, multiplication, zero, unit)"
  by (simp add: isomorphic_as_rings_def) (meson ring_isomorphism.inverse_ring_isomorphism)

context ring_homomorphism begin

text \<open>Corollary\<close>
text \<open>p 107, ll 11--12\<close>
theorem image_is_isomorphic_to_quotient_ring:
  "\<exists>K add mult zero one. Ideal K R (+) (\<cdot>) \<zero> \<one> \<and> (\<eta> ` R, (+'), (\<cdot>'), \<zero>', \<one>') \<cong>\<^sub>R (R / (subgroup_of_additive_group_of_ring.Ring_Congruence K R (+) \<zero>), add, mult, zero, one)"
proof -
  interpret image: ring_homomorphism_fundamental where R' = "\<eta> ` R"
    by unfold_locales (auto simp: target.additive.commutative additive.commutes_with_composition
      multiplicative.commutes_with_composition target.distributive multiplicative.commutes_with_unit)
  have "ring_isomorphism image.additive.induced (R / (subgroup_of_additive_group_of_ring.Ring_Congruence additive.Ker R (+) \<zero>)) ([+]) ([\<cdot>]) (kernel.additive.Class \<zero>) (kernel.additive.Class \<one>) (\<eta> ` R) (+') (\<cdot>') \<zero>' \<one>'"
    by unfold_locales (simp add: image.additive.induced_image bij_betw_def)
  then have "(\<eta> ` R, (+'), (\<cdot>'), \<zero>', \<one>') \<cong>\<^sub>R (R / (subgroup_of_additive_group_of_ring.Ring_Congruence additive.Ker R (+) \<zero>), ([+]), ([\<cdot>]), kernel.additive.Class \<zero>, kernel.additive.Class \<one>)"
    by (simp add: isomorphic_as_rings_def) (meson ring_isomorphism.inverse_ring_isomorphism)
  moreover have "Ideal additive.Ker R (+) (\<cdot>) \<zero> \<one>" ..
  ultimately show ?thesis by blast
qed

end (* ring_homomorphism *)


subsection \<open>Abstract type of rings\<close>

lemma trivial_Ring': "Ring' trivial_monoid trivial_monoid"
proof 
qed (simp_all add: Monoid.mcarrier_monoid Monoid.munit_monoid trivial_Monoid
      trivial_monoid_def Monoid.mmult_monoid trivial_Monoid trivial_Monoid_invertible)

lemma trivial_Ring: "Ring {undefined} (\<lambda>x y. undefined) (\<lambda>x y. undefined) undefined undefined"
proof -
  have "commutative_monoid_axioms {undefined} (\<lambda>x y. undefined)"
    by (simp add: commutative_monoid_axioms.intro)
  moreover have "Ring_axioms {undefined} (\<lambda>x y. undefined) (\<lambda>x y. undefined)"
    by (simp add: Ring_axioms.intro)
  ultimately show ?thesis
    by (auto simp: Ring_def Abelian_Group_def commutative_monoid_def trivial_Group trivial_Monoid)
qed

typedef 'a ring = "{(addition::'a monoid, multiplication). Ring' addition multiplication}"
  morphisms "dest_ring" "ring"
  using trivial_Ring' by blast

declare dest_ring_inverse [simp]

definition "trivial_ring \<equiv> ring (trivial_monoid, trivial_monoid)"

definition radd where "radd m \<equiv> fst (dest_ring m)"

definition rmult where "rmult m \<equiv> snd (dest_ring m)"

definition rcarrier where "rcarrier m \<equiv> mcarrier (radd m)"

lemma ring_is_Ring [iff]: "Ring' (radd m) (rmult m)"
  by (metis Product_Type.Collect_case_prodD dest_ring radd_def rmult_def)

lemma ring_collapse [simp]: "ring (radd r, rmult r) = r"
  by (simp add: radd_def rmult_def)


text \<open>Allows reference to the current ring space within the locale as a value\<close>
definition (in Ring') "Self \<equiv> ring (additive, multiplicative)"

lemma (in Ring') radd_Self [simp]: "radd Self = additive"
  by (simp add: Ring'_axioms Self_def radd_def ring_inverse)

lemma (in Ring') rmult_Self [simp]: "rmult Self = multiplicative"
  by (simp add: Ring'_axioms Self_def ring_inverse rmult_def)


text \<open>Further accessors, mirroring the @{typ "'a monoid"} type: the additive and
  multiplicative operations and the two distinguished constants @{text \<zero>}, @{text \<one>}
  recovered from the component monoids.  (We keep @{const radd}/@{const rmult} returning
  whole @{typ "'a monoid"} values, as @{locale Ring'} is built on those.)\<close>

definition radd_op where "radd_op m \<equiv> mmult (radd m)"

definition rmult_op where "rmult_op m \<equiv> mmult (rmult m)"

definition rzero where "rzero m \<equiv> munit (radd m)"

definition rone where "rone m \<equiv> munit (rmult m)"

text \<open>The value really is a ring: the analogue of @{thm [source] monoid_is_Monoid}.\<close>
lemma Ring_ring [iff]: "Ring (rcarrier m) (radd_op m) (rmult_op m) (rzero m) (rone m)"
  using Ring'.Ring [OF ring_is_Ring [of m]]
  by (simp add: rcarrier_def radd_op_def rmult_op_def rzero_def rone_def)

text \<open>Computing the accessors of a ring built from its component monoids.\<close>
lemma (in Ring') radd_ring [simp]: "radd (ring (additive, multiplicative)) = additive"
  by (simp add: Ring'_axioms radd_def ring_inverse)

lemma (in Ring') rmult_ring [simp]: "rmult (ring (additive, multiplicative)) = multiplicative"
  by (simp add: Ring'_axioms rmult_def ring_inverse)

lemma (in Ring') rcarrier_ring [simp]: "rcarrier (ring (additive, multiplicative)) = mcarrier additive"
  by (simp add: rcarrier_def)

lemma (in Ring') rzero_ring [simp]: "rzero (ring (additive, multiplicative)) = munit additive"
  by (simp add: rzero_def)

lemma (in Ring') rone_ring [simp]: "rone (ring (additive, multiplicative)) = munit multiplicative"
  by (simp add: rone_def)

lemma (in Ring') radd_op_ring [simp]: "radd_op (ring (additive, multiplicative)) = mmult additive"
  by (simp add: radd_op_def)

lemma (in Ring') rmult_op_ring [simp]: "rmult_op (ring (additive, multiplicative)) = mmult multiplicative"
  by (simp add: rmult_op_def)


text \<open>Within the mathematical @{locale Ring} locale, the component monoids form a
  @{locale Ring'}, so the current ring can be referred to as a value.\<close>
lemma (in Ring) Ring'_Self_components:
  "Ring' (monoid (R, (+), \<zero>)) (monoid (R, (\<cdot>), \<one>))"
proof -
  have a: "mcarrier (monoid (R, (+), \<zero>)) = R" "mmult (monoid (R, (+), \<zero>)) = (+)"
          "munit (monoid (R, (+), \<zero>)) = \<zero>"
    by (simp_all add: additive.mcarrier_monoid additive.mmult_monoid additive.munit_monoid)
  have m: "mcarrier (monoid (R, (\<cdot>), \<one>)) = R" "mmult (monoid (R, (\<cdot>), \<one>)) = (\<cdot>)"
          "munit (monoid (R, (\<cdot>), \<one>)) = \<one>"
    by (simp_all add: multiplicative.mcarrier_monoid multiplicative.mmult_monoid multiplicative.munit_monoid)
  show ?thesis
    by (simp add: Ring'_def a m Ring_axioms)
qed

definition (in Ring) "Self \<equiv> ring (monoid (R, (+), \<zero>), monoid (R, (\<cdot>), \<one>))"

lemma (in Ring) rcarrier_Self [simp]: "rcarrier Self = R"
  by (simp add: Self_def Ring'.rcarrier_ring Ring'_Self_components additive.mcarrier_monoid)

lemma (in Ring) rzero_Self [simp]: "rzero Self = \<zero>"
  by (simp add: Self_def Ring'.rzero_ring Ring'_Self_components additive.munit_monoid)

lemma (in Ring) rone_Self [simp]: "rone Self = \<one>"
  by (simp add: Self_def Ring'.rone_ring Ring'_Self_components multiplicative.munit_monoid)

lemma (in Ring) radd_op_Self [simp]: "radd_op Self = (+)"
  by (simp add: Self_def Ring'.radd_op_ring Ring'_Self_components additive.mmult_monoid)

lemma (in Ring) rmult_op_Self [simp]: "rmult_op Self = (\<cdot>)"
  by (simp add: Self_def Ring'.rmult_op_ring Ring'_Self_components multiplicative.mmult_monoid)


text \<open>The one abstract @{typ "'a ring"} type serves all the ring-like structures: which
  one a value belongs to is recorded by a predicate on its accessors.  (We provide the
  field predicate, used in Galois theory; the others follow the same shape.)\<close>
definition is_field where
  "is_field r \<equiv> Field (rcarrier r) (radd_op r) (rmult_op r) (rzero r) (rone r)"

lemma is_fieldI:
  "Field (rcarrier r) (radd_op r) (rmult_op r) (rzero r) (rone r) \<Longrightarrow> is_field r"
  by (simp add: is_field_def)

lemma is_fieldD:
  "is_field r \<Longrightarrow> Field (rcarrier r) (radd_op r) (rmult_op r) (rzero r) (rone r)"
  by (simp add: is_field_def)

end
