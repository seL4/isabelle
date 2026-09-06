section \<open>The Chinese Remainder Theorem for commutative rings\<close>

theory Chinese_Remainder_Rings
  imports Ideal_Theory Ring_Family_Product
begin

text \<open>For two comaximal ideals \<open>I\<close>, \<open>J\<close> of a commutative ring \<open>R\<close> (i.e.\ \<open>I + J = R\<close>), the quotient
  \<open>R / (I \<inter> J)\<close> is isomorphic to the product ring \<open>(R / I) \<times> (R / J)\<close>.  The proof follows the classical
  route: the canonical map \<open>a \<mapsto> (I + a, J + a)\<close> into the product of the two quotient rings is a ring
  homomorphism, surjective by comaximality, with kernel \<open>I \<inter> J\<close>; the fundamental theorem of ring
  homomorphisms then yields the isomorphism.\<close>


subsection \<open>Associative-commutative rewriting in an abelian group\<close>

text \<open>The @{locale Abelian_Group} locale exposes only the raw associativity, commutativity and inverse
  axioms (each with a carrier side condition), so plain @{method simp} cannot ac-normalise sums.  We
  prove a few confluent cancellation lemmas and a couple of rearrangement lemmas that the
  Chinese-Remainder arithmetic below relies on.\<close>

context Abelian_Group
begin

text \<open>Left-nested inverse cancellations (safe as simp rules: not permutative).\<close>
lemma add_assoc_inverse_left [simp]:
  "\<lbrakk> a \<in> G; b \<in> G \<rbrakk> \<Longrightarrow> inverse a \<cdot> (a \<cdot> b) = b"
  by (simp add: associative [symmetric])

lemma add_assoc_inverse_left' [simp]:
  "\<lbrakk> a \<in> G; b \<in> G \<rbrakk> \<Longrightarrow> a \<cdot> (inverse a \<cdot> b) = b"
  by (simp add: associative [symmetric])

text \<open>Rearrangement: @{term "(q \<cdot> p) \<cdot> inverse (s \<cdot> q) = p \<cdot> inverse s"}.  This is the shape needed to
  simplify \<open>(x\<cdot>j + y\<cdot>i) - (x\<cdot>i + x\<cdot>j)\<close> in the surjectivity argument.\<close>
lemma add_diff_cancel_mid:
  assumes q: "q \<in> G" and p: "p \<in> G" and s: "s \<in> G"
  shows "(q \<cdot> p) \<cdot> inverse (s \<cdot> q) = p \<cdot> inverse s"
proof -
  have ninv: "inverse (s \<cdot> q) = inverse q \<cdot> inverse s"
    using q s by (simp add: inverse_composition_commute commutative)
  have "(q \<cdot> p) \<cdot> inverse (s \<cdot> q) = (p \<cdot> q) \<cdot> (inverse q \<cdot> inverse s)"
    using q p by (simp add: ninv commutative)
  also have "\<dots> = p \<cdot> (q \<cdot> (inverse q \<cdot> inverse s))"
    using q p s by (simp add: associative)
  also have "\<dots> = p \<cdot> inverse s" using q s by simp
  finally show ?thesis .
qed

end


subsection \<open>The binary direct product of two rings\<close>

text \<open>The external direct product of two rings, carried on pairs, with pointwise operations.  This
  specialises the indexed direct product of \<open>Ring_Family_Product\<close> to two factors, which keeps the
  carrier type @{typ "'a \<times> 'b"} rather than a dependent function space --- convenient for the two
  quotient rings occurring in the Chinese Remainder Theorem.  The notation follows @{locale
  ring_homomorphism}: primed operations for the second factor.\<close>

locale ring_pair =
  A: Ring R "(+)" "(\<cdot>)" \<zero> \<one> + B: Ring R' "(+')" "(\<cdot>')" "\<zero>'" "\<one>'"
  for R and addition (infixl \<open>+\<close> 65) and multiplication (infixl \<open>\<cdot>\<close> 70) and zero (\<open>\<zero>\<close>) and unit (\<open>\<one>\<close>)
  and R' and addition' (infixl \<open>+''\<close> 65) and multiplication' (infixl \<open>\<cdot>''\<close> 70) and zero' (\<open>\<zero>''\<close>) and unit' (\<open>\<one>''\<close>)
begin

definition Bcarrier :: "('a \<times> 'b) set"
  where "Bcarrier = R \<times> R'"

definition Badd :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b)" (infixl \<open>\<oplus>\<^sub>\<times>\<close> 65)
  where "x \<oplus>\<^sub>\<times> y = (fst x + fst y, snd x +' snd y)"

definition Bmult :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b)" (infixl \<open>\<otimes>\<^sub>\<times>\<close> 70)
  where "x \<otimes>\<^sub>\<times> y = (fst x \<cdot> fst y, snd x \<cdot>' snd y)"

definition Bzero :: "'a \<times> 'b" (\<open>\<zero>\<^sub>\<times>\<close>)
  where "\<zero>\<^sub>\<times> = (\<zero>, \<zero>')"

definition Bone :: "'a \<times> 'b" (\<open>\<one>\<^sub>\<times>\<close>)
  where "\<one>\<^sub>\<times> = (\<one>, \<one>')"

lemma Bcarrier_iff [simp]: "(a, b) \<in> Bcarrier \<longleftrightarrow> a \<in> R \<and> b \<in> R'"
  by (simp add: Bcarrier_def)

lemma Badd_apply [simp]: "(a\<^sub>1, b\<^sub>1) \<oplus>\<^sub>\<times> (a\<^sub>2, b\<^sub>2) = (a\<^sub>1 + a\<^sub>2, b\<^sub>1 +' b\<^sub>2)"
  by (simp add: Badd_def)

lemma Bmult_apply [simp]: "(a\<^sub>1, b\<^sub>1) \<otimes>\<^sub>\<times> (a\<^sub>2, b\<^sub>2) = (a\<^sub>1 \<cdot> a\<^sub>2, b\<^sub>1 \<cdot>' b\<^sub>2)"
  by (simp add: Bmult_def)

theorem Ring_Bcarrier: "Ring Bcarrier (\<oplus>\<^sub>\<times>) (\<otimes>\<^sub>\<times>) \<zero>\<^sub>\<times> \<one>\<^sub>\<times>"
proof (rule Ring.intro)
  show "Abelian_Group Bcarrier (\<oplus>\<^sub>\<times>) \<zero>\<^sub>\<times>"
  proof (rule Abelian_Group.intro)
    show "Group Bcarrier (\<oplus>\<^sub>\<times>) \<zero>\<^sub>\<times>"
    proof (rule GroupI)
      show "\<And>x y. x \<in> Bcarrier \<Longrightarrow> y \<in> Bcarrier \<Longrightarrow> x \<oplus>\<^sub>\<times> y \<in> Bcarrier"
        by (auto simp: Badd_def Bcarrier_def)
      show "\<zero>\<^sub>\<times> \<in> Bcarrier" by (simp add: Bzero_def Bcarrier_def)
    next
      fix x y z assume "x \<in> Bcarrier" "y \<in> Bcarrier" "z \<in> Bcarrier"
      then show "(x \<oplus>\<^sub>\<times> y) \<oplus>\<^sub>\<times> z = x \<oplus>\<^sub>\<times> (y \<oplus>\<^sub>\<times> z)"
        by (auto simp: Badd_def Bcarrier_def A.additive.associative B.additive.associative)
    next
      fix x assume "x \<in> Bcarrier" then show "\<zero>\<^sub>\<times> \<oplus>\<^sub>\<times> x = x"
        by (cases x) (simp add: Bzero_def Bcarrier_def)
    next
      fix x assume "x \<in> Bcarrier" then show "x \<oplus>\<^sub>\<times> \<zero>\<^sub>\<times> = x"
        by (cases x) (simp add: Bzero_def Bcarrier_def)
    next
      fix x assume x: "x \<in> Bcarrier"
      then have x1: "fst x \<in> R" and x2: "snd x \<in> R'" by (auto simp: Bcarrier_def)
      let ?v = "(A.additive.inverse (fst x), B.additive.inverse (snd x))"
      have "?v \<in> Bcarrier" using x1 x2 by (simp add: Bcarrier_def)
      moreover have "x \<oplus>\<^sub>\<times> ?v = \<zero>\<^sub>\<times> \<and> ?v \<oplus>\<^sub>\<times> x = \<zero>\<^sub>\<times>"
        using x1 x2 by (cases x) (simp add: Badd_def Bzero_def)
      ultimately show "\<exists>y \<in> Bcarrier. x \<oplus>\<^sub>\<times> y = \<zero>\<^sub>\<times> \<and> y \<oplus>\<^sub>\<times> x = \<zero>\<^sub>\<times>" by blast
    qed
    show "commutative_monoid Bcarrier (\<oplus>\<^sub>\<times>) \<zero>\<^sub>\<times>"
    proof (rule commutative_monoid.intro)
      show "Monoid Bcarrier (\<oplus>\<^sub>\<times>) \<zero>\<^sub>\<times>"
      proof (unfold_locales)
        show "\<And>x y. x \<in> Bcarrier \<Longrightarrow> y \<in> Bcarrier \<Longrightarrow> x \<oplus>\<^sub>\<times> y \<in> Bcarrier"
          by (auto simp: Badd_def Bcarrier_def)
        show "\<zero>\<^sub>\<times> \<in> Bcarrier" by (simp add: Bzero_def Bcarrier_def)
      next
        fix x y z assume "x \<in> Bcarrier" "y \<in> Bcarrier" "z \<in> Bcarrier"
        then show "(x \<oplus>\<^sub>\<times> y) \<oplus>\<^sub>\<times> z = x \<oplus>\<^sub>\<times> (y \<oplus>\<^sub>\<times> z)"
          by (auto simp: Badd_def Bcarrier_def A.additive.associative B.additive.associative)
      next
        fix x assume "x \<in> Bcarrier" then show "\<zero>\<^sub>\<times> \<oplus>\<^sub>\<times> x = x"
          by (cases x) (simp add: Bzero_def Bcarrier_def)
      next
        fix x assume "x \<in> Bcarrier" then show "x \<oplus>\<^sub>\<times> \<zero>\<^sub>\<times> = x"
          by (cases x) (simp add: Bzero_def Bcarrier_def)
      qed
      show "commutative_monoid_axioms Bcarrier (\<oplus>\<^sub>\<times>)"
      proof (unfold_locales)
        fix x y assume "x \<in> Bcarrier" "y \<in> Bcarrier"
        then show "x \<oplus>\<^sub>\<times> y = y \<oplus>\<^sub>\<times> x"
          by (auto simp: Badd_def Bcarrier_def A.additive.commutative B.additive.commutative)
      qed
    qed
  qed
  show "Monoid Bcarrier (\<otimes>\<^sub>\<times>) \<one>\<^sub>\<times>"
  proof (unfold_locales)
    show "\<And>x y. x \<in> Bcarrier \<Longrightarrow> y \<in> Bcarrier \<Longrightarrow> x \<otimes>\<^sub>\<times> y \<in> Bcarrier"
      by (auto simp: Bmult_def Bcarrier_def)
    show "\<one>\<^sub>\<times> \<in> Bcarrier" by (simp add: Bone_def Bcarrier_def)
  next
    fix x y z assume "x \<in> Bcarrier" "y \<in> Bcarrier" "z \<in> Bcarrier"
    then show "(x \<otimes>\<^sub>\<times> y) \<otimes>\<^sub>\<times> z = x \<otimes>\<^sub>\<times> (y \<otimes>\<^sub>\<times> z)"
      by (auto simp: Bmult_def Bcarrier_def A.multiplicative.associative B.multiplicative.associative)
  next
    fix x assume "x \<in> Bcarrier" then show "\<one>\<^sub>\<times> \<otimes>\<^sub>\<times> x = x"
      by (cases x) (simp add: Bone_def Bcarrier_def)
  next
    fix x assume "x \<in> Bcarrier" then show "x \<otimes>\<^sub>\<times> \<one>\<^sub>\<times> = x"
      by (cases x) (simp add: Bone_def Bcarrier_def)
  qed
  show "Ring_axioms Bcarrier (\<oplus>\<^sub>\<times>) (\<otimes>\<^sub>\<times>)"
  proof
    fix x y z assume "x \<in> Bcarrier" "y \<in> Bcarrier" "z \<in> Bcarrier"
    then show "x \<otimes>\<^sub>\<times> (y \<oplus>\<^sub>\<times> z) = x \<otimes>\<^sub>\<times> y \<oplus>\<^sub>\<times> (x \<otimes>\<^sub>\<times> z)"
      by (auto simp: Bmult_def Badd_def Bcarrier_def A.distributive B.distributive)
  next
    fix x y z assume "x \<in> Bcarrier" "y \<in> Bcarrier" "z \<in> Bcarrier"
    then show "(y \<oplus>\<^sub>\<times> z) \<otimes>\<^sub>\<times> x = y \<otimes>\<^sub>\<times> x \<oplus>\<^sub>\<times> (z \<otimes>\<^sub>\<times> x)"
      by (auto simp: Bmult_def Badd_def Bcarrier_def A.distributive B.distributive)
  qed
qed

sublocale product: Ring Bcarrier "(\<oplus>\<^sub>\<times>)" "(\<otimes>\<^sub>\<times>)" Bzero Bone
  by (rule Ring_Bcarrier)

end


subsection \<open>Sum of two ideals\<close>

text \<open>The sum \<open>I + J\<close> of two ideals: all sums \<open>i + j\<close> with \<open>i \<in> I\<close>, \<open>j \<in> J\<close>.  We work in a commutative
  ring throughout (the setting of the Chinese Remainder Theorem).\<close>

context ideal_in_comm_ring
begin

definition ideal_sum :: "'a set \<Rightarrow> 'a set"
  where "ideal_sum J = {i + j | i j. i \<in> I \<and> j \<in> J}"

lemma ideal_sum_memI: "\<lbrakk> i \<in> I; j \<in> J \<rbrakk> \<Longrightarrow> i + j \<in> ideal_sum J"
  unfolding ideal_sum_def by blast

lemma ideal_sum_memE:
  assumes "x \<in> ideal_sum J"
  obtains i j where "i \<in> I" "j \<in> J" "x = i + j"
  using assms unfolding ideal_sum_def by blast

text \<open>The sum contains both summands (using that ideals contain \<open>\<zero>\<close>).\<close>
lemma I_subset_ideal_sum:
  assumes "Ideal J R (+) (\<cdot>) \<zero> \<one>" shows "I \<subseteq> ideal_sum J"
proof
  interpret J: Ideal J R "(+)" "(\<cdot>)" \<zero> \<one> by (rule assms)
  fix x assume x: "x \<in> I"
  then have xR: "x \<in> R" using additive.subset by blast
  have "x + \<zero> \<in> ideal_sum J" using x J.additive.sub_unit_closed by (rule ideal_sum_memI)
  then show "x \<in> ideal_sum J" using xR by simp
qed

lemma J_subset_ideal_sum:
  assumes "Ideal J R (+) (\<cdot>) \<zero> \<one>" shows "J \<subseteq> ideal_sum J"
proof
  interpret J: Ideal J R "(+)" "(\<cdot>)" \<zero> \<one> by (rule assms)
  fix x assume x: "x \<in> J"
  then have xR: "x \<in> R" using J.additive.subset by blast
  have "\<zero> + x \<in> ideal_sum J" using additive.sub_unit_closed x by (rule ideal_sum_memI)
  then show "x \<in> ideal_sum J" using xR by simp
qed

text \<open>The intersection of the ambient ideal @{term I} with another ideal is again an ideal.\<close>
lemma inter_ideal:
  assumes "Ideal J R (+) (\<cdot>) \<zero> \<one>"
  shows "Ideal (I \<inter> J) R (+) (\<cdot>) \<zero> \<one>"
proof -
  interpret J: Ideal J R "(+)" "(\<cdot>)" \<zero> \<one> by (rule assms)
  have sg: "Subgroup (I \<inter> J) R (+) \<zero>"
  proof (rule additive.subgroupI)
    show "I \<inter> J \<subseteq> R" using additive.subset by blast
    show "\<zero> \<in> I \<inter> J" using additive.sub_unit_closed J.additive.sub_unit_closed by simp
  next
    fix g h assume "g \<in> I \<inter> J" "h \<in> I \<inter> J"
    then show "g + h \<in> I \<inter> J"
      using additive.sub_composition_closed J.additive.sub_composition_closed by auto
  next
    fix g assume "g \<in> I \<inter> J"
    then show "additive.invertible g" using additive.subset by auto
  next
    fix g assume g: "g \<in> I \<inter> J"
    then have gI: "g \<in> I" and gJ: "g \<in> J" by auto
    have "additive.inverse g \<in> I" using gI by simp
    moreover have "additive.inverse g \<in> J"
      using gJ J.additive.submonoid_inverse_closed J.additive.sub.invertible by auto
    ultimately show "additive.inverse g \<in> I \<inter> J" by simp
  qed
  interpret IJ: Subgroup "I \<inter> J" R "(+)" \<zero> by (rule sg)
  show ?thesis
  proof unfold_locales
    fix a b assume a: "a \<in> R" and b: "b \<in> I \<inter> J"
    show "a \<cdot> b \<in> I \<inter> J" using a b Ideal J.Ideal by auto
    show "b \<cdot> a \<in> I \<inter> J" using a b Ideal J.Ideal by auto
  qed
qed

text \<open>Comaximality is preserved under intersection: if @{term I} is comaximal with @{term J} and
  with @{term K} (meaning @{term "\<one> \<in> ideal_sum J"} and @{term "\<one> \<in> ideal_sum K"}), then @{term I}
  is comaximal with @{term "J \<inter> K"}.  The key step multiplies the two witnesses
  @{term "i\<^sub>1 + j = \<one>"}, @{term "i\<^sub>2 + k = \<one>"} and regroups.\<close>
lemma comaximal_inter:
  assumes J: "Ideal J R (+) (\<cdot>) \<zero> \<one>" and K: "Ideal K R (+) (\<cdot>) \<zero> \<one>"
    and comIJ: "\<exists>i\<in>I. \<exists>j\<in>J. i + j = \<one>"
    and comIK: "\<exists>i\<in>I. \<exists>k\<in>K. i + k = \<one>"
  shows "\<exists>i\<in>I. \<exists>m\<in>J \<inter> K. i + m = \<one>"
proof -
  interpret J: Ideal J R "(+)" "(\<cdot>)" \<zero> \<one> by (rule J)
  interpret K: Ideal K R "(+)" "(\<cdot>)" \<zero> \<one> by (rule K)
  obtain i\<^sub>1 j where i1: "i\<^sub>1 \<in> I" and j: "j \<in> J" and ij: "i\<^sub>1 + j = \<one>"
    using comIJ by blast
  obtain i\<^sub>2 k where i2: "i\<^sub>2 \<in> I" and k: "k \<in> K" and ik: "i\<^sub>2 + k = \<one>"
    using comIK by blast
  have i1R: "i\<^sub>1 \<in> R" using i1 additive.subset by blast
  have i2R: "i\<^sub>2 \<in> R" using i2 additive.subset by blast
  have jR: "j \<in> R" using j J.additive.subset by blast
  have kR: "k \<in> R" using k K.additive.subset by blast
  \<comment> \<open>Expand @{term "(i\<^sub>1 + j) \<cdot> (i\<^sub>2 + k) = \<one>"} by distributivity.\<close>
  define m where "m = i\<^sub>1 \<cdot> i\<^sub>2 + i\<^sub>1 \<cdot> k + j \<cdot> i\<^sub>2"
  have mR: "m \<in> R" unfolding m_def using i1R i2R jR kR by simp
  have expand: "(i\<^sub>1 + j) \<cdot> (i\<^sub>2 + k) = m + j \<cdot> k"
  proof -
    have d1: "i\<^sub>1 \<cdot> (i\<^sub>2 + k) = i\<^sub>1 \<cdot> i\<^sub>2 + i\<^sub>1 \<cdot> k"
      using i1R i2R kR by (simp add: distributive)
    have d2: "j \<cdot> (i\<^sub>2 + k) = j \<cdot> i\<^sub>2 + j \<cdot> k"
      using jR i2R kR by (simp add: distributive)
    have "(i\<^sub>1 + j) \<cdot> (i\<^sub>2 + k) = i\<^sub>1 \<cdot> (i\<^sub>2 + k) + j \<cdot> (i\<^sub>2 + k)"
      using distributive(2)[OF _ i1R jR] i2R kR by simp
    also have "\<dots> = (i\<^sub>1 \<cdot> i\<^sub>2 + i\<^sub>1 \<cdot> k) + (j \<cdot> i\<^sub>2 + j \<cdot> k)"
      by (simp add: d1 d2)
    also have "\<dots> = (i\<^sub>1 \<cdot> i\<^sub>2 + i\<^sub>1 \<cdot> k + j \<cdot> i\<^sub>2) + j \<cdot> k"
      using i1R i2R jR kR by (simp add: additive.associative)
    finally show ?thesis unfolding m_def .
  qed
  have eq: "m + j \<cdot> k = \<one>"
    using expand ij ik by simp
  \<comment> \<open>@{term m} lies in @{term I}; @{term "j \<cdot> k \<in> J \<inter> K"}.\<close>
  have m_in_I: "m \<in> I"
  proof -
    have "i\<^sub>1 \<cdot> i\<^sub>2 \<in> I" using i2R i1 by (simp add: Ideal)
    moreover have "i\<^sub>1 \<cdot> k \<in> I" using kR i1 by (simp add: Ideal)
    moreover have "j \<cdot> i\<^sub>2 \<in> I" using jR i2 by (simp add: Ideal)
    ultimately show ?thesis unfolding m_def by (simp add: additive.sub_composition_closed)
  qed
  have jk_in_JK: "j \<cdot> k \<in> J \<inter> K"
  proof
    show "j \<cdot> k \<in> J" using kR j by (simp add: J.Ideal)
    show "j \<cdot> k \<in> K" using jR k by (simp add: K.Ideal)
  qed
  show ?thesis using m_in_I jk_in_JK eq by blast
qed

text \<open>The reduction step underlying Chinese-Remainder surjectivity, phrased for a single ideal (where
  subtraction notation is unambiguous): if @{term "i + j = \<one>"} with @{term "i \<in> I"}, then the element
  @{term "x \<cdot> j + y \<cdot> i"} has the same coset as @{term x} modulo @{term I} (because @{term "x \<cdot> j \<equiv> x"}
  and @{term "y \<cdot> i \<equiv> \<zero>"} modulo @{term I}).\<close>
lemma coset_comaximal:
  assumes x: "x \<in> R" and y: "y \<in> R" and i: "i \<in> I" and jR: "j \<in> R" and ij: "i + j = \<one>"
  shows "coset (x \<cdot> j + y \<cdot> i) = coset x"
proof -
  have iR: "i \<in> R" using i additive.subset by blast
  have sumR: "x \<cdot> j + y \<cdot> i \<in> R" using x y iR jR by simp
  \<comment> \<open>@{term x} decomposes as @{term "x \<cdot> i + x \<cdot> j"} via @{term "i + j = \<one>"}.\<close>
  have xdecomp: "x = x \<cdot> i + x \<cdot> j"
  proof -
    have "x = x \<cdot> (i + j)" using ij x by simp
    also have "\<dots> = x \<cdot> i + x \<cdot> j" using x iR jR by (simp add: distributive)
    finally show ?thesis .
  qed
  \<comment> \<open>An abelian-group rearrangement: @{term "(q + p) - (s + q) = p - s"} for @{term q}, @{term p},
     @{term s} in @{term R}.\<close>
  \<comment> \<open>The difference @{term "(x \<cdot> j + y \<cdot> i) - x"} equals @{term "(y - x) \<cdot> i \<in> I"}.\<close>
  have "(x \<cdot> j + y \<cdot> i) - x = (x \<cdot> j + y \<cdot> i) - (x \<cdot> i + x \<cdot> j)" using xdecomp by simp
  also have "\<dots> = y \<cdot> i - x \<cdot> i"
    using additive.add_diff_cancel_mid[of "x \<cdot> j" "y \<cdot> i" "x \<cdot> i"] x y iR jR by simp
  also have "\<dots> = (y - x) \<cdot> i" using x y iR by (simp add: distributive left_minus)
  finally have eq: "(x \<cdot> j + y \<cdot> i) - x = (y - x) \<cdot> i" .
  have "(y - x) \<cdot> i \<in> I" using x y i by (simp add: Ideal)
  then have "(x \<cdot> j + y \<cdot> i) - x \<in> I" using eq by simp
  then show ?thesis using coset_eq_iff[OF sumR x] by simp
qed

end


subsection \<open>Two comaximal ideals\<close>

text \<open>The Chinese Remainder Theorem setting: a commutative ring @{term R} with two ideals @{term I},
  @{term J} that are \<^emph>\<open>comaximal\<close> (\<open>I + J = R\<close>).  We package these in a locale, giving each ideal its
  own quotient-ring interface (\<open>I.\<close> and \<open>J.\<close>).\<close>

locale comaximal_ideals =
  I: quotient_ring I R "(+)" "(\<cdot>)" \<zero> \<one> + J: quotient_ring J R "(+)" "(\<cdot>)" \<zero> \<one>
  for I and J and R and addition (infixl \<open>+\<close> 65) and multiplication (infixl \<open>\<cdot>\<close> 70) and zero (\<open>\<zero>\<close>) and unit (\<open>\<one>\<close>) +
  assumes comm: "\<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a"
    and comaximal: "\<exists>i\<in>I. \<exists>j\<in>J. i + j = \<one>"
begin

text \<open>Both ideals live in a commutative ring; expose the commutative-ring structure and the
  \<open>ideal_in_comm_ring\<close> facts for each.\<close>
sublocale I: ideal_in_comm_ring I R "(+)" "(\<cdot>)" \<zero> \<one>
  by unfold_locales (rule comm)

sublocale J: ideal_in_comm_ring J R "(+)" "(\<cdot>)" \<zero> \<one>
  by unfold_locales (rule comm)

text \<open>The product ring \<open>(R/I) \<times> (R/J)\<close> of the two quotient rings.\<close>
sublocale prod: ring_pair
  "R / I.Ring_Congruence" "I.additive.quotient_composition" "I.multiplicative.quotient_composition"
    "I.additive.Class \<zero>" "I.additive.Class \<one>"
  "R / J.Ring_Congruence" "J.additive.quotient_composition" "J.multiplicative.quotient_composition"
    "J.additive.Class \<zero>" "J.additive.Class \<one>"
  by unfold_locales

text \<open>The canonical projection \<open>a \<mapsto> (I + a, J + a)\<close> into the product of the two quotients.\<close>
definition canon :: "'a \<Rightarrow> 'a set \<times> 'a set"
  where "canon = restrict (\<lambda>a. (I.coset a, J.coset a)) R"

lemma canon_apply [simp]: "a \<in> R \<Longrightarrow> canon a = (I.coset a, J.coset a)"
  by (simp add: canon_def)

lemma coset_I_in_carrier: "a \<in> R \<Longrightarrow> I.coset a \<in> R / I.Ring_Congruence"
  using I.coset_in_quotient_set by (simp add: I.quotient_set_def)

lemma coset_J_in_carrier: "a \<in> R \<Longrightarrow> J.coset a \<in> R / J.Ring_Congruence"
  using J.coset_in_quotient_set by (simp add: J.quotient_set_def)

text \<open>The canonical projection is a ring homomorphism into the product ring.\<close>
theorem canon_hom:
  "ring_homomorphism canon R (+) (\<cdot>) \<zero> \<one> prod.Bcarrier (prod.Badd) (prod.Bmult) prod.Bzero prod.Bone"
proof (unfold_locales)
  show "canon \<in> R \<rightarrow>\<^sub>E prod.Bcarrier"
  proof (rule PiE_I)
    fix a assume "a \<in> R"
    then show "canon a \<in> prod.Bcarrier"
      by (simp add: prod.Bcarrier_def coset_I_in_carrier coset_J_in_carrier)
  next
    fix a assume "a \<notin> R" then show "canon a = undefined" by (simp add: canon_def)
  qed
next
  fix a b assume ab: "a \<in> R" "b \<in> R"
  have "I.coset (a + b) = I.additive.quotient_composition (I.coset a) (I.coset b)"
    using ab by (simp add: I.coset_def I.additive.Class_commutes_with_composition)
  moreover have "J.coset (a + b) = J.additive.quotient_composition (J.coset a) (J.coset b)"
    using ab by (simp add: J.coset_def J.additive.Class_commutes_with_composition)
  ultimately show "canon (a + b) = prod.Badd (canon a) (canon b)"
    using ab by (simp add: prod.Badd_def)
next
  fix a b assume ab: "a \<in> R" "b \<in> R"
  have "I.coset (a \<cdot> b) = I.multiplicative.quotient_composition (I.coset a) (I.coset b)"
    using ab by (simp add: I.coset_def I.quot_mult_Class)
  moreover have "J.coset (a \<cdot> b) = J.multiplicative.quotient_composition (J.coset a) (J.coset b)"
    using ab by (simp add: J.coset_def J.quot_mult_Class)
  ultimately show "canon (a \<cdot> b) = prod.Bmult (canon a) (canon b)"
    using ab by (simp add: prod.Bmult_def)
next
  show "canon \<zero> = prod.Bzero"
    by (simp add: prod.Bzero_def I.coset_def J.coset_def)
next
  show "canon \<one> = prod.Bone"
    by (simp add: prod.Bone_def I.coset_def J.coset_def)
qed

interpretation canon: ring_homomorphism canon R "(+)" "(\<cdot>)" \<zero> \<one>
  prod.Bcarrier "prod.Badd" "prod.Bmult" prod.Bzero prod.Bone
  by (rule canon_hom)

text \<open>The kernel of the canonical projection is @{term "I \<inter> J"}: an element maps to zero exactly
  when both its cosets vanish, i.e.\ it lies in both ideals.\<close>
theorem canon_kernel: "canon.additive.Ker = I \<inter> J"
proof (rule set_eqI)
  fix a
  have "a \<in> canon.additive.Ker \<longleftrightarrow> a \<in> R \<and> canon a = prod.Bzero"
    unfolding canon.additive.Ker_def by auto
  also have "\<dots> \<longleftrightarrow> a \<in> R \<and> I.coset a = I.coset \<zero> \<and> J.coset a = J.coset \<zero>"
  proof (cases "a \<in> R")
    case True
    then show ?thesis by (simp add: prod.Bzero_def I.coset_def J.coset_def)
  qed simp
  also have "\<dots> \<longleftrightarrow> a \<in> R \<and> a \<in> I \<and> a \<in> J"
    by (simp add: I.coset_def J.coset_def I.Class_eq_zero_iff J.Class_eq_zero_iff cong: conj_cong)
  also have "\<dots> \<longleftrightarrow> a \<in> I \<inter> J"
    using I.additive.subset by blast
  finally show "a \<in> canon.additive.Ker \<longleftrightarrow> a \<in> I \<inter> J" .
qed

text \<open>Comaximality makes the canonical projection surjective: given target cosets of @{term x} and
  @{term y}, the element @{term "x \<cdot> j + y \<cdot> i"} (where @{term "i + j = \<one>"}, @{term "i \<in> I"},
  @{term "j \<in> J"}) reduces to @{term x} mod @{term I} and to @{term y} mod @{term J}.\<close>
theorem canon_surjective: "canon ` R = prod.Bcarrier"
proof (rule set_eqI)
  fix z
  show "z \<in> canon ` R \<longleftrightarrow> z \<in> prod.Bcarrier"
  proof
    assume "z \<in> canon ` R"
    then show "z \<in> prod.Bcarrier" using canon.graph by blast
  next
    assume "z \<in> prod.Bcarrier"
    then obtain X Y where zXY: "z = (X, Y)" and X: "X \<in> R / I.Ring_Congruence"
      and Y: "Y \<in> R / J.Ring_Congruence" by (auto simp: prod.Bcarrier_def)
    obtain x where x: "x \<in> R" and Xx: "X = I.coset x"
      using X I.quotient_set_repr by (metis I.quotient_set_def)
    obtain y where y: "y \<in> R" and Yy: "Y = J.coset y"
      using Y J.quotient_set_repr by (metis J.quotient_set_def)
    \<comment> \<open>The comaximality witness @{term "i + j = \<one>"}.\<close>
    obtain i j where i: "i \<in> I" and j: "j \<in> J" and ij: "i + j = \<one>"
      using comaximal by blast
    have iR: "i \<in> R" using i I.additive.subset by blast
    have jR: "j \<in> R" using j J.additive.subset by blast
    define a where "a = x \<cdot> j + y \<cdot> i"
    have aR: "a \<in> R" unfolding a_def using x y iR jR by simp
    \<comment> \<open>Mod @{term I}: reduces to @{term x} (since @{term "i \<in> I"}, @{term "i + j = \<one>"}).\<close>
    have IX: "I.coset a = I.coset x"
      unfolding a_def by (rule I.coset_comaximal[OF x y i jR ij])
    \<comment> \<open>Mod @{term J}: symmetrically reduces to @{term y}, using @{term "j + i = \<one>"}.\<close>
    have ji: "j + i = \<one>" using ij iR jR by (simp add: I.additive.commutative)
    have "J.coset (y \<cdot> i + x \<cdot> j) = J.coset y"
      by (rule J.coset_comaximal[OF y x j iR ji])
    moreover have "y \<cdot> i + x \<cdot> j = a"
      unfolding a_def using x y iR jR by (simp add: I.additive.commutative)
    ultimately have JY: "J.coset a = J.coset y" by simp
    have "canon a = (X, Y)" using aR IX JY Xx Yy by simp
    then show "z \<in> canon ` R" using aR zXY by auto
  qed
qed


subsection \<open>The Chinese Remainder Theorem\<close>

text \<open>Feeding the canonical projection to the fundamental theorem of ring homomorphisms yields
  @{term "R / Ker canon"} isomorphic to the image, which surjectivity identifies with the whole
  product ring, and the kernel is @{term "I \<inter> J"}.\<close>

interpretation canon: ring_homomorphism_fundamental canon R "(+)" "(\<cdot>)" \<zero> \<one>
  prod.Bcarrier "prod.Badd" "prod.Bmult" prod.Bzero prod.Bone
  by unfold_locales

text \<open>The induced map \<open>\<eta>\<bar>\<close> is an isomorphism from \<open>R / Ker\<close> onto the image; surjectivity identifies the
  image with the whole product ring.  With @{thm [source] canon_kernel} this is
  \<open>R / (I \<inter> J) \<cong> (R / I) \<times> (R / J)\<close>.\<close>
theorem chinese_remainder:
  "(R / (subgroup_of_additive_group_of_ring.Ring_Congruence (I \<inter> J) R (+) \<zero>),
      canon.kernel.additive.quotient_composition, canon.kernel.multiplicative.quotient_composition,
      canon.kernel.additive.Class \<zero>, canon.kernel.additive.Class \<one>)
   \<cong>\<^sub>R (prod.Bcarrier, prod.Badd, prod.Bmult, prod.Bzero, prod.Bone)"
proof -
  have ker: "canon.additive.Ker = I \<inter> J" by (rule canon_kernel)
  \<comment> \<open>The induced map \<open>\<eta>\<bar>\<close> is a ring isomorphism from \<open>R / Ker\<close> onto the whole product ring: it is a
     ring homomorphism (indeed the monomorphism supplied by @{locale ring_homomorphism_fundamental}),
     and it is bijective --- injective as that monomorphism, surjective because \<open>canon\<close> is.\<close>
  have "ring_isomorphism canon.additive.induced
      (R / (subgroup_of_additive_group_of_ring.Ring_Congruence (I \<inter> J) R (+) \<zero>))
      canon.kernel.additive.quotient_composition canon.kernel.multiplicative.quotient_composition
      (canon.kernel.additive.Class \<zero>) (canon.kernel.additive.Class \<one>)
      prod.Bcarrier prod.Badd prod.Bmult prod.Bzero prod.Bone"
    unfolding ker[symmetric]
  proof (rule ring_isomorphism.intro)
    show "ring_homomorphism canon.additive.induced
        (R / (subgroup_of_additive_group_of_ring.Ring_Congruence canon.additive.Ker R (+) \<zero>))
        canon.kernel.additive.quotient_composition canon.kernel.multiplicative.quotient_composition
        (canon.kernel.additive.Class \<zero>) (canon.kernel.additive.Class \<one>)
        prod.Bcarrier prod.Badd prod.Bmult prod.Bzero prod.Bone"
      by (rule canon.induced.ring_homomorphism_axioms)
    show "bijective_map canon.additive.induced
        (R / (subgroup_of_additive_group_of_ring.Ring_Congruence canon.additive.Ker R (+) \<zero>))
        prod.Bcarrier"
    proof
      show "bij_betw canon.additive.induced
          (R / (subgroup_of_additive_group_of_ring.Ring_Congruence canon.additive.Ker R (+) \<zero>))
          prod.Bcarrier"
        using canon.additive.induced_image canon.additive.induced_inj_on canon_surjective
        by (simp add: bij_betw_def)
    qed
  qed
  then show ?thesis
    by (auto simp: isomorphic_as_rings_def)
qed

end


text \<open>Transfer of the ring structure along operations that agree on the carrier.  If \<open>R\<close> is a ring
  under \<open>(+)\<close>, \<open>(\<cdot>)\<close> and the alternative operations \<open>(\<oplus>)\<close>, \<open>(\<otimes>)\<close> agree with them on all pairs of
  carrier elements, then \<open>R\<close> is also a ring under \<open>(\<oplus>)\<close>, \<open>(\<otimes>)\<close>.\<close>
lemma Ring_cong_on_carrier:
  fixes R and addition (infixl \<open>+\<close> 65) and multiplication (infixl \<open>\<cdot>\<close> 70)
    and addition' (infixl \<open>\<oplus>\<close> 65) and multiplication' (infixl \<open>\<otimes>\<close> 70) and zero (\<open>\<zero>\<close>) and unit (\<open>\<one>\<close>)
  assumes ring: "Ring R (+) (\<cdot>) \<zero> \<one>"
    and add_eq: "\<And>a b. \<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> a \<oplus> b = a + b"
    and mult_eq: "\<And>a b. \<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> a \<otimes> b = a \<cdot> b"
  shows "Ring R (\<oplus>) (\<otimes>) \<zero> \<one>"
proof -
  interpret R: Ring R "(+)" "(\<cdot>)" \<zero> \<one> by (rule ring)
  show ?thesis
  proof (rule Ring.intro)
    show "Abelian_Group R (\<oplus>) \<zero>"
    proof (rule Abelian_Group.intro)
      show "Group R (\<oplus>) \<zero>"
      proof (rule GroupI)
        show "\<And>a b. \<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> a \<oplus> b \<in> R" by (simp add: add_eq)
        show "\<zero> \<in> R" by simp
        show "\<And>a b c. \<lbrakk> a \<in> R; b \<in> R; c \<in> R \<rbrakk> \<Longrightarrow> (a \<oplus> b) \<oplus> c = a \<oplus> (b \<oplus> c)"
          by (simp add: add_eq R.additive.associative)
        show "\<And>a. a \<in> R \<Longrightarrow> \<zero> \<oplus> a = a" by (simp add: add_eq)
        show "\<And>a. a \<in> R \<Longrightarrow> a \<oplus> \<zero> = a" by (simp add: add_eq)
        fix u assume u: "u \<in> R"
        have "u \<oplus> R.additive.inverse u = \<zero> \<and> R.additive.inverse u \<oplus> u = \<zero>"
          using u by (simp add: add_eq)
        then show "\<exists>v\<in>R. u \<oplus> v = \<zero> \<and> v \<oplus> u = \<zero>" using u by blast
      qed
      show "commutative_monoid R (\<oplus>) \<zero>"
      proof (rule commutative_monoid.intro)
        show "Monoid R (\<oplus>) \<zero>"
          by unfold_locales (auto simp: add_eq R.additive.associative)
        show "commutative_monoid_axioms R (\<oplus>)"
          by unfold_locales (simp add: add_eq R.additive.commutative)
      qed
    qed
    show "Monoid R (\<otimes>) \<one>"
      by unfold_locales (auto simp: mult_eq R.multiplicative.associative)
    show "Ring_axioms R (\<oplus>) (\<otimes>)"
    proof
      fix a b c assume "a \<in> R" "b \<in> R" "c \<in> R"
      then show "a \<otimes> (b \<oplus> c) = a \<otimes> b \<oplus> (a \<otimes> c)"
        by (simp add: add_eq mult_eq R.distributive)
    next
      fix a b c assume "a \<in> R" "b \<in> R" "c \<in> R"
      then show "(b \<oplus> c) \<otimes> a = b \<otimes> a \<oplus> (c \<otimes> a)"
        by (simp add: add_eq mult_eq R.distributive)
    qed
  qed
qed


section \<open>The n-ary Chinese Remainder Theorem\<close>

text \<open>Generalise the binary CRT to a finite family of pairwise-comaximal ideals:
  @{text "R / (\<Inter>i\<in>S. J i) \<cong>\<^sub>R \<Prod>i\<in>S. R / J i"}.  The proof proceeds by induction on the finite
  index set, reducing (n+1) ideals to the binary theorem via the lemma that comaximality is
  preserved under intersection.\<close>

subsection \<open>Pairwise-comaximal ideals\<close>

locale pairwise_comaximal_ideals =
  fixes S :: "'i set"
    and J :: "'i \<Rightarrow> 'a set"
    and R :: "'a set"
    and addition (infixl \<open>+\<close> 65)
    and multiplication (infixl \<open>\<cdot>\<close> 70)
    and zero (\<open>\<zero>\<close>)
    and unit (\<open>\<one>\<close>)
  assumes fin: "finite S"
    and nonempty: "S \<noteq> {}"
    and comm: "\<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a"
    and ideals: "\<And>i. i \<in> S \<Longrightarrow> quotient_ring (J i) R (+) (\<cdot>) \<zero> \<one>"
    and pairwise: "\<And>i j. \<lbrakk> i \<in> S; j \<in> S; i \<noteq> j \<rbrakk> \<Longrightarrow> \<exists>a\<in>J i. \<exists>b\<in>J j. a + b = \<one>"
begin

sublocale Ring R "(+)" "(\<cdot>)" \<zero> \<one>
proof -
  obtain i where "i \<in> S" using nonempty by blast
  then interpret qi: quotient_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule ideals)
  show "Ring R (+) (\<cdot>) \<zero> \<one>" ..
qed

sublocale commutative_ring R "(+)" "(\<cdot>)" \<zero> \<one>
  by unfold_locales (rule comm)

text \<open>Each @{term "J i"} is an ideal in the commutative ring.\<close>
lemma Ji_ideal: "i \<in> S \<Longrightarrow> Ideal (J i) R (+) (\<cdot>) \<zero> \<one>"
proof -
  assume "i \<in> S"
  then interpret qi: quotient_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule ideals)
  show "Ideal (J i) R (+) (\<cdot>) \<zero> \<one>" ..
qed

lemma Ji_ideal_comm: "i \<in> S \<Longrightarrow> ideal_in_comm_ring (J i) R (+) (\<cdot>) \<zero> \<one>"
  by (intro ideal_in_comm_ring.intro Ji_ideal commutative_ring_axioms)

text \<open>The intersection @{term "\<Inter> (J ` T)"} over a subset @{term "T \<subseteq> S"} is again an ideal.\<close>
lemma Inter_ideal:
  assumes TS: "T \<subseteq> S" and Tne: "T \<noteq> {}"
  shows "Ideal (\<Inter> (J ` T)) R (+) (\<cdot>) \<zero> \<one>"
proof -
  have finT: "finite T" using TS fin finite_subset by blast
  show ?thesis using finT Tne TS
  proof (induction rule: finite_ne_induct)
    case (singleton x)
    then show ?case using Ji_ideal by simp
  next
    case (insert x F)
    then have xS: "x \<in> S" and FS: "F \<subseteq> S" by auto
    interpret Jx: ideal_in_comm_ring "J x" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule Ji_ideal_comm[OF xS])
    have "Ideal (\<Inter> (J ` F)) R (+) (\<cdot>) \<zero> \<one>" using insert by auto
    then have "Ideal (J x \<inter> \<Inter> (J ` F)) R (+) (\<cdot>) \<zero> \<one>"
      by (rule Jx.inter_ideal)
    then show ?case using insert by simp
  qed
qed

text \<open>Key induction step: if @{term "J i"} is comaximal with every @{term "J j"} for @{term "j \<in> T"},
  then @{term "J i"} is comaximal with @{term "\<Inter> (J ` T)"}.\<close>
lemma comaximal_with_Inter:
  assumes iS: "i \<in> S" and TS: "T \<subseteq> S" and Tne: "T \<noteq> {}" and iT: "i \<notin> T"
    and pw: "\<And>j. j \<in> T \<Longrightarrow> \<exists>a\<in>J i. \<exists>b\<in>J j. a + b = \<one>"
  shows "\<exists>a\<in>J i. \<exists>b\<in>\<Inter> (J ` T). a + b = \<one>"
proof -
  have finT: "finite T" using TS fin finite_subset by blast
  show ?thesis using finT Tne TS iT pw
  proof (induction rule: finite_ne_induct)
    case (singleton x)
    then show ?case by simp
  next
    case (insert x F)
    then have xS: "x \<in> S" and FS: "F \<subseteq> S" by auto
    have Fne: "F \<noteq> {}" using insert by simp
    have iF: "i \<notin> F" using insert.prems by simp
    have comF: "\<exists>a\<in>J i. \<exists>b\<in>\<Inter> (J ` F). a + b = \<one>"
      using insert by auto
    have comx: "\<exists>a\<in>J i. \<exists>b\<in>J x. a + b = \<one>" using insert.prems by simp
    interpret Ji: ideal_in_comm_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule Ji_ideal_comm[OF iS])
    have Jx_ideal: "Ideal (J x) R (+) (\<cdot>) \<zero> \<one>" by (rule Ji_ideal[OF xS])
    have IF_ideal: "Ideal (\<Inter> (J ` F)) R (+) (\<cdot>) \<zero> \<one>"
      by (rule Inter_ideal[OF FS Fne])
    have "\<exists>a\<in>J i. \<exists>b\<in>J x \<inter> \<Inter> (J ` F). a + b = \<one>"
      by (rule Ji.comaximal_inter[OF Jx_ideal IF_ideal comx comF])
    then show ?case using insert by simp
  qed
qed


subsection \<open>The canonical projection into the indexed product\<close>

text \<open>The quotient rings form a ring family.  The coset @{text "Ji_Class i a"} is the equivalence
  class of @{term a} modulo the ring congruence induced by @{term "J i"}.  The quotient carrier,
  operations, and constants are defined in terms of this class map.\<close>

definition Ji_Cong :: "'i \<Rightarrow> ('a \<times> 'a) set" where
  "Ji_Cong i = {(a, b). a \<in> R \<and> b \<in> R \<and> a - b \<in> J i}"

definition Ji_Class :: "'i \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "Ji_Class i a = {b \<in> R. (a, b) \<in> Ji_Cong i}"

definition quot_carrier :: "'i \<Rightarrow> 'a set set" where
  "quot_carrier i = Ji_Class i ` R"

definition quot_add :: "'i \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "quot_add i A B = (THE C. \<exists>a\<in>A. \<exists>b\<in>B. C = Ji_Class i (a + b))"

definition quot_mult :: "'i \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "quot_mult i A B = (THE C. \<exists>a\<in>A. \<exists>b\<in>B. C = Ji_Class i (a \<cdot> b))"

definition quot_zero :: "'i \<Rightarrow> 'a set" where
  "quot_zero i = Ji_Class i \<zero>"

definition quot_one :: "'i \<Rightarrow> 'a set" where
  "quot_one i = Ji_Class i \<one>"

lemma Ji_Cong_eq:
  assumes "i \<in> S"
  shows "Ji_Cong i = subgroup_of_additive_group_of_ring.Ring_Congruence (J i) R addition \<zero>"
proof -
  interpret qi: quotient_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule ideals[OF assms])
  show ?thesis
    unfolding Ji_Cong_def qi.Ring_Congruence_def by auto
qed

text \<open>Key bridge: @{const Ji_Class} agrees with the quotient-ring coset.
  The proof is by unfolding definitions within a local interpretation.\<close>
lemma Ji_Class_unfold:
  assumes "a \<in> R"
  shows "Ji_Class i a = {b \<in> R. a - b \<in> J i}"
  unfolding Ji_Class_def Ji_Cong_def using assms by auto

lemma Ji_Cong_sym:
  assumes i: "i \<in> S" and "(a, b) \<in> Ji_Cong i"
  shows "(b, a) \<in> Ji_Cong i"
proof -
  interpret qi: quotient_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule ideals[OF i])
  from assms(2) have aR: "a \<in> R" and bR: "b \<in> R" and d: "a - b \<in> J i"
    unfolding Ji_Cong_def by auto
  have "- (a - b) \<in> J i" using d qi.additive.submonoid_inverse_closed aR bR by simp
  then have "b - a \<in> J i"
    using aR bR by (simp add: additive.inverse_composition_commute additive.commutative)
  then show ?thesis using aR bR unfolding Ji_Cong_def by auto
qed

lemma Ji_Class_mem_sym:
  assumes i: "i \<in> S" and "a \<in> R" "b \<in> Ji_Class i a"
  shows "a \<in> Ji_Class i b"
proof -
  from assms(3) have bR: "b \<in> R" and ab: "(a, b) \<in> Ji_Cong i"
    unfolding Ji_Class_def by auto
  have "(b, a) \<in> Ji_Cong i" by (rule Ji_Cong_sym[OF i ab])
  then show ?thesis using assms(2) unfolding Ji_Class_def by auto
qed

lemma Ji_Class_coset_bridge:
  assumes i: "i \<in> S" and aR: "a \<in> R"
  shows "Ji_Class i a = {b \<in> R. (a, b) \<in> Ji_Cong i}"
  unfolding Ji_Class_def by auto

text \<open>Within an interpretation @{text "qi: quotient_ring (J i) R (+) (\<cdot>) \<zero> \<one>"},
  the coset @{text "qi.coset a"} equals @{term "Ji_Class i a"}.  We package this as a
  fact to use in proofs.\<close>
lemma Ji_Class_qi_coset:
  assumes i: "i \<in> S" and aR: "a \<in> R"
  shows "Ji_Class i a = {b \<in> R. a - b \<in> J i}"
  by (rule Ji_Class_unfold[OF aR])

text \<open>The coset map is well-defined modulo the congruence.\<close>
lemma Ji_Class_cong:
  assumes i: "i \<in> S" and "a \<in> R" "b \<in> R" "(a, b) \<in> Ji_Cong i"
  shows "Ji_Class i a = Ji_Class i b"
proof -
  interpret qi: quotient_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule ideals[OF i])
  have ca: "Ji_Class i a = qi.coset a" and cb: "Ji_Class i b = qi.coset b"
    using \<open>a \<in> R\<close> \<open>b \<in> R\<close> qi.additive.symmetric
    by (auto simp: Ji_Class_def Ji_Cong_eq i qi.coset_def)
  have "qi.coset a = qi.coset b"
    using assms by (simp add: qi.coset_def qi.additive.Class_equivalence
                              qi.additive_congruence Ji_Cong_eq[OF i])
  then show ?thesis using ca cb by simp
qed

lemma Ji_Class_repr:
  assumes i: "i \<in> S" and "A \<in> quot_carrier i"
  obtains a where "a \<in> R" "A = Ji_Class i a"
  using assms unfolding quot_carrier_def by auto

lemma quot_Ring:
  assumes i: "i \<in> S"
  shows "Ring (quot_carrier i) (quot_add i) (quot_mult i) (quot_zero i) (quot_one i)"
proof -
  interpret qi: quotient_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule ideals[OF i])
  have class_eq: "\<And>a. a \<in> R \<Longrightarrow> Ji_Class i a = qi.coset a"
    using qi.additive.symmetric
    by (auto simp: Ji_Class_def Ji_Cong_eq i qi.coset_def)
  have carrier: "quot_carrier i = qi.quotient_set"
    unfolding quot_carrier_def qi.quotient_set_def qi.additive.Partition_def qi.coset_def
    using class_eq qi.coset_def by (auto simp: image_def)
  have qzero: "quot_zero i = qi.coset \<zero>" by (simp add: quot_zero_def class_eq)
  have qone: "quot_one i = qi.coset \<one>" by (simp add: quot_one_def class_eq)
  \<comment> \<open>The quotient operations agree with the locale's.  Each element of the carrier is a coset,
     and the operations THE-select the unique class of any representative pair.\<close>
  have qadd: "quot_add i A B = qi.additive.quotient_composition A B"
    if AB: "A \<in> quot_carrier i" "B \<in> quot_carrier i" for A B
  proof -
    obtain a b where aR: "a \<in> R" "A = Ji_Class i a" and bR: "b \<in> R" "B = Ji_Class i b"
      using AB unfolding quot_carrier_def by auto
    have Aca: "A = qi.coset a" using aR class_eq by simp
    have Bcb: "B = qi.coset b" using bR class_eq by simp
    have rhs: "qi.additive.quotient_composition A B = qi.coset (a + b)"
      using aR(1) bR(1) Aca Bcb by (simp add: qi.coset_def qi.additive.Class_commutes_with_composition)
    have aA: "a \<in> A" using aR(1,2) unfolding Ji_Class_def Ji_Cong_def by auto
    moreover have bB: "b \<in> B" using bR(1,2) unfolding Ji_Class_def Ji_Cong_def by auto
    moreover have "\<And>a' b'. a' \<in> A \<Longrightarrow> b' \<in> B \<Longrightarrow> Ji_Class i (a' + b') = Ji_Class i (a + b)"
    proof -
      fix a' b' assume "a' \<in> A" "b' \<in> B"
      then have a'R: "a' \<in> R" and b'R: "b' \<in> R"
        using AB unfolding quot_carrier_def Ji_Class_def by auto
      have "qi.coset a' = qi.coset a"
        using \<open>a' \<in> A\<close> Aca a'R aR(1) qi.coset_def qi.additive.Class_equivalence qi.additive_congruence
        by auto
      moreover have "qi.coset b' = qi.coset b"
        using \<open>b' \<in> B\<close> Bcb b'R bR(1) qi.coset_def qi.additive.Class_equivalence qi.additive_congruence
        by auto
      ultimately have "qi.coset (a' + b') = qi.coset (a + b)"
      proof -
        assume eq_a: "qi.coset a' = qi.coset a" and eq_b: "qi.coset b' = qi.coset b"
        have "qi.coset (a' + b') = qi.additive.quotient_composition (qi.coset a') (qi.coset b')"
          using a'R b'R by (simp add: qi.coset_def qi.additive.Class_commutes_with_composition)
        also have "\<dots> = qi.additive.quotient_composition (qi.coset a) (qi.coset b)"
          by (simp add: eq_a eq_b)
        also have "\<dots> = qi.coset (a + b)"
          using aR(1) bR(1) by (simp add: qi.coset_def qi.additive.Class_commutes_with_composition)
        finally show "qi.coset (a' + b') = qi.coset (a + b)" .
      qed
      then show "Ji_Class i (a' + b') = Ji_Class i (a + b)"
        using class_eq a'R b'R aR(1) bR(1) by simp
    qed
    ultimately have "quot_add i A B = Ji_Class i (a + b)"
      unfolding quot_add_def by (intro the_equality; blast)
    also have "\<dots> = qi.coset (a + b)" using class_eq aR(1) bR(1) by simp
    finally show ?thesis using rhs by simp
  qed
  have qmult: "quot_mult i A B = qi.multiplicative.quotient_composition A B"
    if AB: "A \<in> quot_carrier i" "B \<in> quot_carrier i" for A B
  proof -
    interpret qi_comm: ideal_in_comm_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule Ji_ideal_comm[OF i])
    obtain a b where aR: "a \<in> R" "A = Ji_Class i a" and bR: "b \<in> R" "B = Ji_Class i b"
      using AB unfolding quot_carrier_def by auto
    have Aca: "A = qi.coset a" using aR class_eq by simp
    have Bcb: "B = qi.coset b" using bR class_eq by simp
    have rhs: "qi.multiplicative.quotient_composition A B = qi.coset (a \<cdot> b)"
      using aR(1) bR(1) Aca Bcb by (simp add: qi.coset_def qi_comm.quot_mult_Class)
    have "a \<in> A" using aR(1,2) unfolding Ji_Class_def Ji_Cong_def by auto
    moreover have "b \<in> B" using bR(1,2) unfolding Ji_Class_def Ji_Cong_def by auto
    moreover have "\<And>a' b'. a' \<in> A \<Longrightarrow> b' \<in> B \<Longrightarrow> Ji_Class i (a' \<cdot> b') = Ji_Class i (a \<cdot> b)"
    proof -
      fix a' b' assume "a' \<in> A" "b' \<in> B"
      then have a'R: "a' \<in> R" and b'R: "b' \<in> R"
        using AB unfolding quot_carrier_def Ji_Class_def by auto
      have "(a, a') \<in> Ji_Cong i" using \<open>a' \<in> A\<close> aR(2) unfolding Ji_Class_def by auto
      then have ca: "(a', a) \<in> qi.Ring_Congruence" using Ji_Cong_sym[OF i] Ji_Cong_eq[OF i] by simp
      have "(b, b') \<in> Ji_Cong i" using \<open>b' \<in> B\<close> bR(2) unfolding Ji_Class_def by auto
      then have cb: "(b', b) \<in> qi.Ring_Congruence" using Ji_Cong_sym[OF i] Ji_Cong_eq[OF i] by simp
      have "(a' \<cdot> b', a \<cdot> b) \<in> qi.Ring_Congruence"
        using ca cb by (rule qi.multiplicative_congruence)
      then have "(a' \<cdot> b', a \<cdot> b) \<in> Ji_Cong i" using Ji_Cong_eq[OF i] by simp
      then show "Ji_Class i (a' \<cdot> b') = Ji_Class i (a \<cdot> b)"
        using Ji_Class_cong[OF i] a'R b'R aR(1) bR(1) by simp
    qed
    ultimately have "quot_mult i A B = Ji_Class i (a \<cdot> b)"
      unfolding quot_mult_def by (intro the_equality; blast)
    also have "\<dots> = qi.coset (a \<cdot> b)" using class_eq aR(1) bR(1) by simp
    finally show ?thesis using rhs by simp
  qed
  \<comment> \<open>Transfer the Ring structure from @{term qi.quotient_set} to our definitional carrier.\<close>
  have "Ring (quot_carrier i) qi.additive.quotient_composition qi.multiplicative.quotient_composition
             (quot_zero i) (quot_one i)"
    unfolding carrier qzero qone qi.quotient_set_def qi.coset_def by unfold_locales
  then show ?thesis
    using qadd qmult by (rule Ring_cong_on_carrier) auto
qed

interpretation prod: ring_family S quot_carrier quot_add quot_mult quot_zero quot_one
  by (rule ring_family.intro) (rule quot_Ring)

text \<open>The coset map for each component — directly uses @{const Ji_Class}.\<close>
definition ncoset :: "'i \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "ncoset i a = Ji_Class i a"

lemma ncoset_in_carrier:
  assumes "i \<in> S" "a \<in> R"
  shows "ncoset i a \<in> quot_carrier i"
  unfolding ncoset_def quot_carrier_def using assms(2) by auto

text \<open>The canonical map \<open>a \<mapsto> (\<lambda>i\<in>S. Ji_Class i a)\<close> into the indexed product.\<close>
definition ncanon :: "'a \<Rightarrow> ('i \<Rightarrow> 'a set)" where
  "ncanon = restrict (\<lambda>a. \<lambda>i\<in>S. ncoset i a) R"

lemma ncanon_apply:
  assumes "a \<in> R" "i \<in> S"
  shows "ncanon a i = ncoset i a"
  using assms by (simp add: ncanon_def)

lemma ncanon_closed:
  assumes "a \<in> R"
  shows "ncanon a \<in> prod.Pcarrier"
proof (rule prod.Pcarrier_memI)
  fix i assume i: "i \<in> S"
  show "ncanon a i \<in> quot_carrier i"
    using assms i by (simp add: ncanon_apply ncoset_in_carrier)
next
  show "ncanon a \<in> extensional S" using assms by (simp add: ncanon_def)
qed

lemma ncanon_outside: "a \<notin> R \<Longrightarrow> ncanon a = undefined"
  by (simp add: ncanon_def)

text \<open>The canonical map is a ring homomorphism.\<close>
theorem ncanon_hom:
  "ring_homomorphism ncanon R (+) (\<cdot>) \<zero> \<one>
     prod.Pcarrier prod.Padd prod.Pmult prod.Pzero prod.Pone"
proof unfold_locales
  show "ncanon \<in> R \<rightarrow>\<^sub>E prod.Pcarrier"
  proof (rule PiE_I)
    fix a assume "a \<in> R" then show "ncanon a \<in> prod.Pcarrier" by (rule ncanon_closed)
  next
    fix a assume "a \<notin> R" then show "ncanon a = undefined" by (rule ncanon_outside)
  qed
next
  fix a b assume ab: "a \<in> R" "b \<in> R"
  show "ncanon (a + b) = prod.Padd (ncanon a) (ncanon b)"
  proof (rule prod.Pcarrier_eqI)
    show "ncanon (a + b) \<in> prod.Pcarrier" using ab by (simp add: ncanon_closed)
    show "prod.Padd (ncanon a) (ncanon b) \<in> prod.Pcarrier"
      using ab by (simp add: ncanon_closed)
  next
    fix i assume i: "i \<in> S"
    interpret qi: quotient_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule ideals[OF i])
    have lhs: "ncanon (a + b) i = Ji_Class i (a + b)"
      using ab i by (simp add: ncanon_apply ncoset_def)
    have rhs: "prod.Padd (ncanon a) (ncanon b) i =
               quot_add i (Ji_Class i a) (Ji_Class i b)"
      using ab i by (simp add: ncanon_apply prod.Padd_apply ncoset_def)
    also have "\<dots> = Ji_Class i (a + b)"
      unfolding quot_add_def
    proof (rule the_equality)
      show "\<exists>a'\<in>Ji_Class i a. \<exists>b'\<in>Ji_Class i b. Ji_Class i (a + b) = Ji_Class i (a' + b')"
      proof (intro bexI)
        show "a \<in> Ji_Class i a" using ab(1) unfolding Ji_Class_def Ji_Cong_def by auto
        show "b \<in> Ji_Class i b" using ab(2) unfolding Ji_Class_def Ji_Cong_def by auto
      qed simp
    next
      fix C assume "\<exists>a'\<in>Ji_Class i a. \<exists>b'\<in>Ji_Class i b. C = Ji_Class i (a' + b')"
      then obtain a' b' where a'A: "a' \<in> Ji_Class i a" and b'B: "b' \<in> Ji_Class i b"
        and Ceq: "C = Ji_Class i (a' + b')" by auto
      have a'R: "a' \<in> R" using a'A unfolding Ji_Class_def by auto
      have b'R: "b' \<in> R" using b'B unfolding Ji_Class_def by auto
      have ca: "(a', a) \<in> qi.Ring_Congruence"
      proof -
        have d: "a - a' \<in> J i" using a'A ab(1) unfolding Ji_Class_def Ji_Cong_def by auto
        have dR: "a - a' \<in> R" using ab(1) a'R by simp
        have "a' - a = - (a - a')"
          using ab(1) a'R by (simp add: additive.inverse_composition_commute additive.commutative)
        also have "- (a - a') \<in> J i" using d dR qi.additive.submonoid_inverse_closed by simp
        finally have "a' - a \<in> J i" .
        then show ?thesis using a'R ab(1) unfolding qi.Ring_Congruence_def by auto
      qed
      have cb: "(b', b) \<in> qi.Ring_Congruence"
      proof -
        have d: "b - b' \<in> J i" using b'B ab(2) unfolding Ji_Class_def Ji_Cong_def by auto
        have dR: "b - b' \<in> R" using ab(2) b'R by simp
        have "b' - b = - (b - b')"
          using ab(2) b'R by (simp add: additive.inverse_composition_commute additive.commutative)
        also have "- (b - b') \<in> J i" using d dR qi.additive.submonoid_inverse_closed by simp
        finally have "b' - b \<in> J i" .
        then show ?thesis using b'R ab(2) unfolding qi.Ring_Congruence_def by auto
      qed
      have "(a' + b', a + b) \<in> qi.Ring_Congruence"
        using qi.additive.cong[simplified qi.additive_congruence, OF ca cb] .
      then have "(a' + b', a + b) \<in> Ji_Cong i" using Ji_Cong_eq[OF i] by simp
      then have "Ji_Class i (a' + b') = Ji_Class i (a + b)"
        using a'R b'R ab(1) ab(2) by (intro Ji_Class_cong[OF i]) auto
      then show "C = Ji_Class i (a + b)" using Ceq by simp
    qed
    finally show "ncanon (a + b) i = prod.Padd (ncanon a) (ncanon b) i"
      using lhs by simp
  qed
next
  fix a b assume ab: "a \<in> R" "b \<in> R"
  show "ncanon (a \<cdot> b) = prod.Pmult (ncanon a) (ncanon b)"
  proof (rule prod.Pcarrier_eqI)
    show "ncanon (a \<cdot> b) \<in> prod.Pcarrier" using ab by (simp add: ncanon_closed)
    show "prod.Pmult (ncanon a) (ncanon b) \<in> prod.Pcarrier"
      using ab by (simp add: ncanon_closed)
  next
    fix i assume i: "i \<in> S"
    interpret qi: quotient_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule ideals[OF i])
    have lhs: "ncanon (a \<cdot> b) i = Ji_Class i (a \<cdot> b)"
      using ab i by (simp add: ncanon_apply ncoset_def)
    have rhs: "prod.Pmult (ncanon a) (ncanon b) i =
               quot_mult i (Ji_Class i a) (Ji_Class i b)"
      using ab i by (simp add: ncanon_apply prod.Pmult_apply ncoset_def)
    also have "\<dots> = Ji_Class i (a \<cdot> b)"
      unfolding quot_mult_def
    proof (rule the_equality)
      show "\<exists>a'\<in>Ji_Class i a. \<exists>b'\<in>Ji_Class i b. Ji_Class i (a \<cdot> b) = Ji_Class i (a' \<cdot> b')"
      proof (intro bexI)
        show "a \<in> Ji_Class i a" using ab(1) unfolding Ji_Class_def Ji_Cong_def by auto
        show "b \<in> Ji_Class i b" using ab(2) unfolding Ji_Class_def Ji_Cong_def by auto
      qed simp
    next
      fix C assume "\<exists>a'\<in>Ji_Class i a. \<exists>b'\<in>Ji_Class i b. C = Ji_Class i (a' \<cdot> b')"
      then obtain a' b' where a'A: "a' \<in> Ji_Class i a" and b'B: "b' \<in> Ji_Class i b"
        and Ceq: "C = Ji_Class i (a' \<cdot> b')" by auto
      have a'R: "a' \<in> R" using a'A unfolding Ji_Class_def by auto
      have b'R: "b' \<in> R" using b'B unfolding Ji_Class_def by auto
      have ca: "(a', a) \<in> qi.Ring_Congruence"
      proof -
        have "a - a' \<in> J i" using a'A ab(1) unfolding Ji_Class_def Ji_Cong_def by auto
        then have "- (a - a') \<in> J i"
          using qi.additive.submonoid_inverse_closed ab(1) a'R by simp
        then have "a' - a \<in> J i"
          using ab(1) a'R by (simp add: additive.inverse_composition_commute additive.commutative)
        then show ?thesis using a'R ab(1) unfolding qi.Ring_Congruence_def by auto
      qed
      have cb: "(b', b) \<in> qi.Ring_Congruence"
      proof -
        have "b - b' \<in> J i" using b'B ab(2) unfolding Ji_Class_def Ji_Cong_def by auto
        then have "- (b - b') \<in> J i"
          using qi.additive.submonoid_inverse_closed ab(2) b'R by simp
        then have "b' - b \<in> J i"
          using ab(2) b'R by (simp add: additive.inverse_composition_commute additive.commutative)
        then show ?thesis using b'R ab(2) unfolding qi.Ring_Congruence_def by auto
      qed
      have "(a' \<cdot> b', a \<cdot> b) \<in> qi.Ring_Congruence"
        using ca cb by (rule qi.multiplicative_congruence)
      then have "(a' \<cdot> b', a \<cdot> b) \<in> Ji_Cong i" using Ji_Cong_eq[OF i] by simp
      then have "Ji_Class i (a' \<cdot> b') = Ji_Class i (a \<cdot> b)"
        using a'R b'R ab(1) ab(2) by (intro Ji_Class_cong[OF i]) auto
      then show "C = Ji_Class i (a \<cdot> b)" using Ceq by simp
    qed
    finally show "ncanon (a \<cdot> b) i = prod.Pmult (ncanon a) (ncanon b) i"
      using lhs by simp
  qed
next
  show "ncanon \<zero> = prod.Pzero"
  proof (rule prod.Pcarrier_eqI)
    show "ncanon \<zero> \<in> prod.Pcarrier" by (simp add: ncanon_closed)
    show "prod.Pzero \<in> prod.Pcarrier" by simp
  next
    fix i assume i: "i \<in> S"
    show "ncanon \<zero> i = prod.Pzero i"
      using i by (simp add: ncanon_apply prod.Pzero_apply quot_zero_def ncoset_def)
  qed
next
  show "ncanon \<one> = prod.Pone"
  proof (rule prod.Pcarrier_eqI)
    show "ncanon \<one> \<in> prod.Pcarrier" by (simp add: ncanon_closed)
    show "prod.Pone \<in> prod.Pcarrier" by simp
  next
    fix i assume i: "i \<in> S"
    show "ncanon \<one> i = prod.Pone i"
      using i by (simp add: ncanon_apply prod.Pone_apply quot_one_def ncoset_def)
  qed
qed

interpretation ncanon: ring_homomorphism ncanon R "(+)" "(\<cdot>)" \<zero> \<one>
  prod.Pcarrier prod.Padd prod.Pmult prod.Pzero prod.Pone
  by (rule ncanon_hom)

interpretation ncanon: ring_homomorphism_fundamental ncanon R "(+)" "(\<cdot>)" \<zero> \<one>
  prod.Pcarrier prod.Padd prod.Pmult prod.Pzero prod.Pone
  by unfold_locales


subsection \<open>Kernel and surjectivity\<close>

text \<open>The kernel of the canonical projection is @{term "\<Inter> (J ` S)"}.\<close>
theorem ncanon_kernel: "ncanon.additive.Ker = \<Inter> (J ` S)"
proof (rule set_eqI)
  fix a
  show "a \<in> ncanon.additive.Ker \<longleftrightarrow> a \<in> \<Inter> (J ` S)"
  proof
    assume ker: "a \<in> ncanon.additive.Ker"
    then have aR: "a \<in> R" and eq: "ncanon a = prod.Pzero"
      unfolding ncanon.additive.Ker_def by auto
    show "a \<in> \<Inter> (J ` S)"
    proof (rule InterI)
      fix X assume "X \<in> J ` S"
      then obtain i where i: "i \<in> S" and Xi: "X = J i" by auto
      interpret qi: quotient_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule ideals[OF i])
      have "ncanon a i = prod.Pzero i" using eq by simp
      then have cls: "Ji_Class i a = Ji_Class i \<zero>"
        using i aR by (simp add: ncanon_apply prod.Pzero_apply ncoset_def quot_zero_def)
      have "a \<in> Ji_Class i a"
        using aR qi.additive.sub_unit_closed unfolding Ji_Class_def Ji_Cong_def by simp
      then have "a \<in> Ji_Class i \<zero>" using cls by simp
      then have "(\<zero>, a) \<in> Ji_Cong i" unfolding Ji_Class_def by simp
      then have "(a, \<zero>) \<in> Ji_Cong i" by (rule Ji_Cong_sym[OF i])
      then have "a - \<zero> \<in> J i" using aR unfolding Ji_Cong_def by simp
      then have "a \<in> J i" using aR by simp
      then show "a \<in> X" using Xi by simp
    qed
  next
    assume aInt: "a \<in> \<Inter> (J ` S)"
    then have aI: "\<And>i. i \<in> S \<Longrightarrow> a \<in> J i" by auto
    have aR: "a \<in> R"
    proof -
      obtain i where "i \<in> S" using nonempty by blast
      then interpret qi: quotient_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule ideals)
      show "a \<in> R" using aI[OF \<open>i \<in> S\<close>] qi.additive.subset by blast
    qed
    have "ncanon a = prod.Pzero"
    proof (rule prod.Pcarrier_eqI)
      show "ncanon a \<in> prod.Pcarrier" by (rule ncanon_closed[OF aR])
      show "prod.Pzero \<in> prod.Pcarrier" by simp
    next
      fix i assume i: "i \<in> S"
      interpret qi: quotient_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule ideals[OF i])
      have "a \<in> J i" using aI[OF i] .
      then have "a - \<zero> \<in> J i" using aR by simp
      then have cong: "(a, \<zero>) \<in> Ji_Cong i" using aR unfolding Ji_Cong_def by auto
      then have "Ji_Class i a = Ji_Class i \<zero>"
        by (intro Ji_Class_cong[OF i aR _ cong]) simp
      then show "ncanon a i = prod.Pzero i"
        using i aR by (simp add: ncanon_apply prod.Pzero_apply ncoset_def quot_zero_def)
    qed
    then show "a \<in> ncanon.additive.Ker"
      unfolding ncanon.additive.Ker_def using aR by auto
  qed
qed

text \<open>The @{const Ji_Class} version of @{thm ideal_in_comm_ring.coset_comaximal}: if
  @{term "m + n = \<one>"} with @{term "m \<in> J i"}, then @{term "x \<cdot> n + y \<cdot> m"} and @{term x} have the
  same class modulo @{term "J i"}.\<close>
lemma Ji_Class_comaximal:
  assumes i: "i \<in> S" and x: "x \<in> R" and y: "y \<in> R"
    and m: "m \<in> J i" and nR: "n \<in> R" and mn: "m + n = \<one>"
  shows "Ji_Class i (x \<cdot> n + y \<cdot> m) = Ji_Class i x"
proof -
  interpret qi: quotient_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule ideals[OF i])
  interpret Ji: ideal_in_comm_ring "J i" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule Ji_ideal_comm[OF i])
  have bridge: "\<And>c. c \<in> R \<Longrightarrow> Ji_Class i c = qi.coset c"
    using qi.additive.symmetric by (auto simp: Ji_Class_def Ji_Cong_eq i qi.coset_def)
  have mR: "m \<in> R" using m qi.additive.subset by blast
  have xnymR: "x \<cdot> n + y \<cdot> m \<in> R" using x y mR nR by simp
  have "qi.coset (x \<cdot> n + y \<cdot> m) = qi.coset x"
    using Ji.coset_comaximal[OF x y m nR mn] by (simp add: qi.coset_def)
  then show ?thesis using bridge[OF xnymR] bridge[OF x] by simp
qed

text \<open>Surjectivity of the canonical map.  We first prove, by induction on a nonempty finite
  subset \<open>T \<subseteq> S\<close>, that any family of target classes over \<open>T\<close> is realised simultaneously by a
  single element of \<open>R\<close>.  The inductive step splits off one index \<open>k\<close> and combines a solution
  over the rest via the comaximality of \<open>J k\<close> with \<open>\<Inter> (J ` F)\<close> (@{thm comaximal_with_Inter}).\<close>
lemma partial_solution:
  assumes "T \<subseteq> S" and "T \<noteq> {}" and "\<And>i. i \<in> T \<Longrightarrow> x i \<in> R"
  shows "\<exists>a\<in>R. \<forall>i\<in>T. Ji_Class i a = Ji_Class i (x i)"
proof -
  have finT: "finite T" using assms(1) fin finite_subset by blast
  have "T \<noteq> {} \<Longrightarrow> T \<subseteq> S \<Longrightarrow> (\<forall>i\<in>T. x i \<in> R) \<Longrightarrow>
        (\<exists>a\<in>R. \<forall>i\<in>T. Ji_Class i a = Ji_Class i (x i))"
    using finT
  proof (induction T rule: finite_induct)
    case empty
    then show ?case by simp
  next
    case (insert k F)
    have kS: "k \<in> S" using insert.prems by auto
    have xkR: "x k \<in> R" using insert.prems by simp
    show ?case
    proof (cases "F = {}")
      case True
      \<comment> \<open>Singleton: @{term "x k"} itself realises the single component.\<close>
      have "\<forall>i\<in>insert k F. Ji_Class i (x k) = Ji_Class i (x i)" using True by simp
      then show ?thesis using xkR by blast
    next
      case Fne: False
      have FS: "F \<subseteq> S" using insert.prems by auto
      have kF: "k \<notin> F" by (rule insert.hyps)
      \<comment> \<open>Solve over @{term F} by the induction hypothesis.\<close>
      obtain y where yR: "y \<in> R" and yF: "\<And>i. i \<in> F \<Longrightarrow> Ji_Class i y = Ji_Class i (x i)"
        using insert.IH Fne FS insert.prems(3) by auto
      \<comment> \<open>Comaximality of @{term "J k"} with @{term "\<Inter> (J ` F)"}.\<close>
      have "\<exists>m\<in>J k. \<exists>n\<in>\<Inter> (J ` F). m + n = \<one>"
      proof (rule comaximal_with_Inter[OF kS FS Fne kF])
        fix j assume j: "j \<in> F"
        then have "j \<in> S" using FS by auto
        then show "\<exists>a\<in>J k. \<exists>b\<in>J j. a + b = \<one>"
          using pairwise[OF kS] kF j by auto
      qed
      then obtain m n where m: "m \<in> J k" and n: "n \<in> \<Inter> (J ` F)" and mn: "m + n = \<one>" by blast
      have mR: "m \<in> R"
      proof -
        interpret Jk: Ideal "J k" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule Ji_ideal[OF kS])
        show ?thesis using m Jk.additive.subset by blast
      qed
      have nR: "n \<in> R"
      proof -
        obtain j where j: "j \<in> F" using Fne by blast
        then interpret Jj: Ideal "J j" R "(+)" "(\<cdot>)" \<zero> \<one> using Ji_ideal FS by blast
        have "n \<in> J j" using n j by blast
        then show ?thesis using Jj.additive.subset by blast
      qed
      define a where "a = x k \<cdot> n + y \<cdot> m"
      have aR: "a \<in> R" unfolding a_def using xkR yR mR nR by simp
      have "\<forall>i\<in>insert k F. Ji_Class i a = Ji_Class i (x i)"
      proof
        fix i assume "i \<in> insert k F"
        then consider "i = k" | "i \<in> F" by auto
        then show "Ji_Class i a = Ji_Class i (x i)"
        proof cases
          case 1
          have "Ji_Class k a = Ji_Class k (x k)"
            unfolding a_def by (rule Ji_Class_comaximal[OF kS xkR yR m nR mn])
          then show ?thesis using 1 by simp
        next
          case 2
          have iS: "i \<in> S" using 2 FS by auto
          have nJi: "n \<in> J i" using n 2 by blast
          have nm: "n + m = \<one>" using mn mR nR by (simp add: additive.commutative)
          have "Ji_Class i (y \<cdot> m + x k \<cdot> n) = Ji_Class i y"
            by (rule Ji_Class_comaximal[OF iS yR xkR nJi mR nm])
          moreover have "y \<cdot> m + x k \<cdot> n = a"
            unfolding a_def using xkR yR mR nR by (simp add: additive.commutative)
          ultimately have "Ji_Class i a = Ji_Class i y" by simp
          then show ?thesis using yF[OF 2] by simp
        qed
      qed
      then show ?thesis using aR by blast
    qed
  qed
  then show ?thesis using assms by blast
qed

theorem ncanon_surjective: "ncanon ` R = prod.Pcarrier"
proof
  show "ncanon ` R \<subseteq> prod.Pcarrier" using ncanon_closed by blast
next
  show "prod.Pcarrier \<subseteq> ncanon ` R"
  proof
    fix f assume f: "f \<in> prod.Pcarrier"
    \<comment> \<open>Choose a representative @{term "x i \<in> R"} of each component @{term "f i"}.\<close>
    have "\<forall>i\<in>S. \<exists>xi\<in>R. f i = Ji_Class i xi"
    proof
      fix i assume i: "i \<in> S"
      have "f i \<in> quot_carrier i" using f i by (simp add: prod.Pcarrier_component)
      then show "\<exists>xi\<in>R. f i = Ji_Class i xi" unfolding quot_carrier_def by auto
    qed
    then obtain x where xR: "\<And>i. i \<in> S \<Longrightarrow> x i \<in> R"
      and fx: "\<And>i. i \<in> S \<Longrightarrow> f i = Ji_Class i (x i)" by metis
    have "\<exists>a\<in>R. \<forall>i\<in>S. Ji_Class i a = Ji_Class i (x i)"
      by (rule partial_solution[OF subset_refl nonempty]) (rule xR)
    then obtain a where aR: "a \<in> R" and aeq: "\<And>i. i \<in> S \<Longrightarrow> Ji_Class i a = Ji_Class i (x i)"
      by blast
    have "ncanon a = f"
    proof (rule prod.Pcarrier_eqI)
      show "ncanon a \<in> prod.Pcarrier" by (rule ncanon_closed[OF aR])
      show "f \<in> prod.Pcarrier" by (rule f)
    next
      fix i assume i: "i \<in> S"
      have "ncanon a i = Ji_Class i a" using aR i by (simp add: ncanon_apply ncoset_def)
      also have "\<dots> = Ji_Class i (x i)" using aeq[OF i] .
      also have "\<dots> = f i" using fx[OF i] by simp
      finally show "ncanon a i = f i" .
    qed
    then show "f \<in> ncanon ` R" using aR by blast
  qed
qed


subsection \<open>The n-ary Chinese Remainder Theorem\<close>

theorem chinese_remainder_general:
  "(R / (subgroup_of_additive_group_of_ring.Ring_Congruence (\<Inter> (J ` S)) R (+) \<zero>),
      ncanon.kernel.additive.quotient_composition, ncanon.kernel.multiplicative.quotient_composition,
      ncanon.kernel.additive.Class \<zero>, ncanon.kernel.additive.Class \<one>)
   \<cong>\<^sub>R (prod.Pcarrier, prod.Padd, prod.Pmult, prod.Pzero, prod.Pone)"
proof -
  have ker: "ncanon.additive.Ker = \<Inter> (J ` S)" by (rule ncanon_kernel)
  have "ring_isomorphism ncanon.additive.induced
      (R / (subgroup_of_additive_group_of_ring.Ring_Congruence (\<Inter> (J ` S)) R (+) \<zero>))
      ncanon.kernel.additive.quotient_composition ncanon.kernel.multiplicative.quotient_composition
      (ncanon.kernel.additive.Class \<zero>) (ncanon.kernel.additive.Class \<one>)
      prod.Pcarrier prod.Padd prod.Pmult prod.Pzero prod.Pone"
    unfolding ker[symmetric]
  proof (rule ring_isomorphism.intro)
    show "ring_homomorphism ncanon.additive.induced
        (R / (subgroup_of_additive_group_of_ring.Ring_Congruence ncanon.additive.Ker R (+) \<zero>))
        ncanon.kernel.additive.quotient_composition ncanon.kernel.multiplicative.quotient_composition
        (ncanon.kernel.additive.Class \<zero>) (ncanon.kernel.additive.Class \<one>)
        prod.Pcarrier prod.Padd prod.Pmult prod.Pzero prod.Pone"
      by (rule ncanon.induced.ring_homomorphism_axioms)
    show "bijective_map ncanon.additive.induced
        (R / (subgroup_of_additive_group_of_ring.Ring_Congruence ncanon.additive.Ker R (+) \<zero>))
        prod.Pcarrier"
    proof
      show "bij_betw ncanon.additive.induced
          (R / (subgroup_of_additive_group_of_ring.Ring_Congruence ncanon.additive.Ker R (+) \<zero>))
          prod.Pcarrier"
        using ncanon.additive.induced_image ncanon.additive.induced_inj_on ncanon_surjective
        by (simp add: bij_betw_def)
    qed
  qed
  then show ?thesis
    by (auto simp: isomorphic_as_rings_def)
qed

end

end
