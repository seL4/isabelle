(*
  File:      Algebra/Algebraic_Closure_Type.thy
  Authors:   Katharina Kreuzer (TU München)
             Manuel Eberl (University of Innsbruck)

  A type definition for the algebraic closure of fields.
*)

theory Algebraic_Closure_Type
imports
  Algebraic_Closure
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Computational_Algebra.Field_as_Ring"
begin


definition (in ring_1) ring_of_type_algebra :: "'a ring"
  where "ring_of_type_algebra = \<lparr> 
    carrier = UNIV, monoid.mult = (\<lambda>x y. x * y),  
    one = 1,
    ring.zero = 0,
    add = (\<lambda> x y. x + y) \<rparr>"

lemma (in comm_ring_1) ring_from_type_algebra [intro]:
  "ring (ring_of_type_algebra :: 'a ring)"
proof -
  have "\<exists>y. x + y = 0" for x :: 'a
    using add.right_inverse by blast
  thus ?thesis
    unfolding ring_of_type_algebra_def using add.right_inverse
    by unfold_locales (auto simp:algebra_simps Units_def)
qed

lemma (in comm_ring_1) cring_from_type_algebra [intro]:
  "cring (ring_of_type_algebra :: 'a ring)"
proof -
  have "\<exists>y. x + y = 0" for x :: 'a
    using add.right_inverse by blast
  thus ?thesis
    unfolding ring_of_type_algebra_def using add.right_inverse
    by unfold_locales (auto simp:algebra_simps Units_def)
qed

lemma (in Fields.field) field_from_type_algebra [intro]:
  "field (ring_of_type_algebra :: 'a ring)"
proof -
  have "\<exists>y. x + y = 0" for x :: 'a
    using add.right_inverse by blast

  moreover have "x \<noteq> 0 \<Longrightarrow> \<exists>y. x * y = 1" for x :: 'a
    by (rule exI[of _ "inverse x"]) auto

  ultimately show ?thesis
    unfolding ring_of_type_algebra_def using add.right_inverse
    by unfold_locales (auto simp:algebra_simps Units_def)
qed



subsection \<open>Definition\<close>

typedef (overloaded) 'a :: field alg_closure =
  "carrier (field.alg_closure (ring_of_type_algebra :: 'a :: field ring))"
proof -
  define K where "K \<equiv> (ring_of_type_algebra :: 'a ring)"
  define L where "L \<equiv> field.alg_closure K"

  interpret K: field K
    unfolding K_def by rule

  interpret algebraic_closure L "range K.indexed_const"
  proof -
    have *: "carrier K = UNIV"
      by (auto simp: K_def ring_of_type_algebra_def)
    show "algebraic_closure L (range K.indexed_const)"
      unfolding * [symmetric] L_def by (rule K.alg_closureE)
  qed

  show "\<exists>x. x \<in> carrier L"
    using zero_closed by blast
qed

setup_lifting type_definition_alg_closure

instantiation alg_closure :: (field) field
begin

context
  fixes L K
  defines "K \<equiv> (ring_of_type_algebra :: 'a :: field ring)"
  defines "L \<equiv> field.alg_closure K"
begin

interpretation K: field K
  unfolding K_def by rule

interpretation algebraic_closure L "range K.indexed_const"
proof -
  have *: "carrier K = UNIV"
    by (auto simp: K_def ring_of_type_algebra_def)
  show "algebraic_closure L (range K.indexed_const)"
    unfolding * [symmetric] L_def by (rule K.alg_closureE)
qed

lift_definition zero_alg_closure :: "'a alg_closure" is "ring.zero L"
  by (fold K_def, fold L_def) (rule ring_simprules)

lift_definition one_alg_closure :: "'a alg_closure" is "monoid.one L"
  by (fold K_def, fold L_def) (rule ring_simprules)

lift_definition plus_alg_closure :: "'a alg_closure \<Rightarrow> 'a alg_closure \<Rightarrow> 'a alg_closure"
  is "ring.add L"
  by (fold K_def, fold L_def) (rule ring_simprules)

lift_definition minus_alg_closure :: "'a alg_closure \<Rightarrow> 'a alg_closure \<Rightarrow> 'a alg_closure"
  is "a_minus L"
  by (fold K_def, fold L_def) (rule ring_simprules)

lift_definition times_alg_closure :: "'a alg_closure \<Rightarrow> 'a alg_closure \<Rightarrow> 'a alg_closure"
  is "monoid.mult L"
  by (fold K_def, fold L_def) (rule ring_simprules)

lift_definition uminus_alg_closure :: "'a alg_closure \<Rightarrow> 'a alg_closure"
  is "a_inv L"
  by (fold K_def, fold L_def) (rule ring_simprules)

lift_definition inverse_alg_closure :: "'a alg_closure \<Rightarrow> 'a alg_closure"
  is "\<lambda>x. if x = ring.zero L then ring.zero L else m_inv L x"
  by (fold K_def, fold L_def) (auto simp: field_Units)

lift_definition divide_alg_closure :: "'a alg_closure \<Rightarrow> 'a alg_closure \<Rightarrow> 'a alg_closure"
  is "\<lambda>x y. if y = ring.zero L then ring.zero L else monoid.mult L x (m_inv L y)"
  by (fold K_def, fold L_def) (auto simp: field_Units)

end

instance proof -
  define K where "K \<equiv> (ring_of_type_algebra :: 'a ring)"
  define L where "L \<equiv> field.alg_closure K"

  interpret K: field K
    unfolding K_def by rule

  interpret algebraic_closure L "range K.indexed_const"
  proof -
    have *: "carrier K = UNIV"
      by (auto simp: K_def ring_of_type_algebra_def)
    show "algebraic_closure L (range K.indexed_const)"
      unfolding * [symmetric] L_def by (rule K.alg_closureE)
  qed

  show "OFCLASS('a alg_closure, field_class)"
  proof (standard, goal_cases)
    case 1
    show ?case
      by (transfer, fold K_def, fold L_def) (rule m_assoc)
  next
    case 2
    show ?case
      by (transfer, fold K_def, fold L_def) (rule m_comm)
  next
    case 3
    show ?case
      by (transfer, fold K_def, fold L_def) (rule l_one)
  next
    case 4
    show ?case
      by (transfer, fold K_def, fold L_def) (rule a_assoc)
  next
    case 5
    show ?case
      by (transfer, fold K_def, fold L_def) (rule a_comm)
  next
    case 6
    show ?case
      by (transfer, fold K_def, fold L_def) (rule l_zero)
  next
    case 7
    show ?case
      by (transfer, fold K_def, fold L_def) (rule ring_simprules)
  next
    case 8
    show ?case
      by (transfer, fold K_def, fold L_def) (rule ring_simprules)
  next
    case 9
    show ?case
      by (transfer, fold K_def, fold L_def) (rule ring_simprules)
  next
    case 10
    show ?case
      by (transfer, fold K_def, fold L_def) (rule zero_not_one)
  next
    case 11
    thus ?case
      by (transfer, fold K_def, fold L_def) (auto simp: field_Units)
  next
    case 12
    thus ?case
      by (transfer, fold K_def, fold L_def) auto
  next
    case 13
    thus ?case
      by transfer auto
  qed
qed

end



subsection \<open>The algebraic closure is algebraically closed\<close>

instance alg_closure :: (field) alg_closed_field
proof
  define K where "K \<equiv> (ring_of_type_algebra :: 'a ring)"
  define L where "L \<equiv> field.alg_closure K"

  interpret K: field K
    unfolding K_def by rule

  interpret algebraic_closure L "range K.indexed_const"
  proof -
    have *: "carrier K = UNIV"
      by (auto simp: K_def ring_of_type_algebra_def)
    show "algebraic_closure L (range K.indexed_const)"
      unfolding * [symmetric] L_def by (rule K.alg_closureE)
  qed

  have [simp]: "Rep_alg_closure x \<in> carrier L" for x
    using Rep_alg_closure[of x] by (simp only: L_def K_def)

  have [simp]: "Rep_alg_closure x = Rep_alg_closure y \<longleftrightarrow> x = y" for x y
    by (simp add: Rep_alg_closure_inject)
  have [simp]: "Rep_alg_closure x = \<zero>\<^bsub>L\<^esub> \<longleftrightarrow> x = 0" for x
  proof -
    have "Rep_alg_closure x = Rep_alg_closure 0 \<longleftrightarrow> x = 0"
      by simp
    also have "Rep_alg_closure 0 = \<zero>\<^bsub>L\<^esub>"
      by (simp add: zero_alg_closure.rep_eq L_def K_def)
    finally show ?thesis .
  qed

  have [simp]: "Rep_alg_closure (x ^ n) = Rep_alg_closure x [^]\<^bsub>L\<^esub> n"
    for x :: "'a alg_closure" and n
    by (induction n)
       (auto simp: one_alg_closure.rep_eq times_alg_closure.rep_eq m_comm
             simp flip: L_def K_def)
  have [simp]: "Rep_alg_closure (Abs_alg_closure x) = x" if "x \<in> carrier L" for x
    using that unfolding L_def K_def by (rule Abs_alg_closure_inverse)

  show "\<exists>x. poly p x = 0" if p: "Polynomial.lead_coeff p = 1" "Polynomial.degree p > 0"
    for p :: "'a alg_closure poly"
  proof -
    define P where "P = rev (map Rep_alg_closure (Polynomial.coeffs p))"
    have deg: "Polynomials.degree P = Polynomial.degree p"
      by (auto simp: P_def degree_eq_length_coeffs)
    have carrier_P: "P \<in> carrier (poly_ring L)"
      by (auto simp: univ_poly_def polynomial_def P_def hd_map hd_rev last_map 
                     last_coeffs_eq_coeff_degree)
    hence "splitted P"
      using roots_over_carrier by blast
    hence "roots P \<noteq> {#}"
      unfolding splitted_def using deg p by auto
    then obtain x where "x \<in># roots P"
      by blast
    hence x: "is_root P x"
      using roots_mem_iff_is_root[OF carrier_P] by auto
    hence [simp]: "x \<in> carrier L"
      by (auto simp: is_root_def)
    define x' where "x' = Abs_alg_closure x"
    define xs where "xs = rev (coeffs p)"

    have "cr_alg_closure (eval (map Rep_alg_closure xs) x) (poly (Poly (rev xs)) x')"
      by (induction xs)
         (auto simp flip: K_def L_def simp: cr_alg_closure_def
                 zero_alg_closure.rep_eq plus_alg_closure.rep_eq
                 times_alg_closure.rep_eq Poly_append poly_monom
                 a_comm m_comm x'_def)
    also have "map Rep_alg_closure xs = P"
      by (simp add: xs_def P_def rev_map)
    also have "Poly (rev xs) = p"
      by (simp add: xs_def)
    finally have "poly p x' = 0"
      using x by (auto simp: is_root_def cr_alg_closure_def)
    thus "\<exists>x. poly p x = 0" ..
  qed
qed



subsection \<open>Converting between the base field and the closure\<close>

context
  fixes L K
  defines "K \<equiv> (ring_of_type_algebra :: 'a :: field ring)"
  defines "L \<equiv> field.alg_closure K"
begin

interpretation K: field K
  unfolding K_def by rule

interpretation algebraic_closure L "range K.indexed_const"
proof -
  have *: "carrier K = UNIV"
    by (auto simp: K_def ring_of_type_algebra_def)
  show "algebraic_closure L (range K.indexed_const)"
    unfolding * [symmetric] L_def by (rule K.alg_closureE)
qed

lemma alg_closure_hom: "K.indexed_const \<in> Ring.ring_hom K L"
  unfolding L_def using K.alg_closureE(2) .

lift_definition%important to_ac :: "'a :: field \<Rightarrow> 'a alg_closure"
  is "ring.indexed_const K"
  by (fold K_def, fold L_def) (use mem_carrier in blast)

lemma to_ac_0 [simp]: "to_ac (0 :: 'a) = 0"
proof -
  have "to_ac (\<zero>\<^bsub>K\<^esub>) = 0"
  proof (transfer fixing: K, fold K_def, fold L_def)
    show "K.indexed_const \<zero>\<^bsub>K\<^esub> = \<zero>\<^bsub>L\<^esub>"
      using Ring.ring_hom_zero[OF alg_closure_hom] K.ring_axioms is_ring
      by simp
  qed
  thus ?thesis
    by (simp add: K_def ring_of_type_algebra_def)
qed

lemma to_ac_1 [simp]: "to_ac (1 :: 'a) = 1"
proof -
  have "to_ac (\<one>\<^bsub>K\<^esub>) = 1"
  proof (transfer fixing: K, fold K_def, fold L_def)
    show "K.indexed_const \<one>\<^bsub>K\<^esub> = \<one>\<^bsub>L\<^esub>"
      using Ring.ring_hom_one[OF alg_closure_hom] K.ring_axioms is_ring
      by simp
  qed
  thus ?thesis
    by (simp add: K_def ring_of_type_algebra_def)
qed

lemma to_ac_add [simp]: "to_ac (x + y :: 'a) = to_ac x + to_ac y"
proof -
  have "to_ac (x \<oplus>\<^bsub>K\<^esub> y) = to_ac x + to_ac y"
  proof (transfer fixing: K x y, fold K_def, fold L_def)
    show "K.indexed_const (x \<oplus>\<^bsub>K\<^esub> y) = K.indexed_const x \<oplus>\<^bsub>L\<^esub> K.indexed_const y"
      using Ring.ring_hom_add[OF alg_closure_hom, of x y] K.ring_axioms is_ring
      by (simp add: K_def ring_of_type_algebra_def)
  qed
  thus ?thesis
    by (simp add: K_def ring_of_type_algebra_def)
qed

lemma to_ac_minus [simp]: "to_ac (-x :: 'a) = -to_ac x"
  using to_ac_add to_ac_0 add_eq_0_iff by metis

lemma to_ac_diff [simp]: "to_ac (x - y :: 'a) = to_ac x - to_ac y"
  using to_ac_add[of x "-y"] by simp

lemma to_ac_mult [simp]: "to_ac (x * y :: 'a) = to_ac x * to_ac y"
proof -
  have "to_ac (x \<otimes>\<^bsub>K\<^esub> y) = to_ac x * to_ac y"
  proof (transfer fixing: K x y, fold K_def, fold L_def)
    show "K.indexed_const (x \<otimes>\<^bsub>K\<^esub> y) = K.indexed_const x \<otimes>\<^bsub>L\<^esub> K.indexed_const y"
      using Ring.ring_hom_mult[OF alg_closure_hom, of x y] K.ring_axioms is_ring
      by (simp add: K_def ring_of_type_algebra_def)
  qed
  thus ?thesis
    by (simp add: K_def ring_of_type_algebra_def)
qed

lemma to_ac_inverse [simp]: "to_ac (inverse x :: 'a) = inverse (to_ac x)"
  using to_ac_mult[of x "inverse x"] to_ac_1 to_ac_0
  by (metis divide_self_if field_class.field_divide_inverse field_class.field_inverse_zero inverse_unique)

lemma to_ac_divide [simp]: "to_ac (x / y :: 'a) = to_ac x / to_ac y"
  using to_ac_mult[of x "inverse y"] to_ac_inverse[of y]
  by (simp add: field_class.field_divide_inverse)

lemma to_ac_power [simp]: "to_ac (x ^ n) = to_ac x ^ n"
  by (induction n) auto

lemma to_ac_of_nat [simp]: "to_ac (of_nat n) = of_nat n"
  by (induction n) auto

lemma to_ac_of_int [simp]: "to_ac (of_int n) = of_int n"
  by (induction n) auto

lemma to_ac_numeral [simp]: "to_ac (numeral n) = numeral n"
  using to_ac_of_nat[of "numeral n"] by (simp del: to_ac_of_nat)

lemma to_ac_sum: "to_ac (\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. to_ac (f x))"
  by (induction A rule: infinite_finite_induct) auto

lemma to_ac_prod: "to_ac (\<Prod>x\<in>A. f x) = (\<Prod>x\<in>A. to_ac (f x))"
  by (induction A rule: infinite_finite_induct) auto

lemma to_ac_sum_list: "to_ac (sum_list xs) = (\<Sum>x\<leftarrow>xs. to_ac x)"
  by (induction xs) auto

lemma to_ac_prod_list: "to_ac (prod_list xs) = (\<Prod>x\<leftarrow>xs. to_ac x)"
  by (induction xs) auto

lemma to_ac_sum_mset: "to_ac (sum_mset xs) = (\<Sum>x\<in>#xs. to_ac x)"
  by (induction xs) auto

lemma to_ac_prod_mset: "to_ac (prod_mset xs) = (\<Prod>x\<in>#xs. to_ac x)"
  by (induction xs) auto

end

lemma (in ring) indexed_const_eq_iff [simp]:
  "indexed_const x = (indexed_const y :: 'c multiset \<Rightarrow> 'a) \<longleftrightarrow> x = y"
proof
  assume "indexed_const x = (indexed_const y :: 'c multiset \<Rightarrow> 'a)"
  hence "indexed_const x ({#} :: 'c multiset) = indexed_const y ({#} :: 'c multiset)"
    by metis
  thus "x = y"
    by (simp add: indexed_const_def)
qed auto

lemma inj_to_ac: "inj to_ac"
  by (transfer, intro injI, subst (asm) ring.indexed_const_eq_iff) auto

lemma to_ac_eq_iff [simp]: "to_ac x = to_ac y \<longleftrightarrow> x = y"
  using inj_to_ac by (auto simp: inj_on_def)

lemma to_ac_eq_0_iff [simp]: "to_ac x = 0 \<longleftrightarrow> x = 0"
  and to_ac_eq_0_iff' [simp]: "0 = to_ac x \<longleftrightarrow> x = 0"
  and to_ac_eq_1_iff [simp]: "to_ac x = 1 \<longleftrightarrow> x = 1"
  and to_ac_eq_1_iff' [simp]: "1 = to_ac x \<longleftrightarrow> x = 1"
  using to_ac_eq_iff to_ac_0 to_ac_1 by metis+


definition of_ac :: "'a :: field alg_closure \<Rightarrow> 'a" where
  "of_ac x = (if x \<in> range to_ac then inv_into UNIV to_ac x else 0)"

lemma of_ac_eqI: "to_ac x = y \<Longrightarrow> of_ac y = x"
  unfolding of_ac_def by (meson inj_to_ac inv_f_f range_eqI)

lemma of_ac_0 [simp]: "of_ac 0 = 0"
  and of_ac_1 [simp]: "of_ac 1 = 1"
  by (rule of_ac_eqI; simp; fail)+

lemma of_ac_to_ac [simp]: "of_ac (to_ac x) = x"
  by (rule of_ac_eqI) auto

lemma to_ac_of_ac: "x \<in> range to_ac \<Longrightarrow> to_ac (of_ac x) = x"
  by auto


lemma CHAR_alg_closure [simp]:
  "CHAR('a :: field alg_closure) = CHAR('a)"
proof (rule CHAR_eqI)
  show "of_nat CHAR('a) = (0 :: 'a alg_closure)"
    by (metis of_nat_CHAR to_ac_0 to_ac_of_nat)
next
  show "CHAR('a) dvd n" if "of_nat n = (0 :: 'a alg_closure)" for n
    using that by (metis of_nat_eq_0_iff_char_dvd to_ac_eq_0_iff' to_ac_of_nat)
qed

instance alg_closure :: (field_char_0) field_char_0
proof
  show "inj (of_nat :: nat \<Rightarrow> 'a alg_closure)"
    by (metis injD inj_of_nat inj_on_def inj_to_ac to_ac_of_nat)
qed


bundle alg_closure_syntax
begin
notation to_ac ("_\<up>" [1000] 999)
notation of_ac ("_\<down>" [1000] 999)
end


bundle alg_closure_syntax'
begin
notation (output) to_ac ("_")
notation (output) of_ac ("_")
end


subsection \<open>The algebraic closure is an algebraic extension\<close>

text \<open>
  The algebraic closure is an algebraic extension, i.e.\ every element in it is
  a root of some non-zero polynomial in the base field.
\<close>
theorem alg_closure_algebraic:
  fixes x :: "'a :: field alg_closure"
  obtains p :: "'a poly" where "p \<noteq> 0" "poly (map_poly to_ac p) x = 0"
proof -
  define K where "K \<equiv> (ring_of_type_algebra :: 'a ring)"
  define L where "L \<equiv> field.alg_closure K"

  interpret K: field K
    unfolding K_def by rule

  interpret algebraic_closure L "range K.indexed_const"
  proof -
    have *: "carrier K = UNIV"
      by (auto simp: K_def ring_of_type_algebra_def)
    show "algebraic_closure L (range K.indexed_const)"
      unfolding * [symmetric] L_def by (rule K.alg_closureE)
  qed

  let ?K = "range K.indexed_const"
  have sr: "subring ?K L"
    by (rule subring_axioms)
  define x' where "x' = Rep_alg_closure x"
  have "x' \<in> carrier L"
    unfolding x'_def L_def K_def by (rule Rep_alg_closure)
  hence alg: "(algebraic over range K.indexed_const) x'"
    using algebraic_extension by blast
  then obtain p where p: "p \<in> carrier (?K[X]\<^bsub>L\<^esub>)" "p \<noteq> []" "eval p x' = \<zero>\<^bsub>L\<^esub>"
    using algebraicE[OF sr \<open>x' \<in> carrier L\<close> alg] by blast

  have [simp]: "Rep_alg_closure x \<in> carrier L" for x
    using Rep_alg_closure[of x] by (simp only: L_def K_def)
  have [simp]: "Abs_alg_closure x = 0 \<longleftrightarrow> x = \<zero>\<^bsub>L\<^esub>" if "x \<in> carrier L" for x
    using that unfolding L_def K_def
    by (metis Abs_alg_closure_inverse zero_alg_closure.rep_eq zero_alg_closure_def)
  have [simp]: "Rep_alg_closure (x ^ n) = Rep_alg_closure x [^]\<^bsub>L\<^esub> n"
    for x :: "'a alg_closure" and n
    by (induction n)
       (auto simp: one_alg_closure.rep_eq times_alg_closure.rep_eq m_comm
             simp flip: L_def K_def)
  have [simp]: "Rep_alg_closure (Abs_alg_closure x) = x" if "x \<in> carrier L" for x
    using that unfolding L_def K_def by (rule Abs_alg_closure_inverse)
  have [simp]: "Rep_alg_closure x = \<zero>\<^bsub>L\<^esub> \<longleftrightarrow> x = 0" for x
    by (metis K_def L_def Rep_alg_closure_inverse zero_alg_closure.rep_eq)

  define p' where "p' = Poly (map Abs_alg_closure (rev p))"
  have "p' \<noteq> 0"
  proof
    assume "p' = 0"
    then obtain n where n: "map Abs_alg_closure (rev p) = replicate n 0"
      by (auto simp: p'_def Poly_eq_0)
    with \<open>p \<noteq> []\<close> have "n > 0"
      by (auto intro!: Nat.gr0I)
    have "last (map Abs_alg_closure (rev p)) = 0"
      using \<open>n > 0\<close> by (subst n) auto
    moreover have "Polynomials.lead_coeff p \<noteq> \<zero>\<^bsub>L\<^esub>" "Polynomials.lead_coeff p \<in> carrier L"
      using p \<open>p \<noteq> []\<close> local.subset
      by (fastforce simp: polynomial_def univ_poly_def)+
    ultimately show False
      using \<open>p \<noteq> []\<close> by (auto simp: last_map last_rev)
  qed

  have "set p \<subseteq> carrier L"
    using local.subset p by (auto simp: univ_poly_def polynomial_def)
  hence "cr_alg_closure (eval p x') (poly p' x)"
    unfolding p'_def
    by (induction p)
       (auto simp flip: K_def L_def simp: cr_alg_closure_def
               zero_alg_closure.rep_eq plus_alg_closure.rep_eq
               times_alg_closure.rep_eq Poly_append poly_monom
               a_comm m_comm x'_def)
  hence "poly p' x = 0"
    using p by (auto simp: cr_alg_closure_def x'_def)

  have coeff_p': "Polynomial.coeff p' i \<in> range to_ac" for i
  proof (cases "i \<ge> length p")
    case False
    have "Polynomial.coeff p' i = Abs_alg_closure (rev p ! i)"
      unfolding p'_def using False
      by (auto simp: nth_default_def)
    moreover have "rev p ! i \<in> ?K"
      using p(1) False by (auto simp: univ_poly_def polynomial_def rev_nth)
    ultimately show ?thesis
      unfolding to_ac.abs_eq K_def by fastforce
  qed (auto simp: p'_def nth_default_def)
  

  define p'' where "p'' = map_poly of_ac p'"
  have p'_eq: "p' = map_poly to_ac p''"
    by (rule poly_eqI) (auto simp: coeff_map_poly p''_def to_ac_of_ac[OF coeff_p'])

  show ?thesis
  proof (rule that)
    show "p'' \<noteq> 0"
      using \<open>p' \<noteq> 0\<close> by (auto simp: p'_eq)
  next
    show "poly (map_poly to_ac p'') x = 0"
      using \<open>poly p' x = 0\<close> by (simp add: p'_eq)
  qed
qed


instantiation alg_closure :: (field)
  "{unique_euclidean_ring, normalization_euclidean_semiring, normalization_semidom_multiplicative}"
begin

definition [simp]: "normalize_alg_closure = (normalize_field :: 'a alg_closure \<Rightarrow> _)"
definition [simp]: "unit_factor_alg_closure = (unit_factor_field :: 'a alg_closure \<Rightarrow> _)"
definition [simp]: "modulo_alg_closure = (mod_field :: 'a alg_closure \<Rightarrow> _)"
definition [simp]: "euclidean_size_alg_closure = (euclidean_size_field :: 'a alg_closure \<Rightarrow> _)"
definition [simp]: "division_segment (x :: 'a alg_closure) = 1"

instance
  by standard
    (simp_all add: dvd_field_iff field_split_simps split: if_splits)

end

instantiation alg_closure :: (field) euclidean_ring_gcd
begin

definition gcd_alg_closure :: "'a alg_closure \<Rightarrow> 'a alg_closure \<Rightarrow> 'a alg_closure" where
  "gcd_alg_closure = Euclidean_Algorithm.gcd"
definition lcm_alg_closure :: "'a alg_closure \<Rightarrow> 'a alg_closure \<Rightarrow> 'a alg_closure" where
  "lcm_alg_closure = Euclidean_Algorithm.lcm"
definition Gcd_alg_closure :: "'a alg_closure set \<Rightarrow> 'a alg_closure" where
 "Gcd_alg_closure = Euclidean_Algorithm.Gcd"
definition Lcm_alg_closure :: "'a alg_closure set \<Rightarrow> 'a alg_closure" where
 "Lcm_alg_closure = Euclidean_Algorithm.Lcm"

instance by standard (simp_all add: gcd_alg_closure_def lcm_alg_closure_def Gcd_alg_closure_def Lcm_alg_closure_def)

end

instance alg_closure :: (field) semiring_gcd_mult_normalize
  ..

end