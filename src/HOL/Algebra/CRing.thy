(*
  Title:     The algebraic hierarchy of rings
  Id:        $Id$
  Author:    Clemens Ballarin, started 9 December 1996
  Copyright: Clemens Ballarin
*)

theory CRing = Summation
files ("ringsimp.ML"):

section {* The Algebraic Hierarchy of Rings *}

subsection {* Basic Definitions *}

record 'a ring = "'a group" +
  zero :: 'a ("\<zero>\<index>")
  add :: "['a, 'a] => 'a" (infixl "\<oplus>\<index>" 65)
  a_inv :: "'a => 'a" ("\<ominus>\<index> _" [81] 80)

locale cring = abelian_monoid R +
  assumes a_abelian_group: "abelian_group (| carrier = carrier R,
      mult = add R, one = zero R, m_inv = a_inv R |)"
    and m_inv_def: "[| EX y. y \<in> carrier R & x \<otimes> y = \<one>; x \<in> carrier R |]
      ==> inv x = (THE y. y \<in> carrier R & x \<otimes> y = \<one>)"
    and l_distr: "[| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
      ==> (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"

text {* Derived operation. *}

constdefs
  minus :: "[('a, 'm) ring_scheme, 'a, 'a] => 'a" (infixl "\<ominus>\<index>" 65)
  "[| x \<in> carrier R; y \<in> carrier R |] ==> minus R x y == add R x (a_inv R y)"

(*
  -- {* Definition of derived operations *}

  minus_def:    "a - b = a + (-b)"
  inverse_def:  "inverse a = (if a dvd 1 then THE x. a*x = 1 else 0)"
  divide_def:   "a / b = a * inverse b"
  power_def:    "a ^ n = nat_rec 1 (%u b. b * a) n"
*)

locale "domain" = cring +
  assumes one_not_zero [simp]: "\<one> ~= \<zero>"
    and integral: "[| a \<otimes> b = \<zero>; a \<in> carrier R; b \<in> carrier R |] ==>
                  a = \<zero> | b = \<zero>"

subsection {* Basic Facts of Rings *}

lemma (in cring) a_magma [simp, intro]:
  "magma (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  using a_abelian_group by (simp only: abelian_group_def)

lemma (in cring) a_l_one [simp, intro]:
  "l_one (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  using a_abelian_group by (simp only: abelian_group_def)

lemma (in cring) a_abelian_group_parts [simp, intro]:
  "semigroup_axioms (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  "group_axioms (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  "abelian_semigroup_axioms (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  using a_abelian_group by (simp_all only: abelian_group_def)

lemma (in cring) a_semigroup:
  "semigroup (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  by (simp add: semigroup_def)

lemma (in cring) a_group:
  "group (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  by (simp add: group_def)

lemma (in cring) a_abelian_semigroup:
  "abelian_semigroup (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  by (simp add: abelian_semigroup_def)

lemmas group_record_simps = semigroup.simps monoid.simps group.simps

lemmas (in cring) a_closed [intro, simp] =
  magma.m_closed [OF a_magma, simplified group_record_simps]

lemmas (in cring) zero_closed [intro, simp] = 
  l_one.one_closed [OF a_l_one, simplified group_record_simps]

lemmas (in cring) a_inv_closed [intro, simp] =
  group.inv_closed [OF a_group, simplified group_record_simps]

lemma (in cring) minus_closed [intro, simp]:
  "[| x \<in> carrier R; y \<in> carrier R |] ==> x \<ominus> y \<in> carrier R"
  by (simp add: minus_def)

lemmas (in cring) a_l_cancel [simp] =
  group.l_cancel [OF a_group, simplified group_record_simps]

lemmas (in cring) a_r_cancel [simp] =
  group.r_cancel [OF a_group, simplified group_record_simps]

lemmas (in cring) a_assoc =
  semigroup.m_assoc [OF a_semigroup, simplified group_record_simps]

lemmas (in cring) l_zero [simp] =
  l_one.l_one [OF a_l_one, simplified group_record_simps]

lemmas (in cring) l_neg =
  group.l_inv [OF a_group, simplified group_record_simps]

lemmas (in cring) a_comm =
  abelian_semigroup.m_comm [OF a_abelian_semigroup,
  simplified group_record_simps]

lemmas (in cring) a_lcomm =
  abelian_semigroup.m_lcomm [OF a_abelian_semigroup, simplified group_record_simps]

lemma (in cring) r_zero [simp]:
  "x \<in> carrier R ==> x \<oplus> \<zero> = x"
  using group.r_one [OF a_group]
  by simp

lemma (in cring) r_neg:
  "x \<in> carrier R ==> x \<oplus> (\<ominus> x) = \<zero>"
  using group.r_inv [OF a_group]
  by simp

lemmas (in cring) minus_zero [simp] =
  group.inv_one [OF a_group, simplified group_record_simps]

lemma (in cring) minus_minus [simp]:
  "x \<in> carrier R ==> \<ominus> (\<ominus> x) = x"
  using group.inv_inv [OF a_group, simplified group_record_simps]
  by simp

lemma (in cring) minus_add:
  "[| x \<in> carrier R; y \<in> carrier R |] ==> \<ominus> (x \<oplus> y) = \<ominus> x \<oplus> \<ominus> y"
  using abelian_group.inv_mult [OF a_abelian_group]
  by simp

lemmas (in cring) a_ac = a_assoc a_comm a_lcomm

subsection {* Normaliser for Commutative Rings *}

lemma (in cring) r_neg2:
  "[| x \<in> carrier R; y \<in> carrier R |] ==> x \<oplus> (\<ominus> x \<oplus> y) = y"
proof -
  assume G: "x \<in> carrier R" "y \<in> carrier R"
  then have "(x \<oplus> \<ominus> x) \<oplus> y = y" by (simp only: r_neg l_zero)
  with G show ?thesis by (simp add: a_ac)
qed

lemma (in cring) r_neg1:
  "[| x \<in> carrier R; y \<in> carrier R |] ==> \<ominus> x \<oplus> (x \<oplus> y) = y"
proof -
  assume G: "x \<in> carrier R" "y \<in> carrier R"
  then have "(\<ominus> x \<oplus> x) \<oplus> y = y" by (simp only: l_neg l_zero)
  with G show ?thesis by (simp add: a_ac)
qed

lemma (in cring) r_distr:
  "[| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
  ==> z \<otimes> (x \<oplus> y) = z \<otimes> x \<oplus> z \<otimes> y"
proof -
  assume G: "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R"
  then have "z \<otimes> (x \<oplus> y) = (x \<oplus> y) \<otimes> z" by (simp add: m_comm)
  also from G have "... = x \<otimes> z \<oplus> y \<otimes> z" by (simp add: l_distr)
  also from G have "... = z \<otimes> x \<oplus> z \<otimes> y" by (simp add: m_comm)
  finally show ?thesis .
qed

text {* 
  The following proofs are from Jacobson, Basic Algebra I, pp.~88--89
*}

lemma (in cring) l_null [simp]:
  "x \<in> carrier R ==> \<zero> \<otimes> x = \<zero>"
proof -
  assume R: "x \<in> carrier R"
  then have "\<zero> \<otimes> x \<oplus> \<zero> \<otimes> x = (\<zero> \<oplus> \<zero>) \<otimes> x"
    by (simp add: l_distr del: l_zero r_zero)
  also from R have "... = \<zero> \<otimes> x \<oplus> \<zero>" by simp
  finally have "\<zero> \<otimes> x \<oplus> \<zero> \<otimes> x = \<zero> \<otimes> x \<oplus> \<zero>" .
  with R show ?thesis by (simp del: r_zero)
qed

lemma (in cring) r_null [simp]:
  "x \<in> carrier R ==> x \<otimes> \<zero> = \<zero>"
proof -
  assume R: "x \<in> carrier R"
  then have "x \<otimes> \<zero> = \<zero> \<otimes> x" by (simp add: ac)
  also from R have "... = \<zero>" by simp
  finally show ?thesis .
qed

lemma (in cring) l_minus:
  "[| x \<in> carrier R; y \<in> carrier R |] ==> \<ominus> x \<otimes> y = \<ominus> (x \<otimes> y)"
proof -
  assume R: "x \<in> carrier R" "y \<in> carrier R"
  then have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y = (\<ominus> x \<oplus> x) \<otimes> y" by (simp add: l_distr)
  also from R have "... = \<zero>" by (simp add: l_neg l_null)
  finally have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y = \<zero>" .
  with R have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y \<oplus> \<ominus> (x \<otimes> y) = \<zero> \<oplus> \<ominus> (x \<otimes> y)" by simp
  with R show ?thesis by (simp add: a_assoc r_neg )
qed

lemma (in cring) r_minus:
  "[| x \<in> carrier R; y \<in> carrier R |] ==> x \<otimes> \<ominus> y = \<ominus> (x \<otimes> y)"
proof -
  assume R: "x \<in> carrier R" "y \<in> carrier R"
  then have "x \<otimes> \<ominus> y = \<ominus> y \<otimes> x" by (simp add: ac)
  also from R have "... = \<ominus> (y \<otimes> x)" by (simp add: l_minus)
  also from R have "... = \<ominus> (x \<otimes> y)" by (simp add: ac)
  finally show ?thesis .
qed

lemmas (in cring) cring_simprules =
  a_closed zero_closed a_inv_closed minus_closed m_closed one_closed
  a_assoc l_zero l_neg a_comm m_assoc l_one l_distr m_comm minus_def
  r_zero r_neg r_neg2 r_neg1 minus_add minus_minus minus_zero
  a_lcomm m_lcomm r_distr l_null r_null l_minus r_minus

use "ringsimp.ML"

method_setup algebra =
  {* Method.ctxt_args cring_normalise *}
  {* computes distributive normal form in commutative rings (locales version) *}

text {* Two examples for use of method algebra *}

lemma
  includes cring R + cring S
  shows "[| a \<in> carrier R; b \<in> carrier R; c \<in> carrier S; d \<in> carrier S |] ==> 
  a \<oplus> \<ominus> (a \<oplus> \<ominus> b) = b & c \<otimes>\<^sub>2 d = d \<otimes>\<^sub>2 c"
  by algebra

lemma
  includes cring
  shows "[| a \<in> carrier R; b \<in> carrier R |] ==> a \<ominus> (a \<ominus> b) = b"
  by algebra

subsection {* Sums over Finite Sets *}

text {*
  This definition makes it easy to lift lemmas from @{term finprod}.
*}

constdefs
  finsum :: "[('b, 'm) ring_scheme, 'a => 'b, 'a set] => 'b"
  "finsum R f A == finprod (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |) f A"

lemma (in cring) a_abelian_monoid:
  "abelian_monoid (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  by (simp add: abelian_monoid_def)

(*
  lemmas (in cring) finsum_empty [simp] =
    abelian_monoid.finprod_empty [OF a_abelian_monoid, simplified]
  is dangeous, because attributes (like simplified) are applied upon opening
  the locale, simplified refers to the simpset at that time!!!
*)

lemmas (in cring) finsum_empty [simp] =
  abelian_monoid.finprod_empty [OF a_abelian_monoid, folded finsum_def,
    simplified group_record_simps]

lemmas (in cring) finsum_insert [simp] =
  abelian_monoid.finprod_insert [OF a_abelian_monoid, folded finsum_def,
    simplified group_record_simps]

lemmas (in cring) finsum_zero =
  abelian_monoid.finprod_one [OF a_abelian_monoid, folded finsum_def,
    simplified group_record_simps]

lemmas (in cring) finsum_closed [simp] =
  abelian_monoid.finprod_closed [OF a_abelian_monoid, folded finsum_def,
    simplified group_record_simps]

lemmas (in cring) finsum_Un_Int =
  abelian_monoid.finprod_Un_Int [OF a_abelian_monoid, folded finsum_def,
    simplified group_record_simps]

lemmas (in cring) finsum_Un_disjoint =
  abelian_monoid.finprod_Un_disjoint [OF a_abelian_monoid, folded finsum_def,
    simplified group_record_simps]

lemmas (in cring) finsum_addf =
  abelian_monoid.finprod_multf [OF a_abelian_monoid, folded finsum_def,
    simplified group_record_simps]

lemmas (in cring) finsum_cong' =
  abelian_monoid.finprod_cong' [OF a_abelian_monoid, folded finsum_def,
    simplified group_record_simps]

lemmas (in cring) finsum_0 [simp] =
  abelian_monoid.finprod_0 [OF a_abelian_monoid, folded finsum_def,
    simplified group_record_simps]

lemmas (in cring) finsum_Suc [simp] =
  abelian_monoid.finprod_Suc [OF a_abelian_monoid, folded finsum_def,
    simplified group_record_simps]

lemmas (in cring) finsum_Suc2 =
  abelian_monoid.finprod_Suc2 [OF a_abelian_monoid, folded finsum_def,
    simplified group_record_simps]

lemmas (in cring) finsum_add [simp] =
  abelian_monoid.finprod_mult [OF a_abelian_monoid, folded finsum_def,
    simplified group_record_simps]

lemmas (in cring) finsum_cong =
  abelian_monoid.finprod_cong [OF a_abelian_monoid, folded finsum_def,
    simplified group_record_simps]

text {*Usually, if this rule causes a failed congruence proof error,
   the reason is that the premise @{text "g \<in> B -> carrier G"} cannot be shown.
   Adding @{thm [source] Pi_def} to the simpset is often useful. *}

lemma (in cring) finsum_ldistr:
  "[| finite A; a \<in> carrier R; f \<in> A -> carrier R |] ==>
   finsum R f A \<otimes> a = finsum R (%i. f i \<otimes> a) A"
proof (induct set: Finites)
  case empty then show ?case by simp
next
  case (insert F x) then show ?case by (simp add: Pi_def l_distr)
qed

lemma (in cring) finsum_rdistr:
  "[| finite A; a \<in> carrier R; f \<in> A -> carrier R |] ==>
   a \<otimes> finsum R f A = finsum R (%i. a \<otimes> f i) A"
proof (induct set: Finites)
  case empty then show ?case by simp
next
  case (insert F x) then show ?case by (simp add: Pi_def r_distr)
qed

subsection {* Facts of Integral Domains *}

lemma (in "domain") zero_not_one [simp]:
  "\<zero> ~= \<one>"
  by (rule not_sym) simp

lemma (in "domain") integral_iff: (* not by default a simp rule! *)
  "[| a \<in> carrier R; b \<in> carrier R |] ==> (a \<otimes> b = \<zero>) = (a = \<zero> | b = \<zero>)"
proof
  assume "a \<in> carrier R" "b \<in> carrier R" "a \<otimes> b = \<zero>"
  then show "a = \<zero> | b = \<zero>" by (simp add: integral)
next
  assume "a \<in> carrier R" "b \<in> carrier R" "a = \<zero> | b = \<zero>"
  then show "a \<otimes> b = \<zero>" by auto
qed

lemma (in "domain") m_lcancel:
  assumes prem: "a ~= \<zero>"
    and R: "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  shows "(a \<otimes> b = a \<otimes> c) = (b = c)"
proof
  assume eq: "a \<otimes> b = a \<otimes> c"
  with R have "a \<otimes> (b \<ominus> c) = \<zero>" by algebra
  with R have "a = \<zero> | (b \<ominus> c) = \<zero>" by (simp add: integral_iff)
  with prem and R have "b \<ominus> c = \<zero>" by auto 
  with R have "b = b \<ominus> (b \<ominus> c)" by algebra 
  also from R have "b \<ominus> (b \<ominus> c) = c" by algebra
  finally show "b = c" .
next
  assume "b = c" then show "a \<otimes> b = a \<otimes> c" by simp
qed

lemma (in "domain") m_rcancel:
  assumes prem: "a ~= \<zero>"
    and R: "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  shows conc: "(b \<otimes> a = c \<otimes> a) = (b = c)"
proof -
  from prem and R have "(a \<otimes> b = a \<otimes> c) = (b = c)" by (rule m_lcancel)
  with R show ?thesis by algebra
qed

end
