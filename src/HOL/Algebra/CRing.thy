(*
  Title:     The algebraic hierarchy of rings
  Id:        $Id$
  Author:    Clemens Ballarin, started 9 December 1996
  Copyright: Clemens Ballarin
*)

header {* The algebraic hierarchy of rings as axiomatic classes *}

theory CRing = Group
files ("ringsimp.ML"):

section {* The Algebraic Hierarchy of Rings *}

subsection {* Basic Definitions *}

record 'a ring = "'a group" +
  zero :: 'a ("\<zero>\<index>")
  add :: "['a, 'a] => 'a" (infixl "\<oplus>\<index>" 65)
  a_inv :: "'a => 'a" ("\<ominus>\<index> _" [81] 80)
  minus :: "['a, 'a] => 'a" (infixl "\<ominus>\<index>" 65)

locale cring = abelian_monoid R +
  assumes a_abelian_group: "abelian_group (| carrier = carrier R,
      mult = add R, one = zero R, m_inv = a_inv R |)"
    and minus_def: "[| x \<in> carrier R; y \<in> carrier R |] ==> x \<ominus> y = x \<oplus> \<ominus> y"
    and m_inv_def: "[| EX y. y \<in> carrier R & x \<otimes> y = \<one>; x \<in> carrier R |]
      ==> inv x = (THE y. y \<in> carrier R & x \<otimes> y = \<one>)"
    and l_distr: "[| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
      ==> (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"

(*
  -- {* Definition of derived operations *}

  minus_def:    "a - b = a + (-b)"
  inverse_def:  "inverse a = (if a dvd 1 then THE x. a*x = 1 else 0)"
  divide_def:   "a / b = a * inverse b"
  power_def:    "a ^ n = nat_rec 1 (%u b. b * a) n"
*)
subsection {* Basic Facts *}

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

lemma (in cring) a_abelian_group:
  "abelian_group (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  by (simp add: abelian_group_def)

lemmas (in cring) a_closed [intro, simp] =
  magma.m_closed [OF a_magma, simplified]

lemmas (in cring) zero_closed [intro, simp] = 
  l_one.one_closed [OF a_l_one, simplified]

lemmas (in cring) a_inv_closed [intro, simp] =
  group.inv_closed [OF a_group, simplified]

lemma (in cring) minus_closed [intro, simp]:
  "[| x \<in> carrier R; y \<in> carrier R |] ==> x \<ominus> y \<in> carrier R"
  by (simp add: minus_def)

lemmas (in cring) a_l_cancel [simp] = group.l_cancel [OF a_group, simplified]

lemmas (in cring) a_r_cancel [simp] = group.r_cancel [OF a_group, simplified]

lemmas (in cring) a_assoc = semigroup.m_assoc [OF a_semigroup, simplified]

lemmas (in cring) l_zero [simp] = l_one.l_one [OF a_l_one, simplified]

lemmas (in cring) l_neg = group.l_inv [OF a_group, simplified]

lemmas (in cring) a_comm = abelian_semigroup.m_comm [OF a_abelian_semigroup,
  simplified]

lemmas (in cring) a_lcomm =
  abelian_semigroup.m_lcomm [OF a_abelian_semigroup, simplified]

lemma (in cring) r_zero [simp]:
  "x \<in> carrier R ==> x \<oplus> \<zero> = x"
  using group.r_one [OF a_group]
  by simp

lemma (in cring) r_neg:
  "x \<in> carrier R ==> x \<oplus> (\<ominus> x) = \<zero>"
  using group.r_inv [OF a_group]
  by simp

lemmas (in cring) minus_zero [simp] = group.inv_one [OF a_group, simplified]

lemma (in cring) minus_minus [simp]:
  "x \<in> carrier R ==> \<ominus> (\<ominus> x) = x"
  using group.inv_inv [OF a_group, simplified]
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

lemma
  includes cring R + cring S
  shows "[| a \<in> carrier R; b \<in> carrier R; c \<in> carrier S; d \<in> carrier S |] ==> 
  a \<oplus> \<ominus> (a \<oplus> \<ominus> b) = b & c \<otimes>\<^sub>2 d = d \<otimes>\<^sub>2 c"
  by algebra

lemma
  includes cring
  shows "[| a \<in> carrier R; b \<in> carrier R |] ==> a \<ominus> (a \<ominus> b) = b"
  by algebra

end
