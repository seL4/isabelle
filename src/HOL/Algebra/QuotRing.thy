(*
  Title:     HOL/Algebra/QuotRing.thy
  Id:        $Id$
  Author:    Stephan Hohe
*)

header {* Quotient Rings *}

theory QuotRing
imports RingHom
begin

subsection {* Multiplication on Cosets *}

constdefs (structure R)
  rcoset_mult :: "[('a, _) ring_scheme, 'a set, 'a set, 'a set] \<Rightarrow> 'a set"
    ("[mod _:] _ \<Otimes>\<index> _" [81,81,81] 80)
  "rcoset_mult R I A B \<equiv> \<Union>a\<in>A. \<Union>b\<in>B. I +> (a \<otimes> b)"


text {* @{const "rcoset_mult"} fulfils the properties required by
  congruences *}
lemma (in ideal) rcoset_mult_add:
  "\<lbrakk>x \<in> carrier R; y \<in> carrier R\<rbrakk> \<Longrightarrow> [mod I:] (I +> x) \<Otimes> (I +> y) = I +> (x \<otimes> y)"
apply rule
apply (rule, simp add: rcoset_mult_def, clarsimp)
defer 1
apply (rule, simp add: rcoset_mult_def)
defer 1
proof -
  fix z x' y'
  assume carr: "x \<in> carrier R" "y \<in> carrier R"
     and x'rcos: "x' \<in> I +> x"
     and y'rcos: "y' \<in> I +> y"
     and zrcos: "z \<in> I +> x' \<otimes> y'"

  from x'rcos 
      have "\<exists>h\<in>I. x' = h \<oplus> x" by (simp add: a_r_coset_def r_coset_def)
  from this obtain hx
      where hxI: "hx \<in> I"
      and x': "x' = hx \<oplus> x"
      by fast+
  
  from y'rcos
      have "\<exists>h\<in>I. y' = h \<oplus> y" by (simp add: a_r_coset_def r_coset_def)
  from this
      obtain hy
      where hyI: "hy \<in> I"
      and y': "y' = hy \<oplus> y"
      by fast+

  from zrcos
      have "\<exists>h\<in>I. z = h \<oplus> (x' \<otimes> y')" by (simp add: a_r_coset_def r_coset_def)
  from this
      obtain hz
      where hzI: "hz \<in> I"
      and z: "z = hz \<oplus> (x' \<otimes> y')"
      by fast+

  note carr = carr hxI[THEN a_Hcarr] hyI[THEN a_Hcarr] hzI[THEN a_Hcarr]

  from z have "z = hz \<oplus> (x' \<otimes> y')" .
  also from x' y'
      have "\<dots> = hz \<oplus> ((hx \<oplus> x) \<otimes> (hy \<oplus> y))" by simp
  also from carr
      have "\<dots> = (hz \<oplus> (hx \<otimes> (hy \<oplus> y)) \<oplus> x \<otimes> hy) \<oplus> x \<otimes> y" by algebra
  finally
      have z2: "z = (hz \<oplus> (hx \<otimes> (hy \<oplus> y)) \<oplus> x \<otimes> hy) \<oplus> x \<otimes> y" .

  from hxI hyI hzI carr
      have "hz \<oplus> (hx \<otimes> (hy \<oplus> y)) \<oplus> x \<otimes> hy \<in> I"  by (simp add: I_l_closed I_r_closed)

  from this and z2
      have "\<exists>h\<in>I. z = h \<oplus> x \<otimes> y" by fast
  thus "z \<in> I +> x \<otimes> y" by (simp add: a_r_coset_def r_coset_def)
next
  fix z
  assume xcarr: "x \<in> carrier R"
     and ycarr: "y \<in> carrier R"
     and zrcos: "z \<in> I +> x \<otimes> y"
  from xcarr
      have xself: "x \<in> I +> x" by (intro a_rcos_self)
  from ycarr
      have yself: "y \<in> I +> y" by (intro a_rcos_self)

  from xself and yself and zrcos
      show "\<exists>a\<in>I +> x. \<exists>b\<in>I +> y. z \<in> I +> a \<otimes> b" by fast
qed


subsection {* Quotient Ring Definition *}

constdefs (structure R)
  FactRing :: "[('a,'b) ring_scheme, 'a set] \<Rightarrow> ('a set) ring"
     (infixl "Quot" 65)
  "FactRing R I \<equiv>
    \<lparr>carrier = a_rcosets I, mult = rcoset_mult R I, one = (I +> \<one>), zero = I, add = set_add R\<rparr>"


subsection {* Factorization over General Ideals *}

text {* The quotient is a ring *}
lemma (in ideal) quotient_is_ring:
  shows "ring (R Quot I)"
apply (rule ringI)
   --{* abelian group *}
   apply (rule comm_group_abelian_groupI)
   apply (simp add: FactRing_def)
   apply (rule a_factorgroup_is_comm_group[unfolded A_FactGroup_def'])
  --{* mult monoid *}
  apply (rule monoidI)
      apply (simp_all add: FactRing_def A_RCOSETS_def RCOSETS_def
             a_r_coset_def[symmetric])
      --{* mult closed *}
      apply (clarify)
      apply (simp add: rcoset_mult_add, fast)
     --{* mult @{text one_closed} *}
     apply (force intro: one_closed)
    --{* mult assoc *}
    apply clarify
    apply (simp add: rcoset_mult_add m_assoc)
   --{* mult one *}
   apply clarify
   apply (simp add: rcoset_mult_add l_one)
  apply clarify
  apply (simp add: rcoset_mult_add r_one)
 --{* distr *}
 apply clarify
 apply (simp add: rcoset_mult_add a_rcos_sum l_distr)
apply clarify
apply (simp add: rcoset_mult_add a_rcos_sum r_distr)
done


text {* This is a ring homomorphism *}

lemma (in ideal) rcos_ring_hom:
  "(op +> I) \<in> ring_hom R (R Quot I)"
apply (rule ring_hom_memI)
   apply (simp add: FactRing_def a_rcosetsI[OF a_subset])
  apply (simp add: FactRing_def rcoset_mult_add)
 apply (simp add: FactRing_def a_rcos_sum)
apply (simp add: FactRing_def)
done

lemma (in ideal) rcos_ring_hom_ring:
  "ring_hom_ring R (R Quot I) (op +> I)"
apply (rule ring_hom_ringI)
     apply (rule is_ring, rule quotient_is_ring)
   apply (simp add: FactRing_def a_rcosetsI[OF a_subset])
  apply (simp add: FactRing_def rcoset_mult_add)
 apply (simp add: FactRing_def a_rcos_sum)
apply (simp add: FactRing_def)
done

text {* The quotient of a cring is also commutative *}
lemma (in ideal) quotient_is_cring:
  includes cring
  shows "cring (R Quot I)"
apply (intro cring.intro comm_monoid.intro comm_monoid_axioms.intro)
  apply (rule quotient_is_ring)
 apply (rule ring.axioms[OF quotient_is_ring])
apply (simp add: FactRing_def A_RCOSETS_defs a_r_coset_def[symmetric])
apply clarify
apply (simp add: rcoset_mult_add m_comm)
done

text {* Cosets as a ring homomorphism on crings *}
lemma (in ideal) rcos_ring_hom_cring:
  includes cring
  shows "ring_hom_cring R (R Quot I) (op +> I)"
apply (rule ring_hom_cringI)
  apply (rule rcos_ring_hom_ring)
 apply (rule R.is_cring)
apply (rule quotient_is_cring)
apply (rule R.is_cring)
done


subsection {* Factorization over Prime Ideals *}

text {* The quotient ring generated by a prime ideal is a domain *}
lemma (in primeideal) quotient_is_domain:
  shows "domain (R Quot I)"
apply (rule domain.intro)
 apply (rule quotient_is_cring, rule is_cring)
apply (rule domain_axioms.intro)
 apply (simp add: FactRing_def) defer 1
 apply (simp add: FactRing_def A_RCOSETS_defs a_r_coset_def[symmetric], clarify)
 apply (simp add: rcoset_mult_add) defer 1
proof (rule ccontr, clarsimp)
  assume "I +> \<one> = I"
  hence "\<one> \<in> I" by (simp only: a_coset_join1 one_closed a_subgroup)
  hence "carrier R \<subseteq> I" by (subst one_imp_carrier, simp, fast)
  from this and a_subset
      have "I = carrier R" by fast
  from this and I_notcarr
      show "False" by fast
next
  fix x y
  assume carr: "x \<in> carrier R" "y \<in> carrier R"
     and a: "I +> x \<otimes> y = I"
     and b: "I +> y \<noteq> I"

  have ynI: "y \<notin> I"
  proof (rule ccontr, simp)
    assume "y \<in> I"
    hence "I +> y = I" by (rule a_rcos_const)
    from this and b
        show "False" by simp
  qed

  from carr
      have "x \<otimes> y \<in> I +> x \<otimes> y" by (simp add: a_rcos_self)
  from this
      have xyI: "x \<otimes> y \<in> I" by (simp add: a)

  from xyI and carr
      have xI: "x \<in> I \<or> y \<in> I" by (simp add: I_prime)
  from this and ynI
      have "x \<in> I" by fast
  thus "I +> x = I" by (rule a_rcos_const)
qed

text {* Generating right cosets of a prime ideal is a homomorphism
        on commutative rings *}
lemma (in primeideal) rcos_ring_hom_cring:
  shows "ring_hom_cring R (R Quot I) (op +> I)"
by (rule rcos_ring_hom_cring, rule is_cring)


subsection {* Factorization over Maximal Ideals *}

text {* In a commutative ring, the quotient ring over a maximal ideal
        is a field.
        The proof follows ``W. Adkins, S. Weintraub: Algebra --
        An Approach via Module Theory'' *}
lemma (in maximalideal) quotient_is_field:
  includes cring
  shows "field (R Quot I)"
apply (intro cring.cring_fieldI2)
  apply (rule quotient_is_cring, rule is_cring)
 defer 1
 apply (simp add: FactRing_def A_RCOSETS_defs a_r_coset_def[symmetric], clarsimp)
 apply (simp add: rcoset_mult_add) defer 1
proof (rule ccontr, simp)
  --{* Quotient is not empty *}
  assume "\<zero>\<^bsub>R Quot I\<^esub> = \<one>\<^bsub>R Quot I\<^esub>"
  hence II1: "I = I +> \<one>" by (simp add: FactRing_def)
  from a_rcos_self[OF one_closed]
  have "\<one> \<in> I" by (simp add: II1[symmetric])
  hence "I = carrier R" by (rule one_imp_carrier)
  from this and I_notcarr
  show "False" by simp
next
  --{* Existence of Inverse *}
  fix a
  assume IanI: "I +> a \<noteq> I"
    and acarr: "a \<in> carrier R"

  --{* Helper ideal @{text "J"} *}
  def J \<equiv> "(carrier R #> a) <+> I :: 'a set"
  have idealJ: "ideal J R"
    apply (unfold J_def, rule add_ideals)
     apply (simp only: cgenideal_eq_rcos[symmetric], rule cgenideal_ideal, rule acarr)
    apply (rule is_ideal)
    done

  --{* Showing @{term "J"} not smaller than @{term "I"} *}
  have IinJ: "I \<subseteq> J"
  proof (rule, simp add: J_def r_coset_def set_add_defs)
    fix x
    assume xI: "x \<in> I"
    have Zcarr: "\<zero> \<in> carrier R" by fast
    from xI[THEN a_Hcarr] acarr
    have "x = \<zero> \<otimes> a \<oplus> x" by algebra

    from Zcarr and xI and this
    show "\<exists>xa\<in>carrier R. \<exists>k\<in>I. x = xa \<otimes> a \<oplus> k" by fast
  qed

  --{* Showing @{term "J \<noteq> I"} *}
  have anI: "a \<notin> I"
  proof (rule ccontr, simp)
    assume "a \<in> I"
    hence "I +> a = I" by (rule a_rcos_const)
    from this and IanI
    show "False" by simp
  qed

  have aJ: "a \<in> J"
  proof (simp add: J_def r_coset_def set_add_defs)
    from acarr
    have "a = \<one> \<otimes> a \<oplus> \<zero>" by algebra
    from one_closed and additive_subgroup.zero_closed[OF is_additive_subgroup] and this
    show "\<exists>x\<in>carrier R. \<exists>k\<in>I. a = x \<otimes> a \<oplus> k" by fast
  qed

  from aJ and anI
  have JnI: "J \<noteq> I" by fast

  --{* Deducing @{term "J = carrier R"} because @{term "I"} is maximal *}
  from idealJ and IinJ
  have "J = I \<or> J = carrier R"
  proof (rule I_maximal, unfold J_def)
    have "carrier R #> a \<subseteq> carrier R"
      using subset_refl acarr
      by (rule r_coset_subset_G)
    from this and a_subset
    show "carrier R #> a <+> I \<subseteq> carrier R" by (rule set_add_closed)
  qed

  from this and JnI
  have Jcarr: "J = carrier R" by simp

  --{* Calculating an inverse for @{term "a"} *}
  from one_closed[folded Jcarr]
  have "\<exists>r\<in>carrier R. \<exists>i\<in>I. \<one> = r \<otimes> a \<oplus> i"
    by (simp add: J_def r_coset_def set_add_defs)
  from this
  obtain r i
    where rcarr: "r \<in> carrier R"
      and iI: "i \<in> I"
      and one: "\<one> = r \<otimes> a \<oplus> i"
    by fast
  from one and rcarr and acarr and iI[THEN a_Hcarr]
  have rai1: "a \<otimes> r = \<ominus>i \<oplus> \<one>" by algebra

  --{* Lifting to cosets *}
  from iI
  have "\<ominus>i \<oplus> \<one> \<in> I +> \<one>"
    by (intro a_rcosI, simp, intro a_subset, simp)
  from this and rai1
  have "a \<otimes> r \<in> I +> \<one>" by simp
  from this have "I +> \<one> = I +> a \<otimes> r"
    by (rule a_repr_independence, simp) (rule a_subgroup)

  from rcarr and this[symmetric]
  show "\<exists>r\<in>carrier R. I +> a \<otimes> r = I +> \<one>" by fast
qed

end
