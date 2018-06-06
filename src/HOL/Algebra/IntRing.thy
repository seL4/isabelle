(*  Title:      HOL/Algebra/IntRing.thy
    Author:     Stephan Hohe, TU Muenchen
    Author:     Clemens Ballarin
*)

theory IntRing
imports "HOL-Computational_Algebra.Primes" QuotRing Lattice 
begin

section \<open>The Ring of Integers\<close>

subsection \<open>Some properties of @{typ int}\<close>

lemma dvds_eq_abseq:
  fixes k :: int
  shows "l dvd k \<and> k dvd l \<longleftrightarrow> \<bar>l\<bar> = \<bar>k\<bar>"
apply rule
 apply (simp add: zdvd_antisym_abs)
apply (simp add: dvd_if_abs_eq)
done


subsection \<open>\<open>\<Z>\<close>: The Set of Integers as Algebraic Structure\<close>

abbreviation int_ring :: "int ring" ("\<Z>")
  where "int_ring \<equiv> \<lparr>carrier = UNIV, mult = ( * ), one = 1, zero = 0, add = (+)\<rparr>"

lemma int_Zcarr [intro!, simp]: "k \<in> carrier \<Z>"
  by simp

lemma int_is_cring: "cring \<Z>"
apply (rule cringI)
  apply (rule abelian_groupI, simp_all)
  defer 1
  apply (rule comm_monoidI, simp_all)
 apply (rule distrib_right)
apply (fast intro: left_minus)
done

(*
lemma int_is_domain:
  "domain \<Z>"
apply (intro domain.intro domain_axioms.intro)
  apply (rule int_is_cring)
 apply (unfold int_ring_def, simp+)
done
*)


subsection \<open>Interpretations\<close>

text \<open>Since definitions of derived operations are global, their
  interpretation needs to be done as early as possible --- that is,
  with as few assumptions as possible.\<close>

interpretation int: monoid \<Z>
  rewrites "carrier \<Z> = UNIV"
    and "mult \<Z> x y = x * y"
    and "one \<Z> = 1"
    and "pow \<Z> x n = x^n"
proof -
  \<comment> \<open>Specification\<close>
  show "monoid \<Z>" by standard auto
  then interpret int: monoid \<Z> .

  \<comment> \<open>Carrier\<close>
  show "carrier \<Z> = UNIV" by simp

  \<comment> \<open>Operations\<close>
  { fix x y show "mult \<Z> x y = x * y" by simp }
  show "one \<Z> = 1" by simp
  show "pow \<Z> x n = x^n" by (induct n) simp_all
qed

interpretation int: comm_monoid \<Z>
  rewrites "finprod \<Z> f A = prod f A"
proof -
  \<comment> \<open>Specification\<close>
  show "comm_monoid \<Z>" by standard auto
  then interpret int: comm_monoid \<Z> .

  \<comment> \<open>Operations\<close>
  { fix x y have "mult \<Z> x y = x * y" by simp }
  note mult = this
  have one: "one \<Z> = 1" by simp
  show "finprod \<Z> f A = prod f A"
    by (induct A rule: infinite_finite_induct, auto)
qed

interpretation int: abelian_monoid \<Z>
  rewrites int_carrier_eq: "carrier \<Z> = UNIV"
    and int_zero_eq: "zero \<Z> = 0"
    and int_add_eq: "add \<Z> x y = x + y"
    and int_finsum_eq: "finsum \<Z> f A = sum f A"
proof -
  \<comment> \<open>Specification\<close>
  show "abelian_monoid \<Z>" by standard auto
  then interpret int: abelian_monoid \<Z> .

  \<comment> \<open>Carrier\<close>
  show "carrier \<Z> = UNIV" by simp

  \<comment> \<open>Operations\<close>
  { fix x y show "add \<Z> x y = x + y" by simp }
  note add = this
  show zero: "zero \<Z> = 0"
    by simp
  show "finsum \<Z> f A = sum f A"
    by (induct A rule: infinite_finite_induct, auto)
qed

interpretation int: abelian_group \<Z>
  (* The equations from the interpretation of abelian_monoid need to be repeated.
     Since the morphisms through which the abelian structures are interpreted are
     not the identity, the equations of these interpretations are not inherited. *)
  (* FIXME *)
  rewrites "carrier \<Z> = UNIV"
    and "zero \<Z> = 0"
    and "add \<Z> x y = x + y"
    and "finsum \<Z> f A = sum f A"
    and int_a_inv_eq: "a_inv \<Z> x = - x"
    and int_a_minus_eq: "a_minus \<Z> x y = x - y"
proof -
  \<comment> \<open>Specification\<close>
  show "abelian_group \<Z>"
  proof (rule abelian_groupI)
    fix x
    assume "x \<in> carrier \<Z>"
    then show "\<exists>y \<in> carrier \<Z>. y \<oplus>\<^bsub>\<Z>\<^esub> x = \<zero>\<^bsub>\<Z>\<^esub>"
      by simp arith
  qed auto
  then interpret int: abelian_group \<Z> .
  \<comment> \<open>Operations\<close>
  { fix x y have "add \<Z> x y = x + y" by simp }
  note add = this
  have zero: "zero \<Z> = 0" by simp
  {
    fix x
    have "add \<Z> (- x) x = zero \<Z>"
      by (simp add: add zero)
    then show "a_inv \<Z> x = - x"
      by (simp add: int.minus_equality)
  }
  note a_inv = this
  show "a_minus \<Z> x y = x - y"
    by (simp add: int.minus_eq add a_inv)
qed (simp add: int_carrier_eq int_zero_eq int_add_eq int_finsum_eq)+

interpretation int: "domain" \<Z>
  rewrites "carrier \<Z> = UNIV"
    and "zero \<Z> = 0"
    and "add \<Z> x y = x + y"
    and "finsum \<Z> f A = sum f A"
    and "a_inv \<Z> x = - x"
    and "a_minus \<Z> x y = x - y"
proof -
  show "domain \<Z>"
    by unfold_locales (auto simp: distrib_right distrib_left)
qed (simp add: int_carrier_eq int_zero_eq int_add_eq int_finsum_eq int_a_inv_eq int_a_minus_eq)+


text \<open>Removal of occurrences of @{term UNIV} in interpretation result
  --- experimental.\<close>

lemma UNIV:
  "x \<in> UNIV \<longleftrightarrow> True"
  "A \<subseteq> UNIV \<longleftrightarrow> True"
  "(\<forall>x \<in> UNIV. P x) \<longleftrightarrow> (\<forall>x. P x)"
  "(\<exists>x \<in> UNIV. P x) \<longleftrightarrow> (\<exists>x. P x)"
  "(True \<longrightarrow> Q) \<longleftrightarrow> Q"
  "(True \<Longrightarrow> PROP R) \<equiv> PROP R"
  by simp_all

interpretation int (* FIXME [unfolded UNIV] *) :
  partial_order "\<lparr>carrier = UNIV::int set, eq = (=), le = (\<le>)\<rparr>"
  rewrites "carrier \<lparr>carrier = UNIV::int set, eq = (=), le = (\<le>)\<rparr> = UNIV"
    and "le \<lparr>carrier = UNIV::int set, eq = (=), le = (\<le>)\<rparr> x y = (x \<le> y)"
    and "lless \<lparr>carrier = UNIV::int set, eq = (=), le = (\<le>)\<rparr> x y = (x < y)"
proof -
  show "partial_order \<lparr>carrier = UNIV::int set, eq = (=), le = (\<le>)\<rparr>"
    by standard simp_all
  show "carrier \<lparr>carrier = UNIV::int set, eq = (=), le = (\<le>)\<rparr> = UNIV"
    by simp
  show "le \<lparr>carrier = UNIV::int set, eq = (=), le = (\<le>)\<rparr> x y = (x \<le> y)"
    by simp
  show "lless \<lparr>carrier = UNIV::int set, eq = (=), le = (\<le>)\<rparr> x y = (x < y)"
    by (simp add: lless_def) auto
qed

interpretation int (* FIXME [unfolded UNIV] *) :
  lattice "\<lparr>carrier = UNIV::int set, eq = (=), le = (\<le>)\<rparr>"
  rewrites "join \<lparr>carrier = UNIV::int set, eq = (=), le = (\<le>)\<rparr> x y = max x y"
    and "meet \<lparr>carrier = UNIV::int set, eq = (=), le = (\<le>)\<rparr> x y = min x y"
proof -
  let ?Z = "\<lparr>carrier = UNIV::int set, eq = (=), le = (\<le>)\<rparr>"
  show "lattice ?Z"
    apply unfold_locales
    apply (simp add: least_def Upper_def)
    apply arith
    apply (simp add: greatest_def Lower_def)
    apply arith
    done
  then interpret int: lattice "?Z" .
  show "join ?Z x y = max x y"
    apply (rule int.joinI)
    apply (simp_all add: least_def Upper_def)
    apply arith
    done
  show "meet ?Z x y = min x y"
    apply (rule int.meetI)
    apply (simp_all add: greatest_def Lower_def)
    apply arith
    done
qed

interpretation int (* [unfolded UNIV] *) :
  total_order "\<lparr>carrier = UNIV::int set, eq = (=), le = (\<le>)\<rparr>"
  by standard clarsimp


subsection \<open>Generated Ideals of \<open>\<Z>\<close>\<close>

lemma int_Idl: "Idl\<^bsub>\<Z>\<^esub> {a} = {x * a | x. True}"
  apply (subst int.cgenideal_eq_genideal[symmetric]) apply simp
  apply (simp add: cgenideal_def)
  done

lemma multiples_principalideal: "principalideal {x * a | x. True } \<Z>"
  by (metis UNIV_I int.cgenideal_eq_genideal int.cgenideal_is_principalideal int_Idl)

lemma prime_primeideal:
  assumes prime: "Factorial_Ring.prime p"
  shows "primeideal (Idl\<^bsub>\<Z>\<^esub> {p}) \<Z>"
apply (rule primeidealI)
   apply (rule int.genideal_ideal, simp)
  apply (rule int_is_cring)
 apply (simp add: int.cgenideal_eq_genideal[symmetric] cgenideal_def)
 apply clarsimp defer 1
 apply (simp add: int.cgenideal_eq_genideal[symmetric] cgenideal_def)
 apply (elim exE)
proof -
  fix a b x
  assume "a * b = x * p"
  then have "p dvd a * b" by simp
  then have "p dvd a \<or> p dvd b"
    by (metis prime prime_dvd_mult_eq_int)
  then show "(\<exists>x. a = x * p) \<or> (\<exists>x. b = x * p)"
    by (metis dvd_def mult.commute)
next
  assume "UNIV = {uu. \<exists>x. uu = x * p}"
  then obtain x where "1 = x * p"
    by best
  then have "\<bar>p * x\<bar> = 1"
    by (simp add: ac_simps)
  then show False using prime
    by (auto simp add: abs_mult zmult_eq_1_iff)
qed


subsection \<open>Ideals and Divisibility\<close>

lemma int_Idl_subset_ideal: "Idl\<^bsub>\<Z>\<^esub> {k} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {l} = (k \<in> Idl\<^bsub>\<Z>\<^esub> {l})"
  by (rule int.Idl_subset_ideal') simp_all

lemma Idl_subset_eq_dvd: "Idl\<^bsub>\<Z>\<^esub> {k} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {l} \<longleftrightarrow> l dvd k"
  apply (subst int_Idl_subset_ideal, subst int_Idl, simp)
  apply (rule, clarify)
  apply (simp add: dvd_def)
  apply (simp add: dvd_def ac_simps)
  done

lemma dvds_eq_Idl: "l dvd k \<and> k dvd l \<longleftrightarrow> Idl\<^bsub>\<Z>\<^esub> {k} = Idl\<^bsub>\<Z>\<^esub> {l}"
proof -
  have a: "l dvd k \<longleftrightarrow> (Idl\<^bsub>\<Z>\<^esub> {k} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {l})"
    by (rule Idl_subset_eq_dvd[symmetric])
  have b: "k dvd l \<longleftrightarrow> (Idl\<^bsub>\<Z>\<^esub> {l} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {k})"
    by (rule Idl_subset_eq_dvd[symmetric])

  have "l dvd k \<and> k dvd l \<longleftrightarrow> Idl\<^bsub>\<Z>\<^esub> {k} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {l} \<and> Idl\<^bsub>\<Z>\<^esub> {l} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {k}"
    by (subst a, subst b, simp)
  also have "Idl\<^bsub>\<Z>\<^esub> {k} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {l} \<and> Idl\<^bsub>\<Z>\<^esub> {l} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {k} \<longleftrightarrow> Idl\<^bsub>\<Z>\<^esub> {k} = Idl\<^bsub>\<Z>\<^esub> {l}"
    by blast
  finally show ?thesis .
qed

lemma Idl_eq_abs: "Idl\<^bsub>\<Z>\<^esub> {k} = Idl\<^bsub>\<Z>\<^esub> {l} \<longleftrightarrow> \<bar>l\<bar> = \<bar>k\<bar>"
  apply (subst dvds_eq_abseq[symmetric])
  apply (rule dvds_eq_Idl[symmetric])
  done


subsection \<open>Ideals and the Modulus\<close>

definition ZMod :: "int \<Rightarrow> int \<Rightarrow> int set"
  where "ZMod k r = (Idl\<^bsub>\<Z>\<^esub> {k}) +>\<^bsub>\<Z>\<^esub> r"

lemmas ZMod_defs =
  ZMod_def genideal_def

lemma rcos_zfact:
  assumes kIl: "k \<in> ZMod l r"
  shows "\<exists>x. k = x * l + r"
proof -
  from kIl[unfolded ZMod_def] have "\<exists>xl\<in>Idl\<^bsub>\<Z>\<^esub> {l}. k = xl + r"
    by (simp add: a_r_coset_defs)
  then obtain xl where xl: "xl \<in> Idl\<^bsub>\<Z>\<^esub> {l}" and k: "k = xl + r"
    by auto
  from xl obtain x where "xl = x * l"
    by (auto simp: int_Idl)
  with k have "k = x * l + r"
    by simp
  then show "\<exists>x. k = x * l + r" ..
qed

lemma ZMod_imp_zmod:
  assumes zmods: "ZMod m a = ZMod m b"
  shows "a mod m = b mod m"
proof -
  interpret ideal "Idl\<^bsub>\<Z>\<^esub> {m}" \<Z>
    by (rule int.genideal_ideal) fast
  from zmods have "b \<in> ZMod m a"
    unfolding ZMod_def by (simp add: a_repr_independenceD)
  then have "\<exists>x. b = x * m + a"
    by (rule rcos_zfact)
  then obtain x where "b = x * m + a"
    by fast
  then have "b mod m = (x * m + a) mod m"
    by simp
  also have "\<dots> = ((x * m) mod m) + (a mod m)"
    by (simp add: mod_add_eq)
  also have "\<dots> = a mod m"
    by simp
  finally have "b mod m = a mod m" .
  then show "a mod m = b mod m" ..
qed

lemma ZMod_mod: "ZMod m a = ZMod m (a mod m)"
proof -
  interpret ideal "Idl\<^bsub>\<Z>\<^esub> {m}" \<Z>
    by (rule int.genideal_ideal) fast
  show ?thesis
    unfolding ZMod_def
    apply (rule a_repr_independence'[symmetric])
    apply (simp add: int_Idl a_r_coset_defs)
  proof -
    have "a = m * (a div m) + (a mod m)"
      by (simp add: mult_div_mod_eq [symmetric])
    then have "a = (a div m) * m + (a mod m)"
      by simp
    then show "\<exists>h. (\<exists>x. h = x * m) \<and> a = h + a mod m"
      by fast
  qed simp
qed

lemma zmod_imp_ZMod:
  assumes modeq: "a mod m = b mod m"
  shows "ZMod m a = ZMod m b"
proof -
  have "ZMod m a = ZMod m (a mod m)"
    by (rule ZMod_mod)
  also have "\<dots> = ZMod m (b mod m)"
    by (simp add: modeq[symmetric])
  also have "\<dots> = ZMod m b"
    by (rule ZMod_mod[symmetric])
  finally show ?thesis .
qed

corollary ZMod_eq_mod: "ZMod m a = ZMod m b \<longleftrightarrow> a mod m = b mod m"
  apply (rule iffI)
  apply (erule ZMod_imp_zmod)
  apply (erule zmod_imp_ZMod)
  done


subsection \<open>Factorization\<close>

definition ZFact :: "int \<Rightarrow> int set ring"
  where "ZFact k = \<Z> Quot (Idl\<^bsub>\<Z>\<^esub> {k})"

lemmas ZFact_defs = ZFact_def FactRing_def

lemma ZFact_is_cring: "cring (ZFact k)"
  apply (unfold ZFact_def)
  apply (rule ideal.quotient_is_cring)
   apply (intro ring.genideal_ideal)
    apply (simp add: cring.axioms[OF int_is_cring] ring.intro)
   apply simp
  apply (rule int_is_cring)
  done

lemma ZFact_zero: "carrier (ZFact 0) = (\<Union>a. {{a}})"
  apply (insert int.genideal_zero)
  apply (simp add: ZFact_defs A_RCOSETS_defs r_coset_def)
  done

lemma ZFact_one: "carrier (ZFact 1) = {UNIV}"
  apply (simp only: ZFact_defs A_RCOSETS_defs r_coset_def ring_record_simps)
  apply (subst int.genideal_one)
  apply (rule, rule, clarsimp)
   apply (rule, rule, clarsimp)
   apply (rule, clarsimp, arith)
  apply (rule, clarsimp)
  apply (rule exI[of _ "0"], clarsimp)
  done

lemma ZFact_prime_is_domain:
  assumes pprime: "Factorial_Ring.prime p"
  shows "domain (ZFact p)"
  apply (unfold ZFact_def)
  apply (rule primeideal.quotient_is_domain)
  apply (rule prime_primeideal[OF pprime])
  done

end
