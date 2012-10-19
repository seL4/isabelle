(*  Title:      HOL/Algebra/IntRing.thy
    Author:     Stephan Hohe, TU Muenchen
    Author:     Clemens Ballarin
*)

theory IntRing
imports QuotRing Lattice Int "~~/src/HOL/Old_Number_Theory/Primes"
begin

section {* The Ring of Integers *}

subsection {* Some properties of @{typ int} *}

lemma dvds_eq_abseq:
  "(l dvd k \<and> k dvd l) = (abs l = abs (k::int))"
apply rule
 apply (simp add: zdvd_antisym_abs)
apply (simp add: dvd_if_abs_eq)
done


subsection {* @{text "\<Z>"}: The Set of Integers as Algebraic Structure *}

abbreviation
  int_ring :: "int ring" ("\<Z>") where
  "int_ring == (| carrier = UNIV, mult = op *, one = 1, zero = 0, add = op + |)"

lemma int_Zcarr [intro!, simp]:
  "k \<in> carrier \<Z>"
  by simp

lemma int_is_cring:
  "cring \<Z>"
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


subsection {* Interpretations *}

text {* Since definitions of derived operations are global, their
  interpretation needs to be done as early as possible --- that is,
  with as few assumptions as possible. *}

interpretation int: monoid \<Z>
  where "carrier \<Z> = UNIV"
    and "mult \<Z> x y = x * y"
    and "one \<Z> = 1"
    and "pow \<Z> x n = x^n"
proof -
  -- "Specification"
  show "monoid \<Z>" by default auto
  then interpret int: monoid \<Z> .

  -- "Carrier"
  show "carrier \<Z> = UNIV" by simp

  -- "Operations"
  { fix x y show "mult \<Z> x y = x * y" by simp }
  note mult = this
  show one: "one \<Z> = 1" by simp
  show "pow \<Z> x n = x^n" by (induct n) simp_all
qed

interpretation int: comm_monoid \<Z>
  where "finprod \<Z> f A = (if finite A then setprod f A else undefined)"
proof -
  -- "Specification"
  show "comm_monoid \<Z>" by default auto
  then interpret int: comm_monoid \<Z> .

  -- "Operations"
  { fix x y have "mult \<Z> x y = x * y" by simp }
  note mult = this
  have one: "one \<Z> = 1" by simp
  show "finprod \<Z> f A = (if finite A then setprod f A else undefined)"
  proof (cases "finite A")
    case True then show ?thesis proof induct
      case empty show ?case by (simp add: one)
    next
      case insert then show ?case by (simp add: Pi_def mult)
    qed
  next
    case False then show ?thesis by (simp add: finprod_def)
  qed
qed

interpretation int: abelian_monoid \<Z>
  where int_carrier_eq: "carrier \<Z> = UNIV"
    and int_zero_eq: "zero \<Z> = 0"
    and int_add_eq: "add \<Z> x y = x + y"
    and int_finsum_eq: "finsum \<Z> f A = (if finite A then setsum f A else undefined)"
proof -
  -- "Specification"
  show "abelian_monoid \<Z>" by default auto
  then interpret int: abelian_monoid \<Z> .

  -- "Carrier"
  show "carrier \<Z> = UNIV" by simp

  -- "Operations"
  { fix x y show "add \<Z> x y = x + y" by simp }
  note add = this
  show zero: "zero \<Z> = 0" by simp
  show "finsum \<Z> f A = (if finite A then setsum f A else undefined)"
  proof (cases "finite A")
    case True then show ?thesis proof induct
      case empty show ?case by (simp add: zero)
    next
      case insert then show ?case by (simp add: Pi_def add)
    qed
  next
    case False then show ?thesis by (simp add: finsum_def finprod_def)
  qed
qed

interpretation int: abelian_group \<Z>
  (* The equations from the interpretation of abelian_monoid need to be repeated.
     Since the morphisms through which the abelian structures are interpreted are
     not the identity, the equations of these interpretations are not inherited. *)
  (* FIXME *)
  where "carrier \<Z> = UNIV"
    and "zero \<Z> = 0"
    and "add \<Z> x y = x + y"
    and "finsum \<Z> f A = (if finite A then setsum f A else undefined)"
    and int_a_inv_eq: "a_inv \<Z> x = - x"
    and int_a_minus_eq: "a_minus \<Z> x y = x - y"
proof -
  -- "Specification"
  show "abelian_group \<Z>"
  proof (rule abelian_groupI)
    show "!!x. x \<in> carrier \<Z> ==> EX y : carrier \<Z>. y \<oplus>\<^bsub>\<Z>\<^esub> x = \<zero>\<^bsub>\<Z>\<^esub>"
      by simp arith
  qed auto
  then interpret int: abelian_group \<Z> .
  -- "Operations"
  { fix x y have "add \<Z> x y = x + y" by simp }
  note add = this
  have zero: "zero \<Z> = 0" by simp
  { fix x
    have "add \<Z> (-x) x = zero \<Z>" by (simp add: add zero)
    then show "a_inv \<Z> x = - x" by (simp add: int.minus_equality) }
  note a_inv = this
  show "a_minus \<Z> x y = x - y" by (simp add: int.minus_eq add a_inv)
qed (simp add: int_carrier_eq int_zero_eq int_add_eq int_finsum_eq)+

interpretation int: "domain" \<Z>
  where "carrier \<Z> = UNIV"
    and "zero \<Z> = 0"
    and "add \<Z> x y = x + y"
    and "finsum \<Z> f A = (if finite A then setsum f A else undefined)"
    and "a_inv \<Z> x = - x"
    and "a_minus \<Z> x y = x - y"
proof -
  show "domain \<Z>" by unfold_locales (auto simp: distrib_right distrib_left)
qed (simp
    add: int_carrier_eq int_zero_eq int_add_eq int_finsum_eq int_a_inv_eq int_a_minus_eq)+


text {* Removal of occurrences of @{term UNIV} in interpretation result
  --- experimental. *}

lemma UNIV:
  "x \<in> UNIV = True"
  "A \<subseteq> UNIV = True"
  "(ALL x : UNIV. P x) = (ALL x. P x)"
  "(EX x : UNIV. P x) = (EX x. P x)"
  "(True --> Q) = Q"
  "(True ==> PROP R) == PROP R"
  by simp_all

interpretation int (* FIXME [unfolded UNIV] *) :
  partial_order "(| carrier = UNIV::int set, eq = op =, le = op \<le> |)"
  where "carrier (| carrier = UNIV::int set, eq = op =, le = op \<le> |) = UNIV"
    and "le (| carrier = UNIV::int set, eq = op =, le = op \<le> |) x y = (x \<le> y)"
    and "lless (| carrier = UNIV::int set, eq = op =, le = op \<le> |) x y = (x < y)"
proof -
  show "partial_order (| carrier = UNIV::int set, eq = op =, le = op \<le> |)"
    by default simp_all
  show "carrier (| carrier = UNIV::int set, eq = op =, le = op \<le> |) = UNIV"
    by simp
  show "le (| carrier = UNIV::int set, eq = op =, le = op \<le> |) x y = (x \<le> y)"
    by simp
  show "lless (| carrier = UNIV::int set, eq = op =, le = op \<le> |) x y = (x < y)"
    by (simp add: lless_def) auto
qed

interpretation int (* FIXME [unfolded UNIV] *) :
  lattice "(| carrier = UNIV::int set, eq = op =, le = op \<le> |)"
  where "join (| carrier = UNIV::int set, eq = op =, le = op \<le> |) x y = max x y"
    and "meet (| carrier = UNIV::int set, eq = op =, le = op \<le> |) x y = min x y"
proof -
  let ?Z = "(| carrier = UNIV::int set, eq = op =, le = op \<le> |)"
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
  total_order "(| carrier = UNIV::int set, eq = op =, le = op \<le> |)"
  by default clarsimp


subsection {* Generated Ideals of @{text "\<Z>"} *}

lemma int_Idl:
  "Idl\<^bsub>\<Z>\<^esub> {a} = {x * a | x. True}"
  apply (subst int.cgenideal_eq_genideal[symmetric]) apply simp
  apply (simp add: cgenideal_def)
  done

lemma multiples_principalideal:
  "principalideal {x * a | x. True } \<Z>"
apply (subst int_Idl[symmetric], rule principalidealI)
 apply (rule int.genideal_ideal, simp)
apply fast
done


lemma prime_primeideal:
  assumes prime: "prime (nat p)"
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

  from prime
      have ppos: "0 <= p" by (simp add: prime_def)
  have unnat: "!!x. nat p dvd nat (abs x) ==> p dvd x"
  proof -
    fix x
    assume "nat p dvd nat (abs x)"
    hence "int (nat p) dvd x" by (simp add: int_dvd_iff[symmetric])
    thus "p dvd x" by (simp add: ppos)
  qed


  assume "a * b = x * p"
  hence "p dvd a * b" by simp
  hence "nat p dvd nat (abs (a * b))" using ppos by (simp add: nat_dvd_iff)
  hence "nat p dvd (nat (abs a) * nat (abs b))" by (simp add: nat_abs_mult_distrib)
  hence "nat p dvd nat (abs a) | nat p dvd nat (abs b)" by (rule prime_dvd_mult[OF prime])
  hence "p dvd a | p dvd b" by (fast intro: unnat)
  thus "(EX x. a = x * p) | (EX x. b = x * p)"
  proof
    assume "p dvd a"
    hence "EX x. a = p * x" by (simp add: dvd_def)
    from this obtain x
        where "a = p * x" by fast
    hence "a = x * p" by simp
    hence "EX x. a = x * p" by simp
    thus "(EX x. a = x * p) | (EX x. b = x * p)" ..
  next
    assume "p dvd b"
    hence "EX x. b = p * x" by (simp add: dvd_def)
    from this obtain x
        where "b = p * x" by fast
    hence "b = x * p" by simp
    hence "EX x. b = x * p" by simp
    thus "(EX x. a = x * p) | (EX x. b = x * p)" ..
  qed
next
  assume "UNIV = {uu. EX x. uu = x * p}"
  from this obtain x 
      where "1 = x * p" by best
  from this [symmetric]
      have "p * x = 1" by (subst mult_commute)
  hence "\<bar>p * x\<bar> = 1" by simp
  hence "\<bar>p\<bar> = 1" by (rule abs_zmult_eq_1)
  from this and prime
      show "False" by (simp add: prime_def)
qed


subsection {* Ideals and Divisibility *}

lemma int_Idl_subset_ideal:
  "Idl\<^bsub>\<Z>\<^esub> {k} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {l} = (k \<in> Idl\<^bsub>\<Z>\<^esub> {l})"
by (rule int.Idl_subset_ideal', simp+)

lemma Idl_subset_eq_dvd:
  "(Idl\<^bsub>\<Z>\<^esub> {k} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {l}) = (l dvd k)"
apply (subst int_Idl_subset_ideal, subst int_Idl, simp)
apply (rule, clarify)
apply (simp add: dvd_def)
apply (simp add: dvd_def mult_ac)
done

lemma dvds_eq_Idl:
  "(l dvd k \<and> k dvd l) = (Idl\<^bsub>\<Z>\<^esub> {k} = Idl\<^bsub>\<Z>\<^esub> {l})"
proof -
  have a: "l dvd k = (Idl\<^bsub>\<Z>\<^esub> {k} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {l})" by (rule Idl_subset_eq_dvd[symmetric])
  have b: "k dvd l = (Idl\<^bsub>\<Z>\<^esub> {l} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {k})" by (rule Idl_subset_eq_dvd[symmetric])

  have "(l dvd k \<and> k dvd l) = ((Idl\<^bsub>\<Z>\<^esub> {k} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {l}) \<and> (Idl\<^bsub>\<Z>\<^esub> {l} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {k}))"
  by (subst a, subst b, simp)
  also have "((Idl\<^bsub>\<Z>\<^esub> {k} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {l}) \<and> (Idl\<^bsub>\<Z>\<^esub> {l} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {k})) = (Idl\<^bsub>\<Z>\<^esub> {k} = Idl\<^bsub>\<Z>\<^esub> {l})" by (rule, fast+)
  finally
    show ?thesis .
qed

lemma Idl_eq_abs:
  "(Idl\<^bsub>\<Z>\<^esub> {k} = Idl\<^bsub>\<Z>\<^esub> {l}) = (abs l = abs k)"
apply (subst dvds_eq_abseq[symmetric])
apply (rule dvds_eq_Idl[symmetric])
done


subsection {* Ideals and the Modulus *}

definition
  ZMod :: "int => int => int set"
  where "ZMod k r = (Idl\<^bsub>\<Z>\<^esub> {k}) +>\<^bsub>\<Z>\<^esub> r"

lemmas ZMod_defs =
  ZMod_def genideal_def

lemma rcos_zfact:
  assumes kIl: "k \<in> ZMod l r"
  shows "EX x. k = x * l + r"
proof -
  from kIl[unfolded ZMod_def]
      have "\<exists>xl\<in>Idl\<^bsub>\<Z>\<^esub> {l}. k = xl + r" by (simp add: a_r_coset_defs)
  from this obtain xl
      where xl: "xl \<in> Idl\<^bsub>\<Z>\<^esub> {l}"
      and k: "k = xl + r"
      by auto
  from xl obtain x
      where "xl = x * l"
      by (simp add: int_Idl, fast)
  from k and this
      have "k = x * l + r" by simp
  thus "\<exists>x. k = x * l + r" ..
qed

lemma ZMod_imp_zmod:
  assumes zmods: "ZMod m a = ZMod m b"
  shows "a mod m = b mod m"
proof -
  interpret ideal "Idl\<^bsub>\<Z>\<^esub> {m}" \<Z> by (rule int.genideal_ideal, fast)
  from zmods
      have "b \<in> ZMod m a"
      unfolding ZMod_def
      by (simp add: a_repr_independenceD)
  from this
      have "EX x. b = x * m + a" by (rule rcos_zfact)
  from this obtain x
      where "b = x * m + a"
      by fast

  hence "b mod m = (x * m + a) mod m" by simp
  also
      have "\<dots> = ((x * m) mod m) + (a mod m)" by (simp add: mod_add_eq)
  also
      have "\<dots> = a mod m" by simp
  finally
      have "b mod m = a mod m" .
  thus "a mod m = b mod m" ..
qed

lemma ZMod_mod:
  shows "ZMod m a = ZMod m (a mod m)"
proof -
  interpret ideal "Idl\<^bsub>\<Z>\<^esub> {m}" \<Z> by (rule int.genideal_ideal, fast)
  show ?thesis
      unfolding ZMod_def
  apply (rule a_repr_independence'[symmetric])
  apply (simp add: int_Idl a_r_coset_defs)
  proof -
    have "a = m * (a div m) + (a mod m)" by (simp add: zmod_zdiv_equality)
    hence "a = (a div m) * m + (a mod m)" by simp
    thus "\<exists>h. (\<exists>x. h = x * m) \<and> a = h + a mod m" by fast
  qed simp
qed

lemma zmod_imp_ZMod:
  assumes modeq: "a mod m = b mod m"
  shows "ZMod m a = ZMod m b"
proof -
  have "ZMod m a = ZMod m (a mod m)" by (rule ZMod_mod)
  also have "\<dots> = ZMod m (b mod m)" by (simp add: modeq[symmetric])
  also have "\<dots> = ZMod m b" by (rule ZMod_mod[symmetric])
  finally show ?thesis .
qed

corollary ZMod_eq_mod:
  shows "(ZMod m a = ZMod m b) = (a mod m = b mod m)"
by (rule, erule ZMod_imp_zmod, erule zmod_imp_ZMod)


subsection {* Factorization *}

definition
  ZFact :: "int \<Rightarrow> int set ring"
  where "ZFact k = \<Z> Quot (Idl\<^bsub>\<Z>\<^esub> {k})"

lemmas ZFact_defs = ZFact_def FactRing_def

lemma ZFact_is_cring:
  shows "cring (ZFact k)"
apply (unfold ZFact_def)
apply (rule ideal.quotient_is_cring)
 apply (intro ring.genideal_ideal)
  apply (simp add: cring.axioms[OF int_is_cring] ring.intro)
 apply simp
apply (rule int_is_cring)
done

lemma ZFact_zero:
  "carrier (ZFact 0) = (\<Union>a. {{a}})"
apply (insert int.genideal_zero)
apply (simp add: ZFact_defs A_RCOSETS_defs r_coset_def ring_record_simps)
done

lemma ZFact_one:
  "carrier (ZFact 1) = {UNIV}"
apply (simp only: ZFact_defs A_RCOSETS_defs r_coset_def ring_record_simps)
apply (subst int.genideal_one)
apply (rule, rule, clarsimp)
 apply (rule, rule, clarsimp)
 apply (rule, clarsimp, arith)
apply (rule, clarsimp)
apply (rule exI[of _ "0"], clarsimp)
done

lemma ZFact_prime_is_domain:
  assumes pprime: "prime (nat p)"
  shows "domain (ZFact p)"
apply (unfold ZFact_def)
apply (rule primeideal.quotient_is_domain)
apply (rule prime_primeideal[OF pprime])
done

end
