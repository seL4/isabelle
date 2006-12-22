(*
  Title:     HOL/Algebra/IntRing.thy
  Id:        $Id$
  Author:    Stephan Hohe, TU Muenchen
*)

theory IntRing
imports QuotRing IntDef
begin


section {* The Ring of Integers *}

subsection {* Some properties of @{typ int} *}

lemma dvds_imp_abseq:
  "\<lbrakk>l dvd k; k dvd l\<rbrakk> \<Longrightarrow> abs l = abs (k::int)"
apply (subst abs_split, rule conjI)
 apply (clarsimp, subst abs_split, rule conjI)
  apply (clarsimp)
  apply (cases "k=0", simp)
  apply (cases "l=0", simp)
  apply (simp add: zdvd_anti_sym)
 apply clarsimp
 apply (cases "k=0", simp)
 apply (simp add: zdvd_anti_sym)
apply (clarsimp, subst abs_split, rule conjI)
 apply (clarsimp)
 apply (cases "l=0", simp)
 apply (simp add: zdvd_anti_sym)
apply (clarsimp)
apply (subgoal_tac "-l = -k", simp)
apply (intro zdvd_anti_sym, simp+)
done

lemma abseq_imp_dvd:
  assumes a_lk: "abs l = abs (k::int)"
  shows "l dvd k"
proof -
  from a_lk
      have "nat (abs l) = nat (abs k)" by simp
  hence "nat (abs l) dvd nat (abs k)" by simp
  hence "int (nat (abs l)) dvd k" by (subst int_dvd_iff)
  hence "abs l dvd k" by simp
  thus "l dvd k" 
  apply (unfold dvd_def, cases "l<0")
   defer 1 apply clarsimp
  proof (clarsimp)
    fix k
    assume l0: "l < 0"
    have "- (l * k) = l * (-k)" by simp
    thus "\<exists>ka. - (l * k) = l * ka" by fast
  qed
qed

lemma dvds_eq_abseq:
  "(l dvd k \<and> k dvd l) = (abs l = abs (k::int))"
apply rule
 apply (simp add: dvds_imp_abseq)
apply (rule conjI)
 apply (simp add: abseq_imp_dvd)+
done



subsection {* The Set of Integers as Algebraic Structure *}

subsubsection {* Definition of @{text "\<Z>"} *}

constdefs
  int_ring :: "int ring" ("\<Z>")
  "int_ring \<equiv> \<lparr>carrier = UNIV, mult = op *, one = 1, zero = 0, add = op +\<rparr>"

lemma int_Zcarr[simp,intro!]:
  "k \<in> carrier \<Z>"
by (simp add: int_ring_def)

lemma int_is_cring:
  "cring \<Z>"
unfolding int_ring_def
apply (rule cringI)
  apply (rule abelian_groupI, simp_all)
  defer 1
  apply (rule comm_monoidI, simp_all)
 apply (rule zadd_zmult_distrib)
apply (fast intro: zadd_zminus_inverse2)
done

lemma int_is_domain:
  "domain \<Z>"
apply (intro domain.intro domain_axioms.intro)
  apply (rule int_is_cring)
 apply (unfold int_ring_def, simp+)
done

interpretation "domain" ["\<Z>"] by (rule int_is_domain)

lemma int_le_total_order:
  "total_order (UNIV::int set) (op \<le>)"
apply (rule partial_order.total_orderI)
 apply (rule partial_order.intro, simp+)
apply clarsimp
done

lemma less_int:
  "order_syntax.less (op \<le>::[int, int] => bool) = (op <)"
  by (auto simp add: expand_fun_eq order_syntax.less_def)

lemma join_int:
  "order_syntax.join (UNIV::int set) (op \<le>) = max"
  apply (simp add: expand_fun_eq max_def)
  apply (rule+)
  apply (rule lattice.joinI)
  apply (simp add: int_le_total_order total_order.axioms)
  apply (simp add: order_syntax.least_def order_syntax.Upper_def)
  apply arith
  apply simp apply simp
  apply (rule lattice.joinI)
  apply (simp add: int_le_total_order total_order.axioms)
  apply (simp add: order_syntax.least_def order_syntax.Upper_def)
  apply arith
  apply simp apply simp
  done

lemma meet_int:
  "order_syntax.meet (UNIV::int set) (op \<le>) = min"
  apply (simp add: expand_fun_eq min_def)
  apply (rule+)
  apply (rule lattice.meetI)
  apply (simp add: int_le_total_order total_order.axioms)
  apply (simp add: order_syntax.greatest_def order_syntax.Lower_def)
  apply arith
  apply simp apply simp
  apply (rule lattice.meetI)
  apply (simp add: int_le_total_order total_order.axioms)
  apply (simp add: order_syntax.greatest_def order_syntax.Lower_def)
  apply arith
  apply simp apply simp
  done

text {* Interpretation unfolding @{text less}, @{text join} and @{text
  meet} since they have natural representations in @{typ int}. *}

interpretation 
  int [unfolded less_int join_int meet_int]:
  total_order ["UNIV::int set" "op \<le>"] by (rule int_le_total_order)


subsubsection {* Generated Ideals of @{text "\<Z>"} *}

lemma int_Idl:
  "Idl\<^bsub>\<Z>\<^esub> {a} = {x * a | x. True}"
apply (subst cgenideal_eq_genideal[symmetric], simp add: int_ring_def)
apply (simp add: cgenideal_def int_ring_def)
done

lemma multiples_principalideal:
  "principalideal {x * a | x. True } \<Z>"
apply (subst int_Idl[symmetric], rule principalidealI)
 apply (rule genideal_ideal, simp)
apply fast
done

lemma prime_primeideal:
  assumes prime: "prime (nat p)"
  shows "primeideal (Idl\<^bsub>\<Z>\<^esub> {p}) \<Z>"
apply (rule primeidealI)
   apply (rule genideal_ideal, simp)
  apply (rule int_is_cring)
 apply (simp add: cgenideal_eq_genideal[symmetric] cgenideal_def)
 apply (simp add: int_ring_def)
 apply clarsimp defer 1
 apply (simp add: cgenideal_eq_genideal[symmetric] cgenideal_def)
 apply (simp add: int_ring_def)
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
  hence "nat p dvd nat (abs (a * b))"
  apply (subst nat_dvd_iff, clarsimp)
  apply (rule conjI, clarsimp, simp add: zabs_def)
  proof (clarsimp)
    assume a: " ~ 0 <= p"
    from prime
        have "0 < p" by (simp add: prime_def)
    from a and this
        have "False" by simp
    thus "nat (abs (a * b)) = 0" ..
  qed
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
      where "1 = x * p" by fast
  from this [symmetric]
      have "p * x = 1" by (subst zmult_commute)
  hence "\<bar>p * x\<bar> = 1" by simp
  hence "\<bar>p\<bar> = 1" by (rule abs_zmult_eq_1)
  from this and prime
      show "False" by (simp add: prime_def)
qed


subsubsection {* Ideals and Divisibility *}

lemma int_Idl_subset_ideal:
  "Idl\<^bsub>\<Z>\<^esub> {k} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {l} = (k \<in> Idl\<^bsub>\<Z>\<^esub> {l})"
by (rule Idl_subset_ideal', simp+)

lemma Idl_subset_eq_dvd:
  "(Idl\<^bsub>\<Z>\<^esub> {k} \<subseteq> Idl\<^bsub>\<Z>\<^esub> {l}) = (l dvd k)"
apply (subst int_Idl_subset_ideal, subst int_Idl, simp)
apply (rule, clarify)
apply (simp add: dvd_def, clarify)
apply (simp add: m_comm)
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


subsubsection {* Ideals and the Modulus *}

constdefs
   ZMod :: "int => int => int set"
  "ZMod k r == (Idl\<^bsub>\<Z>\<^esub> {k}) +>\<^bsub>\<Z>\<^esub> r"

lemmas ZMod_defs =
  ZMod_def genideal_def

lemma rcos_zfact:
  assumes kIl: "k \<in> ZMod l r"
  shows "EX x. k = x * l + r"
proof -
  from kIl[unfolded ZMod_def]
      have "\<exists>xl\<in>Idl\<^bsub>\<Z>\<^esub> {l}. k = xl + r" by (simp add: a_r_coset_defs int_ring_def)
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
  interpret ideal ["Idl\<^bsub>\<Z>\<^esub> {m}" \<Z>] by (rule genideal_ideal, fast)
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
      have "\<dots> = ((x * m) mod m) + (a mod m)" by (simp add: zmod_zadd1_eq)
  also
      have "\<dots> = a mod m" by simp
  finally
      have "b mod m = a mod m" .
  thus "a mod m = b mod m" ..
qed

lemma ZMod_mod:
  shows "ZMod m a = ZMod m (a mod m)"
proof -
  interpret ideal ["Idl\<^bsub>\<Z>\<^esub> {m}" \<Z>] by (rule genideal_ideal, fast)
  show ?thesis
      unfolding ZMod_def
  apply (rule a_repr_independence'[symmetric])
  apply (simp add: int_Idl a_r_coset_defs)
  apply (simp add: int_ring_def)
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


subsubsection {* Factorization *}

constdefs
  ZFact :: "int \<Rightarrow> int set ring"
  "ZFact k == \<Z> Quot (Idl\<^bsub>\<Z>\<^esub> {k})"

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
apply (insert genideal_zero)
apply (simp add: ZFact_defs A_RCOSETS_defs r_coset_def int_ring_def ring_record_simps)
done

lemma ZFact_one:
  "carrier (ZFact 1) = {UNIV}"
apply (simp only: ZFact_defs A_RCOSETS_defs r_coset_def int_ring_def ring_record_simps)
apply (subst genideal_one[unfolded int_ring_def, simplified ring_record_simps])
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
