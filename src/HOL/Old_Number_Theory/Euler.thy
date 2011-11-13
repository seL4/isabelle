(*  Title:      HOL/Old_Number_Theory/Euler.thy
    Authors:    Jeremy Avigad, David Gray, and Adam Kramer
*)

header {* Euler's criterion *}

theory Euler
imports Residues EvenOdd
begin

definition MultInvPair :: "int => int => int => int set"
  where "MultInvPair a p j = {StandardRes p j, StandardRes p (a * (MultInv p j))}"

definition SetS :: "int => int => int set set"
  where "SetS a p = MultInvPair a p ` SRStar p"


subsection {* Property for MultInvPair *}

lemma MultInvPair_prop1a:
  "[| zprime p; 2 < p; ~([a = 0](mod p));
      X \<in> (SetS a p); Y \<in> (SetS a p);
      ~((X \<inter> Y) = {}) |] ==> X = Y"
  apply (auto simp add: SetS_def)
  apply (drule StandardRes_SRStar_prop1a)+ defer 1
  apply (drule StandardRes_SRStar_prop1a)+
  apply (auto simp add: MultInvPair_def StandardRes_prop2 zcong_sym)
  apply (drule notE, rule MultInv_zcong_prop1, auto)[]
  apply (drule notE, rule MultInv_zcong_prop2, auto simp add: zcong_sym)[]
  apply (drule MultInv_zcong_prop2, auto simp add: zcong_sym)[]
  apply (drule MultInv_zcong_prop3, auto simp add: zcong_sym)[]
  apply (drule MultInv_zcong_prop1, auto)[]
  apply (drule MultInv_zcong_prop2, auto simp add: zcong_sym)[]
  apply (drule MultInv_zcong_prop2, auto simp add: zcong_sym)[]
  apply (drule MultInv_zcong_prop3, auto simp add: zcong_sym)[]
  done

lemma MultInvPair_prop1b:
  "[| zprime p; 2 < p; ~([a = 0](mod p));
      X \<in> (SetS a p); Y \<in> (SetS a p);
      X \<noteq> Y |] ==> X \<inter> Y = {}"
  apply (rule notnotD)
  apply (rule notI)
  apply (drule MultInvPair_prop1a, auto)
  done

lemma MultInvPair_prop1c: "[| zprime p; 2 < p; ~([a = 0](mod p)) |] ==>  
    \<forall>X \<in> SetS a p. \<forall>Y \<in> SetS a p. X \<noteq> Y --> X\<inter>Y = {}"
  by (auto simp add: MultInvPair_prop1b)

lemma MultInvPair_prop2: "[| zprime p; 2 < p; ~([a = 0](mod p)) |] ==> 
                          Union ( SetS a p) = SRStar p"
  apply (auto simp add: SetS_def MultInvPair_def StandardRes_SRStar_prop4 
    SRStar_mult_prop2)
  apply (frule StandardRes_SRStar_prop3)
  apply (rule bexI, auto)
  done

lemma MultInvPair_distinct:
  assumes "zprime p" and "2 < p" and
    "~([a = 0] (mod p))" and
    "~([j = 0] (mod p))" and
    "~(QuadRes p a)"
  shows "~([j = a * MultInv p j] (mod p))"
proof
  assume "[j = a * MultInv p j] (mod p)"
  then have "[j * j = (a * MultInv p j) * j] (mod p)"
    by (auto simp add: zcong_scalar)
  then have a:"[j * j = a * (MultInv p j * j)] (mod p)"
    by (auto simp add: mult_ac)
  have "[j * j = a] (mod p)"
  proof -
    from assms(1,2,4) have "[MultInv p j * j = 1] (mod p)"
      by (simp add: MultInv_prop2a)
    from this and a show ?thesis
      by (auto simp add: zcong_zmult_prop2)
  qed
  then have "[j^2 = a] (mod p)" by (simp add: power2_eq_square)
  with assms show False by (simp add: QuadRes_def)
qed

lemma MultInvPair_card_two: "[| zprime p; 2 < p; ~([a = 0] (mod p)); 
                                ~(QuadRes p a); ~([j = 0] (mod p)) |]  ==> 
                             card (MultInvPair a p j) = 2"
  apply (auto simp add: MultInvPair_def)
  apply (subgoal_tac "~ (StandardRes p j = StandardRes p (a * MultInv p j))")
  apply auto
  apply (metis MultInvPair_distinct StandardRes_def aux)
  done


subsection {* Properties of SetS *}

lemma SetS_finite: "2 < p ==> finite (SetS a p)"
  by (auto simp add: SetS_def SRStar_finite [of p])

lemma SetS_elems_finite: "\<forall>X \<in> SetS a p. finite X"
  by (auto simp add: SetS_def MultInvPair_def)

lemma SetS_elems_card: "[| zprime p; 2 < p; ~([a = 0] (mod p)); 
                        ~(QuadRes p a) |]  ==>
                        \<forall>X \<in> SetS a p. card X = 2"
  apply (auto simp add: SetS_def)
  apply (frule StandardRes_SRStar_prop1a)
  apply (rule MultInvPair_card_two, auto)
  done

lemma Union_SetS_finite: "2 < p ==> finite (Union (SetS a p))"
  by (auto simp add: SetS_finite SetS_elems_finite)

lemma card_setsum_aux: "[| finite S; \<forall>X \<in> S. finite (X::int set); 
    \<forall>X \<in> S. card X = n |] ==> setsum card S = setsum (%x. n) S"
  by (induct set: finite) auto

lemma SetS_card:
  assumes "zprime p" and "2 < p" and "~([a = 0] (mod p))" and "~(QuadRes p a)"
  shows "int(card(SetS a p)) = (p - 1) div 2"
proof -
  have "(p - 1) = 2 * int(card(SetS a p))"
  proof -
    have "p - 1 = int(card(Union (SetS a p)))"
      by (auto simp add: assms MultInvPair_prop2 SRStar_card)
    also have "... = int (setsum card (SetS a p))"
      by (auto simp add: assms SetS_finite SetS_elems_finite
        MultInvPair_prop1c [of p a] card_Union_disjoint)
    also have "... = int(setsum (%x.2) (SetS a p))"
      using assms by (auto simp add: SetS_elems_card SetS_finite SetS_elems_finite
        card_setsum_aux simp del: setsum_constant)
    also have "... = 2 * int(card( SetS a p))"
      by (auto simp add: assms SetS_finite setsum_const2)
    finally show ?thesis .
  qed
  then show ?thesis by auto
qed

lemma SetS_setprod_prop: "[| zprime p; 2 < p; ~([a = 0] (mod p));
                              ~(QuadRes p a); x \<in> (SetS a p) |] ==> 
                          [\<Prod>x = a] (mod p)"
  apply (auto simp add: SetS_def MultInvPair_def)
  apply (frule StandardRes_SRStar_prop1a)
  apply (subgoal_tac "StandardRes p x \<noteq> StandardRes p (a * MultInv p x)")
  apply (auto simp add: StandardRes_prop2 MultInvPair_distinct)
  apply (frule_tac m = p and x = x and y = "(a * MultInv p x)" in 
    StandardRes_prop4)
  apply (subgoal_tac "[x * (a * MultInv p x) = a * (x * MultInv p x)] (mod p)")
  apply (drule_tac a = "StandardRes p x * StandardRes p (a * MultInv p x)" and
                   b = "x * (a * MultInv p x)" and
                   c = "a * (x * MultInv p x)" in  zcong_trans, force)
  apply (frule_tac p = p and x = x in MultInv_prop2, auto)
apply (metis StandardRes_SRStar_prop3 mult_1_right mult_commute zcong_sym zcong_zmult_prop1)
  apply (auto simp add: mult_ac)
  done

lemma aux1: "[| 0 < x; (x::int) < a; x \<noteq> (a - 1) |] ==> x < a - 1"
  by arith

lemma aux2: "[| (a::int) < c; b < c |] ==> (a \<le> b | b \<le> a)"
  by auto

lemma d22set_induct_old: "(\<And>a::int. 1 < a \<longrightarrow> P (a - 1) \<Longrightarrow> P a) \<Longrightarrow> P x"
using d22set.induct by blast

lemma SRStar_d22set_prop: "2 < p \<Longrightarrow> (SRStar p) = {1} \<union> (d22set (p - 1))"
  apply (induct p rule: d22set_induct_old)
  apply auto
  apply (simp add: SRStar_def d22set.simps)
  apply (simp add: SRStar_def d22set.simps, clarify)
  apply (frule aux1)
  apply (frule aux2, auto)
  apply (simp_all add: SRStar_def)
  apply (simp add: d22set.simps)
  apply (frule d22set_le)
  apply (frule d22set_g_1, auto)
  done

lemma Union_SetS_setprod_prop1:
  assumes "zprime p" and "2 < p" and "~([a = 0] (mod p))" and
    "~(QuadRes p a)"
  shows "[\<Prod>(Union (SetS a p)) = a ^ nat ((p - 1) div 2)] (mod p)"
proof -
  from assms have "[\<Prod>(Union (SetS a p)) = setprod (setprod (%x. x)) (SetS a p)] (mod p)"
    by (auto simp add: SetS_finite SetS_elems_finite
      MultInvPair_prop1c setprod_Union_disjoint)
  also have "[setprod (setprod (%x. x)) (SetS a p) = 
      setprod (%x. a) (SetS a p)] (mod p)"
    by (rule setprod_same_function_zcong)
      (auto simp add: assms SetS_setprod_prop SetS_finite)
  also (zcong_trans) have "[setprod (%x. a) (SetS a p) = 
      a^(card (SetS a p))] (mod p)"
    by (auto simp add: assms SetS_finite setprod_constant)
  finally (zcong_trans) show ?thesis
    apply (rule zcong_trans)
    apply (subgoal_tac "card(SetS a p) = nat((p - 1) div 2)", auto)
    apply (subgoal_tac "nat(int(card(SetS a p))) = nat((p - 1) div 2)", force)
    apply (auto simp add: assms SetS_card)
    done
qed

lemma Union_SetS_setprod_prop2:
  assumes "zprime p" and "2 < p" and "~([a = 0](mod p))"
  shows "\<Prod>(Union (SetS a p)) = zfact (p - 1)"
proof -
  from assms have "\<Prod>(Union (SetS a p)) = \<Prod>(SRStar p)"
    by (auto simp add: MultInvPair_prop2)
  also have "... = \<Prod>({1} \<union> (d22set (p - 1)))"
    by (auto simp add: assms SRStar_d22set_prop)
  also have "... = zfact(p - 1)"
  proof -
    have "~(1 \<in> d22set (p - 1)) & finite( d22set (p - 1))"
      by (metis d22set_fin d22set_g_1 linorder_neq_iff)
    then have "\<Prod>({1} \<union> (d22set (p - 1))) = \<Prod>(d22set (p - 1))"
      by auto
    then show ?thesis
      by (auto simp add: d22set_prod_zfact)
  qed
  finally show ?thesis .
qed

lemma zfact_prop: "[| zprime p; 2 < p; ~([a = 0] (mod p)); ~(QuadRes p a) |] ==>
                   [zfact (p - 1) = a ^ nat ((p - 1) div 2)] (mod p)"
  apply (frule Union_SetS_setprod_prop1) 
  apply (auto simp add: Union_SetS_setprod_prop2)
  done

text {* \medskip Prove the first part of Euler's Criterion: *}

lemma Euler_part1: "[| 2 < p; zprime p; ~([x = 0](mod p)); 
    ~(QuadRes p x) |] ==> 
      [x^(nat (((p) - 1) div 2)) = -1](mod p)"
  by (metis Wilson_Russ zcong_sym zcong_trans zfact_prop)

text {* \medskip Prove another part of Euler Criterion: *}

lemma aux_1: "0 < p ==> (a::int) ^ nat (p) = a * a ^ (nat (p) - 1)"
proof -
  assume "0 < p"
  then have "a ^ (nat p) =  a ^ (1 + (nat p - 1))"
    by (auto simp add: diff_add_assoc)
  also have "... = (a ^ 1) * a ^ (nat(p) - 1)"
    by (simp only: power_add)
  also have "... = a * a ^ (nat(p) - 1)"
    by auto
  finally show ?thesis .
qed

lemma aux_2: "[| (2::int) < p; p \<in> zOdd |] ==> 0 < ((p - 1) div 2)"
proof -
  assume "2 < p" and "p \<in> zOdd"
  then have "(p - 1):zEven"
    by (auto simp add: zEven_def zOdd_def)
  then have aux_1: "2 * ((p - 1) div 2) = (p - 1)"
    by (auto simp add: even_div_2_prop2)
  with `2 < p` have "1 < (p - 1)"
    by auto
  then have " 1 < (2 * ((p - 1) div 2))"
    by (auto simp add: aux_1)
  then have "0 < (2 * ((p - 1) div 2)) div 2"
    by auto
  then show ?thesis by auto
qed

lemma Euler_part2:
    "[| 2 < p; zprime p; [a = 0] (mod p) |] ==> [0 = a ^ nat ((p - 1) div 2)] (mod p)"
  apply (frule zprime_zOdd_eq_grt_2)
  apply (frule aux_2, auto)
  apply (frule_tac a = a in aux_1, auto)
  apply (frule zcong_zmult_prop1, auto)
  done

text {* \medskip Prove the final part of Euler's Criterion: *}

lemma aux__1: "[| ~([x = 0] (mod p)); [y ^ 2 = x] (mod p)|] ==> ~(p dvd y)"
  by (metis dvdI power2_eq_square zcong_sym zcong_trans zcong_zero_equiv_div dvd_trans)

lemma aux__2: "2 * nat((p - 1) div 2) =  nat (2 * ((p - 1) div 2))"
  by (auto simp add: nat_mult_distrib)

lemma Euler_part3: "[| 2 < p; zprime p; ~([x = 0](mod p)); QuadRes p x |] ==> 
                      [x^(nat (((p) - 1) div 2)) = 1](mod p)"
  apply (subgoal_tac "p \<in> zOdd")
  apply (auto simp add: QuadRes_def)
   prefer 2 
   apply (metis zprime_zOdd_eq_grt_2)
  apply (frule aux__1, auto)
  apply (drule_tac z = "nat ((p - 1) div 2)" in zcong_zpower)
  apply (auto simp add: zpower_zpower) 
  apply (rule zcong_trans)
  apply (auto simp add: zcong_sym [of "x ^ nat ((p - 1) div 2)"])
  apply (metis Little_Fermat even_div_2_prop2 odd_minus_one_even mult_1 aux__2)
  done


text {* \medskip Finally show Euler's Criterion: *}

theorem Euler_Criterion: "[| 2 < p; zprime p |] ==> [(Legendre a p) =
    a^(nat (((p) - 1) div 2))] (mod p)"
  apply (auto simp add: Legendre_def Euler_part2)
  apply (frule Euler_part3, auto simp add: zcong_sym)[]
  apply (frule Euler_part1, auto simp add: zcong_sym)[]
  done

end
