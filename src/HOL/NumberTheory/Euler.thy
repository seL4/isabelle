(*  Title:      HOL/Quadratic_Reciprocity/Euler.thy
    ID:         $Id$
    Authors:    Jeremy Avigad, David Gray, and Adam Kramer
*)

header {* Euler's criterion *}

theory Euler = Residues + EvenOdd:;

constdefs
  MultInvPair :: "int => int => int => int set"
  "MultInvPair a p j == {StandardRes p j, StandardRes p (a * (MultInv p j))}"
  SetS        :: "int => int => int set set"
  "SetS        a p   ==  ((MultInvPair a p) ` (SRStar p))";

(****************************************************************)
(*                                                              *)
(* Property for MultInvPair                                     *)
(*                                                              *)
(****************************************************************)

lemma MultInvPair_prop1a: "[| p \<in> zprime; 2 < p; ~([a = 0](mod p));
                              X \<in> (SetS a p); Y \<in> (SetS a p);
                              ~((X \<inter> Y) = {}) |] ==> 
                           X = Y";
  apply (auto simp add: SetS_def)
  apply (drule StandardRes_SRStar_prop1a)+; defer 1;
  apply (drule StandardRes_SRStar_prop1a)+;
  apply (auto simp add: MultInvPair_def StandardRes_prop2 zcong_sym)
  apply (drule notE, rule MultInv_zcong_prop1, auto)
  apply (drule notE, rule MultInv_zcong_prop2, auto)
  apply (drule MultInv_zcong_prop2, auto)
  apply (drule MultInv_zcong_prop3, auto simp add: zcong_sym)
  apply (drule MultInv_zcong_prop1, auto)
  apply (drule MultInv_zcong_prop2, auto)
  apply (drule MultInv_zcong_prop2, auto)
  apply (drule MultInv_zcong_prop3, auto simp add: zcong_sym)
done

lemma MultInvPair_prop1b: "[| p \<in> zprime; 2 < p; ~([a = 0](mod p));
                              X \<in> (SetS a p); Y \<in> (SetS a p);
                              X \<noteq> Y |] ==>
                              X \<inter> Y = {}";
  apply (rule notnotD)
  apply (rule notI)
  apply (drule MultInvPair_prop1a, auto)
done

lemma MultInvPair_prop1c: "[| p \<in> zprime; 2 < p; ~([a = 0](mod p)) |] ==>  
    \<forall>X \<in> SetS a p. \<forall>Y \<in> SetS a p. X \<noteq> Y --> X\<inter>Y = {}"
  by (auto simp add: MultInvPair_prop1b)

lemma MultInvPair_prop2: "[| p \<in> zprime; 2 < p; ~([a = 0](mod p)) |] ==> 
                          Union ( SetS a p) = SRStar p";
  apply (auto simp add: SetS_def MultInvPair_def StandardRes_SRStar_prop4 
    SRStar_mult_prop2)
  apply (frule StandardRes_SRStar_prop3)
  apply (rule bexI, auto)
done

lemma MultInvPair_distinct: "[| p \<in> zprime; 2 < p; ~([a = 0] (mod p)); 
                                ~([j = 0] (mod p)); 
                                ~(QuadRes p a) |]  ==> 
                             ~([j = a * MultInv p j] (mod p))";
  apply auto
proof -;
  assume "p \<in> zprime" and "2 < p" and "~([a = 0] (mod p))" and 
    "~([j = 0] (mod p))" and "~(QuadRes p a)";
  assume "[j = a * MultInv p j] (mod p)";
  then have "[j * j = (a * MultInv p j) * j] (mod p)";
    by (auto simp add: zcong_scalar)
  then have a:"[j * j = a * (MultInv p j * j)] (mod p)";
    by (auto simp add: zmult_ac)
  have "[j * j = a] (mod p)";
    proof -;
      from prems have b: "[MultInv p j * j = 1] (mod p)";
        by (simp add: MultInv_prop2a)
      from b a show ?thesis;
        by (auto simp add: zcong_zmult_prop2)
    qed;
  then have "[j^2 = a] (mod p)";
    apply(subgoal_tac "2 = Suc(Suc(0))");
    apply (erule ssubst)
    apply (auto simp only: power_Suc power_0)
    by auto
  with prems show False;
    by (simp add: QuadRes_def)
qed;

lemma MultInvPair_card_two: "[| p \<in> zprime; 2 < p; ~([a = 0] (mod p)); 
                                ~(QuadRes p a); ~([j = 0] (mod p)) |]  ==> 
                             card (MultInvPair a p j) = 2";
  apply (auto simp add: MultInvPair_def)
  apply (subgoal_tac "~ (StandardRes p j = StandardRes p (a * MultInv p j))");
  apply auto
  apply (simp only: StandardRes_prop2)
  apply (drule MultInvPair_distinct)
by auto

(****************************************************************)
(*                                                              *)
(* Properties of SetS                                           *)
(*                                                              *)
(****************************************************************)

lemma SetS_finite: "2 < p ==> finite (SetS a p)";
  by (auto simp add: SetS_def SRStar_finite [of p] finite_imageI)

lemma SetS_elems_finite: "\<forall>X \<in> SetS a p. finite X";
  by (auto simp add: SetS_def MultInvPair_def)

lemma SetS_elems_card: "[| p \<in> zprime; 2 < p; ~([a = 0] (mod p)); 
                        ~(QuadRes p a) |]  ==>
                        \<forall>X \<in> SetS a p. card X = 2";
  apply (auto simp add: SetS_def)
  apply (frule StandardRes_SRStar_prop1a)
  apply (rule MultInvPair_card_two, auto)
done

lemma Union_SetS_finite: "2 < p ==> finite (Union (SetS a p))";
  by (auto simp add: SetS_finite SetS_elems_finite finite_union_finite_subsets)

lemma card_setsum_aux: "[| finite S; \<forall>X \<in> S. finite (X::int set); 
    \<forall>X \<in> S. card X = n |] ==> setsum card S = setsum (%x. n) S";
by (induct set: Finites, auto)

lemma SetS_card: "[| p \<in> zprime; 2 < p; ~([a = 0] (mod p)); ~(QuadRes p a) |] ==> 
                  int(card(SetS a p)) = (p - 1) div 2";
proof -;
  assume "p \<in> zprime" and "2 < p" and  "~([a = 0] (mod p))" and "~(QuadRes p a)";
  then have "(p - 1) = 2 * int(card(SetS a p))";
  proof -;
    have "p - 1 = int(card(Union (SetS a p)))";
      by (auto simp add: prems MultInvPair_prop2 SRStar_card)
    also have "... = int (setsum card (SetS a p))";
      by (auto simp add: prems SetS_finite SetS_elems_finite
                         MultInvPair_prop1c [of p a] card_union_disjoint_sets)
    also have "... = int(setsum (%x.2) (SetS a p))";
      apply (insert prems)
      apply (auto simp add: SetS_elems_card SetS_finite SetS_elems_finite 
        card_setsum_aux simp del: setsum_constant_nat)
    done
    also have "... = 2 * int(card( SetS a p))";
      by (auto simp add: prems SetS_finite setsum_const2)
    finally show ?thesis .;
  qed;
  from this show ?thesis;
    by auto
qed;

lemma SetS_setprod_prop: "[| p \<in> zprime; 2 < p; ~([a = 0] (mod p));
                              ~(QuadRes p a); x \<in> (SetS a p) |] ==> 
                          [setprod x = a] (mod p)";
  apply (auto simp add: SetS_def MultInvPair_def)
  apply (frule StandardRes_SRStar_prop1a)
  apply (subgoal_tac "StandardRes p x \<noteq> StandardRes p (a * MultInv p x)");
  apply (auto simp add: StandardRes_prop2 MultInvPair_distinct)
  apply (frule_tac m = p and x = x and y = "(a * MultInv p x)" in 
    StandardRes_prop4);
  apply (subgoal_tac "[x * (a * MultInv p x) = a * (x * MultInv p x)] (mod p)");
  apply (drule_tac a = "StandardRes p x * StandardRes p (a * MultInv p x)" and
                   b = "x * (a * MultInv p x)" and
                   c = "a * (x * MultInv p x)" in  zcong_trans, force);
  apply (frule_tac p = p and x = x in MultInv_prop2, auto)
  apply (drule_tac a = "x * MultInv p x" and b = 1 in zcong_zmult_prop2)
  apply (auto simp add: zmult_ac)
done

lemma aux1: "[| 0 < x; (x::int) < a; x \<noteq> (a - 1) |] ==> x < a - 1";
  by arith

lemma aux2: "[| (a::int) < c; b < c |] ==> (a \<le> b | b \<le> a)";
  by auto

lemma SRStar_d22set_prop [rule_format]: "2 < p --> (SRStar p) = {1} \<union> 
    (d22set (p - 1))";
  apply (induct p rule: d22set.induct, auto)
  apply (simp add: SRStar_def d22set.simps, arith)
  apply (simp add: SRStar_def d22set.simps, clarify)
  apply (frule aux1)
  apply (frule aux2, auto)
  apply (simp_all add: SRStar_def)
  apply (simp add: d22set.simps)
  apply (frule d22set_le)
  apply (frule d22set_g_1, auto)
done

lemma Union_SetS_setprod_prop1: "[| p \<in> zprime; 2 < p; ~([a = 0] (mod p)); ~(QuadRes p a) |] ==>
                                 [setprod (Union (SetS a p)) = a ^ nat ((p - 1) div 2)] (mod p)";
proof -;
  assume "p \<in> zprime" and "2 < p" and  "~([a = 0] (mod p))" and "~(QuadRes p a)";
  then have "[setprod (Union (SetS a p)) = 
      gsetprod setprod (SetS a p)] (mod p)";
    by (auto simp add: SetS_finite SetS_elems_finite
                       MultInvPair_prop1c setprod_disj_sets)
  also; have "[gsetprod setprod (SetS a p) = 
      gsetprod (%x. a) (SetS a p)] (mod p)";
    apply (rule gsetprod_same_function_zcong)
    by (auto simp add: prems SetS_setprod_prop SetS_finite)
  also (zcong_trans) have "[gsetprod (%x. a) (SetS a p) = 
      a^(card (SetS a p))] (mod p)";
    by (auto simp add: prems SetS_finite gsetprod_const)
  finally (zcong_trans) show ?thesis;
    apply (rule zcong_trans)
    apply (subgoal_tac "card(SetS a p) = nat((p - 1) div 2)", auto);
    apply (subgoal_tac "nat(int(card(SetS a p))) = nat((p - 1) div 2)", force);
    apply (auto simp add: prems SetS_card)
  done
qed;

lemma Union_SetS_setprod_prop2: "[| p \<in> zprime; 2 < p; ~([a = 0](mod p)) |] ==> 
                                    setprod (Union (SetS a p)) = zfact (p - 1)";
proof -;
  assume "p \<in> zprime" and "2 < p" and "~([a = 0](mod p))";
  then have "setprod (Union (SetS a p)) = setprod (SRStar p)";
    by (auto simp add: MultInvPair_prop2)
  also have "... = setprod ({1} \<union> (d22set (p - 1)))";
    by (auto simp add: prems SRStar_d22set_prop)
  also have "... = zfact(p - 1)";
  proof -;
     have "~(1 \<in> d22set (p - 1)) & finite( d22set (p - 1))";
      apply (insert prems, auto)
      apply (drule d22set_g_1)
      apply (auto simp add: d22set_fin)
     done
     then have "setprod({1} \<union> (d22set (p - 1))) = setprod (d22set (p - 1))";
       by auto
     then show ?thesis
       by (auto simp add: d22set_prod_zfact)
  qed;
  finally show ?thesis .;
qed;

lemma zfact_prop: "[| p \<in> zprime; 2 < p; ~([a = 0] (mod p)); ~(QuadRes p a) |] ==>
                   [zfact (p - 1) = a ^ nat ((p - 1) div 2)] (mod p)";
  apply (frule Union_SetS_setprod_prop1) 
  apply (auto simp add: Union_SetS_setprod_prop2)
done

(****************************************************************)
(*                                                              *)
(*  Prove the first part of Euler's Criterion:                  *)
(*    ~(QuadRes p x) |] ==>                                     *)
(*                   [x^(nat (((p) - 1) div 2)) = -1](mod p)    *)
(*                                                              *)
(****************************************************************)

lemma Euler_part1: "[| 2 < p; p \<in> zprime; ~([x = 0](mod p)); 
    ~(QuadRes p x) |] ==> 
      [x^(nat (((p) - 1) div 2)) = -1](mod p)";
  apply (frule zfact_prop, auto)
  apply (frule Wilson_Russ)
  apply (auto simp add: zcong_sym)
  apply (rule zcong_trans, auto)
done

(********************************************************************)
(*                                                                  *)
(* Prove another part of Euler Criterion:                           *)
(*        [a = 0] (mod p) ==> [0 = a ^ nat ((p - 1) div 2)] (mod p) *)
(*                                                                  *)
(********************************************************************)

lemma aux_1: "0 < p ==> (a::int) ^ nat (p) = a * a ^ (nat (p) - 1)";
proof -;
  assume "0 < p";
  then have "a ^ (nat p) =  a ^ (1 + (nat p - 1))";
    by (auto simp add: diff_add_assoc)
  also have "... = (a ^ 1) * a ^ (nat(p) - 1)";
    by (simp only: zpower_zadd_distrib)
  also have "... = a * a ^ (nat(p) - 1)";
    by auto
  finally show ?thesis .;
qed;

lemma aux_2: "[| (2::int) < p; p \<in> zOdd |] ==> 0 < ((p - 1) div 2)";
proof -;
  assume "2 < p" and "p \<in> zOdd";
  then have "(p - 1):zEven";
    by (auto simp add: zEven_def zOdd_def)
  then have aux_1: "2 * ((p - 1) div 2) = (p - 1)";
    by (auto simp add: even_div_2_prop2)
  then have "1 < (p - 1)"
    by auto
  then have " 1 < (2 * ((p - 1) div 2))";
    by (auto simp add: aux_1)
  then have "0 < (2 * ((p - 1) div 2)) div 2";
    by auto
  then show ?thesis by auto
qed;

lemma Euler_part2: "[| 2 < p; p \<in> zprime; [a = 0] (mod p) |] ==> [0 = a ^ nat ((p - 1) div 2)] (mod p)";
  apply (frule zprime_zOdd_eq_grt_2)
  apply (frule aux_2, auto)
  apply (frule_tac a = a in aux_1, auto)
  apply (frule zcong_zmult_prop1, auto)
done

(****************************************************************)
(*                                                              *)
(* Prove the final part of Euler's Criterion:                   *)
(*           QuadRes p x |] ==>                                 *)
(*                      [x^(nat (((p) - 1) div 2)) = 1](mod p)  *)
(*                                                              *)
(****************************************************************)

lemma aux__1: "[| ~([x = 0] (mod p)); [y ^ 2 = x] (mod p)|] ==> ~(p dvd y)";
  apply (subgoal_tac "[| ~([x = 0] (mod p)); [y ^ 2 = x] (mod p)|] ==> 
    ~([y ^ 2 = 0] (mod p))");
  apply (auto simp add: zcong_sym [of "y^2" x p] intro: zcong_trans)
  apply (auto simp add: zcong_eq_zdvd_prop intro: zpower_zdvd_prop1)
done

lemma aux__2: "2 * nat((p - 1) div 2) =  nat (2 * ((p - 1) div 2))";
  by (auto simp add: nat_mult_distrib)

lemma Euler_part3: "[| 2 < p; p \<in> zprime; ~([x = 0](mod p)); QuadRes p x |] ==> 
                      [x^(nat (((p) - 1) div 2)) = 1](mod p)";
  apply (subgoal_tac "p \<in> zOdd")
  apply (auto simp add: QuadRes_def)
  apply (frule aux__1, auto)
  apply (drule_tac z = "nat ((p - 1) div 2)" in zcong_zpower);
  apply (auto simp add: zpower_zpower)
  apply (rule zcong_trans)
  apply (auto simp add: zcong_sym [of "x ^ nat ((p - 1) div 2)"]);
  apply (simp add: aux__2)
  apply (frule odd_minus_one_even)
  apply (frule even_div_2_prop2)
  apply (auto intro: Little_Fermat simp add: zprime_zOdd_eq_grt_2)
done

(********************************************************************)
(*                                                                  *)
(* Finally show Euler's Criterion                                   *)
(*                                                                  *)
(********************************************************************)

theorem Euler_Criterion: "[| 2 < p; p \<in> zprime |] ==> [(Legendre a p) =
    a^(nat (((p) - 1) div 2))] (mod p)";
  apply (auto simp add: Legendre_def Euler_part2)
  apply (frule Euler_part3, auto simp add: zcong_sym)
  apply (frule Euler_part1, auto simp add: zcong_sym)
done

end