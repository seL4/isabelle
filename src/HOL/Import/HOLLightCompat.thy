(*  Title:      HOL/Import/HOLLightCompat.thy
    ID:         $Id$
    Author:     Steven Obua and Sebastian Skalberg (TU Muenchen)
*)

theory HOLLightCompat imports HOL4Setup HOL4Compat Divides Primes Real begin

lemma light_imp_def: "(t1 --> t2) = ((t1 & t2) = t1)"
  by auto;

lemma comb_rule: "[| P1 = P2 ; Q1 = Q2 |] ==> P1 Q1 = P2 Q2"
  by simp

lemma light_and_def: "(t1 & t2) = ((%f. f t1 t2::bool) = (%f. f True True))"
proof auto
  assume a: "(%f. f t1 t2::bool) = (%f. f True True)"
  have b: "(%(x::bool) (y::bool). x) = (%x y. x)" ..
  with a
  have "t1 = True"
    by (rule comb_rule)
  thus t1
    by simp
next
  assume a: "(%f. f t1 t2::bool) = (%f. f True True)"
  have b: "(%(x::bool) (y::bool). y) = (%x y. y)" ..
  with a
  have "t2 = True"
    by (rule comb_rule)
  thus t2
    by simp
qed

constdefs
   Pred :: "nat \<Rightarrow> nat"
   "Pred n \<equiv> n - (Suc 0)"

lemma Pred_altdef: "Pred = (SOME PRE. PRE 0 = 0 & (ALL n. PRE (Suc n) = n))"
  apply (rule some_equality[symmetric])
  apply (simp add: Pred_def)
  apply (rule ext)
  apply (induct_tac x)
  apply (auto simp add: Pred_def)
  done

lemma NUMERAL_rew[hol4rew]: "NUMERAL x = x" by (simp add: NUMERAL_def)

lemma REP_ABS_PAIR: "\<forall> x y. Rep_Prod (Abs_Prod (Pair_Rep x y)) = Pair_Rep x y"
  apply (subst Abs_Prod_inverse)
  apply (auto simp add: Prod_def)
  done

lemma fst_altdef: "fst = (%p. SOME x. EX y. p = (x, y))"
  apply (rule ext, rule someI2)
  apply (auto intro: fst_conv[symmetric])
  done

lemma snd_altdef: "snd = (%p. SOME x. EX y. p = (y, x))"
  apply (rule ext, rule someI2)
  apply (auto intro: snd_conv[symmetric])
  done

lemma add_altdef: "op + = (SOME add. (ALL n. add 0 n = n) & (ALL m n. add (Suc m) n = Suc (add m n)))"
  apply (rule some_equality[symmetric])
  apply auto
  apply (rule ext)+
  apply (induct_tac x)
  apply auto
  done

lemma mult_altdef: "op * = (SOME mult. (ALL n. mult 0 n = 0) & (ALL m n. mult (Suc m) n = mult m n + n))"
  apply (rule some_equality[symmetric])
  apply auto
  apply (rule ext)+
  apply (induct_tac x)
  apply auto
  done

lemma sub_altdef: "op - = (SOME sub. (ALL m. sub m 0 = m) & (ALL m n. sub m (Suc n) = Pred (sub m n)))"
  apply (simp add: Pred_def)
  apply (rule some_equality[symmetric])
  apply auto
  apply (rule ext)+
  apply (induct_tac xa)
  apply auto
  done

constdefs
  NUMERAL_BIT0 :: "nat \<Rightarrow> nat"
  "NUMERAL_BIT0 n \<equiv> n + n"

lemma NUMERAL_BIT1_altdef: "NUMERAL_BIT1 n = Suc (n + n)"
  by (simp add: NUMERAL_BIT1_def)



end
