(*  Title:      HOL/Quadratic_Reciprocity/Gauss.thy
    Authors:    Jeremy Avigad, David Gray, and Adam Kramer
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {*Integers: Divisibility and Congruences*}

theory Int2 = Finite2 + WilsonRuss:;

text{*Note.  This theory is being revised.  See the web page
\url{http://www.andrew.cmu.edu/~avigad/isabelle}.*}

constdefs
  MultInv :: "int => int => int" 
  "MultInv p x == x ^ nat (p - 2)";

(*****************************************************************)
(*                                                               *)
(* Useful lemmas about dvd and powers                            *)
(*                                                               *)
(*****************************************************************)

lemma zpower_zdvd_prop1 [rule_format]: "((0 < n) & (p dvd y)) --> 
    p dvd ((y::int) ^ n)";
  by (induct_tac n, auto simp add: zdvd_zmult zdvd_zmult2 [of p y])

lemma zdvd_bounds: "n dvd m ==> (m \<le> (0::int) | n \<le> m)";
proof -;
  assume "n dvd m";
  then have "~(0 < m & m < n)";
    apply (insert zdvd_not_zless [of m n])
    by (rule contrapos_pn, auto)
  then have "(~0 < m | ~m < n)"  by auto
  then show ?thesis by auto
qed;

lemma aux4: " -(m * n) = (-m) * (n::int)";
  by auto

lemma zprime_zdvd_zmult_better: "[| p \<in> zprime;  p dvd (m * n) |] ==> 
    (p dvd m) | (p dvd n)";
  apply (case_tac "0 \<le> m")
  apply (simp add: zprime_zdvd_zmult)
  by (insert zprime_zdvd_zmult [of "-m" p n], auto)

lemma zpower_zdvd_prop2 [rule_format]: "p \<in> zprime --> p dvd ((y::int) ^ n) 
    --> 0 < n --> p dvd y";
  apply (induct_tac n, auto)
  apply (frule zprime_zdvd_zmult_better, auto)
done

lemma stupid: "(0 :: int) \<le> y ==> x \<le> x + y";
  by arith

lemma div_prop1: "[| 0 < z; (x::int) < y * z |] ==> x div z < y";
proof -;
  assume "0 < z";
  then have "(x div z) * z \<le> (x div z) * z + x mod z";
  apply (rule_tac x = "x div z * z" in stupid)
  by (simp add: pos_mod_sign)
  also have "... = x";
    by (auto simp add: zmod_zdiv_equality [THEN sym] zmult_ac)
  also assume  "x < y * z";
  finally show ?thesis;
    by (auto simp add: prems mult_less_cancel_right, insert prems, arith)
qed;

lemma div_prop2: "[| 0 < z; (x::int) < (y * z) + z |] ==> x div z \<le> y";
proof -;
  assume "0 < z" and "x < (y * z) + z";
  then have "x < (y + 1) * z" by (auto simp add: int_distrib)
  then have "x div z < y + 1";
    by (rule_tac y = "y + 1" in div_prop1, auto simp add: prems)
  then show ?thesis by auto
qed;

lemma zdiv_leq_prop: "[| 0 < y |] ==> y * (x div y) \<le> (x::int)";
proof-;
  assume "0 < y";
  from zmod_zdiv_equality have "x = y * (x div y) + x mod y" by auto
  moreover have "0 \<le> x mod y";
    by (auto simp add: prems pos_mod_sign)
  ultimately show ?thesis;
    by arith
qed;

(*****************************************************************)
(*                                                               *)
(* Useful properties of congruences                              *)
(*                                                               *)
(*****************************************************************)

lemma zcong_eq_zdvd_prop: "[x = 0](mod p) = (p dvd x)";
  by (auto simp add: zcong_def)

lemma zcong_id: "[m = 0] (mod m)";
  by (auto simp add: zcong_def zdvd_0_right)

lemma zcong_shift: "[a = b] (mod m) ==> [a + c = b + c] (mod m)";
  by (auto simp add: zcong_refl zcong_zadd)

lemma zcong_zpower: "[x = y](mod m) ==> [x^z = y^z](mod m)";
  by (induct_tac z, auto simp add: zcong_zmult)

lemma zcong_eq_trans: "[| [a = b](mod m); b = c; [c = d](mod m) |] ==> 
    [a = d](mod m)";
  by (auto, rule_tac b = c in zcong_trans)

lemma aux1: "a - b = (c::int) ==> a = c + b";
  by auto

lemma zcong_zmult_prop1: "[a = b](mod m) ==> ([c = a * d](mod m) = 
    [c = b * d] (mod m))";
  apply (auto simp add: zcong_def dvd_def)
  apply (rule_tac x = "ka + k * d" in exI)
  apply (drule aux1)+;
  apply (auto simp add: int_distrib)
  apply (rule_tac x = "ka - k * d" in exI)
  apply (drule aux1)+;
  apply (auto simp add: int_distrib)
done

lemma zcong_zmult_prop2: "[a = b](mod m) ==> 
    ([c = d * a](mod m) = [c = d * b] (mod m))";
  by (auto simp add: zmult_ac zcong_zmult_prop1)

lemma zcong_zmult_prop3: "[|p \<in> zprime; ~[x = 0] (mod p); 
    ~[y = 0] (mod p) |] ==> ~[x * y = 0] (mod p)";
  apply (auto simp add: zcong_def)
  apply (drule zprime_zdvd_zmult_better, auto)
done

lemma zcong_less_eq: "[| 0 < x; 0 < y; 0 < m; [x = y] (mod m); 
    x < m; y < m |] ==> x = y";
  apply (simp add: zcong_zmod_eq)
  apply (subgoal_tac "(x mod m) = x");
  apply (subgoal_tac "(y mod m) = y");
  apply simp
  apply (rule_tac [1-2] mod_pos_pos_trivial)
by auto

lemma zcong_neg_1_impl_ne_1: "[| 2 < p; [x = -1] (mod p) |] ==> 
    ~([x = 1] (mod p))";
proof;
  assume "2 < p" and "[x = 1] (mod p)" and "[x = -1] (mod p)"
  then have "[1 = -1] (mod p)";
    apply (auto simp add: zcong_sym)
    apply (drule zcong_trans, auto)
  done
  then have "[1 + 1 = -1 + 1] (mod p)";
    by (simp only: zcong_shift)
  then have "[2 = 0] (mod p)";
    by auto
  then have "p dvd 2";
    by (auto simp add: dvd_def zcong_def)
  with prems show False;
    by (auto simp add: zdvd_not_zless)
qed;

lemma zcong_zero_equiv_div: "[a = 0] (mod m) = (m dvd a)";
  by (auto simp add: zcong_def)

lemma zcong_zprime_prod_zero: "[| p \<in> zprime; 0 < a |] ==> 
  [a * b = 0] (mod p) ==> [a = 0] (mod p) | [b = 0] (mod p)"; 
  by (auto simp add: zcong_zero_equiv_div zprime_zdvd_zmult)

lemma zcong_zprime_prod_zero_contra: "[| p \<in> zprime; 0 < a |] ==>
  ~[a = 0](mod p) & ~[b = 0](mod p) ==> ~[a * b = 0] (mod p)";
  apply auto 
  apply (frule_tac a = a and b = b and p = p in zcong_zprime_prod_zero)
by auto

lemma zcong_not_zero: "[| 0 < x; x < m |] ==> ~[x = 0] (mod m)"; 
  by (auto simp add: zcong_zero_equiv_div zdvd_not_zless)

lemma zcong_zero: "[| 0 \<le> x; x < m; [x = 0](mod m) |] ==> x = 0";
  apply (drule order_le_imp_less_or_eq, auto)
by (frule_tac m = m in zcong_not_zero, auto)

lemma all_relprime_prod_relprime: "[| finite A; \<forall>x \<in> A. (zgcd(x,y) = 1) |]
    ==> zgcd (gsetprod id A,y) = 1";
  by (induct set: Finites, auto simp add: zgcd_zgcd_zmult)

(*****************************************************************)
(*                                                               *)
(* Some properties of MultInv                                    *)
(*                                                               *)
(*****************************************************************)

lemma MultInv_prop1: "[| 2 < p; [x = y] (mod p) |] ==> 
    [(MultInv p x) = (MultInv p y)] (mod p)";
  by (auto simp add: MultInv_def zcong_zpower)

lemma MultInv_prop2: "[| 2 < p; p \<in> zprime; ~([x = 0](mod p)) |] ==> 
  [(x * (MultInv p x)) = 1] (mod p)";
proof (simp add: MultInv_def zcong_eq_zdvd_prop);
  assume "2 < p" and "p \<in> zprime" and "~ p dvd x";
  have "x * x ^ nat (p - 2) = x ^ (nat (p - 2) + 1)";
    by auto
  also from prems have "nat (p - 2) + 1 = nat (p - 2 + 1)";
    by (simp only: nat_add_distrib, auto)
  also have "p - 2 + 1 = p - 1" by arith
  finally have "[x * x ^ nat (p - 2) = x ^ nat (p - 1)] (mod p)";
    by (rule ssubst, auto)
  also from prems have "[x ^ nat (p - 1) = 1] (mod p)";
    by (auto simp add: Little_Fermat) 
  finally (zcong_trans) show "[x * x ^ nat (p - 2) = 1] (mod p)";.;
qed;

lemma MultInv_prop2a: "[| 2 < p; p \<in> zprime; ~([x = 0](mod p)) |] ==> 
    [(MultInv p x) * x = 1] (mod p)";
  by (auto simp add: MultInv_prop2 zmult_ac)

lemma aux_1: "2 < p ==> ((nat p) - 2) = (nat (p - 2))";
  by (simp add: nat_diff_distrib)

lemma aux_2: "2 < p ==> 0 < nat (p - 2)";
  by auto

lemma MultInv_prop3: "[| 2 < p; p \<in> zprime; ~([x = 0](mod p)) |] ==> 
    ~([MultInv p x = 0](mod p))";
  apply (auto simp add: MultInv_def zcong_eq_zdvd_prop aux_1)
  apply (drule aux_2)
  apply (drule zpower_zdvd_prop2, auto)
done

lemma aux__1: "[| 2 < p; p \<in> zprime; ~([x = 0](mod p))|] ==> 
    [(MultInv p (MultInv p x)) = (x * (MultInv p x) * 
      (MultInv p (MultInv p x)))] (mod p)";
  apply (drule MultInv_prop2, auto)
  apply (drule_tac k = "MultInv p (MultInv p x)" in zcong_scalar, auto);
  apply (auto simp add: zcong_sym)
done

lemma aux__2: "[| 2 < p; p \<in> zprime; ~([x = 0](mod p))|] ==>
    [(x * (MultInv p x) * (MultInv p (MultInv p x))) = x] (mod p)";
  apply (frule MultInv_prop3, auto)
  apply (insert MultInv_prop2 [of p "MultInv p x"], auto)
  apply (drule MultInv_prop2, auto)
  apply (drule_tac k = x in zcong_scalar2, auto)
  apply (auto simp add: zmult_ac)
done

lemma MultInv_prop4: "[| 2 < p; p \<in> zprime; ~([x = 0](mod p)) |] ==> 
    [(MultInv p (MultInv p x)) = x] (mod p)";
  apply (frule aux__1, auto)
  apply (drule aux__2, auto)
  apply (drule zcong_trans, auto)
done

lemma MultInv_prop5: "[| 2 < p; p \<in> zprime; ~([x = 0](mod p)); 
    ~([y = 0](mod p)); [(MultInv p x) = (MultInv p y)] (mod p) |] ==> 
    [x = y] (mod p)";
  apply (drule_tac a = "MultInv p x" and b = "MultInv p y" and 
    m = p and k = x in zcong_scalar)
  apply (insert MultInv_prop2 [of p x], simp)
  apply (auto simp only: zcong_sym [of "MultInv p x * x"])
  apply (auto simp add:  zmult_ac)
  apply (drule zcong_trans, auto)
  apply (drule_tac a = "x * MultInv p y" and k = y in zcong_scalar, auto)
  apply (insert MultInv_prop2a [of p y], auto simp add: zmult_ac)
  apply (insert zcong_zmult_prop2 [of "y * MultInv p y" 1 p y x])
  apply (auto simp add: zcong_sym)
done

lemma MultInv_zcong_prop1: "[| 2 < p; [j = k] (mod p) |] ==> 
    [a * MultInv p j = a * MultInv p k] (mod p)";
  by (drule MultInv_prop1, auto simp add: zcong_scalar2)

lemma aux___1: "[j = a * MultInv p k] (mod p) ==> 
    [j * k = a * MultInv p k * k] (mod p)";
  by (auto simp add: zcong_scalar)

lemma aux___2: "[|2 < p; p \<in> zprime; ~([k = 0](mod p)); 
    [j * k = a * MultInv p k * k] (mod p) |] ==> [j * k = a] (mod p)";
  apply (insert MultInv_prop2a [of p k] zcong_zmult_prop2 
    [of "MultInv p k * k" 1 p "j * k" a])
  apply (auto simp add: zmult_ac)
done

lemma aux___3: "[j * k = a] (mod p) ==> [(MultInv p j) * j * k = 
     (MultInv p j) * a] (mod p)";
  by (auto simp add: zmult_assoc zcong_scalar2)

lemma aux___4: "[|2 < p; p \<in> zprime; ~([j = 0](mod p)); 
    [(MultInv p j) * j * k = (MultInv p j) * a] (mod p) |]
       ==> [k = a * (MultInv p j)] (mod p)";
  apply (insert MultInv_prop2a [of p j] zcong_zmult_prop1 
    [of "MultInv p j * j" 1 p "MultInv p j * a" k])
  apply (auto simp add: zmult_ac zcong_sym)
done

lemma MultInv_zcong_prop2: "[| 2 < p; p \<in> zprime; ~([k = 0](mod p)); 
    ~([j = 0](mod p)); [j = a * MultInv p k] (mod p) |] ==> 
    [k = a * MultInv p j] (mod p)";
  apply (drule aux___1)
  apply (frule aux___2, auto)
  by (drule aux___3, drule aux___4, auto)

lemma MultInv_zcong_prop3: "[| 2 < p; p \<in> zprime; ~([a = 0](mod p)); 
    ~([k = 0](mod p)); ~([j = 0](mod p));
    [a * MultInv p j = a * MultInv p k] (mod p) |] ==> 
      [j = k] (mod p)";
  apply (auto simp add: zcong_eq_zdvd_prop [of a p])
  apply (frule zprime_imp_zrelprime, auto)
  apply (insert zcong_cancel2 [of p a "MultInv p j" "MultInv p k"], auto)
  apply (drule MultInv_prop5, auto)
done

end
