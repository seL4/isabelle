(*
    Abstract class ring (commutative, with 1)
    $Id$
    Author: Clemens Ballarin, started 9 December 1996
*)

Blast.overloaded ("Divides.op dvd", domain_type);

val a_assoc = thm "plus_ac0.assoc";
val l_zero = thm "plus_ac0.zero";
val a_comm = thm "plus_ac0.commute";

section "Rings";

fun make_left_commute assoc commute s =
  [rtac (commute RS trans) 1, rtac (assoc RS trans) 1,
   rtac (commute RS arg_cong) 1];

(* addition *)

qed_goal "a_lcomm" Ring.thy "!!a::'a::ring. a+(b+c) = b+(a+c)"
  (make_left_commute a_assoc a_comm);

val a_ac = [a_assoc, a_comm, a_lcomm];

Goal "!!a::'a::ring. a + 0 = a";
by (rtac (a_comm RS trans) 1);
by (rtac l_zero 1);
qed "r_zero";

Goal "!!a::'a::ring. a + (-a) = 0";
by (rtac (a_comm RS trans) 1);
by (rtac l_neg 1);
qed "r_neg";

Goal "!! a::'a::ring. a + b = a + c ==> b = c";
by (rtac box_equals 1);
by (rtac l_zero 2);
by (rtac l_zero 2);
by (res_inst_tac [("a1", "a")] (l_neg RS subst) 1);
by (asm_simp_tac (simpset() addsimps [a_assoc]) 1);
qed "a_lcancel";

Goal "!! a::'a::ring. b + a = c + a ==> b = c";
by (rtac a_lcancel 1);
by (asm_simp_tac (simpset() addsimps a_ac) 1);
qed "a_rcancel";

Goal "!! a::'a::ring. (a + b = a + c) = (b = c)";
by (auto_tac (claset() addSDs [a_lcancel], simpset()));
qed "a_lcancel_eq";

Goal "!! a::'a::ring. (b + a = c + a) = (b = c)";
by (simp_tac (simpset() addsimps [a_lcancel_eq, a_comm]) 1);
qed "a_rcancel_eq";

Addsimps [a_lcancel_eq, a_rcancel_eq];

Goal "!!a::'a::ring. -(-a) = a";
by (rtac a_lcancel 1);
by (rtac (r_neg RS trans) 1);
by (rtac (l_neg RS sym) 1);
qed "minus_minus";

Goal "- 0 = (0::'a::ring)";
by (rtac a_lcancel 1);
by (rtac (r_neg RS trans) 1);
by (rtac (l_zero RS sym) 1);
qed "minus0";

Goal "!!a::'a::ring. -(a + b) = (-a) + (-b)";
by (res_inst_tac [("a", "a+b")] a_lcancel 1);
by (simp_tac (simpset() addsimps ([r_neg, l_neg, l_zero]@a_ac)) 1);
qed "minus_add";

(* multiplication *)

qed_goal "m_lcomm" Ring.thy "!!a::'a::ring. a*(b*c) = b*(a*c)"
  (make_left_commute m_assoc m_comm);

val m_ac = [m_assoc, m_comm, m_lcomm];

Goal "!!a::'a::ring. a * <1> = a";
by (rtac (m_comm RS trans) 1);
by (rtac l_one 1);
qed "r_one";

(* distributive and derived *)

Goal "!!a::'a::ring. a * (b + c) = a * b + a * c";
by (rtac (m_comm RS trans) 1);
by (rtac (l_distr RS trans) 1);
by (simp_tac (simpset() addsimps [m_comm]) 1);
qed "r_distr";

val m_distr = m_ac @ [l_distr, r_distr];

(* the following two proofs can be found in
   Jacobson, Basic Algebra I, pp. 88-89 *)

Goal "!!a::'a::ring. 0 * a = 0";
by (rtac a_lcancel 1);
by (rtac (l_distr RS sym RS trans) 1);
by (simp_tac (simpset() addsimps [r_zero]) 1);
qed "l_null";

Goal "!!a::'a::ring. a * 0 = 0";
by (rtac (m_comm RS trans) 1);
by (rtac l_null 1);
qed "r_null";

Goal "!!a::'a::ring. (-a) * b = - (a * b)";
by (rtac a_lcancel 1);
by (rtac (r_neg RS sym RSN (2, trans)) 1);
by (rtac (l_distr RS sym RS trans) 1);
by (simp_tac (simpset() addsimps [l_null, r_neg]) 1);
qed "l_minus";

Goal "!!a::'a::ring. a * (-b) = - (a * b)";
by (rtac a_lcancel 1);
by (rtac (r_neg RS sym RSN (2, trans)) 1);
by (rtac (r_distr RS sym RS trans) 1);
by (simp_tac (simpset() addsimps [r_null, r_neg]) 1);
qed "r_minus";

val m_minus = [l_minus, r_minus];

Addsimps [l_zero, r_zero, l_neg, r_neg, minus_minus, minus0, 
	  l_one, r_one, l_null, r_null];

(* further rules *)

Goal "!!a::'a::ring. -a = 0 ==> a = 0";
by (res_inst_tac [("t", "a")] (minus_minus RS subst) 1);
by (Asm_simp_tac 1);
qed "uminus_monom";

Goal "!!a::'a::ring. a ~= 0 ==> -a ~= 0";
by (blast_tac (claset() addIs [uminus_monom]) 1); 
qed "uminus_monom_neq";

Goal "!!a::'a::ring. a * b ~= 0 ==> a ~= 0";
by Auto_tac;  
qed "l_nullD";

Goal "!!a::'a::ring. a * b ~= 0 ==> b ~= 0";
by Auto_tac;  
qed "r_nullD";

(* reflection between a = b and a -- b = 0 *)

Goal "!!a::'a::ring. a = b ==> a + (-b) = 0";
by (Asm_simp_tac 1);
qed "eq_imp_diff_zero";

Goal "!!a::'a::ring. a + (-b) = 0 ==> a = b";
by (res_inst_tac [("a", "-b")] a_rcancel 1);
by (Asm_simp_tac 1);
qed "diff_zero_imp_eq";

(* this could be a rewrite rule, but won't terminate
   ==> make it a simproc?
Goal "!!a::'a::ring. (a = b) = (a -- b = 0)";
*)

(* Power *)

Goal "!!a::'a::ring. a ^ 0 = <1>";
by (simp_tac (simpset() addsimps [power_ax]) 1);
qed "power_0";

Goal "!!a::'a::ring. a ^ Suc n = a ^ n * a";
by (simp_tac (simpset() addsimps [power_ax]) 1);
qed "power_Suc";

Addsimps [power_0, power_Suc];

Goal "<1> ^ n = (<1>::'a::ring)";
by (induct_tac "n" 1);
by Auto_tac;
qed "power_one";

Goal "!!n. n ~= 0 ==> 0 ^ n = (0::'a::ring)";
by (etac rev_mp 1);
by (induct_tac "n" 1);
by Auto_tac;
qed "power_zero";

Addsimps [power_zero, power_one];

Goal "!! a::'a::ring. a ^ m * a ^ n = a ^ (m + n)";
by (induct_tac "m" 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps m_ac) 1);
qed "power_mult";

(* Divisibility *)
section "Divisibility";

Goalw [dvd_def] "!! a::'a::ring. a dvd 0";
by (res_inst_tac [("x", "0")] exI 1);
by (Simp_tac 1);
qed "dvd_zero_right";

Goalw [dvd_def] "!! a::'a::ring. 0 dvd a ==> a = 0";
by Auto_tac;
qed "dvd_zero_left";

Goalw [dvd_def] "!! a::'a::ring. a dvd a";
by (res_inst_tac [("x", "<1>")] exI 1);
by (Simp_tac 1);
qed "dvd_refl_ring";

Goalw [dvd_def] "!! a::'a::ring. [| a dvd b; b dvd c |] ==> a dvd c";
by (Step_tac 1);
by (res_inst_tac [("x", "k * ka")] exI 1);
by (simp_tac (simpset() addsimps m_ac) 1);
qed "dvd_trans_ring";

Addsimps [dvd_zero_right, dvd_refl_ring];

Goalw [dvd_def]
  "!!a::'a::ring. [| a dvd <1>; b dvd <1> |] ==> a * b dvd <1>";
by (Clarify_tac 1);
by (res_inst_tac [("x", "k * ka")] exI 1);
by (asm_full_simp_tac (simpset() addsimps m_ac) 1);
qed "unit_mult";

Goal "!!a::'a::ring. a dvd <1> ==> a^n dvd <1>";
by (induct_tac "n" 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [unit_mult]) 1);
qed "unit_power";

Goalw [dvd_def]
  "!! a::'a::ring. [| a dvd b; a dvd c |] ==> a dvd b + c";
by (Clarify_tac 1);
by (res_inst_tac [("x", "k + ka")] exI 1);
by (simp_tac (simpset() addsimps [r_distr]) 1);
qed "dvd_add_right";

Goalw [dvd_def]
  "!! a::'a::ring. a dvd b ==> a dvd -b";
by (Clarify_tac 1);
by (res_inst_tac [("x", "-k")] exI 1);
by (simp_tac (simpset() addsimps [r_minus]) 1);
qed "dvd_uminus_right";

Goalw [dvd_def]
  "!! a::'a::ring. a dvd b ==> a dvd c*b";
by (Clarify_tac 1);
by (res_inst_tac [("x", "c * k")] exI 1);
by (simp_tac (simpset() addsimps m_ac) 1);
qed "dvd_l_mult_right";

Goalw [dvd_def]
  "!! a::'a::ring. a dvd b ==> a dvd b*c";
by (Clarify_tac 1);
by (res_inst_tac [("x", "k * c")] exI 1);
by (simp_tac (simpset() addsimps m_ac) 1);
qed "dvd_r_mult_right";

Addsimps [dvd_add_right, dvd_uminus_right, dvd_l_mult_right, dvd_r_mult_right];

(* Inverse of multiplication *)

section "inverse";

Goal "!! a::'a::ring. [| a * x = <1>; a * y = <1> |] ==> x = y";
by (res_inst_tac [("a", "(a*y)*x"), ("b", "y*(a*x)")] box_equals 1);
by (simp_tac (simpset() addsimps m_ac) 1);
by Auto_tac;
qed "inverse_unique";

Goal "!! a::'a::ring. a dvd <1> ==> a * inverse a = <1>";
by (asm_full_simp_tac (simpset () addsimps [inverse_ax, dvd_def]) 1);
by (Clarify_tac 1);
by (rtac someI 1);
by (rtac sym 1);
by (assume_tac 1);
qed "r_inverse_ring";

Goal "!! a::'a::ring. a dvd <1> ==> inverse a * a= <1>";
by (asm_simp_tac (simpset() addsimps r_inverse_ring::m_ac) 1);
qed "l_inverse_ring";

(* Integral domain *)

section "Integral domains";

Goal "0 ~= (<1>::'a::domain)";
by (rtac not_sym 1);
by (rtac one_not_zero 1);
qed "zero_not_one";

Goal "!! a::'a::domain. a dvd <1> ==> a ~= 0";
by (auto_tac (claset() addDs [dvd_zero_left],
  simpset() addsimps [one_not_zero] ));
qed "unit_imp_nonzero";

Goal "[| a * b = 0; a ~= 0 |] ==> (b::'a::domain) = 0";
by (dtac integral 1);
by (Fast_tac 1);
qed "r_integral";

Goal "[| a * b = 0; b ~= 0 |] ==> (a::'a::domain) = 0";
by (dtac integral 1);
by (Fast_tac 1);
qed "l_integral";

Goal "!! a::'a::domain. [| a ~= 0; b ~= 0 |] ==> a * b ~= 0";
by (blast_tac (claset() addIs [l_integral]) 1); 
qed "not_integral";

Addsimps [not_integral, one_not_zero, zero_not_one];

Goal "!! a::'a::domain. [| a * x = x; x ~= 0 |] ==> a = <1>";
by (res_inst_tac [("a", "- <1>")] a_lcancel 1);
by (Simp_tac 1);
by (rtac l_integral 1);
by (assume_tac 2);
by (asm_simp_tac (simpset() addsimps [l_distr, l_minus]) 1);
qed "l_one_integral";

Goal "!! a::'a::domain. [| x * a = x; x ~= 0 |] ==> a = <1>";
by (res_inst_tac [("a", "- <1>")] a_rcancel 1);
by (Simp_tac 1);
by (rtac r_integral 1);
by (assume_tac 2);
by (asm_simp_tac (simpset() addsimps [r_distr, r_minus]) 1);
qed "r_one_integral";

(* cancellation laws for multiplication *)

Goal "!! a::'a::domain. [| a ~= 0; a * b = a * c |] ==> b = c";
by (rtac diff_zero_imp_eq 1);
by (dtac eq_imp_diff_zero 1);
by (full_simp_tac (simpset() addsimps [r_minus RS sym, r_distr RS sym]) 1);
by (fast_tac (claset() addIs [l_integral]) 1);
qed "m_lcancel";

Goal "!! a::'a::domain. [| a ~= 0; b * a = c * a |] ==> b = c";
by (rtac m_lcancel 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps m_ac) 1);
qed "m_rcancel";

Goal "!! a::'a::domain. a ~= 0 ==> (a * b = a * c) = (b = c)";
by (auto_tac (claset() addDs [m_lcancel], simpset()));
qed "m_lcancel_eq";

Goal "!! a::'a::domain. a ~= 0 ==> (b * a = c * a) = (b = c)";
by (asm_simp_tac (simpset() addsimps [m_lcancel_eq, m_comm]) 1);
qed "m_rcancel_eq";

Addsimps [m_lcancel_eq, m_rcancel_eq];

(* Fields *)

section "Fields";

Goal "!! a::'a::field. (a dvd <1>) = (a ~= 0)";
by (auto_tac (claset() addDs [field_ax, dvd_zero_left],
  simpset() addsimps [field_one_not_zero]));
qed "field_unit";

Addsimps [field_unit];

Goal "!! a::'a::field. a ~= 0 ==> a * inverse a = <1>";
by (asm_full_simp_tac (simpset() addsimps [r_inverse_ring]) 1);
qed "r_inverse";

Goal "!! a::'a::field. a ~= 0 ==> inverse a * a= <1>";
by (asm_full_simp_tac (simpset() addsimps [l_inverse_ring]) 1);
qed "l_inverse";

Addsimps [l_inverse, r_inverse];

(* fields are integral domains *)

Goal "!! a::'a::field. a * b = 0 ==> a = 0 | b = 0";
by (Step_tac 1);
by (res_inst_tac [("a", "(a*b)*inverse b")] box_equals 1);
by (rtac refl 3);
by (simp_tac (simpset() addsimps m_ac) 2);
by Auto_tac;
qed "field_integral";

(* fields are factorial domains *)

Goalw [prime_def, irred_def] "!! a::'a::field. irred a ==> prime a";
by (blast_tac (claset() addIs [field_ax]) 1);
qed "field_fact_prime";
