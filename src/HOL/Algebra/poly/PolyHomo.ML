(*
    Universal property and evaluation homomorphism of univariate polynomials
    $Id$
    Author: Clemens Ballarin, started 16 April 1997
*)

(* Ring homomorphisms and polynomials *)

Goal "homo (const::'a::ring=>'a up)";
by (auto_tac (claset() addSIs [homoI], simpset()));
qed "const_homo";

Delsimps [const_add, const_mult, const_one, const_zero];
Addsimps [const_homo];

Goal
  "!!f::'a::ring up=>'b::ring. homo f ==> f (a *s p) = f (const a) * f p";
by (asm_simp_tac (simpset() addsimps [const_mult_is_smult RS sym]) 1);
qed "homo_smult";

Addsimps [homo_smult];

(* Evaluation homomorphism *)

Goal
  "!! phi::('a::ring=>'b::ring). homo phi ==> homo (EVAL2 phi a)";
by (rtac homoI 1);
by (rewtac EVAL2_def);
(* + commutes *)
(* degree estimations:
  bound of all sums can be extended to max (deg aa) (deg b) *)
by (res_inst_tac [("m", "deg (aa + b)"), ("n", "max (deg aa) (deg b)")]
  SUM_shrink 1);
by (rtac deg_add 1);
by (asm_simp_tac (simpset() delsimps [coeff_add] addsimps [deg_aboveD]) 1);
by (res_inst_tac [("m", "deg aa"), ("n", "max (deg aa) (deg b)")]
  SUM_shrink 1);
by (rtac le_maxI1 1);
by (asm_simp_tac (simpset() addsimps [deg_aboveD]) 1);
by (res_inst_tac [("m", "deg b"), ("n", "max (deg aa) (deg b)")]
  SUM_shrink 1);
by (rtac le_maxI2 1);
by (asm_simp_tac (simpset() addsimps [deg_aboveD]) 1);
(* actual homom property + *)
by (asm_simp_tac (simpset() addsimps [l_distr, SUM_add]) 1);

(* * commutes *)
by (res_inst_tac [("m", "deg (aa * b)"), ("n", "deg aa + deg b")]
  SUM_shrink 1);
by (rtac deg_mult_ring 1);
by (asm_simp_tac (simpset() delsimps [coeff_mult] addsimps [deg_aboveD]) 1);
by (rtac trans 1);
by (rtac CauchySum 2);
by (asm_simp_tac (simpset() addsimps [boundI, deg_aboveD]) 2);
by (asm_simp_tac (simpset() addsimps [boundI, deg_aboveD]) 2);
(* getting a^i and a^(k-i) together is difficult, so we do is manually *)
by (res_inst_tac [("s", 
"        SUM (deg aa + deg b) \
\           (%k. SUM k \
\                 (%i. phi (coeff i aa) * (phi (coeff (k - i) b) * \
\                      (a ^ i * a ^ (k - i)))))")] trans 1);
by (asm_simp_tac (simpset()
    addsimps [power_mult, leD RS add_diff_inverse, SUM_ldistr]) 1);
by (simp_tac (simpset() addsimps m_ac) 1);
by (simp_tac (simpset() addsimps m_ac) 1);
(* <1> commutes *)
by (Asm_simp_tac 1);
qed "EVAL2_homo";

Goalw [EVAL2_def]
  "!! phi::'a::ring=>'b::ring. EVAL2 phi a (const b) = phi b";
by (Simp_tac 1);
qed "EVAL2_const";

(* This is probably redundant *)
Goalw [EVAL2_def]
  "!! phi::'a::ring=>'b::ring. homo phi ==> EVAL2 phi a (monom 1) = a";
by (Asm_simp_tac 1);
qed "EVAL2_monom1";

Goalw [EVAL2_def]
  "!! phi::'a::ring=>'b::ring. homo phi ==> EVAL2 phi a (monom n) = a ^ n";
by (Simp_tac 1);
by (nat_ind_tac "n" 1);  (* really a case split *)
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
qed "EVAL2_monom";

Goal
  "!! phi::'a::ring=>'b::ring. \
\    homo phi ==> EVAL2 phi a (b *s p) = phi b * EVAL2 phi a p";
by (asm_simp_tac
  (simpset() addsimps [const_mult_is_smult RS sym, EVAL2_homo, EVAL2_const]) 1);
qed "EVAL2_smult";

Goalw [EVAL_def] "!! a::'a::ring. homo (EVAL a)";
by (asm_simp_tac (simpset() addsimps [EVAL2_homo, id_homo]) 1);
qed "EVAL_homo";

Goalw [EVAL_def] "!! a::'a::ring. EVAL a (const b) = b";
by (asm_simp_tac (simpset() addsimps [EVAL2_const]) 1);
qed "EVAL_const";

Goalw [EVAL_def] "!! a::'a::ring. EVAL a (monom n) = a ^ n";
by (asm_simp_tac (simpset() addsimps [EVAL2_monom]) 1);
qed "EVAL_monom";

Goalw [EVAL_def] "!! a::'a::ring. EVAL a (b *s p) = b * EVAL a p";
by (asm_simp_tac (simpset() addsimps [EVAL2_smult]) 1);
qed "EVAL_smult";

(* Examples *)

Goal
  "EVAL (x::'a::ring) (a*X^2 + b*X^1 + c*X^0) = a * x ^ 2 + b * x ^ 1 + c";
by (asm_simp_tac (simpset() delsimps [power_Suc]
    addsimps [EVAL_homo, EVAL_monom, EVAL_smult]) 1);
result();

Goal
  "EVAL (y::'a::ring) \
\    (EVAL (const x) (monom 1 + const (a*X^2 + b*X^1 + c*X^0))) = \
\  x ^ 1 + (a * y ^ 2 + b * y ^ 1 + c)";
by (asm_simp_tac (simpset() delsimps [power_Suc]
    addsimps [EVAL_homo, EVAL_monom, EVAL_smult, EVAL_const]) 1);
result();

