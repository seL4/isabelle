(*
    Long division of polynomials
    $Id$
    Author: Clemens Ballarin, started 23 June 1999
*)

Goal
  "!!p::('a::ring up). \
\    [| deg p <= deg r; deg q <= deg r; \
\       coeff (deg r) p = - (coeff (deg r) q); deg r ~= 0 |] ==> \
\    deg (p + q) < deg r";
by (res_inst_tac [("j", "deg r - 1")] le_less_trans 1);
by (arith_tac 2);
by (rtac deg_aboveI 1);
by (strip_tac 1);
by (case_tac "deg r = m" 1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
(* case "deg q ~= m" *)
by (subgoal_tac "deg p < m & deg q < m" 1);
by (asm_simp_tac (simpset() addsimps [deg_aboveD]) 1);
by (arith_tac 1);
qed "deg_lcoeff_cancel";

Goal
  "!!p::('a::ring up). \
\    [| deg p <= deg r; deg q <= deg r; \
\       p ~= -q; coeff (deg r) p = - (coeff (deg r) q) |] ==> \
\    deg (p + q) < deg r";
by (rtac deg_lcoeff_cancel 1);
by (REPEAT (atac 1));
by (rtac classical 1);
by (Clarify_tac 1);
by (etac notE 1);
by (res_inst_tac [("p", "p")] up_repr2D 1 THEN atac 1);
by (res_inst_tac [("p", "q")] up_repr2D 1 THEN atac 1);
by (rotate_tac ~1 1);
by (asm_full_simp_tac (simpset() addsimps [smult_l_minus]) 1);
qed "deg_lcoeff_cancel2";

Goal
  "!!g::('a::ring up). g ~= <0> ==> \
\    Ex (% (q, r, k). \
\      (lcoeff g)^k *s f = q * g + r & (eucl_size r < eucl_size g))";
by (res_inst_tac [("P", "%f. Ex (% (q, r, k). \
\      (lcoeff g)^k *s f = q * g + r & (eucl_size r < eucl_size g))")]
  wf_induct 1);
(* TO DO: replace by measure_induct *)
by (res_inst_tac [("f", "eucl_size")] wf_measure 1);
by (case_tac "eucl_size x < eucl_size g" 1);
by (res_inst_tac [("x", "(<0>, x, 0)")] exI 1);
by (Asm_simp_tac 1);
(* case "eucl_size x >= eucl_size g" *)
by (dres_inst_tac [("x", "lcoeff g *s x -- (lcoeff x *s monom (deg x - deg g)) * g")] spec 1);
by (etac impE 1);
by (full_simp_tac (simpset() addsimps [inv_image_def, measure_def, lcoeff_def]) 1);
by (case_tac "x = <0>" 1);
by (rotate_tac ~1 1);
by (asm_full_simp_tac (simpset() addsimps [eucl_size_def]) 1);
(* case "x ~= <0> *)
by (rotate_tac ~1 1);
by (asm_full_simp_tac (simpset() addsimps [eucl_size_def]) 1);
by (Simp_tac 1);
by (rtac impI 1);
by (rtac deg_lcoeff_cancel2 1);
  (* replace by linear arithmetic??? *)
  by (rtac le_trans 1);
  by (rtac deg_smult_ring 1);
  by (Simp_tac 1);
  by (Simp_tac 1);
  by (rtac le_trans 1);
  by (rtac deg_mult_ring 1);
  by (rtac le_trans 1);
  by (rtac add_le_mono1 1);
  by (rtac deg_smult_ring 1);
  by (asm_simp_tac (simpset() addsimps [leI]) 1);
by (Force_tac 1);
by (Simp_tac 1);
by (res_inst_tac [("m", "deg x - deg g"), ("n", "deg x")] SUM_extend 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [less_not_refl2 RS not_sym]) 1);
by (res_inst_tac [("m", "deg x - deg g"), ("n", "deg x - deg g")]
    SUM_extend_below 1);
by (rtac le_refl 1);
by (asm_simp_tac (simpset() addsimps [less_not_refl2]) 1);
by (asm_simp_tac (simpset() addsimps [diff_diff_right, leI, m_comm]) 1);
(* end of subproof deg f1 < deg f *)
by (etac exE 1);
by (res_inst_tac [("x", "((%(q,r,k). ((lcoeff g ^ k * lcoeff x) *s monom (deg x - deg g) + q)) xa, (%(q,r,k). r) xa, (%(q,r,k). Suc k) xa)")] exI 1);
by (Clarify_tac 1);
by (rtac conjI 1);
by (dtac sym 1);
by (simp_tac (simpset() addsimps [l_distr, a_assoc]) 1);
by (Asm_simp_tac 1);
by (simp_tac (simpset() addsimps a_ac@[smult_l_distr, smult_r_distr, smult_r_minus, smult_assoc2, smult_assoc1]) 1);
by Auto_tac;
qed "long_div_eucl_size";

Goal
  "!!g::('a::ring up). g ~= <0> ==> \
\    Ex (% (q, r, k). \
\      (lcoeff g)^k *s f = q * g + r & (r = <0> | deg r < deg g))";
by (forw_inst_tac [("f", "f")]
  (simplify (simpset() addsimps [eucl_size_def]) long_div_eucl_size) 1);
by Auto_tac;
by (case_tac "aa = <0>" 1);
by (Blast_tac 1);
(* case "aa ~= <0> *)
by (rotate_tac ~1 1);
by Auto_tac;
qed "long_div_ring";

Goal
  "!!g::('a::ring up). [| g ~= <0>; (lcoeff g) dvd <1> |] ==> \
\    Ex (% (q, r). f = q * g + r & (r = <0> | deg r < deg g))";
by (forw_inst_tac [("f", "f")] long_div_ring 1);
by (etac exE 1);
by (res_inst_tac [("x", "((%(q,r,k). (inverse(lcoeff g ^k) *s q)) x, \
\  (%(q,r,k). inverse(lcoeff g ^k) *s r) x)")] exI 1);
by (Clarify_tac 1);
by (Simp_tac 1);
by (rtac conjI 1);
by (dtac sym 1);
by (asm_simp_tac (simpset() addsimps [smult_r_distr RS sym, smult_assoc2]) 1);
by (asm_simp_tac (simpset() addsimps [l_inverse_ring, unit_power, smult_assoc1 RS sym]) 1);
(* degree property *)
by (etac disjE 1);
by (Asm_simp_tac 1);
by (rtac disjI2 1);
by (rtac le_less_trans 1);
by (rtac deg_smult_ring 1);
by (Asm_simp_tac 1);
qed "long_div_unit";

Goal
  "!!g::('a::field up). g ~= <0> ==> \
\    Ex (% (q, r). f = q * g + r & (r = <0> | deg r < deg g))";
by (rtac long_div_unit 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps [lcoeff_def, nonzero_lcoeff, field_ax]) 1);
qed "long_div_theorem";

Goal
  "!!g::('a::field up). [| g ~= <0>; \
\    f = q1 * g + r1; (r1 = <0> | deg r1 < deg g); \
\    f = q2 * g + r2; (r2 = <0> | deg r2 < deg g) |] ==> q1 = q2";
by (subgoal_tac "(q1 -- q2) * g = r2 -- r1" 1); (* 1 *)
by (thin_tac "f = ?x" 1);
by (thin_tac "f = ?x" 1);
by (rtac diff_zero_imp_eq 1);
by (rtac classical 1);
by (etac disjE 1);
(* r1 = <0> *)
by (etac disjE 1);
(* r2 = <0> *)
by (force_tac (claset() addDs [integral], simpset()) 1);
(* r2 ~= <0> *)
by (dres_inst_tac [("f", "deg"), ("y", "r2 -- r1")] arg_cong 1);
by (Force_tac 1);
(* r1 ~=<0> *)
by (etac disjE 1);
(* r2 = <0> *)
by (dres_inst_tac [("f", "deg"), ("y", "r2 -- r1")] arg_cong 1);
by (Force_tac 1);
(* r2 ~= <0> *)
by (dres_inst_tac [("f", "deg"), ("y", "r2 -- r1")] arg_cong 1);
by (Asm_full_simp_tac 1);
by (dtac (order_eq_refl RS add_leD2) 1);
by (dtac leD 1);
by (etac notE 1 THEN rtac (deg_add RS le_less_trans) 1);
by (Asm_simp_tac 1);
(* proof of 1 *)
by (rtac diff_zero_imp_eq 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("a", "?x+?y")] eq_imp_diff_zero 1);
by (asm_full_simp_tac (simpset() addsimps (l_distr::minus_add::l_minus::a_ac)) 1);
qed "long_div_quo_unique";

Goal
  "!!g::('a::field up). [| g ~= <0>; \
\    f = q1 * g + r1; (r1 = <0> | deg r1 < deg g); \
\    f = q2 * g + r2; (r2 = <0> | deg r2 < deg g) |] ==> r1 = r2";
by (subgoal_tac "q1 = q2" 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [a_lcancel_eq]) 1);
by (rtac long_div_quo_unique 1);
by (REPEAT (atac 1));
qed "long_div_rem_unique";
