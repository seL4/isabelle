(*
    Long division of polynomials
    $Id$
    Author: Clemens Ballarin, started 23 June 1999
*)

(* legacy bindings and theorems *)

val deg_aboveI = thm "deg_aboveI";
val smult_l_minus = thm "smult_l_minus";
val deg_monom_ring = thm "deg_monom_ring";
val deg_smult_ring = thm "deg_smult_ring";
val smult_l_distr = thm "smult_l_distr";
val smult_r_distr = thm "smult_r_distr";
val smult_r_minus = thm "smult_r_minus";
val smult_assoc2 = thm "smult_assoc2";
val smult_assoc1 = thm "smult_assoc1";
val monom_mult_smult = thm "monom_mult_smult";
val field_ax = thm "field_ax";
val lcoeff_nonzero = thm "lcoeff_nonzero";

Goal
  "!! f::(nat=>'a::ring). \
\    (ALL i. i < m --> f i = 0) --> \
\      setsum (%i. f (i+m)) {..d} = setsum f {..m+d}";
by (induct_tac "d" 1);
(* Base case *)
by (induct_tac "m" 1);
by (Simp_tac 1);
by (Force_tac 1);
(* Induction step *)
by (asm_simp_tac (simpset() addsimps add_ac) 1);
val SUM_shrink_below_lemma = result();

Goal
  "!! f::(nat=>'a::ring). \
\    [| m <= n; !!i. i < m ==> f i = 0; P (setsum (%i. f (i+m)) {..n-m}) |] \
\    ==> P (setsum f {..n})";
by (asm_full_simp_tac 
    (simpset() addsimps [SUM_shrink_below_lemma, add_diff_inverse, leD]) 1);
qed "SUM_extend_below";

Goal
  "!! p::'a::ring up. \
\  [| deg p <= n; P (setsum (%i. monom (coeff p i) i) {..n}) |] \
\    ==> P p";
by (asm_full_simp_tac (simpset() addsimps [thm "up_repr_le"]) 1);
qed "up_repr2D";

(* Start of LongDiv *)

Goal
  "!!p::('a::ring up). \
\    [| deg p <= deg r; deg q <= deg r; \
\       coeff p (deg r) = - (coeff q (deg r)); deg r ~= 0 |] ==> \
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
\       p ~= -q; coeff p (deg r) = - (coeff q (deg r)) |] ==> \
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
  "!!g::('a::ring up). g ~= 0 ==> \
\    Ex (% (q, r, k). \
\      (lcoeff g)^k *s f = q * g + r & (eucl_size r < eucl_size g))";
by (res_inst_tac [("P", "%f. Ex (% (q, r, k). \
\      (lcoeff g)^k *s f = q * g + r & (eucl_size r < eucl_size g))")]
  wf_induct 1);
(* TO DO: replace by measure_induct *)
by (res_inst_tac [("f", "eucl_size")] wf_measure 1);
by (case_tac "eucl_size x < eucl_size g" 1);
by (res_inst_tac [("x", "(0, x, 0)")] exI 1);
by (Asm_simp_tac 1);
(* case "eucl_size x >= eucl_size g" *)
by (dres_inst_tac [("x", "lcoeff g *s x - (monom (lcoeff x) (deg x - deg g)) * g")] spec 1);
by (etac impE 1);
by (full_simp_tac (simpset() addsimps [inv_image_def, measure_def, lcoeff_def]) 1);
by (case_tac "x = 0" 1);
by (rotate_tac ~1 1);
by (asm_full_simp_tac (simpset() addsimps [eucl_size_def]) 1);
(* case "x ~= 0 *)
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
(**)
  by (rtac add_le_mono 1); by (rtac le_refl 1);
    (* term order forces to use this instead of add_le_mono1 *)
  by (rtac deg_monom_ring 1);
  by (Asm_simp_tac 1);
(**)
(*
  by (rtac add_le_mono1 1);
  by (rtac deg_smult_ring 1);
(*  by (asm_simp_tac (simpset() addsimps [leI]) 1); *)
  by (Asm_simp_tac 1);
  by (cut_inst_tac [("m", "deg x - deg g"), ("'a", "'a")] deg_monom_ring 1);
  by (arith_tac 1);
*)
by (Force_tac 1);
by (Simp_tac 1);
(**)
  (* This change is probably caused by application of commutativity *)
by (res_inst_tac [("m", "deg g"), ("n", "deg x")] SUM_extend 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
by (arith_tac 1);
by (res_inst_tac [("m", "deg g"), ("n", "deg g")] SUM_extend_below 1);
by (rtac le_refl 1);
by (Asm_simp_tac 1);
by (arith_tac 1);
by (Simp_tac 1);
(**)
(*
by (res_inst_tac [("m", "deg x - deg g"), ("n", "deg x")] SUM_extend 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [less_not_refl2 RS not_sym]) 1);
by (res_inst_tac [("m", "deg x - deg g"), ("n", "deg x - deg g")]
    SUM_extend_below 1);
by (rtac le_refl 1);
by (asm_simp_tac (simpset() addsimps [less_not_refl2]) 1);
by (asm_simp_tac (simpset() addsimps [diff_diff_right, leI, m_comm]) 1);
*)
(* end of subproof deg f1 < deg f *)
by (etac exE 1);
by (res_inst_tac [("x", "((%(q,r,k). (monom (lcoeff g ^ k * lcoeff x) (deg x - deg g) + q)) xa, (%(q,r,k). r) xa, (%(q,r,k). Suc k) xa)")] exI 1);
by (Clarify_tac 1);
by (dtac sym 1);
by (simp_tac (simpset() addsimps [l_distr, a_assoc]
  delsimprocs [ring_simproc]) 1);
by (asm_simp_tac (simpset() delsimprocs [ring_simproc]) 1);
by (simp_tac (simpset() addsimps [minus_def, smult_r_distr, smult_r_minus,
    monom_mult_smult, smult_assoc1, smult_assoc2]
  delsimprocs [ring_simproc]) 1);
by (Simp_tac 1);
qed "long_div_eucl_size";

Goal
  "!!g::('a::ring up). g ~= 0 ==> \
\    Ex (% (q, r, k). \
\      (lcoeff g)^k *s f = q * g + r & (r = 0 | deg r < deg g))";
by (forw_inst_tac [("f", "f")]
  (simplify (simpset() addsimps [eucl_size_def]
    delsimprocs [ring_simproc]) long_div_eucl_size) 1);
by (auto_tac (claset(), simpset() delsimprocs [ring_simproc]));
by (case_tac "aa = 0" 1);
by (Blast_tac 1);
(* case "aa ~= 0 *)
by (rotate_tac ~1 1);
by Auto_tac;
qed "long_div_ring";

(* Next one fails *)
Goal
  "!!g::('a::ring up). [| g ~= 0; (lcoeff g) dvd 1 |] ==> \
\    Ex (% (q, r). f = q * g + r & (r = 0 | deg r < deg g))";
by (forw_inst_tac [("f", "f")] long_div_ring 1);
by (etac exE 1);
by (res_inst_tac [("x", "((%(q,r,k). (inverse(lcoeff g ^k) *s q)) x, \
\  (%(q,r,k). inverse(lcoeff g ^k) *s r) x)")] exI 1);
by (Clarify_tac 1);
(* by (Simp_tac 1); *)
by (rtac conjI 1);
by (dtac sym 1);
by (asm_simp_tac (simpset() addsimps [smult_r_distr RS sym, smult_assoc2]
  delsimprocs [ring_simproc]) 1);
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
  "!!g::('a::field up). g ~= 0 ==> \
\    Ex (% (q, r). f = q * g + r & (r = 0 | deg r < deg g))";
by (rtac long_div_unit 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps [lcoeff_def, lcoeff_nonzero, field_ax]) 1);
qed "long_div_theorem";

Goal "- (0::'a::ring) = 0";
by (Simp_tac 1);
val uminus_zero = result();

Goal "!!a::'a::ring. a - b = 0 ==> a = b";
br trans 1;
by (res_inst_tac [("b", "a")] (thm "bug") 2);
by (Asm_simp_tac 1);
val diff_zero_imp_eq = result();

Goal "!!a::'a::ring. a = b ==> a + (-b) = 0";
by (Asm_simp_tac 1);
val eq_imp_diff_zero = result();

Goal
  "!!g::('a::field up). [| g ~= 0; \
\    f = q1 * g + r1; (r1 = 0 | deg r1 < deg g); \
\    f = q2 * g + r2; (r2 = 0 | deg r2 < deg g) |] ==> q1 = q2";
by (subgoal_tac "(q1 - q2) * g = r2 - r1" 1); (* 1 *)
by (thin_tac "f = ?x" 1);
by (thin_tac "f = ?x" 1);
by (rtac diff_zero_imp_eq 1);
by (rtac classical 1);
by (etac disjE 1);
(* r1 = 0 *)
by (etac disjE 1);
(* r2 = 0 *)
by (asm_full_simp_tac (simpset()
  addsimps [thm "integral_iff", minus_def, l_zero, uminus_zero]
  delsimprocs [ring_simproc]) 1);
(* r2 ~= 0 *)
by (dres_inst_tac [("f", "deg"), ("y", "r2 - r1")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [minus_def, l_zero, uminus_zero]
  delsimprocs [ring_simproc]) 1);
(* r1 ~=0 *)
by (etac disjE 1);
(* r2 = 0 *)
by (dres_inst_tac [("f", "deg"), ("y", "r2 - r1")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [minus_def, l_zero, uminus_zero]
  delsimprocs [ring_simproc]) 1);
(* r2 ~= 0 *)
by (dres_inst_tac [("f", "deg"), ("y", "r2 - r1")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [minus_def]
  delsimprocs [ring_simproc]) 1);
by (dtac (order_eq_refl RS add_leD2) 1);
by (dtac leD 1);
by (etac notE 1 THEN rtac (deg_add RS le_less_trans) 1);
by (Asm_simp_tac 1);
(* proof of 1 *)
by (rtac diff_zero_imp_eq 1);
by (hyp_subst_tac 1);
by (dres_inst_tac [("a", "?x+?y")] eq_imp_diff_zero 1);
by (Asm_full_simp_tac 1);
qed "long_div_quo_unique";

Goal
  "!!g::('a::field up). [| g ~= 0; \
\    f = q1 * g + r1; (r1 = 0 | deg r1 < deg g); \
\    f = q2 * g + r2; (r2 = 0 | deg r2 < deg g) |] ==> r1 = r2";
by (subgoal_tac "q1 = q2" 1);
by (Clarify_tac 1);
by (res_inst_tac [("a", "q2 * g + r1 - q2 * g"), ("b", "q2 * g + r2 - q2 * g")]
  box_equals 1);
by (Asm_full_simp_tac 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (rtac long_div_quo_unique 1);
by (REPEAT (atac 1));
qed "long_div_rem_unique";
