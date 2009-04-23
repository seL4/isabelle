(*
    Experimental theory: long division of polynomials
    Author: Clemens Ballarin, started 23 June 1999
*)

theory LongDiv imports PolyHomo begin

definition
  lcoeff :: "'a::ring up => 'a" where
  "lcoeff p = coeff p (deg p)"

definition
  eucl_size :: "'a::zero up => nat" where
  "eucl_size p = (if p = 0 then 0 else deg p + 1)"

lemma SUM_shrink_below_lemma:
  "!! f::(nat=>'a::ring). (ALL i. i < m --> f i = 0) --> 
  setsum (%i. f (i+m)) {..d} = setsum f {..m+d}"
  apply (induct_tac d)
   apply (induct_tac m)
    apply simp
   apply force
  apply (simp add: add_commute [of m]) 
  done

lemma SUM_extend_below: 
  "!! f::(nat=>'a::ring).  
     [| m <= n; !!i. i < m ==> f i = 0; P (setsum (%i. f (i+m)) {..n-m}) |]  
     ==> P (setsum f {..n})"
  by (simp add: SUM_shrink_below_lemma add_diff_inverse leD)

lemma up_repr2D: 
  "!! p::'a::ring up.  
   [| deg p <= n; P (setsum (%i. monom (coeff p i) i) {..n}) |]  
     ==> P p"
  by (simp add: up_repr_le)


(* Start of LongDiv *)

lemma deg_lcoeff_cancel: 
  "!!p::('a::ring up).  
     [| deg p <= deg r; deg q <= deg r;  
        coeff p (deg r) = - (coeff q (deg r)); deg r ~= 0 |] ==>  
     deg (p + q) < deg r"
  apply (rule le_less_trans [of _ "deg r - 1"])
   prefer 2
   apply arith
  apply (rule deg_aboveI)
  apply (case_tac "deg r = m")
   apply clarify
   apply simp
  (* case "deg q ~= m" *)
   apply (subgoal_tac "deg p < m & deg q < m")
    apply (simp (no_asm_simp) add: deg_aboveD)
  apply arith
  done

lemma deg_lcoeff_cancel2: 
  "!!p::('a::ring up).  
     [| deg p <= deg r; deg q <= deg r;  
        p ~= -q; coeff p (deg r) = - (coeff q (deg r)) |] ==>  
     deg (p + q) < deg r"
  apply (rule deg_lcoeff_cancel)
     apply assumption+
  apply (rule classical)
  apply clarify
  apply (erule notE)
  apply (rule_tac p = p in up_repr2D, assumption)
  apply (rule_tac p = q in up_repr2D, assumption)
  apply (rotate_tac -1)
  apply (simp add: smult_l_minus)
  done

lemma long_div_eucl_size: 
  "!!g::('a::ring up). g ~= 0 ==>  
     Ex (% (q, r, k).  
       (lcoeff g)^k *s f = q * g + r & (eucl_size r < eucl_size g))"
  apply (rule_tac P = "%f. Ex (% (q, r, k) . (lcoeff g) ^k *s f = q * g + r & (eucl_size r < eucl_size g))" in wf_induct)
  (* TO DO: replace by measure_induct *)
  apply (rule_tac f = eucl_size in wf_measure)
  apply (case_tac "eucl_size x < eucl_size g")
   apply (rule_tac x = "(0, x, 0)" in exI)
   apply (simp (no_asm_simp))
  (* case "eucl_size x >= eucl_size g" *)
  apply (drule_tac x = "lcoeff g *s x - (monom (lcoeff x) (deg x - deg g)) * g" in spec)
  apply (erule impE)
   apply (simp (no_asm_use) add: inv_image_def measure_def lcoeff_def)
   apply (case_tac "x = 0")
    apply (rotate_tac -1)
    apply (simp add: eucl_size_def)
    (* case "x ~= 0 *)
    apply (rotate_tac -1)
   apply (simp add: eucl_size_def)
   apply (rule impI)
   apply (rule deg_lcoeff_cancel2)
  (* replace by linear arithmetic??? *)
      apply (rule_tac [2] le_trans)
       apply (rule_tac [2] deg_smult_ring)
      prefer 2
      apply simp
     apply (simp (no_asm))
     apply (rule le_trans)
      apply (rule deg_mult_ring)
     apply (rule le_trans)
(**)
      apply (rule add_le_mono)
       apply (rule le_refl)
    (* term order forces to use this instead of add_le_mono1 *)
      apply (rule deg_monom_ring)
     apply (simp (no_asm_simp))
    apply force
   apply (simp (no_asm))
(**)
   (* This change is probably caused by application of commutativity *)
   apply (rule_tac m = "deg g" and n = "deg x" in SUM_extend)
     apply (simp (no_asm))
    apply (simp (no_asm_simp))
    apply arith
   apply (rule_tac m = "deg g" and n = "deg g" in SUM_extend_below)
     apply (rule le_refl)
    apply (simp (no_asm_simp))
    apply arith
   apply (simp (no_asm))
(**)
(* end of subproof deg f1 < deg f *)
  apply (erule exE)
  apply (rule_tac x = "((% (q,r,k) . (monom (lcoeff g ^ k * lcoeff x) (deg x - deg g) + q)) xa, (% (q,r,k) . r) xa, (% (q,r,k) . Suc k) xa) " in exI)
  apply clarify
  apply (drule sym)
  apply (tactic {* simp_tac (@{simpset} addsimps [@{thm l_distr}, @{thm a_assoc}]
    delsimprocs [ring_simproc]) 1 *})
  apply (tactic {* asm_simp_tac (@{simpset} delsimprocs [ring_simproc]) 1 *})
  apply (tactic {* simp_tac (@{simpset} addsimps [thm "minus_def", thm "smult_r_distr",
    thm "smult_r_minus", thm "monom_mult_smult", thm "smult_assoc2"]
    delsimprocs [ring_simproc]) 1 *})
  apply (simp add: smult_assoc1 [symmetric])
  done

ML {*
 bind_thm ("long_div_ring_aux",
    simplify (@{simpset} addsimps [@{thm eucl_size_def}]
    delsimprocs [ring_simproc]) (@{thm long_div_eucl_size}))
*}

lemma long_div_ring: 
  "!!g::('a::ring up). g ~= 0 ==>  
     Ex (% (q, r, k).  
       (lcoeff g)^k *s f = q * g + r & (r = 0 | deg r < deg g))"
  apply (frule_tac f = f in long_div_ring_aux)
  apply (tactic {* auto_tac (@{claset}, @{simpset} delsimprocs [ring_simproc]) *})
  apply (case_tac "aa = 0")
   apply blast
  (* case "aa ~= 0 *)
  apply (rotate_tac -1)
  apply auto
  done

(* Next one fails *)
lemma long_div_unit: 
  "!!g::('a::ring up). [| g ~= 0; (lcoeff g) dvd 1 |] ==>  
     Ex (% (q, r). f = q * g + r & (r = 0 | deg r < deg g))"
  apply (frule_tac f = "f" in long_div_ring)
  apply (erule exE)
  apply (rule_tac x = "((% (q,r,k) . (inverse (lcoeff g ^k) *s q)) x, (% (q,r,k) . inverse (lcoeff g ^k) *s r) x) " in exI)
  apply clarify
  apply (rule conjI)
   apply (drule sym)
   apply (tactic {* asm_simp_tac
     (@{simpset} addsimps [thm "smult_r_distr" RS sym, thm "smult_assoc2"]
     delsimprocs [ring_simproc]) 1 *})
   apply (simp (no_asm_simp) add: l_inverse_ring unit_power smult_assoc1 [symmetric])
  (* degree property *)
   apply (erule disjE)
    apply (simp (no_asm_simp))
  apply (rule disjI2)
  apply (rule le_less_trans)
   apply (rule deg_smult_ring)
  apply (simp (no_asm_simp))
  done

lemma long_div_theorem: 
  "!!g::('a::field up). g ~= 0 ==>  
     Ex (% (q, r). f = q * g + r & (r = 0 | deg r < deg g))"
  apply (rule long_div_unit)
   apply assumption
  apply (simp (no_asm_simp) add: lcoeff_def lcoeff_nonzero field_ax)
  done

lemma uminus_zero: "- (0::'a::ring) = 0"
  by simp

lemma diff_zero_imp_eq: "!!a::'a::ring. a - b = 0 ==> a = b"
  apply (rule_tac s = "a - (a - b) " in trans)
   apply (tactic {* asm_simp_tac (@{simpset} delsimprocs [ring_simproc]) 1 *})
   apply simp
  apply (simp (no_asm))
  done

lemma eq_imp_diff_zero: "!!a::'a::ring. a = b ==> a + (-b) = 0"
  by simp

lemma long_div_quo_unique: 
  "!!g::('a::field up). [| g ~= 0;  
     f = q1 * g + r1; (r1 = 0 | deg r1 < deg g);  
     f = q2 * g + r2; (r2 = 0 | deg r2 < deg g) |] ==> q1 = q2"
  apply (subgoal_tac "(q1 - q2) * g = r2 - r1") (* 1 *)
   apply (erule_tac V = "f = ?x" in thin_rl)
  apply (erule_tac V = "f = ?x" in thin_rl)
  apply (rule diff_zero_imp_eq)
  apply (rule classical)
  apply (erule disjE)
  (* r1 = 0 *)
    apply (erule disjE)
  (* r2 = 0 *)
     apply (tactic {* asm_full_simp_tac (@{simpset}
       addsimps [thm "integral_iff", thm "minus_def", thm "l_zero", thm "uminus_zero"]
       delsimprocs [ring_simproc]) 1 *})
  (* r2 ~= 0 *)
    apply (drule_tac f = "deg" and y = "r2 - r1" in arg_cong)
    apply (tactic {* asm_full_simp_tac (@{simpset} addsimps
      [thm "minus_def", thm "l_zero", thm "uminus_zero"] delsimprocs [ring_simproc]) 1 *})
  (* r1 ~=0 *)
   apply (erule disjE)
  (* r2 = 0 *)
    apply (drule_tac f = "deg" and y = "r2 - r1" in arg_cong)
    apply (tactic {* asm_full_simp_tac (@{simpset} addsimps
      [thm "minus_def", thm "l_zero", thm "uminus_zero"] delsimprocs [ring_simproc]) 1 *})
  (* r2 ~= 0 *)
   apply (drule_tac f = "deg" and y = "r2 - r1" in arg_cong)
   apply (tactic {* asm_full_simp_tac (@{simpset} addsimps [thm "minus_def"]
     delsimprocs [ring_simproc]) 1 *})
   apply (drule order_eq_refl [THEN add_leD2])
   apply (drule leD)
   apply (erule notE, rule deg_add [THEN le_less_trans])
   apply (simp (no_asm_simp))
  (* proof of 1 *)
   apply (rule diff_zero_imp_eq)
  apply hypsubst
  apply (drule_tac a = "?x+?y" in eq_imp_diff_zero)
  apply simp
  done

lemma long_div_rem_unique: 
  "!!g::('a::field up). [| g ~= 0;  
     f = q1 * g + r1; (r1 = 0 | deg r1 < deg g);  
     f = q2 * g + r2; (r2 = 0 | deg r2 < deg g) |] ==> r1 = r2"
  apply (subgoal_tac "q1 = q2")
   apply (metis a_comm a_lcancel m_comm)
  apply (metis a_comm l_zero long_div_quo_unique m_comm conc)
  done

end
