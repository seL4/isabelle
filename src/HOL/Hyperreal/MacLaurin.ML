(*  Title       : MacLaurin.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh
    Description : MacLaurin series
*)

Goal "sumr 0 n (%m. f (m + k)) = sumr 0 (n + k) f - sumr 0 k f";
by (induct_tac "n" 1);
by Auto_tac;
qed "sumr_offset";

Goal "ALL f. sumr 0 n (%m. f (m + k)) = sumr 0 (n + k) f - sumr 0 k f";
by (induct_tac "n" 1);
by Auto_tac;
qed "sumr_offset2";

Goal "sumr 0 (n + k) f = sumr 0 n (%m. f (m + k)) + sumr 0 k f";
by (simp_tac (simpset() addsimps [sumr_offset]) 1);
qed "sumr_offset3";

Goal "ALL n f. sumr 0 (n + k) f = sumr 0 n (%m. f (m + k)) + sumr 0 k f";
by (simp_tac (simpset() addsimps [sumr_offset]) 1);
qed "sumr_offset4";

Goal "0 < n ==> \
\     sumr (Suc 0) (Suc n) (%n. (if even(n) then 0 else \
\            ((- 1) ^ ((n - (Suc 0)) div 2))/(real (fact n))) * a ^ n) = \
\     sumr 0 (Suc n) (%n. (if even(n) then 0 else \
\            ((- 1) ^ ((n - (Suc 0)) div 2))/(real (fact n))) * a ^ n)";
by (res_inst_tac [("n1","1")] (sumr_split_add RS subst) 1);
by Auto_tac;
qed "sumr_from_1_from_0";

(*---------------------------------------------------------------------------*)
(* Maclaurin's theorem with Lagrange form of remainder                       *)
(*---------------------------------------------------------------------------*)

(* Annoying: Proof is now even longer due mostly to 
   change in behaviour of simplifier  since Isabelle99 *)
Goal " [| 0 < h; 0 < n; diff 0 = f; \
\      ALL m t. \
\         m < n & 0 <= t & t <= h --> DERIV (diff m) t :> diff (Suc m) t |] \
\   ==> EX t. 0 < t & \
\             t < h & \
\             f h = \
\             sumr 0 n (%m. (diff m 0 / real (fact m)) * h ^ m) + \
\             (diff n t / real (fact n)) * h ^ n";
by (case_tac "n = 0" 1);
by (Force_tac 1);
by (dtac not0_implies_Suc 1);
by (etac exE 1);
by (subgoal_tac 
     "EX B. f h = sumr 0 n (%m. (diff m 0 / real (fact m)) * (h ^ m)) \
\                  + (B * ((h ^ n) / real (fact n)))" 1);

by (simp_tac (HOL_ss addsimps [real_add_commute, real_divide_def,
    ARITH_PROVE "(x = z + (y::real)) = (x - y = z)"]) 2);
by (res_inst_tac 
  [("x","(f(h) - sumr 0 n (%m. (diff(m)(0) / real (fact m)) * (h ^ m))) \
\        * real (fact n) / (h ^ n)")] exI 2);
by (simp_tac (HOL_ss addsimps [real_mult_assoc,real_divide_def]) 2);
 by (rtac (CLAIM "x = (1::real) ==>  a = a * (x::real)") 2);
by (asm_simp_tac (HOL_ss addsimps 
    [CLAIM "(a::real) * (b * (c * d)) = (d * a) * (b * c)"]
     delsimps [realpow_Suc]) 2);
by (stac left_inverse 2);
by (stac left_inverse 3);
by (rtac (real_not_refl2 RS not_sym) 2);
by (etac zero_less_power 2);
by (rtac real_of_nat_fact_not_zero 2);
by (Simp_tac 2);
by (etac exE 1);
by (cut_inst_tac [("b","%t. f t - \
\      (sumr 0 n (%m. (diff m 0 / real (fact m)) * (t ^ m)) + \
\                       (B * ((t ^ n) / real (fact n))))")] 
    (CLAIM "EX g. g = b") 1);
by (etac exE 1);
by (subgoal_tac "g 0 = 0 & g h =0" 1);
by (asm_simp_tac (simpset() addsimps 
    [ARITH_PROVE "(x - y = z) = (x = z + (y::real))"]
    delsimps [sumr_Suc]) 2);
by (cut_inst_tac [("n","m"),("k","1")] sumr_offset2 2);
by (asm_full_simp_tac (simpset() addsimps 
    [ARITH_PROVE "(x = y - z) = (y = x + (z::real))"]
    delsimps [sumr_Suc]) 2);
by (cut_inst_tac [("b","%m t. diff m t - \
\      (sumr 0 (n - m) (%p. (diff (m + p) 0 / real (fact p)) * (t ^ p)) \
\       + (B * ((t ^ (n - m)) / real (fact(n - m)))))")] 
    (CLAIM "EX difg. difg = b") 1);
by (etac exE 1);
by (subgoal_tac "difg 0 = g" 1);
by (asm_simp_tac (simpset() delsimps [realpow_Suc,fact_Suc]) 2);
by (subgoal_tac "ALL m t. m < n & 0 <= t & t <= h --> \
\                   DERIV (difg m) t :> difg (Suc m) t" 1);
by (Clarify_tac 2);
by (rtac DERIV_diff 2);
by (Asm_simp_tac 2);
by DERIV_tac;
by DERIV_tac;
by (rtac lemma_DERIV_subst 3);
by (rtac DERIV_quotient 3);
by (rtac DERIV_const 4);
by (rtac DERIV_pow 3);
by (asm_simp_tac (simpset() addsimps [inverse_mult_distrib,
    CLAIM_SIMP "(a::real) * b * c * (d * e) = a * b * (c * d) * e" 
    mult_ac,fact_diff_Suc]) 4);
by (Asm_simp_tac 3);
by (forw_inst_tac [("m","ma")] less_add_one 2);
by (Clarify_tac 2);
by (asm_simp_tac (simpset() addsimps 
    [CLAIM "Suc m = ma + d + 1 ==> m - ma = d"]
    delsimps [sumr_Suc]) 2);
by (asm_simp_tac (simpset() addsimps [(simplify (simpset() delsimps [sumr_Suc]) 
          (read_instantiate [("k","1")] sumr_offset4))] 
    delsimps [sumr_Suc,fact_Suc,realpow_Suc]) 2);
by (rtac lemma_DERIV_subst 2);
by (rtac DERIV_add 2);
by (rtac DERIV_const 3);
by (rtac DERIV_sumr 2);
by (Clarify_tac 2);
by (Simp_tac 3);
by (simp_tac (simpset() addsimps [real_divide_def,real_mult_assoc] 
    delsimps [fact_Suc,realpow_Suc]) 2);
by (rtac DERIV_cmult 2);
by (rtac lemma_DERIV_subst 2);
by DERIV_tac;
by (stac fact_Suc 2);
by (stac real_of_nat_mult 2);
by (simp_tac (simpset() addsimps [inverse_mult_distrib] @
    mult_ac) 2);
by (subgoal_tac "ALL ma. ma < n --> \
\        (EX t. 0 < t & t < h & difg (Suc ma) t = 0)" 1);
by (rotate_tac 11 1);
by (dres_inst_tac [("x","m")] spec 1);
by (etac impE 1);
by (Asm_simp_tac 1);
by (etac exE 1);
by (res_inst_tac [("x","t")] exI 1);
by (asm_full_simp_tac (simpset() addsimps 
     [ARITH_PROVE "(x - y = 0) = (y = (x::real))"] 
      delsimps [realpow_Suc,fact_Suc]) 1);
by (subgoal_tac "ALL m. m < n --> difg m 0 = 0" 1);
by (Clarify_tac 2);
by (Asm_simp_tac 2);
by (forw_inst_tac [("m","ma")] less_add_one 2);
by (Clarify_tac 2);
by (asm_simp_tac (simpset() delsimps [sumr_Suc]) 2);
by (asm_simp_tac (simpset() addsimps [(simplify (simpset() delsimps [sumr_Suc]) 
          (read_instantiate [("k","1")] sumr_offset4))] 
    delsimps [sumr_Suc,fact_Suc,realpow_Suc]) 2);
by (subgoal_tac "ALL m. m < n --> (EX t. 0 < t & t < h & \
\                DERIV (difg m) t :> 0)" 1);
by (rtac allI 1 THEN rtac impI 1);
by (rotate_tac 12 1);
by (dres_inst_tac [("x","ma")] spec 1);
by (etac impE 1 THEN assume_tac 1);
by (etac exE 1);
by (res_inst_tac [("x","t")] exI 1);
(* do some tidying up *)
by (ALLGOALS(thin_tac "difg = \
\          (%m t. diff m t - \
\                 (sumr 0 (n - m) \
\                   (%p. diff (m + p) 0 / real (fact p) * t ^ p) + \
\                  B * (t ^ (n - m) / real (fact (n - m)))))"));
by (ALLGOALS(thin_tac "g = \
\          (%t. f t - \
\               (sumr 0 n (%m. diff m 0 / real  (fact m) * t ^ m) + \
\                B * (t ^ n / real (fact n))))"));
by (ALLGOALS(thin_tac "f h = \
\          sumr 0 n (%m. diff m 0 / real (fact m) * h ^ m) + \
\          B * (h ^ n / real (fact n))"));
(* back to business *)
by (Asm_simp_tac 1);
by (rtac DERIV_unique 1);
by (Blast_tac 2);
by (Force_tac 1);
by (rtac allI 1 THEN induct_tac "ma" 1);
by (rtac impI 1 THEN rtac Rolle 1);
by (assume_tac 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "ALL t. 0 <= t & t <= h --> g differentiable t" 1);
by (asm_full_simp_tac (simpset() addsimps [differentiable_def]) 1);
by (blast_tac (claset() addDs [DERIV_isCont]) 1);
by (asm_full_simp_tac (simpset() addsimps [differentiable_def]) 1);
by (Clarify_tac 1);
by (res_inst_tac [("x","difg (Suc 0) t")] exI 1);
by (Force_tac 1);
by (asm_full_simp_tac (simpset() addsimps [differentiable_def]) 1);
by (Clarify_tac 1);
by (res_inst_tac [("x","difg (Suc 0) x")] exI 1);
by (Force_tac 1);
by (Step_tac 1);
by (Force_tac 1);
by (subgoal_tac "EX ta. 0 < ta & ta < t & \
\                DERIV difg (Suc n) ta :> 0" 1);
by (rtac Rolle 2 THEN assume_tac 2);
by (Asm_full_simp_tac 2);
by (rotate_tac 2 2);
by (dres_inst_tac [("x","n")] spec 2);
by (ftac (ARITH_PROVE "n < m  ==> n < Suc m") 2);
by (rtac DERIV_unique 2);
by (assume_tac 3);
by (Force_tac 2);
by (subgoal_tac 
    "ALL ta. 0 <= ta & ta <= t --> (difg (Suc n)) differentiable ta" 2);
by (asm_full_simp_tac (simpset() addsimps [differentiable_def]) 2);
by (blast_tac (claset() addSDs [DERIV_isCont]) 2);
by (asm_full_simp_tac (simpset() addsimps [differentiable_def]) 2);
by (Clarify_tac 2);
by (res_inst_tac [("x","difg (Suc (Suc n)) ta")] exI 2);
by (Force_tac 2);
by (asm_full_simp_tac (simpset() addsimps [differentiable_def]) 2);
by (Clarify_tac 2);
by (res_inst_tac [("x","difg (Suc (Suc n)) x")] exI 2);
by (Force_tac 2);
by (Step_tac 1);
by (res_inst_tac [("x","ta")] exI 1);
by (Force_tac 1);
qed "Maclaurin";

Goal "0 < h & 0 < n & diff 0 = f & \
\      (ALL m t. \
\         m < n & 0 <= t & t <= h --> DERIV (diff m) t :> diff (Suc m) t) \
\   --> (EX t. 0 < t & \
\             t < h & \
\             f h = \
\             sumr 0 n (%m. diff m 0 / real (fact m) * h ^ m) + \
\             diff n t / real (fact n) * h ^ n)";
by (blast_tac (claset() addIs [Maclaurin]) 1);
qed "Maclaurin_objl";

Goal " [| 0 < h; diff 0 = f; \
\      ALL m t. \
\         m < n & 0 <= t & t <= h --> DERIV (diff m) t :> diff (Suc m) t |] \
\   ==> EX t. 0 < t & \
\             t <= h & \
\             f h = \
\             sumr 0 n (%m. diff m 0 / real (fact m) * h ^ m) + \
\             diff n t / real (fact n) * h ^ n";
by (case_tac "n" 1);
by Auto_tac;
by (dtac Maclaurin 1 THEN Auto_tac);
qed "Maclaurin2";

Goal "0 < h & diff 0 = f & \
\      (ALL m t. \
\         m < n & 0 <= t & t <= h --> DERIV (diff m) t :> diff (Suc m) t) \
\   --> (EX t. 0 < t & \
\             t <= h & \
\             f h = \
\             sumr 0 n (%m. diff m 0 / real (fact m) * h ^ m) + \
\             diff n t / real (fact n) * h ^ n)";
by (blast_tac (claset() addIs [Maclaurin2]) 1);
qed "Maclaurin2_objl";

Goal " [| h < 0; 0 < n; diff 0 = f; \
\      ALL m t. \
\         m < n & h <= t & t <= 0 --> DERIV (diff m) t :> diff (Suc m) t |] \
\   ==> EX t. h < t & \
\             t < 0 & \
\             f h = \
\             sumr 0 n (%m. diff m 0 / real (fact m) * h ^ m) + \
\             diff n t / real (fact n) * h ^ n";
by (cut_inst_tac [("f","%x. f (-x)"),
                 ("diff","%n x. ((- 1) ^ n) * diff n (-x)"),
                 ("h","-h"),("n","n")] Maclaurin_objl 1);
by (Asm_full_simp_tac 1);
by (etac impE 1 THEN Step_tac 1);
by (stac minus_mult_right 1);
by (rtac DERIV_cmult 1);
by (rtac lemma_DERIV_subst 1);
by (rtac (read_instantiate [("g","uminus")] DERIV_chain2) 1);
by (rtac DERIV_minus 2 THEN rtac DERIV_Id 2);
by (Force_tac 2);
by (Force_tac 1);
by (res_inst_tac [("x","-t")] exI 1);
by Auto_tac;
by (rtac (CLAIM "[| x = x'; y = y' |] ==> x + y = x' + (y'::real)") 1);
by (rtac sumr_fun_eq 1);
by (Asm_full_simp_tac 1);
by (auto_tac (claset(),simpset() addsimps [real_divide_def,
    CLAIM "((a * b) * c) * d = (b * c) * (a * (d::real))",
    power_mult_distrib RS sym]));
qed "Maclaurin_minus";

Goal "(h < 0 & 0 < n & diff 0 = f & \
\      (ALL m t. \
\         m < n & h <= t & t <= 0 --> DERIV (diff m) t :> diff (Suc m) t))\
\   --> (EX t. h < t & \
\             t < 0 & \
\             f h = \
\             sumr 0 n (%m. diff m 0 / real (fact m) * h ^ m) + \
\             diff n t / real (fact n) * h ^ n)";
by (blast_tac (claset() addIs [Maclaurin_minus]) 1);
qed "Maclaurin_minus_objl";

(* ------------------------------------------------------------------------- *)
(* More convenient "bidirectional" version.                                  *)
(* ------------------------------------------------------------------------- *)

(* not good for PVS sin_approx, cos_approx *)
Goal " [| diff 0 = f; \
\      ALL m t. \
\         m < n & abs t <= abs x --> DERIV (diff m) t :> diff (Suc m) t |] \
\   ==> EX t. abs t <= abs x & \
\             f x = \
\             sumr 0 n (%m. diff m 0 / real (fact m) * x ^ m) + \
\             diff n t / real (fact n) * x ^ n";
by (case_tac "n = 0" 1);
by (Force_tac 1);
by (case_tac "x = 0" 1);
by (res_inst_tac [("x","0")] exI 1);
by (Asm_full_simp_tac 1);
by (res_inst_tac [("P","0 < n")] impE 1);
by (assume_tac 2 THEN assume_tac 2);
by (induct_tac "n" 1);
by (Simp_tac 1);
by Auto_tac;
by (cut_inst_tac [("x","x"),("y","0")] linorder_less_linear 1);
by Auto_tac;
by (cut_inst_tac [("f","diff 0"),
                 ("diff","diff"),
                 ("h","x"),("n","n")] Maclaurin_objl 2);
by (Step_tac 2);
by (blast_tac (claset() addDs 
    [ARITH_PROVE "[|(0::real) <= t;t <= x |] ==> abs t <= abs x"]) 2);
by (res_inst_tac [("x","t")] exI 2);
by (force_tac (claset() addIs 
    [ARITH_PROVE "[| 0 < t; (t::real) < x|] ==> abs t <= abs x"],simpset()) 2);
by (cut_inst_tac [("f","diff 0"),
                 ("diff","diff"),
                 ("h","x"),("n","n")] Maclaurin_minus_objl 1);
by (Step_tac 1);
by (blast_tac (claset() addDs 
    [ARITH_PROVE "[|x <= t;t <= (0::real) |] ==> abs t <= abs x"]) 1);
by (res_inst_tac [("x","t")] exI 1);
by (force_tac (claset() addIs 
    [ARITH_PROVE "[| x < t; (t::real) < 0|] ==> abs t <= abs x"],simpset()) 1);
qed "Maclaurin_bi_le";

Goal "[| diff 0 = f; \
\        ALL m x. DERIV (diff m) x :> diff(Suc m) x; \ 
\       x ~= 0; 0 < n \
\     |] ==> EX t. 0 < abs t & abs t < abs x & \
\              f x = sumr 0 n (%m. (diff m 0 / real (fact m)) * x ^ m) + \
\                    (diff n t / real (fact n)) * x ^ n";
by (res_inst_tac [("x","x"),("y","0")] linorder_cases 1);
by (Blast_tac 2);
by (dtac Maclaurin_minus 1);
by (dtac Maclaurin 5);
by (TRYALL(assume_tac));
by (Blast_tac 1);
by (Blast_tac 2);
by (Step_tac 1);
by (ALLGOALS(res_inst_tac [("x","t")] exI));
by (Step_tac 1);
by (ALLGOALS(arith_tac));
qed "Maclaurin_all_lt";

Goal "diff 0 = f & \
\     (ALL m x. DERIV (diff m) x :> diff(Suc m) x) & \
\     x ~= 0 & 0 < n \
\     --> (EX t. 0 < abs t & abs t < abs x & \
\              f x = sumr 0 n (%m. (diff m 0 / real (fact m)) * x ^ m) + \
\                    (diff n t / real (fact n)) * x ^ n)";
by (blast_tac (claset() addIs [Maclaurin_all_lt]) 1);
qed "Maclaurin_all_lt_objl";

Goal "x = (0::real)  \
\     ==> 0 < n --> \
\         sumr 0 n (%m. (diff m (0::real) / real (fact m)) * x ^ m) = \
\         diff 0 0";
by (Asm_simp_tac 1);
by (induct_tac "n" 1);
by Auto_tac; 
qed_spec_mp "Maclaurin_zero";

Goal "[| diff 0 = f; \
\       ALL m x. DERIV (diff m) x :> diff (Suc m) x \
\     |] ==> EX t. abs t <= abs x & \
\             f x = sumr 0 n (%m. (diff m 0 / real (fact m)) * x ^ m) + \
\                   (diff n t / real (fact n)) * x ^ n";
by (cut_inst_tac [("n","n"),("m","0")] 
       (ARITH_PROVE "n <= m | m < (n::nat)") 1);
by (etac disjE 1);
by (Force_tac 1);
by (case_tac "x = 0" 1);
by (forw_inst_tac [("diff","diff"),("n","n")] Maclaurin_zero 1);
by (assume_tac 1);
by (dtac (gr_implies_not0 RS  not0_implies_Suc) 1);
by (res_inst_tac [("x","0")] exI 1);
by (Force_tac 1);
by (forw_inst_tac [("diff","diff"),("n","n")] Maclaurin_all_lt 1);
by (TRYALL(assume_tac));
by (Step_tac 1);
by (res_inst_tac [("x","t")] exI 1);
by Auto_tac;
qed "Maclaurin_all_le";

Goal "diff 0 = f & \
\     (ALL m x. DERIV (diff m) x :> diff (Suc m) x)  \
\     --> (EX t. abs t <= abs x & \
\             f x = sumr 0 n (%m. (diff m 0 / real (fact m)) * x ^ m) + \
\                   (diff n t / real (fact n)) * x ^ n)";
by (blast_tac (claset() addIs [Maclaurin_all_le]) 1);
qed "Maclaurin_all_le_objl";

(* ------------------------------------------------------------------------- *)
(* Version for exp.                                                          *)
(* ------------------------------------------------------------------------- *)

Goal "[| x ~= 0; 0 < n |] \
\     ==> (EX t. 0 < abs t & \
\               abs t < abs x & \
\               exp x = sumr 0 n (%m. (x ^ m) / real (fact m)) + \
\                       (exp t / real (fact n)) * x ^ n)";
by (cut_inst_tac [("diff","%n. exp"),("f","exp"),("x","x"),("n","n")] 
    Maclaurin_all_lt_objl 1);
by Auto_tac;
qed "Maclaurin_exp_lt";

Goal "EX t. abs t <= abs x & \
\           exp x = sumr 0 n (%m. (x ^ m) / real (fact m)) + \
\                      (exp t / real (fact n)) * x ^ n";
by (cut_inst_tac [("diff","%n. exp"),("f","exp"),("x","x"),("n","n")] 
    Maclaurin_all_le_objl 1);
by Auto_tac;
qed "Maclaurin_exp_le";

(* ------------------------------------------------------------------------- *)
(* Version for sin function                                                  *)
(* ------------------------------------------------------------------------- *)

Goal "[| a < b; ALL x. a <= x & x <= b --> DERIV f x :> f'(x) |] \
\     ==> EX z. a < z & z < b & (f b - f a = (b - a) * f'(z))";
by (dtac MVT 1);
by (blast_tac (claset() addIs [DERIV_isCont]) 1);
by (force_tac (claset() addDs [order_less_imp_le],
    simpset() addsimps [differentiable_def]) 1);
by (blast_tac (claset() addDs [DERIV_unique,order_less_imp_le]) 1);
qed "MVT2";

Goal "d < (4::nat) ==> d = 0 | d = 1 | d = 2 | d = 3";
by (case_tac "d" 1 THEN Auto_tac);
qed "lemma_exhaust_less_4";

bind_thm ("real_mult_le_lemma",
          simplify (simpset()) (inst "b" "1" mult_right_mono));


Goal "abs(sin x - \
\          sumr 0 n (%m. (if even m then 0 \
\                         else ((- 1) ^ ((m - (Suc 0)) div 2)) / real (fact m)) * \
\                         x ^ m)) \
\      <= inverse(real (fact n)) * abs(x) ^ n";
by (cut_inst_tac [("f","sin"),("n","n"),("x","x"),
       ("diff","%n x. if n mod 4 = 0 then sin(x) \
\                     else if n mod 4 = 1 then cos(x) \
\                     else if n mod 4 = 2 then -sin(x) \
\                     else -cos(x)")] Maclaurin_all_le_objl 1);
by (Step_tac 1);
by (Asm_full_simp_tac 1);
by (stac mod_Suc_eq_Suc_mod 1);
by (cut_inst_tac [("m1","m")] (CLAIM "0 < (4::nat)" RS mod_less_divisor
    RS lemma_exhaust_less_4) 1);
by (Step_tac 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (rtac DERIV_minus 1 THEN Simp_tac 1);
by (Asm_simp_tac 1);
by (rtac lemma_DERIV_subst 1 THEN rtac DERIV_minus 1 THEN rtac DERIV_cos 1);
by (Simp_tac 1);
by (dtac ssubst 1 THEN assume_tac 2);
by (rtac (ARITH_PROVE "[|x = y; abs u <= (v::real) |] ==> abs ((x + u) - y) <= v") 1);
by (rtac sumr_fun_eq 1);
by (Step_tac 1);
by (rtac (CLAIM "x = y ==> x * z = y * (z::real)") 1);
by (stac even_even_mod_4_iff 1);
by (cut_inst_tac [("m1","r")] (CLAIM "0 < (4::nat)" RS mod_less_divisor
    RS lemma_exhaust_less_4) 1);
by (Step_tac 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [even_num_iff]) 2);
by (asm_simp_tac (simpset() addsimps [even_num_iff]) 1);
by (asm_simp_tac (simpset() addsimps [even_num_iff]) 2);
by (dtac lemma_even_mod_4_div_2 1);
by (asm_full_simp_tac (simpset() addsimps [numeral_2_eq_2,real_divide_def]) 1);
by (dtac lemma_odd_mod_4_div_2 1);
by (asm_full_simp_tac (simpset() addsimps [numeral_2_eq_2, real_divide_def]) 1);
by (auto_tac (claset() addSIs [real_mult_le_lemma,mult_right_mono],
      simpset() addsimps [real_divide_def,abs_mult,abs_inverse,power_abs RS
sym]));
qed "Maclaurin_sin_bound";

Goal "0 < n --> Suc (Suc (2 * n - 2)) = 2*n";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "Suc_Suc_mult_two_diff_two";
Addsimps [Suc_Suc_mult_two_diff_two];

Goal "0 < n --> Suc (Suc (4*n - 2)) = 4*n";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "lemma_Suc_Suc_4n_diff_2";
Addsimps [lemma_Suc_Suc_4n_diff_2];

Goal "0 < n --> Suc (2 * n - 1) = 2*n";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "Suc_mult_two_diff_one";
Addsimps [Suc_mult_two_diff_one];

Goal "EX t. sin x = \
\      (sumr 0 n (%m. (if even m then 0 \
\                      else ((- 1) ^ ((m - (Suc 0)) div 2)) / real (fact m)) * \
\                      x ^ m)) \
\     + ((sin(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)";
by (cut_inst_tac [("f","sin"),("n","n"),("x","x"),
       ("diff","%n x. sin(x + 1/2*real (n)*pi)")] 
       Maclaurin_all_lt_objl 1);
by (Safe_tac);
by (Simp_tac 1);
by (Simp_tac 1);
by (case_tac "n" 1);
by (Clarify_tac 1); 
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("x","0")] spec 1 THEN Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (rtac ccontr 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("x","x")] spec 1 THEN Asm_full_simp_tac 1);
by (dtac ssubst 1 THEN assume_tac 2);
by (res_inst_tac [("x","t")] exI 1);
by (rtac (CLAIM "[|x = y; x' = y'|] ==> x + x' = y + (y'::real)") 1);
by (rtac sumr_fun_eq 1);
by (auto_tac (claset(),simpset() addsimps [odd_not_even RS sym]));
by (auto_tac (claset(),simpset() addsimps [odd_Suc_mult_two_ex,
    even_mult_two_ex] delsimps [fact_Suc,realpow_Suc]));
qed "Maclaurin_sin_expansion";

Goal "EX t. abs t <= abs x &  \
\      sin x = \
\      (sumr 0 n (%m. (if even m then 0 \
\                      else ((- 1) ^ ((m - (Suc 0)) div 2)) / real (fact m)) * \
\                      x ^ m)) \
\     + ((sin(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)";

by (cut_inst_tac [("f","sin"),("n","n"),("x","x"),
       ("diff","%n x. sin(x + 1/2*real (n)*pi)")] 
       Maclaurin_all_lt_objl 1);
by (Step_tac 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (case_tac "n" 1);
by (Clarify_tac 1); 
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (rtac ccontr 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("x","x")] spec 1 THEN Asm_full_simp_tac 1);
by (dtac ssubst 1 THEN assume_tac 2);
by (res_inst_tac [("x","t")] exI 1);
by (rtac conjI 1);
by (arith_tac 1);
by (rtac (CLAIM "[|x = y; x' = y'|] ==> x + x' = y + (y'::real)") 1);
by (rtac sumr_fun_eq 1);
by (auto_tac (claset(),simpset() addsimps [odd_not_even RS sym]));
by (auto_tac (claset(),simpset() addsimps [odd_Suc_mult_two_ex,
    even_mult_two_ex] delsimps [fact_Suc,realpow_Suc]));
qed "Maclaurin_sin_expansion2";

Goal "[| 0 < n; 0 < x |] ==> \
\      EX t. 0 < t & t < x & \
\      sin x = \
\      (sumr 0 n (%m. (if even m then 0 \
\                      else ((- 1) ^ ((m - (Suc 0)) div 2)) / real (fact m)) * \
\                      x ^ m)) \
\     + ((sin(t + 1/2 * real(n) *pi) / real (fact n)) * x ^ n)";
by (cut_inst_tac [("f","sin"),("n","n"),("h","x"),
       ("diff","%n x. sin(x + 1/2*real (n)*pi)")] 
       Maclaurin_objl 1);
by (Step_tac 1);
by (Asm_full_simp_tac 1);
by (Simp_tac 1);
by (dtac ssubst 1 THEN assume_tac 2);
by (res_inst_tac [("x","t")] exI 1);
by (rtac conjI 1 THEN rtac conjI 2);
by (assume_tac 1 THEN assume_tac 1);
by (rtac (CLAIM "[|x = y; x' = y'|] ==> x + x' = y + (y'::real)") 1);
by (rtac sumr_fun_eq 1);
by (auto_tac (claset(),simpset() addsimps [odd_not_even RS sym]));
by (auto_tac (claset(),simpset() addsimps [odd_Suc_mult_two_ex,
    even_mult_two_ex] delsimps [fact_Suc,realpow_Suc]));
qed "Maclaurin_sin_expansion3";

Goal "0 < x ==> \
\      EX t. 0 < t & t <= x & \
\      sin x = \
\      (sumr 0 n (%m. (if even m then 0 \
\                      else ((- 1) ^ ((m - (Suc 0)) div 2)) / real (fact m)) * \
\                      x ^ m)) \
\     + ((sin(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)";
by (cut_inst_tac [("f","sin"),("n","n"),("h","x"),
       ("diff","%n x. sin(x + 1/2*real (n)*pi)")] 
       Maclaurin2_objl 1);
by (Step_tac 1);
by (Asm_full_simp_tac 1);
by (Simp_tac 1);
by (dtac ssubst 1 THEN assume_tac 2);
by (res_inst_tac [("x","t")] exI 1);
by (rtac conjI 1 THEN rtac conjI 2);
by (assume_tac 1 THEN assume_tac 1);
by (rtac (CLAIM "[|x = y; x' = y'|] ==> x + x' = y + (y'::real)") 1);
by (rtac sumr_fun_eq 1);
by (auto_tac (claset(),simpset() addsimps [odd_not_even RS sym]));
by (auto_tac (claset(),simpset() addsimps [odd_Suc_mult_two_ex,
    even_mult_two_ex] delsimps [fact_Suc,realpow_Suc]));
qed "Maclaurin_sin_expansion4";

(*-----------------------------------------------------------------------------*)
(* Maclaurin expansion for cos                                                 *)
(*-----------------------------------------------------------------------------*)

Goal "sumr 0 (Suc n) \
\        (%m. (if even m \
\              then (- 1) ^ (m div 2)/(real  (fact m)) \
\              else 0) * \
\             0 ^ m) = 1";
by (induct_tac "n" 1);
by Auto_tac;
qed "sumr_cos_zero_one";
Addsimps [sumr_cos_zero_one];

Goal "EX t. abs t <= abs x & \
\      cos x = \
\      (sumr 0 n (%m. (if even m \
\                      then (- 1) ^ (m div 2)/(real (fact m)) \
\                      else 0) * \
\                      x ^ m)) \
\     + ((cos(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)";
by (cut_inst_tac [("f","cos"),("n","n"),("x","x"),
       ("diff","%n x. cos(x + 1/2*real (n)*pi)")] 
       Maclaurin_all_lt_objl 1);
by (Step_tac 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (case_tac "n" 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() delsimps [sumr_Suc]) 1);
by (rtac ccontr 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("x","x")] spec 1 THEN Asm_full_simp_tac 1);
by (dtac ssubst 1 THEN assume_tac 2);
by (res_inst_tac [("x","t")] exI 1);
by (rtac conjI 1);
by (arith_tac 1);
by (rtac (CLAIM "[|x = y; x' = y'|] ==> x + x' = y + (y'::real)") 1);
by (rtac sumr_fun_eq 1);
by (auto_tac (claset(),simpset() addsimps [odd_not_even RS sym]));
by (auto_tac (claset(),simpset() addsimps [odd_Suc_mult_two_ex,
    even_mult_two_ex,left_distrib,cos_add]  delsimps 
    [fact_Suc,realpow_Suc]));
by (auto_tac (claset(),simpset() addsimps [real_mult_commute]));
qed "Maclaurin_cos_expansion";

Goal "[| 0 < x; 0 < n |] ==> \
\      EX t. 0 < t & t < x & \
\      cos x = \
\      (sumr 0 n (%m. (if even m \
\                      then (- 1) ^ (m div 2)/(real (fact m)) \
\                      else 0) * \
\                      x ^ m)) \
\     + ((cos(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)";
by (cut_inst_tac [("f","cos"),("n","n"),("h","x"),
       ("diff","%n x. cos(x + 1/2*real (n)*pi)")] 
       Maclaurin_objl 1);
by (Step_tac 1);
by (Asm_full_simp_tac 1);
by (Simp_tac 1);
by (dtac ssubst 1 THEN assume_tac 2);
by (res_inst_tac [("x","t")] exI 1);
by (rtac conjI 1 THEN rtac conjI 2);
by (assume_tac 1 THEN assume_tac 1);
by (rtac (CLAIM "[|x = y; x' = y'|] ==> x + x' = y + (y'::real)") 1);
by (rtac sumr_fun_eq 1);
by (auto_tac (claset(),simpset() addsimps [odd_not_even RS sym]));
by (auto_tac (claset(),simpset() addsimps [odd_Suc_mult_two_ex,
    even_mult_two_ex,left_distrib,cos_add]  delsimps 
    [fact_Suc,realpow_Suc]));
by (auto_tac (claset(),simpset() addsimps [real_mult_commute]));
qed "Maclaurin_cos_expansion2";

Goal "[| x < 0; 0 < n |] ==> \
\      EX t. x < t & t < 0 & \
\      cos x = \
\      (sumr 0 n (%m. (if even m \
\                      then (- 1) ^ (m div 2)/(real (fact m)) \
\                      else 0) * \
\                      x ^ m)) \
\     + ((cos(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)";
by (cut_inst_tac [("f","cos"),("n","n"),("h","x"),
       ("diff","%n x. cos(x + 1/2*real (n)*pi)")] 
       Maclaurin_minus_objl 1);
by (Step_tac 1);
by (Asm_full_simp_tac 1);
by (Simp_tac 1);
by (dtac ssubst 1 THEN assume_tac 2);
by (res_inst_tac [("x","t")] exI 1);
by (rtac conjI 1 THEN rtac conjI 2);
by (assume_tac 1 THEN assume_tac 1);
by (rtac (CLAIM "[|x = y; x' = y'|] ==> x + x' = y + (y'::real)") 1);
by (rtac sumr_fun_eq 1);
by (auto_tac (claset(),simpset() addsimps [odd_not_even RS sym]));
by (auto_tac (claset(),simpset() addsimps [odd_Suc_mult_two_ex,
    even_mult_two_ex,left_distrib,cos_add]  delsimps 
    [fact_Suc,realpow_Suc]));
by (auto_tac (claset(),simpset() addsimps [real_mult_commute]));
qed "Maclaurin_minus_cos_expansion";

(* ------------------------------------------------------------------------- *)
(* Version for ln(1 +/- x). Where is it??                                    *)
(* ------------------------------------------------------------------------- *)

