(*
    Degree of polynomials
    $Id$
    written by Clemens Ballarin, started 22 January 1997
*)

(* Relating degree and bound *)

goal ProtoPoly.thy
  "!! f. [| bound m f; f n ~= <0> |] ==> n <= m";
by (rtac classical 1);
by (dtac not_leE 1);
by (dtac boundD 1 THEN atac 1);
by (etac notE 1);
by (assume_tac 1);
qed "below_bound";

goal UnivPoly.thy "bound (LEAST n. bound n (Rep_UP p)) (Rep_UP p)";
by (rtac exE 1);
by (rtac LeastI 2);
by (assume_tac 2);
by (res_inst_tac [("a", "Rep_UP p")] CollectD 1);
by (rtac (rewrite_rule [UP_def] Rep_UP) 1);
qed "Least_is_bound";

Goalw [coeff_def, deg_def]
  "!! p. ALL m. n < m --> coeff m p = <0> ==> deg p <= n";
by (rtac Least_le 1);
by (Fast_tac 1);
qed "deg_aboveI";

Goalw [coeff_def, deg_def]
  "!! p. (n ~= 0 --> coeff n p ~= <0>) ==> n <= deg p";
by (case_tac "n = 0" 1);
(* Case n=0 *)
by (Asm_simp_tac 1);
(* Case n~=0 *)
by (rotate_tac 1 1);
by (Asm_full_simp_tac 1);
by (rtac below_bound 1);
by (assume_tac 2);
by (rtac Least_is_bound 1);
qed "deg_belowI";

Goalw [coeff_def, deg_def]
  "!! p. deg p < m ==> coeff m p = <0>";
by (rtac exE 1); (* create !! x. *)
by (rtac boundD 2);
by (assume_tac 3);
by (rtac LeastI 2);
by (assume_tac 2);
by (res_inst_tac [("a", "Rep_UP p")] CollectD 1);
by (rtac (rewrite_rule [UP_def] Rep_UP) 1);
qed "deg_aboveD";

Goalw [deg_def]
  "!! p. deg p = Suc y ==> ~ bound y (Rep_UP p)";
by (rtac not_less_Least 1);
by (Asm_simp_tac 1);
val lemma1 = result();

Goalw [deg_def, coeff_def]
  "!! p. deg p = Suc y ==> coeff (deg p) p ~= <0>";
by (rtac classical 1);
by (dtac notnotD 1);
by (cut_inst_tac [("p", "p")] Least_is_bound 1);
by (subgoal_tac "bound y (Rep_UP p)" 1);
(* prove subgoal *)
by (rtac boundI 2);  
by (case_tac "Suc y < m" 2);
(* first case *)
by (rtac boundD 2);  
by (assume_tac 2);
by (Asm_simp_tac 2);
(* second case *)
by (dtac leI 2);
by (dtac Suc_leI 2);
by (dtac le_anti_sym 2);
by (assume_tac 2);
by (Asm_full_simp_tac 2);
(* end prove subgoal *)
by (fold_goals_tac [deg_def]);
by (dtac lemma1 1);
by (etac notE 1);
by (assume_tac 1);
val lemma2 = result();

Goal
  "!! p. deg p ~= 0 ==> coeff (deg p) p ~= <0>";
by (rtac lemma2 1);
by (Full_simp_tac 1);
by (dtac Suc_pred 1);
by (rtac sym 1);
by (Asm_simp_tac 1);
qed "deg_lcoeff";

Goal
  "!! p. p ~= <0> ==> coeff (deg p) p ~= <0>";
by (etac contrapos 1);
by (ftac contrapos2 1);
by (rtac deg_lcoeff 1);
by (assume_tac 1);
by (rtac up_eqI 1);
by (case_tac "n=0" 1);
by (rotate_tac ~2 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [deg_aboveD]) 1);
qed "nonzero_lcoeff";

Goal "(deg p <= n) = bound n (Rep_UP p)";
by (rtac iffI 1);
(* ==> *)
by (rtac boundI 1);
by (fold_goals_tac [coeff_def]);
by (rtac deg_aboveD 1);
by (fast_arith_tac 1);
(* <== *)
by (rtac deg_aboveI 1);
by (rewtac coeff_def);
by (Fast_tac 1);
qed "deg_above_is_bound";

(* Lemmas on the degree function *)

Goalw [max_def]
  "!! p::'a::ring up. deg (p + q) <= max (deg p) (deg q)";
by (case_tac "deg p <= deg q" 1);
(* case deg p <= deg q *)
by (rtac deg_aboveI 1);
by (Asm_simp_tac 1);
by (strip_tac 1);
by (dtac le_less_trans 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps [deg_aboveD]) 1);
(* case deg p > deg q *)
by (rtac deg_aboveI 1);
by (Asm_simp_tac 1);
by (dtac not_leE 1);
by (strip_tac 1);
by (dtac less_trans 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps [deg_aboveD]) 1);
qed "deg_add";

Goal "!!p::('a::ring up). deg p < deg q ==> deg (p + q) = deg q";
by (rtac order_antisym 1);
by (rtac le_trans 1);
by (rtac deg_add 1);
by (Asm_simp_tac 1);
by (rtac deg_belowI 1);
by (asm_simp_tac (simpset() addsimps [deg_aboveD, deg_lcoeff]) 1);
qed "deg_add_equal";

Goal "deg (monom m::'a::ring up) = m";
by (rtac le_anti_sym 1);
(* <= *)
by (asm_simp_tac 
  (simpset() addsimps [deg_aboveI, less_not_refl2 RS not_sym]) 1);
(* >= *)
by (asm_simp_tac 
  (simpset() addsimps [deg_belowI, less_not_refl2 RS not_sym]) 1);
qed "deg_monom";

Goal "!! a::'a::ring. deg (const a) = 0";
by (rtac le_anti_sym 1);
by (rtac deg_aboveI 1);
by (simp_tac (simpset() addsimps [less_not_refl2]) 1);
by (rtac deg_belowI 1);
by (simp_tac (simpset() addsimps [less_not_refl2]) 1);
qed "deg_const";

Goal "deg (<0>::'a::ringS up) = 0";
by (rtac le_anti_sym 1);
by (rtac deg_aboveI 1);
by (Simp_tac 1);
by (rtac deg_belowI 1);
by (Simp_tac 1);
qed "deg_zero";

Goal "deg (<1>::'a::ring up) = 0";
by (rtac le_anti_sym 1);
by (rtac deg_aboveI 1);
by (simp_tac (simpset() addsimps [less_not_refl2]) 1);
by (rtac deg_belowI 1);
by (Simp_tac 1);
qed "deg_one";

Goal "!!p::('a::ring) up. deg (-p) = deg p";
by (rtac le_anti_sym 1);
(* <= *)
by (simp_tac (simpset() addsimps [deg_aboveI, deg_aboveD]) 1);
by (simp_tac (simpset() addsimps [deg_belowI, deg_lcoeff, uminus_monom_neq]) 1);
qed "deg_uminus";

Addsimps [deg_monom, deg_const, deg_zero, deg_one, deg_uminus];

Goal
  "!! a::'a::ring. deg (a *s p) <= (if a = <0> then 0 else deg p)";
by (case_tac "a = <0>" 1);
by (REPEAT (asm_simp_tac (simpset() addsimps [deg_aboveI, deg_aboveD]) 1));
qed "deg_smult_ring";

Goal
  "!! a::'a::domain. deg (a *s p) = (if a = <0> then 0 else deg p)";
by (rtac le_anti_sym 1);
by (rtac deg_smult_ring 1);
by (case_tac "a = <0>" 1);
by (REPEAT (asm_simp_tac (simpset() addsimps [deg_belowI, deg_lcoeff]) 1));
qed "deg_smult";

Goal
  "!! p::'a::ring up. [| deg p + deg q < k |] ==> \
\       coeff i p * coeff (k - i) q = <0>";
by (simp_tac (simpset() addsimps [coeff_def]) 1);
by (rtac bound_mult_zero 1);
by (assume_tac 3);
by (simp_tac (simpset() addsimps [deg_above_is_bound RS sym]) 1);
by (simp_tac (simpset() addsimps [deg_above_is_bound RS sym]) 1);
qed "deg_above_mult_zero";

Goal
  "!! p::'a::ring up. deg (p * q) <= deg p + deg q";
by (rtac deg_aboveI 1);
by (asm_simp_tac (simpset() addsimps [deg_above_mult_zero]) 1);
qed "deg_mult_ring";

goal Main.thy 
  "!!k::nat. k < n ==> m < n + m - k";
by (arith_tac 1);
qed "less_add_diff";

Goal "!!p. coeff n p ~= <0> ==> n <= deg p";
(* More general than deg_belowI, and simplifies the next proof! *)
by (rtac deg_belowI 1);
by (Fast_tac 1);
qed "deg_below2I";

Goal
  "!! p::'a::domain up. \
\    [| p ~= <0>; q ~= <0> |] ==> deg (p * q) = deg p + deg q";
by (rtac le_anti_sym 1);
by (rtac deg_mult_ring 1);
(* deg p + deg q <= deg (p * q) *)
by (rtac deg_below2I 1);
by (Simp_tac 1);
(*
by (rtac conjI 1);
by (rtac impI 1);
*)
by (res_inst_tac [("m", "deg p"), ("n", "deg p + deg q")] SUM_extend 1);
by (rtac le_add1 1);
by (asm_simp_tac (simpset() addsimps [deg_aboveD]) 1);
by (res_inst_tac [("m", "deg p"), ("n", "deg p")] SUM_extend_below 1);
by (rtac le_refl 1);
by (asm_simp_tac (simpset() addsimps [deg_aboveD, less_add_diff]) 1);
by (asm_simp_tac (simpset() addsimps [nonzero_lcoeff]) 1);
(*
by (rtac impI 1);
by (res_inst_tac [("m", "deg p"), ("n", "deg p + deg q")] SUM_extend 1);
by (rtac le_add1 1);
by (asm_simp_tac (simpset() addsimps [deg_aboveD, less_add_diff]) 1);
by (res_inst_tac [("m", "deg p"), ("n", "deg p")] SUM_extend_below 1);
by (rtac le_refl 1);
by (asm_simp_tac (simpset() addsimps [deg_aboveD, less_add_diff]) 1);
by (asm_simp_tac (simpset() addsimps [nonzero_lcoeff]) 1);
*)
qed "deg_mult";

Addsimps [deg_smult, deg_mult];

(* Representation theorems about polynomials *)

goal PolyRing.thy
  "!! p::nat=>'a::ring up. coeff k (SUM n p) = SUM n (%i. coeff k (p i))";
by (induct_tac "n" 1);
by Auto_tac;
qed "coeff_SUM";

goal UnivPoly.thy
  "!! f::(nat=>'a::ring). \
\    bound n f ==> SUM n (%i. if i = x then f i else <0>) = f x";
by (simp_tac (simpset() addsimps [SUM_if_singleton]) 1);
by (auto_tac
    (claset() addDs [not_leE],
     simpset()));
qed "bound_SUM_if";

Goal
  "!! p::'a::ring up. deg p <= n ==> SUM n (%i. coeff i p *s monom i) = p";
by (rtac up_eqI 1);
by (simp_tac (simpset() addsimps [coeff_SUM]) 1);
by (rtac trans 1);
by (res_inst_tac [("x", "na")] bound_SUM_if 2);
by (full_simp_tac (simpset() addsimps [deg_above_is_bound, coeff_def]) 2);
by (rtac SUM_cong 1);
by (rtac refl 1);
by (Asm_simp_tac 1);
qed "up_repr";

Goal
  "!! p::'a::ring up. [| deg p <= n; P p |] ==> \
\  P (SUM n (%i. coeff i p *s monom i))";
by (asm_simp_tac (simpset() addsimps [up_repr]) 1);
qed "up_reprD";

Goal
  "!! p::'a::ring up. [| deg p <= n; P (SUM n (%i. coeff i p *s monom i)) |] \
\    ==> P p";
by (asm_full_simp_tac (simpset() addsimps [up_repr]) 1);
qed "up_repr2D";

(*
Goal
  "!! p::'a::ring up. [| deg p <= n; deg q <= m |] ==> \
\    (SUM n (%i. coeff i p *s monom i) = SUM m (%i. coeff i q *s monom i)) \
\    = (coeff k f = coeff k g)
...
qed "up_unique";
*)

(* Polynomials over integral domains are again integral domains *)

Goal "!!p::'a::domain up. p * q = <0> ==> p = <0> | q = <0>";
by (rtac classical 1);
by (subgoal_tac "deg p = 0 & deg q = 0" 1);
by (res_inst_tac [("p", "p"), ("n", "0")] up_repr2D 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("p", "q"), ("n", "0")] up_repr2D 1);
by (Asm_simp_tac 1);
by (subgoal_tac "coeff 0 p = <0> | coeff 0 q = <0>" 1);
by (force_tac (claset() addIs [up_eqI], simpset()) 1);
by (rtac integral 1);
by (subgoal_tac "coeff 0 (p * q) = <0>" 1);
by (Asm_simp_tac 2);
by (Full_simp_tac 1);
by (dres_inst_tac [("f", "deg")] arg_cong 1);
by (Asm_full_simp_tac 1);
qed "up_integral";

Goal "!! a::'a::domain. a *s p = <0> ==> a = <0> | p = <0>";
by (full_simp_tac (simpset() addsimps [const_mult_is_smult RS sym]) 1);
by (dtac up_integral 1);
by Auto_tac;
by (rtac (const_inj RS injD) 1);
by (Simp_tac 1);
qed "smult_integral";

(* Divisibility and degree *)

Goalw [dvd_def]
  "!! p::'a::domain up. [| p dvd q; q ~= <0> |] ==> deg p <= deg q";
by (etac exE 1);
by (hyp_subst_tac 1);
by (case_tac "p = <0>" 1);
by (Asm_simp_tac 1);
by (dtac r_nullD 1);
by (asm_simp_tac (simpset() addsimps [le_add1]) 1);
qed "dvd_imp_deg";
