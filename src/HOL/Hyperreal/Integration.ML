(*  Title       : Integration.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 2000  University of Edinburgh
    Description : Theory of integration (c.f. Harison's HOL development)
*)

Goalw [psize_def] "a = b ==> psize (%n. if n = 0 then a else b) = 0";
by Auto_tac;
qed "partition_zero";
Addsimps [partition_zero];

Goalw [psize_def] "a < b ==> psize (%n. if n = 0 then a else b) = 1";
by Auto_tac;
by (rtac some_equality 1);
by Auto_tac;
by (dres_inst_tac [("x","1")] spec 1);
by Auto_tac;
qed "partition_one";
Addsimps [partition_one];

Goalw [partition_def] 
   "a <= b ==> partition(a,b)(%n. if n = 0 then a else b)";
by (auto_tac (claset(),simpset() addsimps [real_le_less]));
qed "partition_single";
Addsimps [partition_single];

Goalw [partition_def] "partition(a,b) D ==> (D(0) = a)";
by Auto_tac;
qed "partition_lhs";

Goalw [partition_def]
       "(partition(a,b) D) = \
\       ((D 0 = a) & \
\        (ALL n. n < (psize D) --> D n < D(Suc n)) & \
\        (ALL n. (psize D) <= n --> (D n = b)))";
by Auto_tac;
by (ALLGOALS(subgoal_tac "psize D = N"));
by Auto_tac;
by (ALLGOALS(simp_tac (simpset() addsimps [psize_def])));
by (ALLGOALS(rtac some_equality));
by (Blast_tac 1 THEN Blast_tac 2);
by (ALLGOALS(rtac ccontr));
by (ALLGOALS(dtac (ARITH_PROVE "n ~= (N::nat) ==> n < N | N < n")));
by (Step_tac 1);
by (dres_inst_tac [("x","Na")] spec 1);
by (rotate_tac 3 1);
by (dres_inst_tac [("x","Suc Na")] spec 1);
by (Asm_full_simp_tac 1);
by (rotate_tac 2 1);
by (dres_inst_tac [("x","N")] spec 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("x","Na")] spec 1);
by (rotate_tac 3 1);
by (dres_inst_tac [("x","Suc Na")] spec 1);
by (Asm_full_simp_tac 1);
by (rotate_tac 2 1);
by (dres_inst_tac [("x","N")] spec 1);
by (Asm_full_simp_tac 1);
qed "partition";

Goal "partition(a,b) D ==> (D(psize D) = b)";
by (dtac (partition RS subst) 1);
by (Step_tac 1);
by (REPEAT(dres_inst_tac [("x","psize D")] spec 1));
by Auto_tac;
qed "partition_rhs";

Goal "[|partition(a,b) D; psize D <= n |] ==> (D n = b)";
by (dtac (partition RS subst) 1);
by (Blast_tac 1);
qed "partition_rhs2";

Goal 
 "partition(a,b) D & m + Suc d <= n & n <= (psize D) --> D(m) < D(m + Suc d)";
by (induct_tac "d" 1);
by Auto_tac;
by (ALLGOALS(dtac (partition RS subst)));
by (Step_tac 1);
by (ALLGOALS(dtac (ARITH_PROVE "Suc m <= n ==> m < n")));
by (ALLGOALS(dtac less_le_trans));
by (assume_tac 1 THEN assume_tac 2);
by (ALLGOALS(blast_tac (claset() addIs [real_less_trans])));
qed_spec_mp "lemma_partition_lt_gen";

Goal "m < n ==> EX d. n = m + Suc d";
by (auto_tac (claset(),simpset() addsimps [less_iff_Suc_add]));
qed "less_eq_add_Suc";

Goal "[|partition(a,b) D; m < n; n <= (psize D)|] ==> D(m) < D(n)";
by (auto_tac (claset() addDs [less_eq_add_Suc] addIs [lemma_partition_lt_gen],
    simpset()));
qed "partition_lt_gen";

Goal "partition(a,b) D ==> (n < (psize D) --> D(0) < D(Suc n))";
by (dtac (partition RS subst) 1);
by (induct_tac "n" 1);
by (Blast_tac 1);
by (blast_tac (claset() addSDs [leI] addDs 
    [(ARITH_PROVE "m <= n ==> m <= Suc n"),
    le_less_trans,real_less_trans]) 1);
qed_spec_mp "partition_lt";

Goal "partition(a,b) D ==> a <= b";
by (ftac (partition RS subst) 1);
by (Step_tac 1);
by (rotate_tac 2 1);
by (dres_inst_tac [("x","psize D")] spec 1);
by (Step_tac 1);
by (rtac ccontr 1);
by (case_tac "psize D = 0" 1);
by (Step_tac 1);
by (dres_inst_tac [("n","psize D - 1")] partition_lt 2);
by Auto_tac;
qed "partition_le";

Goal "[|partition(a,b) D; n < (psize D)|] ==> D(n) < D(psize D)";
by (auto_tac (claset() addIs [partition_lt_gen],simpset()));
qed "partition_gt";

Goal "partition(a,b) D ==> ((a = b) = (psize D = 0))";
by (ftac (partition RS subst) 1);
by (Step_tac 1);
by (rotate_tac 2 1);
by (dres_inst_tac [("x","psize D")] spec 1);
by (rtac ccontr 1);
by (dres_inst_tac [("n","psize D - 1")] partition_lt 1);
by (Blast_tac 3 THEN Auto_tac);
qed "partition_eq";

Goal "partition(a,b) D ==> a <= D(r)";
by (ftac (partition RS subst) 1);
by (Step_tac 1);
by (induct_tac "r" 1);
by (cut_inst_tac [("m","Suc n"),("n","psize D")] 
    (ARITH_PROVE "m < n | n <= (m::nat)") 2);
by (Step_tac 1);
by (eres_inst_tac [("j","D n")] real_le_trans 1);
by (dres_inst_tac [("x","n")] spec 1);
by (blast_tac (claset() addIs [less_trans,order_less_imp_le]) 1);
by (res_inst_tac [("j","b")] real_le_trans 1);
by (etac partition_le 1);
by (Blast_tac 1);
qed "partition_lb";

Goal "[| partition(a,b) D; psize D ~= 0 |] ==> a < D(Suc n)";
by (res_inst_tac [("t","a")] (partition_lhs RS subst) 1);
by (assume_tac 1);
by (cut_inst_tac [("m","psize D"),("n","Suc n")] 
    (ARITH_PROVE "m < n | n <= (m::nat)") 1);
by (ftac (partition RS subst) 1);
by (Step_tac 1);
by (rotate_tac 3 1);
by (dres_inst_tac [("x","Suc n")] spec 1);
by (etac impE 1);
by (etac less_imp_le 1);
by (ftac partition_rhs 1);
by (dtac partition_gt 1 THEN assume_tac 1);
by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [partition_lt,less_le_trans]) 1);
qed "partition_lb_lt";

Goal "partition(a,b) D ==> D(r) <= b";
by (ftac (partition RS subst) 1);
by (cut_inst_tac [("m","r"),("n","psize D")] 
    (ARITH_PROVE "m < n | n <= (m::nat)") 1);
by (Step_tac 1);
by (Blast_tac 2);
by (subgoal_tac "ALL x. D((psize D) - x) <= b" 1);
by (rotate_tac 4 1);
by (dres_inst_tac [("x","psize D - r")] spec 1);
by (dtac (ARITH_PROVE "p < m ==> m - (m - p) = (p::nat)") 1);
by (thin_tac "ALL n. psize D <= n --> D n = b" 1);
by (Asm_full_simp_tac 1);
by (Step_tac 1);
by (induct_tac "x" 1);
by (Simp_tac 1 THEN Blast_tac 1);
by (case_tac "psize D - Suc n = 0" 1);
by (thin_tac "ALL n. psize D <= n --> D n = b" 1);
by (asm_simp_tac (simpset() addsimps [partition_le]) 1);
by (rtac real_le_trans 1 THEN assume_tac 2);
by (rtac (ARITH_PROVE "0 < m - Suc n ==> (m - n) = Suc(m - Suc n)" 
          RS ssubst) 1);
by (dres_inst_tac [("x","psize D - Suc n")] spec 2);
by (thin_tac "ALL n. psize D <= n --> D n = b" 2);
by (Asm_full_simp_tac 2);
by (Blast_tac 1);
qed "partition_ub";

Goal "[| partition(a,b) D; n < psize D |] ==> D(n) < b"; 
by (blast_tac (claset() addIs [partition_rhs RS subst] addIs
    [partition_gt]) 1);
qed "partition_ub_lt";

Goal "[| partition (a, b) D1; partition (b, c) D2 |] \
\      ==> (ALL n. \
\            n < psize D1 + psize D2 --> \
\            (if n < psize D1 then D1 n else D2 (n - psize D1)) \
\            < (if Suc n < psize D1 then D1 (Suc n) \
\               else D2 (Suc n - psize D1))) & \
\        (ALL n. \
\            psize D1 + psize D2 <= n --> \
\            (if n < psize D1 then D1 n else D2 (n - psize D1)) = \
\            (if psize D1 + psize D2 < psize D1 then D1 (psize D1 + psize D2) \
\             else D2 (psize D1 + psize D2 - psize D1)))";
by (Step_tac 1);
by (auto_tac (claset() addIs [partition_lt_gen],simpset()));
by (dres_inst_tac [("m","psize D1")] 
    (leI RSN(2,ARITH_PROVE "[| n < m; m <= Suc n |] ==> m = Suc n")) 1);
by (assume_tac 1);
by (auto_tac (claset() addSIs [partition_lt_gen],
    simpset() addsimps [partition_lhs,partition_ub_lt]));
by (blast_tac (claset() addIs [ARITH_PROVE "~n < m ==> n - m < Suc n - m"]) 1);
by (auto_tac (claset(),simpset() addsimps [
    ARITH_PROVE "~ n < m ==> (Suc n - m <= p) = (Suc n <= m + p)"]));
by (dtac (ARITH_PROVE "p + q <= (n::nat) ==> q <= n - p") 1);
by (auto_tac (claset() addSIs [partition_rhs2], simpset() addsimps 
    [partition_rhs]));
qed "lemma_partition_append1";

Goal "[| partition (a, b) D1; partition (b, c) D2; N < psize D1 |] \
\     ==> D1(N) < D2 (psize D2)";
by (res_inst_tac [("y","D1(psize D1)")] order_less_le_trans 1);
by (etac partition_gt 1 THEN assume_tac 1);
by (auto_tac (claset(),simpset() addsimps [partition_rhs,partition_le]));
qed "lemma_psize1";

Goal "[| partition (a, b) D1; partition (b, c) D2 |] \
\     ==> psize (%n. if n < psize D1 then D1 n else D2 (n - psize D1)) = \
\         psize D1 + psize D2";
by (res_inst_tac 
    [("D2","%n. if n < psize D1 then D1 n else D2 (n - psize D1)")] 
    ((psize_def RS meta_eq_to_obj_eq) RS ssubst) 1);
by (rtac some1_equality 1);
by (blast_tac (claset() addSIs [lemma_partition_append1]) 2);
by (rtac ex1I 1 THEN rtac lemma_partition_append1 1);
by Auto_tac;
by (rtac ccontr 1);
by (dtac (ARITH_PROVE "m ~= n ==> m < n | n < (m::nat)") 1);
by (Step_tac 1);
by (rotate_tac 3 1);
by (dres_inst_tac [("x","psize D1 + psize D2")] spec 1);
by Auto_tac;
by (case_tac "N < psize D1" 1);
by (auto_tac (claset() addDs [lemma_psize1],simpset()));
by (dtac leI 1);
by (dtac (ARITH_PROVE "[|p <= n; n < p + m|] ==> n - p < (m::nat)") 1);
by (assume_tac 1);
by (dres_inst_tac [("a","b"),("b","c")] partition_gt 1);
by Auto_tac;
by (dres_inst_tac [("x","psize D1 + psize D2")] spec 1);
by (auto_tac (claset(),simpset() addsimps [partition_rhs2]));
qed "lemma_partition_append2";

Goalw [tpart_def]
"[|psize D = 0; tpart(a,b) (D,p)|] ==> a = b";
by (auto_tac (claset(),simpset() addsimps [partition_eq]));
qed "tpart_eq_lhs_rhs";

Goalw [tpart_def] "tpart(a,b) (D,p) ==> partition(a,b) D";
by Auto_tac;
qed "tpart_partition";

Goal "[| tpart(a,b) (D1,p1); fine(g) (D1,p1); \
\        tpart(b,c) (D2,p2); fine(g) (D2,p2) |] \ 
\      ==> EX D p. tpart(a,c) (D,p) & fine(g) (D,p)";
by (res_inst_tac 
    [("x","%n. if n < psize D1 then D1 n else D2 (n - psize D1)")] exI 1);
by (res_inst_tac 
    [("x","%n. if n < psize D1 then p1 n else p2 (n - psize D1)")] exI 1);
by (cut_inst_tac [("m","psize D1")] (ARITH_PROVE "0 < (m::nat) | m = 0") 1);
by (auto_tac (claset() addDs [tpart_eq_lhs_rhs],simpset()));
by (asm_full_simp_tac (simpset() addsimps [fine_def,
    [tpart_partition,tpart_partition] MRS lemma_partition_append2]) 2);
by Auto_tac;
by (dres_inst_tac [("m","psize D1"),("n","n")] 
    (leI RSN(2,ARITH_PROVE "[| n < m; m <= Suc n |] ==> m = Suc n")) 2);
by Auto_tac;
by (dtac (tpart_partition RS partition_rhs) 2);
by (dtac (tpart_partition RS partition_lhs) 2);
by Auto_tac;
by (rotate_tac 3 2);
by (dres_inst_tac [("x","n - psize D1")] spec 2);
by (auto_tac (claset(),simpset() addsimps 
    [ARITH_PROVE "[| (0::nat) < p; p <= n |] ==> (n - p < m) = (n < p + m)",
     ARITH_PROVE "~n < p ==> Suc n - p = Suc(n - p)"]));
by (auto_tac (claset(),simpset() addsimps [tpart_def,
    ARITH_PROVE "~n < p ==> Suc n - p = Suc(n - p)"]));
by (dres_inst_tac [("m","psize D1"),("n","n")] 
    (leI RSN(2,ARITH_PROVE "[| n < m; m <= Suc n |] ==> m = Suc n")) 2);
by Auto_tac;
by (dtac partition_rhs 2);
by (dtac partition_lhs 2);
by Auto_tac;
by (rtac (partition RS ssubst) 1);
by (rtac (lemma_partition_append2 RS ssubst) 1);
by (rtac conjI 3);
by (dtac lemma_partition_append1 4);
by (auto_tac (claset(),simpset() addsimps [partition_lhs,partition_rhs]));
qed "partition_append";

(* ------------------------------------------------------------------------ *)
(* We can always find a division which is fine wrt any gauge                *)
(* ------------------------------------------------------------------------ *)

Goal "[| a <= b; gauge(%x. a <= x & x <= b) g |] \
\     ==> EX D p. tpart(a,b) (D,p) & fine g (D,p)";
by (cut_inst_tac 
 [("P","%(u,v). a <= u & v <= b --> (EX D p. tpart(u,v) (D,p) & fine(g) (D,p))")]
 lemma_BOLZANO2 1);
by (Step_tac 1);
by (REPEAT(blast_tac (claset() addIs [real_le_trans]) 1));
by (auto_tac (claset() addIs [partition_append],simpset()));
by (case_tac "a <= x & x <= b" 1);
by (res_inst_tac [("x","1")] exI 2);
by Auto_tac;
by (res_inst_tac [("x","g x")] exI 1);
by (auto_tac (claset(),simpset() addsimps [gauge_def]));
by (res_inst_tac [("x","%n. if n = 0 then aa else ba")] exI 1);
by (res_inst_tac [("x","%n. if n = 0 then x else ba")] exI 1);
by (auto_tac (claset(),simpset() addsimps [tpart_def,fine_def]));
qed "partition_exists";

(* ------------------------------------------------------------------------ *)
(* Lemmas about combining gauges                                            *)
(* ------------------------------------------------------------------------ *)

Goalw [gauge_def] 
     "[| gauge(E) g1; gauge(E) g2 |] \
\     ==> gauge(E) (%x. if g1(x) < g2(x) then g1(x) else g2(x))";
by Auto_tac;
qed "gauge_min";

Goalw [fine_def]
      "fine (%x. if g1(x) < g2(x) then g1(x) else g2(x)) (D,p) \
\      ==> fine(g1) (D,p) & fine(g2) (D,p)";
by (auto_tac (claset(),simpset() addsimps [split_if]));
qed "fine_min";


(* ------------------------------------------------------------------------ *)
(* The integral is unique if it exists                                      *)
(* ------------------------------------------------------------------------ *)

Goalw [Integral_def] 
    "[| a <= b; Integral(a,b) f k1; Integral(a,b) f k2 |] ==> k1 = k2";
by Auto_tac;
by (REPEAT(dres_inst_tac [("x","abs(k1 - k2)/2")] spec 1));
by (Auto_tac THEN TRYALL(arith_tac));
by (dtac gauge_min 1 THEN assume_tac 1);
by (dres_inst_tac [("g","%x. if g x < ga x then g x else ga x")] 
    partition_exists 1 THEN assume_tac 1);
by Auto_tac;
by (dtac fine_min 1);
by (REPEAT(dtac spec 1) THEN Auto_tac);
by (subgoal_tac 
    "abs((rsum(D,p) f - k2) - (rsum(D,p) f - k1)) < abs(k1 - k2)" 1);
by (arith_tac 1);
by (dtac real_add_less_mono 1 THEN assume_tac 1);
by (auto_tac (claset(),
    HOL_ss addsimps [real_add_mult_distrib RS sym,
                     real_mult_2_right RS sym, mult_less_cancel_right]));
by (ALLGOALS(arith_tac));
qed "Integral_unique";

Goalw [Integral_def] "Integral(a,a) f 0";
by Auto_tac;
by (res_inst_tac [("x","%x. 1")] exI 1);
by (auto_tac (claset() addDs [partition_eq],simpset() addsimps [gauge_def,
     tpart_def,rsum_def]));
qed "Integral_zero"; 
Addsimps [Integral_zero];

Goal "sumr 0 m (%n. D (Suc n) - D n) = D(m) - D 0";
by (induct_tac "m" 1);
by Auto_tac;
qed "sumr_partition_eq_diff_bounds";
Addsimps [sumr_partition_eq_diff_bounds];

Goal "a <= b ==> Integral(a,b) (%x. 1) (b - a)";
by (dtac real_le_imp_less_or_eq 1 THEN Auto_tac);
by (auto_tac (claset(),simpset() addsimps [rsum_def,Integral_def]));
by (res_inst_tac [("x","%x. b - a")] exI 1);
by (auto_tac (claset(),simpset() addsimps [gauge_def,
    abs_interval_iff,tpart_def,partition]));
qed "Integral_eq_diff_bounds";

Goal "a <= b ==> Integral(a,b) (%x. c)  (c*(b - a))";
by (dtac real_le_imp_less_or_eq 1 THEN Auto_tac);
by (auto_tac (claset(),simpset() addsimps [rsum_def,Integral_def]));
by (res_inst_tac [("x","%x. b - a")] exI 1);
by (auto_tac (claset(),simpset() addsimps 
    [sumr_mult RS sym,gauge_def,abs_interval_iff,
     real_diff_mult_distrib2 RS sym,partition,tpart_def]));
qed "Integral_mult_const";

Goal "[| a <= b; Integral(a,b) f k |] ==> Integral(a,b) (%x. c * f x) (c * k)";
by (dtac real_le_imp_less_or_eq 1);
by (auto_tac (claset() addDs [[real_le_refl,Integral_zero] MRS Integral_unique],
    simpset()));
by (auto_tac (claset(),simpset() addsimps [rsum_def,Integral_def,
    sumr_mult RS sym,real_mult_assoc]));
by (res_inst_tac [("a2","c")] ((abs_ge_zero RS real_le_imp_less_or_eq)
    RS disjE) 1);
by (dtac sym 2);
by (Asm_full_simp_tac 2 THEN Blast_tac 2);
by (dres_inst_tac [("x","e/abs c")] spec 1 THEN Auto_tac);
by (asm_full_simp_tac (simpset() addsimps [real_0_less_mult_iff,
    real_divide_def]) 1);
by (rtac exI 1 THEN Auto_tac);
by (REPEAT(dtac spec 1) THEN Auto_tac);
by (res_inst_tac [("z1","inverse(abs c)")] (real_mult_less_iff1 RS iffD1) 1);
by (fold_tac [real_divide_def]);
by (auto_tac (claset(),simpset() addsimps [real_diff_mult_distrib2 
    RS sym,abs_mult,real_mult_assoc RS sym,
    ARITH_PROVE "c ~= 0 ==> abs (c::real) ~= 0",real_inverse_gt_0]));
qed "Integral_mult";

(* ------------------------------------------------------------------------ *)
(* Fundamental theorem of calculus (Part I)                                 *)
(* ------------------------------------------------------------------------ *)

(* "Straddle Lemma" : Swartz & Thompson: AMM 95(7) 1988 *)

Goal "ALL x. P(x) --> (EX y. Q x y) ==> EX f. (ALL x. P(x) --> Q x (f x))";
by (cut_inst_tac [("S","Collect (%x. P x)"),("Q","Q")] (CLAIM_SIMP 
    "(ALL x:S. (EX y. Q x y)) --> (EX f. (ALL x:S. Q x (f x)))" [bchoice]) 1);
by Auto_tac;
qed "choiceP";

Goal "ALL x. P(x) --> (EX y. R(y) & (EX z. Q x y z)) ==> \
\     EX f fa. (ALL x. P(x) --> R(f x) & Q x (f x) (fa x))";
by (dtac (CLAIM "(ALL x. P(x) --> (EX y. R(y) & (EX z. Q x y z))) = \
\                (ALL x. P(x) --> (EX y z. R(y) & Q x y z))" RS iffD1) 1);;
by (dtac choiceP 1 THEN Step_tac 1);
by (dtac choiceP 1 THEN Auto_tac);
qed "choiceP2";

Goal "ALL x. (EX y. R(y) & (EX z. Q x y z)) ==> \
\     EX f fa. (ALL x. R(f x) & Q x (f x) (fa x))";
by (dtac (CLAIM "(ALL x. (EX y. R(y) & (EX z. Q x y z))) = \
\                (ALL x. (EX y z. R(y) & Q x y z))" RS iffD1) 1);;
by (dtac choice 1 THEN Step_tac 1);
by (dtac choice 1 THEN Auto_tac);
qed "choice2";

(* new simplifications e.g. (y < x/n) = (y * n < x) are a real nuisance 
   they break the original proofs and make new proofs longer!                 *)
Goalw [gauge_def]
     "[| ALL x. a <= x & x <= b --> DERIV f x :> f'(x); 0 < e |]\
\     ==> EX g. gauge(%x. a <= x & x <= b) g & \
\               (ALL x u v. a <= u & u <= x & x <= v & v <= b & (v - u) < g(x) \
\                 --> abs((f(v) - f(u)) - (f'(x) * (v - u))) <= e * (v - u))";
by (subgoal_tac "ALL x. a <= x & x <= b --> \
\                  (EX d. 0 < d & \
\                     (ALL u v. u <= x & x <= v & (v - u) < d --> \
\                     abs((f(v) - f(u)) - (f'(x) * (v - u))) <= e * (v - u)))" 1);
by (dtac choiceP 1);
by Auto_tac;
by (dtac spec 1 THEN Auto_tac);
by (auto_tac (claset(),simpset() addsimps [DERIV_iff2,LIM_def]));
by (dres_inst_tac [("x","e/2")] spec 1);
by Auto_tac;
by (subgoal_tac "ALL z. abs(z - x) < s --> \
\        abs((f(z) - f(x)) - (f'(x) * (z - x))) <= (e / 2) * abs(z - x)" 1);
by Auto_tac;
by (case_tac "0 < abs(z - x)" 2);
by (dtac (ARITH_PROVE "~ 0 < abs z ==> z = (0::real)") 3);
by (asm_full_simp_tac (simpset() addsimps 
    [ARITH_PROVE "(z - x = 0) = (z = (x::real))"]) 3);
by (dres_inst_tac [("x","z")] spec 2);
by (res_inst_tac [("z1","abs(inverse(z - x))")] 
         (real_mult_le_cancel_iff2 RS iffD1) 2);
by (Asm_full_simp_tac 2);
by (asm_full_simp_tac (simpset() 
     delsimps [abs_inverse]
     addsimps [abs_mult RS sym, real_mult_assoc RS sym]) 2);
by (subgoal_tac "inverse (z - x) * (f z - f x - f' x * (z - x)) = \
\                (f z - f x)/(z - x) - f' x" 2);
by (asm_full_simp_tac (simpset() addsimps [abs_mult RS sym] @ real_mult_ac) 2);
by (asm_full_simp_tac (simpset() addsimps [real_diff_def]) 2);
by (rtac (real_mult_commute RS subst) 2);
by (asm_full_simp_tac (simpset() addsimps [real_add_mult_distrib,
    real_diff_def]) 2);
by (dtac (CLAIM "z ~= x ==> z + -x ~= (0::real)") 2);
by (asm_full_simp_tac (simpset() addsimps [real_mult_assoc,
    real_divide_def]) 2);
by (simp_tac (simpset() addsimps [real_add_mult_distrib]) 2);
by (res_inst_tac [("x","s")] exI 1 THEN Auto_tac);
by (res_inst_tac [("u1","u"),("v1","v")] (ARITH_PROVE "u < v | v <= (u::real)"
    RS disjE) 1);
by (dres_inst_tac [("x","v")] real_le_imp_less_or_eq 2);
by Auto_tac;
(*29*)
by (res_inst_tac [("j","abs((f(v) - f(x)) - (f'(x) * (v - x))) + \
\                  abs((f(x) - f(u)) - (f'(x) * (x - u)))")] real_le_trans 1);
by (rtac (abs_triangle_ineq RSN (2,real_le_trans)) 1);
by (asm_full_simp_tac (simpset() addsimps [real_diff_mult_distrib2]) 1);
by (arith_tac 1);
by (res_inst_tac [("t","e*(v - u)")] (real_sum_of_halves RS subst) 1);
by (rtac real_add_le_mono 1);
by (res_inst_tac [("j","(e / 2) * abs(v - x)")] real_le_trans 1);

by (Asm_full_simp_tac 2 THEN arith_tac 2);
by (ALLGOALS (thin_tac "ALL xa. \
\             xa ~= x & abs (xa + - x) < s --> \
\             abs ((f xa + - f x) / (xa + - x) + - f' x) * 2 < e"));
by (dres_inst_tac [("x","v")] spec 1 THEN Auto_tac);
by (arith_tac 1);
by (dres_inst_tac [("x","u")] spec 1 THEN Auto_tac);
by (arith_tac 1);
by (subgoal_tac "abs (f u - f x - f' x * (u - x)) = \
\                abs (f x - f u - f' x * (x - u))" 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_mult_distrib2,
    real_diff_def]) 2);
by (arith_tac 2);
by(rtac real_le_trans 1);
by Auto_tac;
by (arith_tac 1);
qed "lemma_straddle";

Goal "((number_of c - 1) * x <= 0) =((number_of c ::real) * x <= x)";
by (rtac ((ARITH_PROVE "(x <= y) = (x - y <= (0::real))") RS ssubst) 1);
by (simp_tac (simpset() addsimps [real_diff_mult_distrib,
    CLAIM_SIMP "c * x - x = (c - 1) * (x::real)" [real_diff_mult_distrib]]) 1);
qed "lemma_number_of_mult_le";
 

Goal "[|a <= b; ALL x. a <= x & x <= b --> DERIV f x :> f'(x) |] \
\     ==> Integral(a,b) f' (f(b) - f(a))";
by (dtac real_le_imp_less_or_eq 1 THEN Auto_tac);
by (auto_tac (claset(),simpset() addsimps [Integral_def]));
by (rtac ccontr 1);
by (subgoal_tac "ALL e. 0 < e --> \ 
\                   (EX g. gauge (%x. a <= x & x <= b) g & \
\                   (ALL D p. \
\                       tpart (a, b) (D, p) & fine g (D, p) --> \
\                       abs (rsum (D, p) f' - (f b - f a)) <= e))" 1);
by (rotate_tac 3 1);
by (dres_inst_tac [("x","e/2")] spec 1 THEN Auto_tac);
by (dtac spec 1 THEN Auto_tac);
by (REPEAT(dtac spec 1) THEN Auto_tac);
by (dres_inst_tac [("e","ea/(b - a)")] lemma_straddle 1);
by (auto_tac (claset(),simpset() addsimps [thm"Ring_and_Field.zero_less_divide_iff"]));
by (rtac exI 1);
by (auto_tac (claset(),simpset() addsimps [tpart_def,rsum_def]));
by (subgoal_tac "sumr 0 (psize D) (%n. f(D(Suc n)) - f(D n)) = \
\   f b - f a" 1);
by (cut_inst_tac [("D","%n. f(D n)"),("m","psize D")] 
    sumr_partition_eq_diff_bounds 2);
by (asm_full_simp_tac (simpset() addsimps [partition_lhs,partition_rhs]) 2);
by (dtac sym 1 THEN Asm_full_simp_tac 1);
by (simp_tac (simpset() addsimps [sumr_diff]) 1);
by (rtac (sumr_rabs RS real_le_trans) 1);
by (subgoal_tac 
    "ea = sumr 0 (psize D) (%n. (ea / (b - a)) * (D(Suc n) - (D n)))" 1);
by (asm_full_simp_tac (simpset() addsimps 
    [ARITH_PROVE "abs(y - (x::real)) = abs(x - y)"]) 1);
by (res_inst_tac [("t","ea")] ssubst 1 THEN assume_tac 1);
by (rtac sumr_le2 1);
by (rtac (sumr_mult RS subst) 2);
by (auto_tac (claset(),simpset() addsimps [partition_rhs,
    partition_lhs,partition_lb,partition_ub,fine_def]));
qed "FTC1";


Goal "[| Integral(a,b) f k1; k2 = k1 |] ==> Integral(a,b) f k2";
by (Asm_simp_tac 1);
qed "Integral_subst";

Goal "[| a <= b; b <= c; Integral(a,b) f' k1; Integral(b,c) f' k2; \
\        ALL x. a <= x & x <= c --> DERIV f x :> f' x |] \
\    ==> Integral(a,c) f' (k1 + k2)";
by (rtac (FTC1 RS Integral_subst) 1);
by Auto_tac;
by (ftac FTC1 1 THEN Auto_tac);
by (forw_inst_tac [("a","b")] FTC1 1 THEN Auto_tac);
by (dres_inst_tac [("x","x")] spec 1 THEN Auto_tac);
by (dres_inst_tac [("k2.0","f b - f a")] Integral_unique 1);
by (dres_inst_tac [("k2.0","f c - f b")] Integral_unique 3);
by Auto_tac;
qed "Integral_add";

Goal "partition(a,b) D ==> psize D = (LEAST n. D(n) = b)";
by (auto_tac (claset() addSIs [Least_equality RS sym,partition_rhs],simpset()));
by (rtac ccontr 1);
by (dtac partition_ub_lt 1);
by Auto_tac;
qed "partition_psize_Least";

Goal "partition (a, c) D ==> ~ (EX n. c < D(n))";
by (Step_tac 1);
by (dres_inst_tac [("r","n")] partition_ub 1);
by Auto_tac;
qed "lemma_partition_bounded";

Goal "partition (a, c) D ==> D = (%n. if D n < c then D n else c)";
by (rtac ext 1 THEN Auto_tac);
by (auto_tac (claset() addSDs [lemma_partition_bounded],simpset()));
by (dres_inst_tac [("x","n")] spec 1);
by Auto_tac;
qed "lemma_partition_eq";

Goal "partition (a, c) D ==> D = (%n. if D n <= c then D n else c)";
by (rtac ext 1 THEN Auto_tac);
by (auto_tac (claset() addSDs [lemma_partition_bounded],simpset()));
by (dres_inst_tac [("x","n")] spec 1);
by Auto_tac;
qed "lemma_partition_eq2";

Goal "[| partition(a,b) D; n < psize D |] ==> D n < D (Suc n)";
by (auto_tac (claset(),simpset() addsimps [partition]));
qed "partition_lt_Suc";

Goal "tpart(a,c) (D,p) ==> p = (%n. if D n < c then p n else c)";
by (rtac ext 1);
by (auto_tac (claset(),simpset() addsimps [tpart_def]));
by (dtac real_leI 1);
by (dres_inst_tac [("r","Suc n")] partition_ub 1);
by (dres_inst_tac [("x","n")] spec 1);
by Auto_tac;
qed "tpart_tag_eq";

(*----------------------------------------------------------------------------*)
(* Lemmas for Additivity Theorem of gauge integral                            *)
(*----------------------------------------------------------------------------*)

Goal "[| a <= D n; D n < b; partition(a,b) D |] ==> n < psize D";
by (dtac (partition RS iffD1) 1 THEN Step_tac 1);
by (rtac ccontr 1 THEN dtac leI 1);
by Auto_tac;
val lemma_additivity1 = result();

Goal "[| a <= D n; partition(a,D n) D |] ==> psize D <= n";
by (rtac ccontr 1 THEN dtac not_leE 1);
by (ftac (partition RS iffD1) 1 THEN Step_tac 1);
by (forw_inst_tac [("r","Suc n")] partition_ub 1);
by (auto_tac (claset() addSDs [spec],simpset()));
val lemma_additivity2 = result();

Goal "[| partition(a,b) D; psize D < m |] ==> D(m) = D(psize D)";
by (auto_tac (claset(),simpset() addsimps [partition]));
qed "partition_eq_bound";

Goal "[| partition(a,b) D; psize D < m |] ==> D(r) <= D(m)";
by (ftac (partition RS iffD1) 1 THEN Auto_tac);
by (etac partition_ub 1);
qed "partition_ub2";

Goalw [tpart_def]
    "[| tpart(a,b) (D,p); psize D <= m |] ==> p(m) = D(m)";
by Auto_tac;
by (dres_inst_tac [("x","m")] spec 1);
by (auto_tac (claset(),simpset() addsimps [partition_rhs2]));
qed "tag_point_eq_partition_point";

Goal "[| partition(a,b) D; D m < D n |] ==> m < n";
by (cut_inst_tac [("m","n"),("n","psize D")] less_linear 1);
by Auto_tac;
by (rtac ccontr 1 THEN dtac leI 1 THEN dtac le_imp_less_or_eq 1);
by (cut_inst_tac [("m","m"),("n","psize D")] less_linear 1);
by (auto_tac (claset() addDs [partition_gt],simpset()));
by (dres_inst_tac [("n","m")] partition_lt_gen 1 THEN Auto_tac);
by (ftac partition_eq_bound 1);
by (dtac partition_gt 2);
by Auto_tac;
by (rtac ccontr 1 THEN dtac leI 1 THEN dtac le_imp_less_or_eq 1);
by (auto_tac (claset() addDs [partition_eq_bound],simpset()));
by (rtac ccontr 1 THEN dtac leI 1 THEN dtac le_imp_less_or_eq 1);
by (ftac partition_eq_bound 1 THEN assume_tac 1);
by (dres_inst_tac [("m","m")] partition_eq_bound 1);
by Auto_tac;
qed "partition_lt_cancel";

Goalw [psize_def] 
     "[| a <= D n; D n < b; partition (a, b) D |] \
\     ==> psize (%x. if D x < D n then D(x) else D n) = n";
by (ftac lemma_additivity1 1);
by (assume_tac 1 THEN assume_tac 1);
by (rtac some_equality 1);
by (auto_tac (claset() addIs [partition_lt_Suc],simpset()));
by (dres_inst_tac [("n","n")] partition_lt_gen 1);
by (assume_tac 1 THEN arith_tac 1 THEN arith_tac 1);
by (cut_inst_tac [("m","na"),("n","psize D")] less_linear 1);
by (auto_tac (claset() addDs [partition_lt_cancel],simpset()));
by (rtac ccontr 1);
by (dtac (ARITH_PROVE "m ~= (n::nat) ==> m < n | n < m") 1);
by (etac disjE 1);
by (rotate_tac 5 1);
by (dres_inst_tac [("x","n")] spec 1);
by Auto_tac;
by (dres_inst_tac [("n","n")] partition_lt_gen 1);
by Auto_tac;
by (arith_tac 1);
by (dres_inst_tac [("x","n")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [split_if]) 1);
qed "lemma_additivity4_psize_eq";

Goal "partition (a, b) D  \
\     ==> psize (%x. if D x < D n then D(x) else D n) <= psize D";
by (forw_inst_tac [("r","n")] partition_ub 1);
by (dres_inst_tac [("x","D n")] real_le_imp_less_or_eq 1);
by (auto_tac (claset(),simpset() addsimps 
    [lemma_partition_eq RS sym]));
by (forw_inst_tac [("r","n")] partition_lb 1);
by (dtac lemma_additivity4_psize_eq 1);
by (rtac ccontr 3 THEN Auto_tac);
by (ftac (not_leE RSN (2,partition_eq_bound)) 1);
by (auto_tac (claset(),simpset() addsimps [partition_rhs]));
qed "lemma_psize_left_less_psize";

Goal "[| partition(a,b) D; na < psize (%x. if D x < D n then D(x) else D n) |] \
\     ==> na < psize D";
by (etac (lemma_psize_left_less_psize RSN (2,less_le_trans)) 1);
by (assume_tac 1);
qed "lemma_psize_left_less_psize2";


Goal "[| partition(a,b) D; D na < D n; D n < D (Suc na); \
\        n < psize D |] \
\     ==> False";
by (cut_inst_tac [("m","n"),("n","Suc na")] less_linear 1);
by Auto_tac;
by (dres_inst_tac [("n","n")] partition_lt_gen 2);
by Auto_tac;
by (cut_inst_tac [("m","psize D"),("n","na")] less_linear 1);
by (auto_tac (claset(),simpset() addsimps [partition_rhs2]));
by (dtac (ARITH_PROVE "n < Suc na ==> n < na | n = na") 1);
by Auto_tac;
by (dres_inst_tac [("n","na")] partition_lt_gen 1);
by Auto_tac;
val lemma_additivity3 = result();

Goalw [psize_def] "psize (%x. k) = 0";
by Auto_tac;
qed "psize_const";
Addsimps [psize_const];

Goal "[| partition(a,b) D; D na < D n; D n < D (Suc na); \
\        na < psize D |] \
\     ==> False";
by (forw_inst_tac [("m","n")] partition_lt_cancel 1);
by (auto_tac (claset() addIs [lemma_additivity3],simpset()));
val lemma_additivity3a = result();

Goal "[| partition(a,b) D; D n < b |] ==> psize (%x. D (x + n)) <= psize D - n";
by (res_inst_tac [("D2","(%x. D (x + n))")] (psize_def RS 
    meta_eq_to_obj_eq RS ssubst) 1);
by (res_inst_tac [("a","psize D - n")] someI2 1);
by Auto_tac;
by (dtac (ARITH_PROVE "(m::nat) < n - p  ==> m + p < n") 1);
by (asm_full_simp_tac (simpset() addsimps [partition]) 1);
by (dtac (ARITH_PROVE "(m::nat) - n <= p  ==> m <= p + n") 1);
by (case_tac "psize D <= n" 1);
by (dtac not_leE 2);
by (asm_simp_tac (simpset() addsimps 
    [ARITH_PROVE "p <= n ==> p - n = (0::nat)"]) 1);
by (blast_tac (claset() addDs [partition_rhs2]) 1);
by (asm_full_simp_tac (simpset() addsimps [partition]) 1);
by (rtac ccontr 1 THEN dtac not_leE 1);
by (dres_inst_tac [("x","psize D - n")] spec 1);
by Auto_tac;
by (ftac partition_rhs 1 THEN Step_tac 1); 
by (ftac partition_lt_cancel 1 THEN assume_tac 1);
by (dtac (partition  RS iffD1) 1 THEN Step_tac 1);
by (subgoal_tac "~  D (psize D - n + n) < D (Suc (psize D - n + n))" 1);
by (Blast_tac 1);
by (rotate_tac 6 1 THEN dres_inst_tac [("x","Suc (psize D)")] spec 1);
by (Asm_simp_tac 1);
qed "better_lemma_psize_right_eq1";

Goal "partition (a, D n) D ==> psize D <= n";
by (rtac ccontr 1 THEN dtac not_leE 1);
by (ftac partition_lt_Suc 1 THEN assume_tac 1);
by (forw_inst_tac [("r","Suc n")] partition_ub 1);
by Auto_tac;
qed "psize_le_n";

Goal "partition(a,D n) D ==> psize (%x. D (x + n)) <= psize D - n";
by (res_inst_tac [("D2","(%x. D (x + n))")] (psize_def RS 
    meta_eq_to_obj_eq RS ssubst) 1);
by (res_inst_tac [("a","psize D - n")] someI2 1);
by Auto_tac;
by (dtac (ARITH_PROVE "(m::nat) < n - p  ==> m + p < n") 1);
by (asm_full_simp_tac (simpset() addsimps [partition]) 1);
by (dtac (ARITH_PROVE "(m::nat) - n <= p  ==> m <= p + n") 1);
by (case_tac "psize D <= n" 1);
by (dtac not_leE 2);
by (asm_simp_tac (simpset() addsimps 
    [ARITH_PROVE "p <= n ==> p - n = (0::nat)"]) 1);
by (blast_tac (claset() addDs [partition_rhs2]) 1);
by (asm_full_simp_tac (simpset() addsimps [partition]) 1);
by (rtac ccontr 1 THEN dtac not_leE 1);
by (ftac psize_le_n 1);
by (dres_inst_tac [("x","psize D - n")] spec 1);
by (asm_full_simp_tac (simpset() addsimps 
    [ARITH_PROVE "p <= n ==> p - n = (0::nat)"]) 1);
by (dtac (partition  RS iffD1) 1 THEN Step_tac 1);
by (rotate_tac 5 1 THEN dres_inst_tac [("x","Suc n")] spec 1);
by Auto_tac;
qed "better_lemma_psize_right_eq1a";

Goal "partition(a,b) D ==> psize (%x. D (x + n)) <= psize D - n";
by (forw_inst_tac [("r1","n")] (partition_ub RS real_le_imp_less_or_eq) 1);
by (blast_tac (claset() addIs [better_lemma_psize_right_eq1a,
    better_lemma_psize_right_eq1]) 1);
qed "better_lemma_psize_right_eq";

Goal "[| partition(a,b) D; D n < b |] ==> psize (%x. D (x + n)) <= psize D";
by (res_inst_tac [("D2","(%x. D (x + n))")] (psize_def RS 
    meta_eq_to_obj_eq RS ssubst) 1);
by (res_inst_tac [("a","psize D - n")] someI2 1);
by Auto_tac;
by (dtac (ARITH_PROVE "(m::nat) < n - p  ==> m + p < n") 1);
by (asm_full_simp_tac (simpset() addsimps [partition]) 1);
by (subgoal_tac "n <= psize D" 1);
by (dtac (ARITH_PROVE "(m::nat) - n <= p  ==> m <= p + n") 1);
by (asm_full_simp_tac (simpset() addsimps [partition]) 1);
by (rtac ccontr 1 THEN dtac not_leE 1);
by (dtac (less_imp_le RSN (2,partition_rhs2)) 1);
by Auto_tac;
by (rtac ccontr 1 THEN dtac not_leE 1);
by (dres_inst_tac [("x","psize D")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [partition]) 1);
qed "lemma_psize_right_eq1";

(* should be combined with previous theorem; also proof has redundancy *)
Goal "partition(a,D n) D ==> psize (%x. D (x + n)) <= psize D";
by (res_inst_tac [("D2","(%x. D (x + n))")] (psize_def RS 
    meta_eq_to_obj_eq RS ssubst) 1);
by (res_inst_tac [("a","psize D - n")] someI2 1);
by Auto_tac;
by (dtac (ARITH_PROVE "(m::nat) < n - p  ==> m + p < n") 1);
by (asm_full_simp_tac (simpset() addsimps [partition]) 1);
by (dtac (ARITH_PROVE "(m::nat) - n <= p  ==> m <= p + n") 1);
by (case_tac "psize D <= n" 1);
by (dtac not_leE 2);
by (asm_simp_tac (simpset() addsimps 
    [ARITH_PROVE "p <= n ==> p - n = (0::nat)"]) 1);
by (blast_tac (claset() addDs [partition_rhs2]) 1);
by (asm_full_simp_tac (simpset() addsimps [partition]) 1);
by (rtac ccontr 1 THEN dtac not_leE 1);
by (dres_inst_tac [("x","psize D")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [partition]) 1);
qed "lemma_psize_right_eq1a";

Goal "[| partition(a,b) D |] ==> psize (%x. D (x + n)) <= psize D";
by (forw_inst_tac [("r1","n")] (partition_ub RS real_le_imp_less_or_eq) 1);
by (blast_tac (claset() addIs [lemma_psize_right_eq1a,lemma_psize_right_eq1]) 1);
qed "lemma_psize_right_eq";

Goal "[| a <= D n; tpart (a, b) (D, p) |] \
\     ==> tpart(a, D n) (%x. if D x < D n then D(x) else D n, \
\         %x. if D x < D n then p(x) else D n)";
by (forw_inst_tac [("r","n")] (tpart_partition RS partition_ub) 1);
by (dres_inst_tac [("x","D n")] real_le_imp_less_or_eq 1);
by (auto_tac (claset(),simpset() addsimps 
    [tpart_partition RS lemma_partition_eq RS sym,
     tpart_tag_eq RS sym]));
by (ftac (tpart_partition RSN (3,lemma_additivity1)) 1); 
by (auto_tac (claset(),simpset() addsimps [tpart_def]));
by (dtac (real_leI RS real_le_imp_less_or_eq) 2);
by (Auto_tac);
by (blast_tac (claset() addDs [lemma_additivity3]) 2);
by (dtac real_leI 2 THEN dres_inst_tac [("x","na")] spec 2);
by (arith_tac 2);
by (ftac lemma_additivity4_psize_eq 1);
by (REPEAT(assume_tac 1));
by (rtac (partition RS iffD2) 1);
by (ftac (partition RS iffD1) 1);
by (auto_tac (claset() addIs [partition_lt_gen],simpset() addsimps []));
by (dres_inst_tac [("n","n")] partition_lt_gen 1);
by (assume_tac 1 THEN arith_tac 1);
by (Blast_tac 1);
by (dtac partition_lt_cancel 1 THEN Auto_tac);
qed "tpart_left1";

Goal "[| a <= D n; tpart (a, b) (D, p); gauge (%x. a <= x & x <= D n) g;\
\        fine (%x. if x < D n then min (g x) ((D n - x)/ 2) \
\                else if x = D n then min (g (D n)) (ga (D n)) \
\                     else min (ga x) ((x - D n)/ 2)) (D, p) |] \
\     ==> fine g \
\          (%x. if D x < D n then D(x) else D n, \
\           %x. if D x < D n then p(x) else D n)";
by (auto_tac (claset(),simpset() addsimps [fine_def,tpart_def,gauge_def]));
by (ALLGOALS (ftac lemma_psize_left_less_psize2));
by (TRYALL(assume_tac));
by (ALLGOALS (dres_inst_tac [("x","na")] spec) THEN Auto_tac);
by (ALLGOALS(dres_inst_tac [("x","na")] spec));
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [split_if]) 1);
by (dtac (real_leI RS real_le_imp_less_or_eq) 1);
by (Step_tac 1);
by (blast_tac (claset() addDs [lemma_additivity3a]) 1);
by (dtac sym 1 THEN Auto_tac);
qed "fine_left1";

Goal "[| a <= D n; tpart (a, b) (D, p) |] \
\     ==> tpart(D n, b) (%x. D(x + n),%x. p(x + n))";
by (asm_full_simp_tac (simpset() addsimps [tpart_def,partition_def]) 1);
by (Step_tac 1);
by (res_inst_tac [("x","N - n")] exI 1 THEN Auto_tac);
by (rotate_tac 2 1);
by (dres_inst_tac [("x","na + n")] spec 1);
by (rotate_tac 3 2);
by (dres_inst_tac [("x","na + n")] spec 2);
by (ALLGOALS(arith_tac));
qed "tpart_right1";

Goal "[| a <= D n; tpart (a, b) (D, p); gauge (%x. D n <= x & x <= b) ga;\
\        fine (%x. if x < D n then min (g x) ((D n - x)/ 2) \
\                else if x = D n then min (g (D n)) (ga (D n)) \
\                     else min (ga x) ((x - D n)/ 2)) (D, p) |] \
\     ==> fine ga (%x. D(x + n),%x. p(x + n))";
by (auto_tac (claset(),simpset() addsimps [fine_def,gauge_def]));
by (dres_inst_tac [("x","na + n")] spec 1);
by (forw_inst_tac [("n","n")] (tpart_partition RS better_lemma_psize_right_eq) 1);
by Auto_tac;
by (arith_tac 1);
by (asm_full_simp_tac (simpset() addsimps [tpart_def]) 1 THEN Step_tac 1);
by (subgoal_tac "D n <= p (na + n)" 1);
by (dres_inst_tac [("y","p (na + n)")] real_le_imp_less_or_eq 1);
by (Step_tac 1);
by (asm_full_simp_tac (simpset() addsimps [split_if]) 1);
by (Asm_full_simp_tac 1);
by (dtac less_le_trans 1 THEN assume_tac 1);
by (rotate_tac 5 1);
by (dres_inst_tac [("x","na + n")] spec 1 THEN Step_tac 1);
by (rtac real_le_trans 1 THEN assume_tac 2);
by (case_tac "na = 0" 1 THEN Auto_tac);
by (rtac (partition_lt_gen RS order_less_imp_le) 1);
by Auto_tac;
by (arith_tac 1);
qed "fine_right1";

Goalw [rsum_def] 
   "rsum (D, p) (%x. f x + g x) =  rsum (D, p) f + rsum(D, p) g";
by (auto_tac (claset(),simpset() addsimps [sumr_add,real_add_mult_distrib]));
qed "rsum_add";

(* Bartle/Sherbert: Theorem 10.1.5 p. 278 *)
Goalw [Integral_def] 
    "[| a <= b; Integral(a,b) f k1; Integral(a,b) g k2 |] \
\    ==> Integral(a,b) (%x. f x + g x) (k1 + k2)";
by Auto_tac;
by (REPEAT(dres_inst_tac [("x","e/2")] spec 1));
by Auto_tac;
by (dtac gauge_min 1 THEN assume_tac 1);
by (res_inst_tac [("x","(%x. if ga x < gaa x then ga x else gaa x)")] exI 1);
by Auto_tac;
by (dtac fine_min 1);
by (REPEAT(dtac spec 1) THEN Auto_tac);
by (dres_inst_tac  [("R1.0","abs (rsum (D, p) f - k1)* 2"),
    ("R2.0","abs (rsum (D, p) g - k2) * 2")] 
    real_add_less_mono 1 THEN assume_tac 1);
by (auto_tac (claset(),HOL_ss addsimps [rsum_add,real_add_mult_distrib RS sym,
    real_mult_2_right RS sym,real_mult_less_iff1,CLAIM "(0::real) < 2"]));
by (arith_tac 1);
qed "Integral_add_fun";

Goal "[| partition(a,b) D; r < psize D |] ==> 0 < D (Suc r) - D r";
by (auto_tac (claset(),simpset() addsimps [partition]));
qed "partition_lt_gen2";

Goalw [tpart_def] 
     "[| ALL x. a <= x & x <= b --> f x <= g x; \
\        tpart(a,b) (D,p) \
\     |] ==> ALL n. n <= psize D --> f (p n) <= g (p n)";
by (Auto_tac THEN ftac (partition RS iffD1) 1);
by Auto_tac;
by (dres_inst_tac [("x","p n")] spec 1);
by Auto_tac;
by (case_tac "n = 0" 1);
by (rtac (partition_lt_gen RS order_less_le_trans RS order_less_imp_le) 2);
by Auto_tac;
by (dtac le_imp_less_or_eq 1 THEN Auto_tac);
by (dres_inst_tac [("x","psize D")] spec 2 THEN Auto_tac);
by (dres_inst_tac [("r","Suc n")] partition_ub 1);
by (dres_inst_tac [("x","n")] spec 1);
by Auto_tac;
qed "lemma_Integral_le";

Goalw [rsum_def] 
     "[| ALL x. a <= x & x <= b --> f x <= g x; \
\        tpart(a,b) (D,p) \
\     |] ==> rsum(D,p) f <= rsum(D,p) g";
by (auto_tac (claset() addSIs [sumr_le2] addDs 
    [tpart_partition RS partition_lt_gen2] addSDs 
    [lemma_Integral_le],simpset()));
qed "lemma_Integral_rsum_le";

Goalw [Integral_def] 
    "[| a <= b; \
\       ALL x. a <= x & x <= b --> f(x) <= g(x); \
\       Integral(a,b) f k1; Integral(a,b) g k2 \
\    |] ==> k1 <= k2";
by Auto_tac;
by (rotate_tac 2 1);
by (dres_inst_tac [("x","abs(k1 - k2)/2")] spec 1);
by (dres_inst_tac [("x","abs(k1 - k2)/2")] spec 1);
by Auto_tac;
by (dtac gauge_min 1 THEN assume_tac 1);
by (dres_inst_tac [("g","%x. if ga x < gaa x then ga x else gaa x")] 
    partition_exists 1 THEN assume_tac 1);
by Auto_tac;
by (dtac fine_min 1);
by (dres_inst_tac [("x","D")] spec 1 THEN dres_inst_tac [("x","D")] spec 1);
by (dres_inst_tac [("x","p")] spec 1 THEN dres_inst_tac [("x","p")] spec 1);
by Auto_tac;
by (ftac lemma_Integral_rsum_le 1 THEN assume_tac 1);
by (subgoal_tac 
    "abs((rsum(D,p) f - k1) - (rsum(D,p) g - k2)) < abs(k1 - k2)" 1);
by (arith_tac 1);
by (dtac real_add_less_mono 1 THEN assume_tac 1);
by (auto_tac (claset(),HOL_ss addsimps [real_add_mult_distrib RS sym,
    real_mult_2_right RS sym,real_mult_less_iff1,CLAIM "(0::real) < 2"]));
by (arith_tac 1);
qed "Integral_le";

Goalw [Integral_def] 
     "(EX k. Integral(a,b) f k) ==> \
\     (ALL e. 0 < e --> \
\              (EX g. gauge (%x. a <= x & x <= b) g & \
\                      (ALL D1 D2 p1 p2. \
\                           tpart(a,b) (D1, p1) & fine g (D1,p1) & \
\                           tpart(a,b) (D2, p2) & fine g (D2,p2) --> \ 
\                           abs(rsum(D1,p1) f - rsum(D2,p2) f) < e)))";
by Auto_tac;
by (dres_inst_tac [("x","e/2")] spec 1);
by Auto_tac;
by (rtac exI 1 THEN Auto_tac);
by (forw_inst_tac [("x","D1")] spec 1);
by (forw_inst_tac [("x","D2")] spec 1);
by (REPEAT(dtac spec 1) THEN Auto_tac);
by (thin_tac "0 < e" 1);
by (dtac real_add_less_mono 1 THEN assume_tac 1);
by (auto_tac (claset(),HOL_ss addsimps [real_add_mult_distrib RS sym,
    real_mult_2_right RS sym,real_mult_less_iff1,CLAIM "(0::real) < 2"]));
by (arith_tac 1);
qed "Integral_imp_Cauchy";

Goalw [Cauchy_def] 
     "Cauchy X = \
\     (ALL j. (EX M. ALL m n. M <= m & M <= n --> \
\              abs (X m + - X n) < inverse(real (Suc j))))";
by Auto_tac;
by (dtac reals_Archimedean 1);
by (Step_tac 1);
by (dres_inst_tac [("x","n")] spec 1);
by Auto_tac;
by (res_inst_tac [("x","M")] exI 1);
by Auto_tac;
by (dres_inst_tac [("x","m")] spec 1);
by (dres_inst_tac [("x","na")] spec 1);
by Auto_tac;
qed "Cauchy_iff2";

Goal "[| a <= b; ALL n. gauge (%x. a <= x & x <= b) (fa n) |] \
\     ==> ALL n. EX D p. tpart (a, b) (D, p) & fine (fa n) (D, p)";
by (Step_tac 1);
by (rtac partition_exists 1 THEN Auto_tac);
qed "partition_exists2";

Goal "[| a <= b; ALL c. a <= c & c <= b --> f' c <= g' c; \
\        ALL x. DERIV f x :> f' x; ALL x. DERIV g x :> g' x \
\     |] ==> f b - f a <= g b - g a";
by (rtac Integral_le 1);
by (assume_tac 1);
by (rtac FTC1 2);
by (rtac FTC1 4);
by Auto_tac;
qed "monotonic_anti_derivative";
