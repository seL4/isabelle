(*  Title:       IntFloor.ML
    Author:      Jacques D. Fleuriot
    Copyright:   2001,2002  University of Edinburgh
    Description: Floor and ceiling operations over reals
*)

Goal "((number_of n) < real (m::int)) = (number_of n < m)";
by Auto_tac;
by (rtac (real_of_int_less_iff RS iffD1) 1);
by (dtac (real_of_int_less_iff RS iffD2) 2);
by Auto_tac;
qed "number_of_less_real_of_int_iff";
Addsimps [number_of_less_real_of_int_iff];

Goal "(real (m::int) < (number_of n)) = (m < number_of n)";
by Auto_tac;
by (rtac (real_of_int_less_iff RS iffD1) 1);
by (dtac (real_of_int_less_iff RS iffD2) 2);
by Auto_tac;
qed "number_of_less_real_of_int_iff2";
Addsimps [number_of_less_real_of_int_iff2];

Goalw [real_le_def,zle_def] 
   "((number_of n) <= real (m::int)) = (number_of n <= m)";
by Auto_tac;
qed "number_of_le_real_of_int_iff";
Addsimps [number_of_le_real_of_int_iff];

Goalw [real_le_def,zle_def] 
   "(real (m::int) <= (number_of n)) = (m <= number_of n)";
by Auto_tac;
qed "number_of_le_real_of_int_iff2";
Addsimps [number_of_le_real_of_int_iff2];

Goalw [floor_def] "floor 0 = 0";
by (rtac Least_equality 1);
by Auto_tac;
qed "floor_zero";
Addsimps [floor_zero];

Goal "floor (real (0::nat)) = 0";
by Auto_tac;
qed "floor_real_of_nat_zero";
Addsimps [floor_real_of_nat_zero];

Goalw  [floor_def] "floor (real (n::nat)) = int n";
by (rtac Least_equality 1);
by (dtac (real_of_int_real_of_nat RS ssubst) 2);
by (dtac (real_of_int_less_iff RS iffD1) 2);
by (auto_tac (claset(),simpset() addsimps [real_of_int_real_of_nat]));
qed "floor_real_of_nat";
Addsimps [floor_real_of_nat];

Goalw [floor_def] "floor (- real (n::nat)) = - int n";
by (rtac Least_equality 1);
by (dtac (real_of_int_real_of_nat RS ssubst) 2);
by (dtac (real_of_int_minus RS subst) 2);
by (dtac (real_of_int_less_iff RS iffD1) 2);
by (auto_tac (claset(),simpset() addsimps [real_of_int_real_of_nat]));
qed "floor_minus_real_of_nat";
Addsimps [floor_minus_real_of_nat];

Goalw  [floor_def] "floor (real (n::int)) = n";
by (rtac Least_equality 1);
by (dtac (real_of_int_real_of_nat RS ssubst) 2);
by (dtac (real_of_int_less_iff RS iffD1) 2);
by Auto_tac;
qed "floor_real_of_int";
Addsimps [floor_real_of_int];

Goalw  [floor_def] "floor (- real (n::int)) = - n";
by (rtac Least_equality 1);
by (dtac (real_of_int_minus RS subst) 2);
by (dtac (real_of_int_real_of_nat RS ssubst) 2);
by (dtac (real_of_int_less_iff RS iffD1) 2);
by Auto_tac;
qed "floor_minus_real_of_int";
Addsimps [floor_minus_real_of_int];

Goal "0 <= r ==> EX (n::nat). real (n - 1) <= r & r < real (n)";
by (cut_inst_tac [("x","r")] reals_Archimedean2 1);
by (Step_tac 1);
by (forw_inst_tac [("P","%k. r < real k"),("k","n"),("m","%x. x")] 
    (thm "ex_has_least_nat") 1);
by Auto_tac;
by (res_inst_tac [("x","x")] exI 1);
by (dres_inst_tac [("x","x - 1")] spec 1);
by (auto_tac (claset() addDs [ARITH_PROVE "x <= x - Suc 0 ==> x = (0::nat)"],
    simpset()));
qed "reals_Archimedean6";

Goal "0 <= r ==> EX n. real (n) <= r & r < real (Suc n)";
by (dtac reals_Archimedean6 1);
by Auto_tac;
qed "reals_Archimedean6a";

Goal "0 <= r ==> EX n. real n <= r & r < real ((n::int) + 1)";
by (dtac reals_Archimedean6a 1);
by Auto_tac;
by (res_inst_tac [("x","int n")] exI 1);
by (auto_tac (claset(),simpset() addsimps [real_of_int_real_of_nat,
    real_of_nat_Suc]));
qed "reals_Archimedean_6b_int";

Goal "r < 0 ==> EX n. real n <= r & r < real ((n::int) + 1)";
by (dtac (CLAIM "r < (0::real) ==> 0 <= -r") 1);
by (dtac reals_Archimedean_6b_int 1);
by Auto_tac;
by (dtac real_le_imp_less_or_eq 1 THEN Auto_tac);
by (res_inst_tac [("x","- n - 1")] exI 1);
by (res_inst_tac [("x","- n")] exI 2);
by Auto_tac;
qed "reals_Archimedean_6c_int";

Goal " EX (n::int). real n <= r & r < real ((n::int) + 1)";
by (cut_inst_tac [("r","r")] (CLAIM "0 <= r | r < (0::real)") 1);
by (blast_tac (claset() addIs [reals_Archimedean_6b_int,
    reals_Archimedean_6c_int]) 1);
qed "real_lb_ub_int";

Goal "[| real n <= r;  r < real y + 1 |] ==> n <= (y::int)";
by (dres_inst_tac [("x","real n"),("z","real y + 1")] order_le_less_trans 1);
by (rotate_tac 1 2);
by (dtac ((CLAIM "real (1::int) = 1") RS ssubst) 2);
by (rotate_tac 1 2);
by (dres_inst_tac [("x1","y")] (real_of_int_add RS subst) 2);
by (dtac (real_of_int_less_iff RS iffD1) 2);
by Auto_tac;
val lemma_floor = result();

Goalw  [floor_def,Least_def] "real (floor r) <= r";
by (cut_inst_tac [("r","r")] real_lb_ub_int 1 THEN Step_tac 1);
by (rtac theI2 1);
by Auto_tac;
qed "real_of_int_floor_le";
Addsimps [real_of_int_floor_le];

Goalw [floor_def,Least_def] 
    "x < y ==> floor x <= floor y";
by (cut_inst_tac [("r","x")] real_lb_ub_int 1 THEN Step_tac 1);
by (cut_inst_tac [("r","y")] real_lb_ub_int 1 THEN Step_tac 1);
by (rtac theI2 1);
by (rtac theI2 3);
by Auto_tac;
by (auto_tac (claset() addIs [lemma_floor],simpset()));
by (ALLGOALS(force_tac (claset() addDs [lemma_floor],simpset())));
qed "floor_le";

Goal "x <= y ==> floor x <= floor y";
by (auto_tac (claset() addDs [real_le_imp_less_or_eq],simpset() 
    addsimps [floor_le]));
qed "floor_le2";

Goal "real na < real (x::int) + 1 ==> na <= x";
by (auto_tac (claset() addIs [lemma_floor],simpset()));
val lemma_floor2 = result();

Goalw [floor_def,Least_def]  
    "(real (floor x) = x) = (EX (n::int). x = real n)";
by (cut_inst_tac [("r","x")] real_lb_ub_int 1 THEN etac exE 1);
by (rtac theI2 1);
by (auto_tac (claset() addIs [lemma_floor],simpset()));
qed "real_of_int_floor_cancel";
Addsimps [real_of_int_floor_cancel];

Goalw [floor_def] 
  "[| real n < x; x < real n + 1 |] ==> floor x = n";
by (rtac Least_equality 1);
by (auto_tac (claset() addIs [lemma_floor],simpset()));
qed "floor_eq";

Goalw [floor_def] 
  "[| real n <= x; x < real n + 1 |] ==> floor x = n";
by (rtac Least_equality 1);
by (auto_tac (claset() addIs [lemma_floor],simpset()));
qed "floor_eq2";

Goal "[| real n < x; x < real (Suc n) |] ==> nat(floor x) = n";
by (rtac (inj_int RS injD) 1);
by (rtac (CLAIM "0 <= x ==> int (nat x) = x" RS ssubst) 1);
by (rtac floor_eq 2);
by (auto_tac (claset(),simpset() addsimps [real_of_nat_Suc,
    real_of_int_real_of_nat]));
by (rtac (floor_le RSN (2,zle_trans)) 1 THEN Auto_tac);
qed "floor_eq3";

Goal "[| real n <= x; x < real (Suc n) |] ==> nat(floor x) = n";
by (dtac order_le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [floor_eq3],simpset()));
qed "floor_eq4";

Goalw [real_number_of_def] 
       "floor(number_of n :: real) = (number_of n :: int)";
by (rtac floor_eq2 1);
by (rtac (CLAIM "x < x + (1::real)") 2);
by (rtac real_le_refl 1);
qed "floor_number_of_eq";
Addsimps [floor_number_of_eq];

Goalw [floor_def,Least_def] "r - 1 <= real(floor r)";
by (cut_inst_tac [("r","r")] real_lb_ub_int 1 THEN Step_tac 1);
by (rtac theI2 1);
by (auto_tac (claset() addIs [lemma_floor],simpset()));
qed "real_of_int_floor_ge_diff_one";
Addsimps [real_of_int_floor_ge_diff_one];

Goal "r <= real(floor r) + 1";
by (cut_inst_tac [("r","r")] real_of_int_floor_ge_diff_one 1);
by (auto_tac (claset(),simpset() delsimps [real_of_int_floor_ge_diff_one]));
qed "real_of_int_floor_add_one_ge";
Addsimps [real_of_int_floor_add_one_ge];


(*--------------------------------------------------------------------------------*)
(* ceiling function for positive reals                                            *)
(*--------------------------------------------------------------------------------*)

Goalw [ceiling_def] "ceiling 0 = 0";
by Auto_tac;
qed "ceiling_zero";
Addsimps [ceiling_zero];

Goalw  [ceiling_def] "ceiling (real (n::nat)) = int n";
by Auto_tac;
qed "ceiling_real_of_nat";
Addsimps [ceiling_real_of_nat];

Goal "ceiling (real (0::nat)) = 0";
by Auto_tac;
qed "ceiling_real_of_nat_zero";
Addsimps [ceiling_real_of_nat_zero];

Goalw  [ceiling_def] "ceiling (real (floor r)) = floor r";
by Auto_tac;
qed "ceiling_floor";
Addsimps [ceiling_floor];

Goalw  [ceiling_def] "floor (real (ceiling r)) = ceiling r";
by Auto_tac;
qed "floor_ceiling";
Addsimps [floor_ceiling];

Goalw [ceiling_def] "r <= real (ceiling r)";
by Auto_tac;
by (rtac (CLAIM "x <= -y ==> (y::real) <= - x") 1);
by Auto_tac;
qed "real_of_int_ceiling_ge";
Addsimps [real_of_int_ceiling_ge];

Goalw [ceiling_def] "x < y ==> ceiling x <= ceiling y";
by (auto_tac (claset() addIs [floor_le],simpset()));
qed "ceiling_le";

Goalw [ceiling_def] "x <= y ==> ceiling x <= ceiling y";
by (auto_tac (claset() addIs [floor_le2],simpset()));
qed "ceiling_le2";

Goalw [ceiling_def] "(real (ceiling x) = x) = (EX (n::int). x = real n)";
by Auto_tac;
by (dtac (CLAIM "- x = y ==> (x::real) = -y") 1);
by Auto_tac;
by (res_inst_tac [("x","-n")] exI 1);
by Auto_tac;
qed "real_of_int_ceiling_cancel";
Addsimps [real_of_int_ceiling_cancel];

Goalw [ceiling_def] 
  "[| real n < x; x < real n + 1 |] ==> ceiling x = n + 1";
by (rtac (CLAIM "x = - y ==> - (x::int) = y") 1);
by (auto_tac (claset() addIs [floor_eq],simpset()));
qed "ceiling_eq";

Goalw [ceiling_def] 
   "[| real n < x; x <= real n + 1 |] ==> ceiling x = n + 1";
by (rtac (CLAIM "x = - y ==> - (x::int) = y") 1);
by (auto_tac (claset() addIs [floor_eq2],simpset()));
qed "ceiling_eq2";

Goalw [ceiling_def] "[| real n - 1 < x; x <= real n  |] ==> ceiling x = n";
by (rtac (CLAIM "x = -(y::int) ==> - x = y") 1);
by (auto_tac (claset() addIs [floor_eq2],simpset()));
qed "ceiling_eq3";

Goalw [ceiling_def,real_number_of_def] 
  "ceiling (number_of n :: real) = (number_of n :: int)";
by (rtac (CLAIM "x = - y ==> - (x::int) = y") 1);
by (rtac (floor_minus_real_of_int RS ssubst) 1);
by Auto_tac;
qed "ceiling_number_of_eq";
Addsimps [ceiling_number_of_eq];

Goalw [ceiling_def] "real (ceiling r) - 1 <= r";
by (rtac (CLAIM "-x <= -y ==> (y::real) <= x") 1);
by (auto_tac (claset(),simpset() addsimps [real_diff_def]));
qed "real_of_int_ceiling_diff_one_le";
Addsimps [real_of_int_ceiling_diff_one_le];

Goal "real (ceiling r) <= r + 1";
by (cut_inst_tac [("r","r")] real_of_int_ceiling_diff_one_le 1);
by (auto_tac (claset(),simpset() delsimps [real_of_int_ceiling_diff_one_le]));
qed "real_of_int_ceiling_le_add_one";
Addsimps [real_of_int_ceiling_le_add_one];

