(*  Title:      IntDef.ML
    ID:         $Id$
    Authors:    Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

The integers as equivalence classes over nat*nat.
*)


(*Rewrite the overloaded 0::int to (int 0)*)
Addsimps [Zero_def];

Goalw  [intrel_def] "((x1,y1),(x2,y2)): intrel = (x1+y2 = x2+y1)";
by (Blast_tac 1);
qed "intrel_iff";

Goalw [intrel_def, equiv_def, refl_def, sym_def, trans_def]
    "equiv UNIV intrel";
by Auto_tac;
qed "equiv_intrel";

bind_thm ("equiv_intrel_iff", 
	  [equiv_intrel, UNIV_I, UNIV_I] MRS eq_equiv_class_iff);

Goalw [Integ_def,intrel_def,quotient_def]
     "intrel^^{(x,y)}:Integ";
by (Fast_tac 1);
qed "intrel_in_integ";

Goal "inj_on Abs_Integ Integ";
by (rtac inj_on_inverseI 1);
by (etac Abs_Integ_inverse 1);
qed "inj_on_Abs_Integ";

Addsimps [equiv_intrel_iff, inj_on_Abs_Integ RS inj_on_iff,
          intrel_iff, intrel_in_integ, Abs_Integ_inverse];

Goal "inj(Rep_Integ)";
by (rtac inj_inverseI 1);
by (rtac Rep_Integ_inverse 1);
qed "inj_Rep_Integ";


(** int: the injection from "nat" to "int" **)

Goal "inj int";
by (rtac injI 1);
by (rewtac int_def);
by (dtac (inj_on_Abs_Integ RS inj_onD) 1);
by (REPEAT (rtac intrel_in_integ 1));
by (dtac eq_equiv_class 1);
by (rtac equiv_intrel 1);
by (Fast_tac 1);
by (asm_full_simp_tac (simpset() addsimps [intrel_def]) 1);
qed "inj_int";


(**** zminus: unary negation on Integ ****)

Goalw [congruent_def, intrel_def]
     "congruent intrel (%(x,y). intrel^^{(y,x)})";
by (auto_tac (claset(), simpset() addsimps add_ac));
qed "zminus_congruent";

Goalw [zminus_def]
      "- Abs_Integ(intrel^^{(x,y)}) = Abs_Integ(intrel ^^ {(y,x)})";
by (simp_tac (simpset() addsimps 
	      [equiv_intrel RS UN_equiv_class, zminus_congruent]) 1);
qed "zminus";

(*Every integer can be written in the form Abs_Integ(...) *)
val [prem] = Goal "(!!x y. z = Abs_Integ(intrel^^{(x,y)}) ==> P) ==> P";
by (res_inst_tac [("x1","z")] 
    (rewrite_rule [Integ_def] Rep_Integ RS quotientE) 1);
by (dres_inst_tac [("f","Abs_Integ")] arg_cong 1);
by (res_inst_tac [("p","x")] PairE 1);
by (rtac prem 1);
by (asm_full_simp_tac (simpset() addsimps [Rep_Integ_inverse]) 1);
qed "eq_Abs_Integ";

Goal "- (- z) = (z::int)";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zminus]) 1);
qed "zminus_zminus";
Addsimps [zminus_zminus];

Goal "inj(%z::int. -z)";
by (rtac injI 1);
by (dres_inst_tac [("f","uminus")] arg_cong 1);
by (Asm_full_simp_tac 1);
qed "inj_zminus";

Goalw [int_def] "- (int 0) = int 0";
by (simp_tac (simpset() addsimps [zminus]) 1);
qed "zminus_int0";

Addsimps [zminus_int0];


(**** neg: the test for negative integers ****)


Goalw [neg_def, int_def] "~ neg(int n)";
by (Simp_tac 1);
qed "not_neg_int";

Goalw [neg_def, int_def] "neg(- (int (Suc n)))";
by (simp_tac (simpset() addsimps [zminus]) 1);
qed "neg_zminus_int";

Addsimps [neg_zminus_int, not_neg_int]; 


(**** zadd: addition on Integ ****)

Goalw [zadd_def]
  "Abs_Integ(intrel^^{(x1,y1)}) + Abs_Integ(intrel^^{(x2,y2)}) = \
\  Abs_Integ(intrel^^{(x1+x2, y1+y2)})";
by (asm_simp_tac (simpset() addsimps [UN_UN_split_split_eq]) 1);
by (stac (equiv_intrel RS UN_equiv_class2) 1);
by (auto_tac (claset(), simpset() addsimps [congruent2_def]));
qed "zadd";

Goal "- (z + w) = (- z) + (- w::int)";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zminus,zadd]) 1);
qed "zminus_zadd_distrib";
Addsimps [zminus_zadd_distrib];

Goal "(z::int) + w = w + z";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps add_ac @ [zadd]) 1);
qed "zadd_commute";

Goal "((z1::int) + z2) + z3 = z1 + (z2 + z3)";
by (res_inst_tac [("z","z1")] eq_Abs_Integ 1);
by (res_inst_tac [("z","z2")] eq_Abs_Integ 1);
by (res_inst_tac [("z","z3")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zadd, add_assoc]) 1);
qed "zadd_assoc";

(*For AC rewriting*)
Goal "(x::int)+(y+z)=y+(x+z)";
by (rtac (zadd_commute RS trans) 1);
by (rtac (zadd_assoc RS trans) 1);
by (rtac (zadd_commute RS arg_cong) 1);
qed "zadd_left_commute";

(*Integer addition is an AC operator*)
bind_thms ("zadd_ac", [zadd_assoc,zadd_commute,zadd_left_commute]);

Goalw [int_def] "(int m) + (int n) = int (m + n)";
by (simp_tac (simpset() addsimps [zadd]) 1);
qed "zadd_int";

Goal "(int m) + (int n + z) = int (m + n) + z";
by (simp_tac (simpset() addsimps [zadd_int, zadd_assoc RS sym]) 1);
qed "zadd_int_left";

Goal "int (Suc m) = int 1 + (int m)";
by (simp_tac (simpset() addsimps [zadd_int]) 1);
qed "int_Suc_int_1";

Goalw [int_def] "int 0 + z = z";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zadd]) 1);
qed "zadd_int0";

Goal "z + int 0 = z";
by (rtac (zadd_commute RS trans) 1);
by (rtac zadd_int0 1);
qed "zadd_int0_right";

Goalw [int_def] "z + (- z) = int 0";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zminus, zadd, add_commute]) 1);
qed "zadd_zminus_inverse";

Goal "(- z) + z = int 0";
by (rtac (zadd_commute RS trans) 1);
by (rtac zadd_zminus_inverse 1);
qed "zadd_zminus_inverse2";

Addsimps [zadd_int0, zadd_int0_right,
	  zadd_zminus_inverse, zadd_zminus_inverse2];

(*for the instance declaration int :: plus_ac0*)
Goal "0 + z = (z::int)";
by (Simp_tac 1);
qed "zadd_zero";

Goal "z + (- z + w) = (w::int)";
by (simp_tac (simpset() addsimps [zadd_assoc RS sym]) 1);
qed "zadd_zminus_cancel";

Goal "(-z) + (z + w) = (w::int)";
by (simp_tac (simpset() addsimps [zadd_assoc RS sym]) 1);
qed "zminus_zadd_cancel";

Addsimps [zadd_zminus_cancel, zminus_zadd_cancel];

Goal "int 0 - x = -x";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff_int0";

Goal "x - int 0 = x";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff_int0_right";

Goal "x - x = int 0";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff_self";

Addsimps [zdiff_int0, zdiff_int0_right, zdiff_self];


(** Lemmas **)

Goal "(z::int) + v = z' + v' ==> z + (v + w) = z' + (v' + w)";
by (asm_simp_tac (simpset() addsimps [zadd_assoc RS sym]) 1);
qed "zadd_assoc_cong";

Goal "(z::int) + (v + w) = v + (z + w)";
by (REPEAT (ares_tac [zadd_commute RS zadd_assoc_cong] 1));
qed "zadd_assoc_swap";


(**** zmult: multiplication on Integ ****)

(*Congruence property for multiplication*)
Goal "congruent2 intrel \
\       (%p1 p2. (%(x1,y1). (%(x2,y2).   \
\                   intrel^^{(x1*x2 + y1*y2, x1*y2 + y1*x2)}) p2) p1)";
by (rtac (equiv_intrel RS congruent2_commuteI) 1);
by (pair_tac "w" 2);
by (ALLGOALS Clarify_tac);
by (simp_tac (simpset() addsimps add_ac@mult_ac) 1);
by (asm_simp_tac (simpset() delsimps [equiv_intrel_iff]
                            addsimps add_ac@mult_ac) 1);
by (rename_tac "x1 x2 y1 y2 z1 z2" 1);
by (rtac ([equiv_intrel, intrel_iff RS iffD2] MRS equiv_class_eq) 1);
by (asm_full_simp_tac (simpset() addsimps [intrel_def]) 1);
by (subgoal_tac 
    "x1*z1 + y2*z1 = y1*z1 + x2*z1 & x1*z2 + y2*z2 = y1*z2 + x2*z2" 1);
by (asm_simp_tac (simpset() addsimps [add_mult_distrib RS sym]) 2);
by (arith_tac 1);
qed "zmult_congruent2";

Goalw [zmult_def]
   "Abs_Integ((intrel^^{(x1,y1)})) * Abs_Integ((intrel^^{(x2,y2)})) =   \
\   Abs_Integ(intrel ^^ {(x1*x2 + y1*y2, x1*y2 + y1*x2)})";
by (asm_simp_tac
    (simpset() addsimps [UN_UN_split_split_eq, zmult_congruent2,
			 equiv_intrel RS UN_equiv_class2]) 1);
qed "zmult";

Goal "(- z) * w = - (z * (w::int))";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zminus, zmult] @ add_ac) 1);
qed "zmult_zminus";

Goal "(z::int) * w = w * z";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zmult] @ add_ac @ mult_ac) 1);
qed "zmult_commute";

Goal "((z1::int) * z2) * z3 = z1 * (z2 * z3)";
by (res_inst_tac [("z","z1")] eq_Abs_Integ 1);
by (res_inst_tac [("z","z2")] eq_Abs_Integ 1);
by (res_inst_tac [("z","z3")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [add_mult_distrib2,zmult] @ 
                                     add_ac @ mult_ac) 1);
qed "zmult_assoc";

(*For AC rewriting*)
Goal "(z1::int)*(z2*z3) = z2*(z1*z3)";
by (rtac (zmult_commute RS trans) 1);
by (rtac (zmult_assoc RS trans) 1);
by (rtac (zmult_commute RS arg_cong) 1);
qed "zmult_left_commute";

(*Integer multiplication is an AC operator*)
bind_thms ("zmult_ac", [zmult_assoc, zmult_commute, zmult_left_commute]);

Goal "((z1::int) + z2) * w = (z1 * w) + (z2 * w)";
by (res_inst_tac [("z","z1")] eq_Abs_Integ 1);
by (res_inst_tac [("z","z2")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by (asm_simp_tac 
    (simpset() addsimps [add_mult_distrib2, zadd, zmult] @ 
                        add_ac @ mult_ac) 1);
qed "zadd_zmult_distrib";

val zmult_commute'= inst "z" "w" zmult_commute;

Goal "w * (- z) = - (w * (z::int))";
by (simp_tac (simpset() addsimps [zmult_commute', zmult_zminus]) 1);
qed "zmult_zminus_right";

Goal "(w::int) * (z1 + z2) = (w * z1) + (w * z2)";
by (simp_tac (simpset() addsimps [zmult_commute',zadd_zmult_distrib]) 1);
qed "zadd_zmult_distrib2";

Goalw [zdiff_def] "((z1::int) - z2) * w = (z1 * w) - (z2 * w)";
by (stac zadd_zmult_distrib 1);
by (simp_tac (simpset() addsimps [zmult_zminus]) 1);
qed "zdiff_zmult_distrib";

Goal "(w::int) * (z1 - z2) = (w * z1) - (w * z2)";
by (simp_tac (simpset() addsimps [zmult_commute',zdiff_zmult_distrib]) 1);
qed "zdiff_zmult_distrib2";

bind_thms ("int_distrib",
  [zadd_zmult_distrib, zadd_zmult_distrib2, zdiff_zmult_distrib, zdiff_zmult_distrib2]);

Goalw [int_def] "(int m) * (int n) = int (m * n)";
by (simp_tac (simpset() addsimps [zmult]) 1);
qed "zmult_int";

Goalw [int_def] "int 0 * z = int 0";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zmult]) 1);
qed "zmult_int0";

Goalw [int_def] "int 1 * z = z";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zmult]) 1);
qed "zmult_int1";

Goal "z * int 0 = int 0";
by (rtac ([zmult_commute, zmult_int0] MRS trans) 1);
qed "zmult_int0_right";

Goal "z * int 1 = z";
by (rtac ([zmult_commute, zmult_int1] MRS trans) 1);
qed "zmult_int1_right";

Addsimps [zmult_int0, zmult_int0_right, zmult_int1, zmult_int1_right];


(* Theorems about less and less_equal *)

(*This lemma allows direct proofs of other <-properties*)
Goalw [zless_def, neg_def, zdiff_def, int_def] 
    "(w < z) = (EX n. z = w + int(Suc n))";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [zadd, zminus]) 1);
by (safe_tac (claset() addSDs [less_eq_Suc_add]));
by (res_inst_tac [("x","k")] exI 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps add_ac)));
qed "zless_iff_Suc_zadd";

Goal "z < z + int (Suc n)";
by (auto_tac (claset(),
	      simpset() addsimps [zless_iff_Suc_zadd, zadd_assoc, 
				  zadd_int]));
qed "zless_zadd_Suc";

Goal "[| z1<z2; z2<z3 |] ==> z1 < (z3::int)";
by (auto_tac (claset(),
	      simpset() addsimps [zless_iff_Suc_zadd, zadd_assoc, 
				  zadd_int]));
qed "zless_trans";

Goal "!!w::int. z<w ==> ~w<z";
by (safe_tac (claset() addSDs [zless_iff_Suc_zadd RS iffD1]));
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [int_def, zadd]) 1);
qed "zless_not_sym";

(* [| n<m;  ~P ==> m<n |] ==> P *)
bind_thm ("zless_asym", zless_not_sym RS swap);

Goal "!!z::int. ~ z<z";
by (resolve_tac [zless_asym RS notI] 1);
by (REPEAT (assume_tac 1));
qed "zless_not_refl";

(* z<z ==> R *)
bind_thm ("zless_irrefl", zless_not_refl RS notE);
AddSEs [zless_irrefl];

Goal "z<w ==> w ~= (z::int)";
by (Blast_tac 1);
qed "zless_not_refl2";

(* s < t ==> s ~= t *)
bind_thm ("zless_not_refl3", zless_not_refl2 RS not_sym);


(*"Less than" is a linear ordering*)
Goalw [zless_def, neg_def, zdiff_def] 
    "z<w | z=w | w<(z::int)";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by Safe_tac;
by (asm_full_simp_tac
    (simpset() addsimps [zadd, zminus, Image_iff, Bex_def]) 1);
by (res_inst_tac [("m1", "x+ya"), ("n1", "xa+y")] (less_linear RS disjE) 1);
by (ALLGOALS (force_tac (claset(), simpset() addsimps add_ac)));
qed "zless_linear";

Goal "!!w::int. (w ~= z) = (w<z | z<w)";
by (cut_facts_tac [zless_linear] 1);
by (Blast_tac 1);
qed "int_neq_iff";

(*** eliminates ~= in premises ***)
bind_thm("int_neqE", int_neq_iff RS iffD1 RS disjE);

Goal "(int m = int n) = (m = n)"; 
by (fast_tac (claset() addSEs [inj_int RS injD]) 1); 
qed "int_int_eq"; 
AddIffs [int_int_eq]; 

Goal "(int m < int n) = (m<n)";
by (simp_tac (simpset() addsimps [less_iff_Suc_add, zless_iff_Suc_zadd, 
				  zadd_int]) 1);
qed "zless_int";
Addsimps [zless_int];


(*** Properties of <= ***)

Goalw [zle_def, le_def] "(int m <= int n) = (m<=n)";
by (Simp_tac 1);
qed "zle_int";
Addsimps [zle_int];

Goalw [zle_def] "z <= w ==> z < w | z=(w::int)";
by (cut_facts_tac [zless_linear] 1);
by (blast_tac (claset() addEs [zless_asym]) 1);
qed "zle_imp_zless_or_eq";

Goalw [zle_def] "z<w | z=w ==> z <= (w::int)";
by (cut_facts_tac [zless_linear] 1);
by (blast_tac (claset() addEs [zless_asym]) 1);
qed "zless_or_eq_imp_zle";

Goal "(x <= (y::int)) = (x < y | x=y)";
by (REPEAT(ares_tac [iffI, zless_or_eq_imp_zle, zle_imp_zless_or_eq] 1));
qed "int_le_less";

Goal "w <= (w::int)";
by (simp_tac (simpset() addsimps [int_le_less]) 1);
qed "zle_refl";

Goalw [zle_def] "z < w ==> z <= (w::int)";
by (blast_tac (claset() addEs [zless_asym]) 1);
qed "zless_imp_zle";

(* Axiom 'linorder_linear' of class 'linorder': *)
Goal "(z::int) <= w | w <= z";
by (simp_tac (simpset() addsimps [int_le_less]) 1);
by (cut_facts_tac [zless_linear] 1);
by (Blast_tac 1);
qed "zle_linear";

Goal "[| i <= j; j < k |] ==> i < (k::int)";
by (dtac zle_imp_zless_or_eq 1);
by (blast_tac (claset() addIs [zless_trans]) 1);
qed "zle_zless_trans";

Goal "[| i < j; j <= k |] ==> i < (k::int)";
by (dtac zle_imp_zless_or_eq 1);
by (blast_tac (claset() addIs [zless_trans]) 1);
qed "zless_zle_trans";

Goal "[| i <= j; j <= k |] ==> i <= (k::int)";
by (EVERY1 [dtac zle_imp_zless_or_eq, dtac zle_imp_zless_or_eq,
            rtac zless_or_eq_imp_zle, 
	    blast_tac (claset() addIs [zless_trans])]);
qed "zle_trans";

Goal "[| z <= w; w <= z |] ==> z = (w::int)";
by (EVERY1 [dtac zle_imp_zless_or_eq, dtac zle_imp_zless_or_eq,
            blast_tac (claset() addEs [zless_asym])]);
qed "zle_anti_sym";

(* Axiom 'order_less_le' of class 'order': *)
Goal "(w::int) < z = (w <= z & w ~= z)";
by (simp_tac (simpset() addsimps [zle_def, int_neq_iff]) 1);
by (blast_tac (claset() addSEs [zless_asym]) 1);
qed "int_less_le";

(* [| w <= z; w ~= z |] ==> w < z *)
bind_thm ("zle_neq_implies_zless", [int_less_le, conjI] MRS iffD2);



(*** Subtraction laws ***)

Goal "x + (y - z) = (x + y) - (z::int)";
by (simp_tac (simpset() addsimps zdiff_def::zadd_ac) 1);
qed "zadd_zdiff_eq";

Goal "(x - y) + z = (x + z) - (y::int)";
by (simp_tac (simpset() addsimps zdiff_def::zadd_ac) 1);
qed "zdiff_zadd_eq";

Goal "(x - y) - z = x - (y + (z::int))";
by (simp_tac (simpset() addsimps zdiff_def::zadd_ac) 1);
qed "zdiff_zdiff_eq";

Goal "x - (y - z) = (x + z) - (y::int)";
by (simp_tac (simpset() addsimps zdiff_def::zadd_ac) 1);
qed "zdiff_zdiff_eq2";

Goalw [zless_def, zdiff_def] "(x-y < z) = (x < z + (y::int))";
by (simp_tac (simpset() addsimps zadd_ac) 1);
qed "zdiff_zless_eq";

Goalw [zless_def, zdiff_def] "(x < z-y) = (x + (y::int) < z)";
by (simp_tac (simpset() addsimps zadd_ac) 1);
qed "zless_zdiff_eq";

Goalw [zle_def] "(x-y <= z) = (x <= z + (y::int))";
by (simp_tac (simpset() addsimps [zless_zdiff_eq]) 1);
qed "zdiff_zle_eq";

Goalw [zle_def] "(x <= z-y) = (x + (y::int) <= z)";
by (simp_tac (simpset() addsimps [zdiff_zless_eq]) 1);
qed "zle_zdiff_eq";

Goalw [zdiff_def] "(x-y = z) = (x = z + (y::int))";
by (auto_tac (claset(), simpset() addsimps [zadd_assoc]));
qed "zdiff_eq_eq";

Goalw [zdiff_def] "(x = z-y) = (x + (y::int) = z)";
by (auto_tac (claset(), simpset() addsimps [zadd_assoc]));
qed "eq_zdiff_eq";

(*This list of rewrites simplifies (in)equalities by bringing subtractions
  to the top and then moving negative terms to the other side.  
  Use with zadd_ac*)
bind_thms ("zcompare_rls",
    [symmetric zdiff_def,
     zadd_zdiff_eq, zdiff_zadd_eq, zdiff_zdiff_eq, zdiff_zdiff_eq2, 
     zdiff_zless_eq, zless_zdiff_eq, zdiff_zle_eq, zle_zdiff_eq, 
     zdiff_eq_eq, eq_zdiff_eq]);


(** Cancellation laws **)

Goal "!!w::int. (z + w' = z + w) = (w' = w)";
by Safe_tac;
by (dres_inst_tac [("f", "%x. x + (-z)")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps zadd_ac) 1);
qed "zadd_left_cancel";

Addsimps [zadd_left_cancel];

Goal "!!z::int. (w' + z = w + z) = (w' = w)";
by (asm_full_simp_tac (simpset() addsimps zadd_ac) 1);
qed "zadd_right_cancel";

Addsimps [zadd_right_cancel];


(** For the cancellation simproc.
    The idea is to cancel like terms on opposite sides by subtraction **)

Goal "(x::int) - y = x' - y' ==> (x<y) = (x'<y')";
by (asm_simp_tac (simpset() addsimps [zless_def]) 1);
qed "zless_eqI";

Goal "(x::int) - y = x' - y' ==> (y<=x) = (y'<=x')";
by (dtac zless_eqI 1);
by (asm_simp_tac (simpset() addsimps [zle_def]) 1);
qed "zle_eqI";

Goal "(x::int) - y = x' - y' ==> (x=y) = (x'=y')";
by Safe_tac;
by (ALLGOALS
    (asm_full_simp_tac (simpset() addsimps [eq_zdiff_eq, zdiff_eq_eq])));
qed "zeq_eqI";

