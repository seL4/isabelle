(*  Title:      ZF/ex/Bin.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Arithmetic on binary integers.
*)


AddTCs bin.intrs;

Goal "NCons(Pls,0) = Pls";
by (Asm_simp_tac 1);
qed "NCons_Pls_0";

Goal "NCons(Pls,1) = Pls BIT 1";
by (Asm_simp_tac 1);
qed "NCons_Pls_1";

Goal "NCons(Min,0) = Min BIT 0";
by (Asm_simp_tac 1);
qed "NCons_Min_0";

Goal "NCons(Min,1) = Min";
by (Asm_simp_tac 1);
qed "NCons_Min_1";

Goal "NCons(w BIT x,b) = w BIT x BIT b";
by (asm_simp_tac (simpset() addsimps bin.case_eqns) 1);
qed "NCons_BIT";

val NCons_simps = [NCons_Pls_0, NCons_Pls_1, 
		   NCons_Min_0, NCons_Min_1,
		   NCons_BIT];
Addsimps NCons_simps;


(** Type checking **)

Goal "w: bin ==> integ_of(w) : int";
by (induct_tac "w" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [bool_into_nat])));
qed "integ_of_type";
AddTCs [integ_of_type];

Goal "[| w: bin; b: bool |] ==> NCons(w,b) : bin";
by (induct_tac "w" 1);
by Auto_tac;
qed "NCons_type";
AddTCs [NCons_type];

Goal "w: bin ==> bin_succ(w) : bin";
by (induct_tac "w" 1);
by Auto_tac;
qed "bin_succ_type";
AddTCs [bin_succ_type];

Goal "w: bin ==> bin_pred(w) : bin";
by (induct_tac "w" 1);
by Auto_tac;
qed "bin_pred_type";
AddTCs [bin_pred_type];

Goal "w: bin ==> bin_minus(w) : bin";
by (induct_tac "w" 1);
by Auto_tac;
qed "bin_minus_type";
AddTCs [bin_minus_type];

(*This proof is complicated by the mutual recursion*)
Goalw [bin_add_def] "v: bin ==> ALL w: bin. bin_add(v,w) : bin";
by (induct_tac "v" 1);
by (rtac ballI 3);
by (rename_tac "w'" 3);
by (induct_tac "w'" 3);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [NCons_type])));
qed_spec_mp "bin_add_type";
AddTCs [bin_add_type];

Goal "[| v: bin; w: bin |] ==> bin_mult(v,w) : bin";
by (induct_tac "v" 1);
by Auto_tac;
qed "bin_mult_type";
AddTCs [bin_mult_type];


(**** The carry/borrow functions, bin_succ and bin_pred ****)

(*NCons preserves the integer value of its argument*)
Goal "[| w: bin; b: bool |] ==>     \
\         integ_of(NCons(w,b)) = integ_of(w BIT b)";
by (etac bin.elim 1);
by (Asm_simp_tac 3);
by (ALLGOALS (etac boolE));
by (ALLGOALS Asm_simp_tac);
qed "integ_of_NCons";

Addsimps [integ_of_NCons];

Goal "w: bin ==> integ_of(bin_succ(w)) = $#1 $+ integ_of(w)";
by (etac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (etac boolE 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps zadd_ac)));
qed "integ_of_succ";

Goal "w: bin ==> integ_of(bin_pred(w)) = $- ($#1) $+ integ_of(w)";
by (etac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (etac boolE 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps zadd_ac)));
qed "integ_of_pred";

Addsimps [integ_of_succ, integ_of_pred];


(*** bin_minus: (unary!) negation of binary integers ***)

Goal "w: bin ==> integ_of(bin_minus(w)) = $- integ_of(w)";
by (etac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (etac boolE 1);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps zadd_ac@[zminus_zadd_distrib])));
qed "integ_of_minus";


(*** bin_add: binary addition ***)

Goalw [bin_add_def] "w: bin ==> bin_add(Pls,w) = w";
by (Asm_simp_tac 1);
qed "bin_add_Pls";

Goalw [bin_add_def] "w: bin ==> bin_add(Min,w) = bin_pred(w)";
by (Asm_simp_tac 1);
qed "bin_add_Min";

Goalw [bin_add_def] "bin_add(v BIT x,Pls) = v BIT x";
by (Simp_tac 1);
qed "bin_add_BIT_Pls";

Goalw [bin_add_def] "bin_add(v BIT x,Min) = bin_pred(v BIT x)";
by (Simp_tac 1);
qed "bin_add_BIT_Min";

Goalw [bin_add_def] "[| w: bin;  y: bool |]              \
\     ==> bin_add(v BIT x, w BIT y) = \
\         NCons(bin_add(v, cond(x and y, bin_succ(w), w)), x xor y)";
by (Asm_simp_tac 1);
qed "bin_add_BIT_BIT";

Addsimps [bin_add_Pls, bin_add_Min, bin_add_BIT_Pls,
	  bin_add_BIT_Min, bin_add_BIT_BIT,
	  integ_of_succ, integ_of_pred];

Goal "v: bin ==> \
\         ALL w: bin. integ_of(bin_add(v,w)) = integ_of(v) $+ integ_of(w)";
by (etac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (rtac ballI 1);
by (induct_tac "wa" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps zadd_ac setloop (etac boolE))));
qed_spec_mp "integ_of_add";


(*** bin_mult: binary multiplication ***)

Goal "[| v: bin;  w: bin |]   \
\     ==> integ_of(bin_mult(v,w)) = integ_of(v) $* integ_of(w)";
by (induct_tac "v" 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [integ_of_minus]) 1);
by (etac boolE 1);
by (asm_simp_tac (simpset() addsimps [zadd_zmult_distrib]) 2);
by (asm_simp_tac (simpset() addsimps [integ_of_add,
				      zadd_zmult_distrib] @ zadd_ac) 1);
qed "integ_of_mult";

(**** Computations ****)

(** extra rules for bin_succ, bin_pred **)

Goal "bin_succ(w BIT 1) = bin_succ(w) BIT 0";
by (Simp_tac 1);
qed "bin_succ_BIT1";

Goal "bin_succ(w BIT 0) = NCons(w,1)";
by (Simp_tac 1);
qed "bin_succ_BIT0";

Goal "bin_pred(w BIT 1) = NCons(w,0)";
by (Simp_tac 1);
qed "bin_pred_BIT1";

Goal "bin_pred(w BIT 0) = bin_pred(w) BIT 1";
by (Simp_tac 1);
qed "bin_pred_BIT0";

(** extra rules for bin_minus **)

Goal "bin_minus(w BIT 1) = bin_pred(NCons(bin_minus(w), 0))";
by (Simp_tac 1);
qed "bin_minus_BIT1";

Goal "bin_minus(w BIT 0) = bin_minus(w) BIT 0";
by (Simp_tac 1);
qed "bin_minus_BIT0";

(** extra rules for bin_add **)

Goal "w: bin ==> bin_add(v BIT 1, w BIT 1) = \
\                    NCons(bin_add(v, bin_succ(w)), 0)";
by (Asm_simp_tac 1);
qed "bin_add_BIT_BIT11";

Goal "w: bin ==> bin_add(v BIT 1, w BIT 0) =  \
\                    NCons(bin_add(v,w), 1)";
by (Asm_simp_tac 1);
qed "bin_add_BIT_BIT10";

Goal "[| w: bin;  y: bool |] ==> \
\           bin_add(v BIT 0, w BIT y) = NCons(bin_add(v,w), y)";
by (Asm_simp_tac 1);
qed "bin_add_BIT_BIT0";

(** extra rules for bin_mult **)

Goal "bin_mult(v BIT 1, w) = bin_add(NCons(bin_mult(v,w),0), w)";
by (Simp_tac 1);
qed "bin_mult_BIT1";

Goal "bin_mult(v BIT 0, w) = NCons(bin_mult(v,w),0)";
by (Simp_tac 1);
qed "bin_mult_BIT0";


(** Simplification rules with integer constants **)

Goal "#0 $+ z = intify(z)";
by (Simp_tac 1);
qed "zadd_0_intify";

Goal "z $+ #0 = intify(z)";
by (Simp_tac 1);
qed "zadd_0_right_intify";

Addsimps [zadd_0_intify, zadd_0_right_intify];

Goal "#1 $* z = intify(z)";
by (Simp_tac 1);
qed "zmult_1_intify";

Goal "z $* #1 = intify(z)";
by (stac zmult_commute 1);
by (Simp_tac 1);
qed "zmult_1_right_intify";

Addsimps [zmult_1_intify, zmult_1_right_intify];

Goal "#0 $* z = #0";
by (Simp_tac 1);
qed "zmult_0";

Goal "z $* #0 = #0";
by (stac zmult_commute 1);
by (Simp_tac 1);
qed "zmult_0_right";

Addsimps [zmult_0, zmult_0_right];


(*Delete the original rewrites, with their clumsy conditional expressions*)
Delsimps [bin_succ_BIT, bin_pred_BIT, bin_minus_BIT, 
          NCons_Pls, NCons_Min, bin_adder_BIT, bin_mult_BIT];

(*Hide the binary representation of integer constants*)
Delsimps [integ_of_Pls, integ_of_Min, integ_of_BIT];


Addsimps [integ_of_add RS sym,   (*invoke bin_add*)
	  integ_of_minus RS sym, (*invoke bin_minus*)
	  integ_of_mult RS sym,  (*invoke bin_mult*)
	  bin_succ_Pls, bin_succ_Min,
	  bin_succ_BIT1, bin_succ_BIT0,
	  bin_pred_Pls, bin_pred_Min,
	  bin_pred_BIT1, bin_pred_BIT0,
	  bin_minus_Pls, bin_minus_Min,
	  bin_minus_BIT1, bin_minus_BIT0,
	  bin_add_Pls, bin_add_Min, bin_add_BIT_Pls, 
	  bin_add_BIT_Min, bin_add_BIT_BIT0, 
	  bin_add_BIT_BIT10, bin_add_BIT_BIT11,
	  bin_mult_Pls, bin_mult_Min,
	  bin_mult_BIT1, bin_mult_BIT0];
