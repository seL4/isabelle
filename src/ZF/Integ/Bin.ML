(*  Title:      ZF/ex/Bin.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Arithmetic on binary integers.
*)


Addsimps bin.intrs;
Addsimps int_typechecks;

Goal "NCons(Pls,0) = Pls";
by (Asm_simp_tac 1);
qed "NCons_Pls_0";

Goal "NCons(Pls,1) = Cons(Pls,1)";
by (Asm_simp_tac 1);
qed "NCons_Pls_1";

Goal "NCons(Min,0) = Cons(Min,0)";
by (Asm_simp_tac 1);
qed "NCons_Min_0";

Goal "NCons(Min,1) = Min";
by (Asm_simp_tac 1);
qed "NCons_Min_1";

Goal "NCons(Cons(w,x),b) = Cons(Cons(w,x),b)";
by (asm_simp_tac (simpset() addsimps bin.case_eqns) 1);
qed "NCons_Cons";

val NCons_simps = [NCons_Pls_0, NCons_Pls_1, 
		   NCons_Min_0, NCons_Min_1,
		   NCons_Cons];
Addsimps NCons_simps;


(** Type checking **)

Addsimps [bool_into_nat];

Goal "w: bin ==> integ_of(w) : int";
by (induct_tac "w" 1);
by (ALLGOALS (Asm_simp_tac));
qed "integ_of_type";
Addsimps [integ_of_type];

Goal "[| w: bin; b: bool |] ==> NCons(w,b) : bin";
by (induct_tac "w" 1);
by Auto_tac;
qed "NCons_type";
Addsimps [NCons_type];

Goal "w: bin ==> bin_succ(w) : bin";
by (induct_tac "w" 1);
by Auto_tac;
qed "bin_succ_type";
Addsimps [bin_succ_type];

Goal "w: bin ==> bin_pred(w) : bin";
by (induct_tac "w" 1);
by Auto_tac;
qed "bin_pred_type";
Addsimps [bin_pred_type];

Goal "w: bin ==> bin_minus(w) : bin";
by (induct_tac "w" 1);
by Auto_tac;
qed "bin_minus_type";
Addsimps [bin_minus_type];

(*This proof is complicated by the mutual recursion*)
Goal "v: bin ==> ALL w: bin. bin_add(v,w) : bin";
by (induct_tac "v" 1);
by (rtac ballI 3);
by (rename_tac "w'" 3);
by (induct_tac "w'" 3);
by Auto_tac;
qed_spec_mp "bin_add_type";
Addsimps [bin_add_type];

Goal "[| v: bin; w: bin |] ==> bin_mult(v,w) : bin";
by (induct_tac "v" 1);
by Auto_tac;
qed "bin_mult_type";
Addsimps [bin_mult_type];


(**** The carry/borrow functions, bin_succ and bin_pred ****)

(*NCons preserves the integer value of its argument*)
Goal "[| w: bin; b: bool |] ==>     \
\         integ_of(NCons(w,b)) = integ_of(Cons(w,b))";
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

Goal "w: bin ==> integ_of(bin_pred(w)) = $~ ($#1) $+ integ_of(w)";
by (etac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (etac boolE 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps zadd_ac)));
qed "integ_of_pred";

Addsimps [integ_of_succ, integ_of_pred];


(*** bin_minus: (unary!) negation of binary integers ***)

Goal "w: bin ==> integ_of(bin_minus(w)) = $~ integ_of(w)";
by (etac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (etac boolE 1);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps zadd_ac@[zminus_zadd_distrib])));
qed "integ_of_minus";

Addsimps [integ_of_minus];


(*** bin_add: binary addition ***)

Goal "w: bin ==> bin_add(Pls,w) = w";
by (Asm_simp_tac 1);
qed "bin_add_Pls";

Goal "w: bin ==> bin_add(Min,w) = bin_pred(w)";
by (Asm_simp_tac 1);
qed "bin_add_Min";

Goal "bin_add(Cons(v,x),Pls) = Cons(v,x)";
by (Simp_tac 1);
qed "bin_add_Cons_Pls";

Goal "bin_add(Cons(v,x),Min) = bin_pred(Cons(v,x))";
by (Simp_tac 1);
qed "bin_add_Cons_Min";

Goal "[| w: bin;  y: bool |]              \
\     ==> bin_add(Cons(v,x), Cons(w,y)) = \
\         NCons(bin_add(v, cond(x and y, bin_succ(w), w)), x xor y)";
by (Asm_simp_tac 1);
qed "bin_add_Cons_Cons";

Addsimps [bin_add_Pls, bin_add_Min, bin_add_Cons_Pls,
	  bin_add_Cons_Min, bin_add_Cons_Cons,
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
Addsimps [integ_of_add];


(*** bin_add: binary multiplication ***)

Goal "[| v: bin;  w: bin |]   \
\     ==> integ_of(bin_mult(v,w)) = integ_of(v) $* integ_of(w)";
by (induct_tac "v" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (etac boolE 1);
by (asm_simp_tac (simpset() addsimps [zadd_zmult_distrib]) 2);
by (asm_simp_tac (simpset() addsimps [zadd_zmult_distrib] @ zadd_ac) 1);
qed "integ_of_mult";

(**** Computations ****)

(** extra rules for bin_succ, bin_pred **)

Goal "bin_succ(Cons(w,1)) = Cons(bin_succ(w), 0)";
by (Simp_tac 1);
qed "bin_succ_Cons1";

Goal "bin_succ(Cons(w,0)) = NCons(w,1)";
by (Simp_tac 1);
qed "bin_succ_Cons0";

Goal "bin_pred(Cons(w,1)) = NCons(w,0)";
by (Simp_tac 1);
qed "bin_pred_Cons1";

Goal "bin_pred(Cons(w,0)) = Cons(bin_pred(w), 1)";
by (Simp_tac 1);
qed "bin_pred_Cons0";

(** extra rules for bin_minus **)

Goal "bin_minus(Cons(w,1)) = bin_pred(NCons(bin_minus(w), 0))";
by (Simp_tac 1);
qed "bin_minus_Cons1";

Goal "bin_minus(Cons(w,0)) = Cons(bin_minus(w), 0)";
by (Simp_tac 1);
qed "bin_minus_Cons0";

(** extra rules for bin_add **)

Goal "w: bin ==> bin_add(Cons(v,1), Cons(w,1)) = \
\                    NCons(bin_add(v, bin_succ(w)), 0)";
by (Asm_simp_tac 1);
qed "bin_add_Cons_Cons11";

Goal "w: bin ==> bin_add(Cons(v,1), Cons(w,0)) =  \
\                    NCons(bin_add(v,w), 1)";
by (Asm_simp_tac 1);
qed "bin_add_Cons_Cons10";

Goal "[| w: bin;  y: bool |] ==> \
\           bin_add(Cons(v,0), Cons(w,y)) = NCons(bin_add(v,w), y)";
by (Asm_simp_tac 1);
qed "bin_add_Cons_Cons0";

(** extra rules for bin_mult **)

Goal "bin_mult(Cons(v,1), w) = bin_add(NCons(bin_mult(v,w),0), w)";
by (Simp_tac 1);
qed "bin_mult_Cons1";

Goal "bin_mult(Cons(v,0), w) = NCons(bin_mult(v,w),0)";
by (Simp_tac 1);
qed "bin_mult_Cons0";


(*** The computation simpset ***)

(*Adding the typechecking rules as rewrites is much slower, unfortunately...*)
val bin_comp_ss = simpset_of Int.thy 
    addsimps [integ_of_add RS sym,   (*invoke bin_add*)
              integ_of_minus RS sym, (*invoke bin_minus*)
              integ_of_mult RS sym,  (*invoke bin_mult*)
              bin_succ_Pls, bin_succ_Min,
              bin_succ_Cons1, bin_succ_Cons0,
              bin_pred_Pls, bin_pred_Min,
              bin_pred_Cons1, bin_pred_Cons0,
              bin_minus_Pls, bin_minus_Min,
              bin_minus_Cons1, bin_minus_Cons0,
              bin_add_Pls, bin_add_Min, bin_add_Cons_Pls, 
              bin_add_Cons_Min, bin_add_Cons_Cons0, 
              bin_add_Cons_Cons10, bin_add_Cons_Cons11,
              bin_mult_Pls, bin_mult_Min,
              bin_mult_Cons1, bin_mult_Cons0]
             @ NCons_simps
    setSolver (type_auto_tac ([bool_1I, bool_0I] @ bin.intrs));
