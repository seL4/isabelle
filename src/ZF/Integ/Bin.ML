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

bind_thms ("NCons_simps",
 [NCons_Pls_0, NCons_Pls_1,
  NCons_Min_0, NCons_Min_1,
  NCons_BIT]);
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
Goal "[| w: bin; b: bool |] ==> integ_of(NCons(w,b)) = integ_of(w BIT b)";
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

Goalw [bin_add_def] "w: bin ==> bin_add(w,Pls) = w";
by (etac bin.induct 1);
by Auto_tac;
qed "bin_add_Pls_right";

Goalw [bin_add_def] "w: bin ==> bin_add(Min,w) = bin_pred(w)";
by (Asm_simp_tac 1);
qed "bin_add_Min";

Goalw [bin_add_def] "w: bin ==> bin_add(w,Min) = bin_pred(w)";
by (etac bin.induct 1);
by Auto_tac;
qed "bin_add_Min_right";

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

(*Subtraction*)
Goalw [zdiff_def]
     "[| v: bin;  w: bin |]   \
\     ==> integ_of(v) $- integ_of(w) = integ_of(bin_add (v, bin_minus(w)))";
by (asm_simp_tac (simpset() addsimps [integ_of_add, integ_of_minus]) 1);
qed "diff_integ_of_eq";


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
qed "bin_succ_1";

Goal "bin_succ(w BIT 0) = NCons(w,1)";
by (Simp_tac 1);
qed "bin_succ_0";

Goal "bin_pred(w BIT 1) = NCons(w,0)";
by (Simp_tac 1);
qed "bin_pred_1";

Goal "bin_pred(w BIT 0) = bin_pred(w) BIT 1";
by (Simp_tac 1);
qed "bin_pred_0";

(** extra rules for bin_minus **)

Goal "bin_minus(w BIT 1) = bin_pred(NCons(bin_minus(w), 0))";
by (Simp_tac 1);
qed "bin_minus_1";

Goal "bin_minus(w BIT 0) = bin_minus(w) BIT 0";
by (Simp_tac 1);
qed "bin_minus_0";

(** extra rules for bin_add **)

Goal "w: bin ==> bin_add(v BIT 1, w BIT 1) = \
\                    NCons(bin_add(v, bin_succ(w)), 0)";
by (Asm_simp_tac 1);
qed "bin_add_BIT_11";

Goal "w: bin ==> bin_add(v BIT 1, w BIT 0) =  \
\                    NCons(bin_add(v,w), 1)";
by (Asm_simp_tac 1);
qed "bin_add_BIT_10";

Goal "[| w: bin;  y: bool |] \
\     ==> bin_add(v BIT 0, w BIT y) = NCons(bin_add(v,w), y)";
by (Asm_simp_tac 1);
qed "bin_add_BIT_0";

(** extra rules for bin_mult **)

Goal "bin_mult(v BIT 1, w) = bin_add(NCons(bin_mult(v,w),0), w)";
by (Simp_tac 1);
qed "bin_mult_1";

Goal "bin_mult(v BIT 0, w) = NCons(bin_mult(v,w),0)";
by (Simp_tac 1);
qed "bin_mult_0";


(** Simplification rules with integer constants **)

Goal "$#0 = #0";
by (Simp_tac 1);
qed "int_of_0";

Goal "$# succ(n) = #1 $+ $#n";
by (simp_tac (simpset() addsimps [int_of_add RS sym, natify_succ]) 1);
qed "int_of_succ";

Goal "$- #0 = #0";
by (Simp_tac 1);
qed "zminus_0";

Addsimps [zminus_0];

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

Goal "#-1 $* z = $-z";
by (simp_tac (simpset() addsimps zcompare_rls) 1);
qed "zmult_minus1";

Goal "z $* #-1 = $-z";
by (stac zmult_commute 1);
by (rtac zmult_minus1 1);
qed "zmult_minus1_right";

Addsimps [zmult_minus1, zmult_minus1_right];


(*** Simplification rules for comparison of binary numbers (N Voelker) ***)

(** Equals (=) **)

Goalw [iszero_def]
     "[| v: bin;  w: bin |]   \
\     ==> ((integ_of(v)) = integ_of(w)) <-> \
\         iszero (integ_of (bin_add (v, bin_minus(w))))"; 
by (asm_simp_tac (simpset() addsimps
              (zcompare_rls @ [integ_of_add, integ_of_minus])) 1); 
qed "eq_integ_of_eq"; 

Goalw [iszero_def] "iszero (integ_of(Pls))"; 
by (Simp_tac 1); 
qed "iszero_integ_of_Pls";


Goalw [iszero_def] "~ iszero (integ_of(Min))"; 
by (simp_tac (simpset() addsimps [zminus_equation]) 1);
qed "nonzero_integ_of_Min"; 

Goalw [iszero_def]
     "[| w: bin; x: bool |] \
\     ==> iszero (integ_of (w BIT x)) <-> (x=0 & iszero (integ_of(w)))"; 
by (Simp_tac 1);
by (subgoal_tac "integ_of(w) : int" 1);
by (Asm_simp_tac 2);
by (dtac int_cases 1);
by (auto_tac (claset() addSEs [boolE], 
              simpset() addsimps [int_of_add RS sym]));  
by (ALLGOALS (asm_full_simp_tac 
	      (simpset() addsimps zcompare_rls @ 
			  [zminus_zadd_distrib RS sym, int_of_add RS sym])));
by (subgoal_tac "znegative ($- $# succ(x)) <-> znegative ($# succ(x))" 1);
by (Asm_simp_tac 2);
by (Full_simp_tac 1);
qed "iszero_integ_of_BIT"; 

Goal "w: bin ==> iszero (integ_of (w BIT 0)) <-> iszero (integ_of(w))"; 
by (asm_simp_tac (ZF_ss addsimps [iszero_integ_of_BIT]) 1); 
qed "iszero_integ_of_0"; 

Goal "w: bin ==> ~ iszero (integ_of (w BIT 1))"; 
by (asm_simp_tac (ZF_ss addsimps [iszero_integ_of_BIT]) 1); 
qed "iszero_integ_of_1"; 



(** Less-than (<) **)

Goalw [zless_def,zdiff_def] 
     "[| v: bin;  w: bin |]   \
\     ==> integ_of(v) $< integ_of(w) \
\         <-> znegative (integ_of (bin_add (v, bin_minus(w))))";
by (asm_simp_tac (simpset() addsimps [integ_of_minus, integ_of_add]) 1);
qed "less_integ_of_eq_neg"; 

Goal "~ znegative (integ_of(Pls))"; 
by (Simp_tac 1); 
qed "not_neg_integ_of_Pls"; 

Goal "znegative (integ_of(Min))"; 
by (Simp_tac 1);
qed "neg_integ_of_Min"; 

Goal "[| w: bin; x: bool |] \
\     ==> znegative (integ_of (w BIT x)) <-> znegative (integ_of(w))"; 
by (Asm_simp_tac 1); 
by (subgoal_tac "integ_of(w) : int" 1);
by (Asm_simp_tac 2);
by (dtac int_cases 1);
by (auto_tac (claset() addSEs [boolE], 
              simpset() addsimps [int_of_add RS sym] @ zcompare_rls));  
by (ALLGOALS (asm_full_simp_tac 
	      (simpset() addsimps [zminus_zadd_distrib RS sym, zdiff_def,
				   int_of_add RS sym])));
by (subgoal_tac "$#1 $- $# succ(succ(x #+ x)) = $- $# succ(x #+ x)" 1);
by (asm_full_simp_tac (simpset() addsimps [zdiff_def])1);
by (asm_simp_tac (simpset() addsimps [equation_zminus, int_of_diff RS sym])1);
qed "neg_integ_of_BIT"; 

Goal "w: bin ==> iszero (integ_of (w BIT 0)) <-> iszero (integ_of(w))"; 
by (asm_simp_tac (ZF_ss addsimps [iszero_integ_of_BIT]) 1); 
qed "iszero_integ_of_0"; 

(** Less-than-or-equals (<=) **)

Goal "(integ_of(x) $<= (integ_of(w))) <-> ~ (integ_of(w) $< (integ_of(x)))";
by (simp_tac (simpset() addsimps [not_zless_iff_zle RS iff_sym]) 1);
qed "le_integ_of_eq_not_less"; 


(*Delete the original rewrites, with their clumsy conditional expressions*)
Delsimps [bin_succ_BIT, bin_pred_BIT, bin_minus_BIT, 
          NCons_Pls, NCons_Min, bin_adder_BIT, bin_mult_BIT];

(*Hide the binary representation of integer constants*)
Delsimps [integ_of_Pls, integ_of_Min, integ_of_BIT];


bind_thms ("NCons_simps", 
	   [NCons_Pls_0, NCons_Pls_1, NCons_Min_0, NCons_Min_1, NCons_BIT]);


bind_thms ("bin_arith_extra_simps",
    [integ_of_add RS sym,   (*invoke bin_add*)
     integ_of_minus RS sym, (*invoke bin_minus*)
     integ_of_mult RS sym,  (*invoke bin_mult*)
     bin_succ_1, bin_succ_0, 
     bin_pred_1, bin_pred_0, 
     bin_minus_1, bin_minus_0,  
     bin_add_Pls_right, bin_add_Min_right,
     bin_add_BIT_0, bin_add_BIT_10, bin_add_BIT_11,
     diff_integ_of_eq,
     bin_mult_1, bin_mult_0] @ NCons_simps);


(*For making a minimal simpset, one must include these default simprules
  of thy.  Also include simp_thms, or at least (~False)=True*)
bind_thms ("bin_arith_simps",
    [bin_pred_Pls, bin_pred_Min,
     bin_succ_Pls, bin_succ_Min,
     bin_add_Pls, bin_add_Min,
     bin_minus_Pls, bin_minus_Min,
     bin_mult_Pls, bin_mult_Min] @ bin_arith_extra_simps);

(*Simplification of relational operations*)
bind_thms ("bin_rel_simps",
    [eq_integ_of_eq, iszero_integ_of_Pls, nonzero_integ_of_Min,
     iszero_integ_of_0, iszero_integ_of_1,
     less_integ_of_eq_neg,
     not_neg_integ_of_Pls, neg_integ_of_Min, neg_integ_of_BIT,
     le_integ_of_eq_not_less]);

Addsimps bin_arith_simps;
Addsimps bin_rel_simps;


(** Simplification of arithmetic when nested to the right **)

Goal "[| v: bin;  w: bin |]   \
\     ==> integ_of(v) $+ (integ_of(w) $+ z) = (integ_of(bin_add(v,w)) $+ z)";
by (asm_simp_tac (simpset() addsimps [zadd_assoc RS sym]) 1);
qed "add_integ_of_left";

Goal "[| v: bin;  w: bin |]   \
\     ==> integ_of(v) $* (integ_of(w) $* z) = (integ_of(bin_mult(v,w)) $* z)";
by (asm_simp_tac (simpset() addsimps [zmult_assoc RS sym]) 1);
qed "mult_integ_of_left";

Goalw [zdiff_def]
    "[| v: bin;  w: bin |]   \
\     ==> integ_of(v) $+ (integ_of(w) $- c) = integ_of(bin_add(v,w)) $- (c)";
by (rtac add_integ_of_left 1);
by Auto_tac;  
qed "add_integ_of_diff1";

Goal "[| v: bin;  w: bin |]   \
\     ==> integ_of(v) $+ (c $- integ_of(w)) = \
\         integ_of (bin_add (v, bin_minus(w))) $+ (c)";
by (stac (diff_integ_of_eq RS sym) 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps zdiff_def::zadd_ac)));
qed "add_integ_of_diff2";

Addsimps [add_integ_of_left, mult_integ_of_left,
	  add_integ_of_diff1, add_integ_of_diff2]; 


(** More for integer constants **)

Addsimps [int_of_0, int_of_succ];

Goal "#0 $- x = $-x";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff0";

Goal "x $- #0 = intify(x)";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff0_right";

Goal "x $- x = #0";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff_self";

Addsimps [zdiff0, zdiff0_right, zdiff_self];

Goal "k: int ==> znegative(k) <-> k $< #0";
by (asm_simp_tac (simpset() addsimps [zless_def]) 1);
qed "znegative_iff_zless_0";

Goal "[| #0 $< k; k: int |] ==> znegative($-k)";
by (asm_full_simp_tac (simpset() addsimps [zless_def]) 1);
qed "zero_zless_imp_znegative_zminus";

Goal "#0 $<= $# n";
by (simp_tac (simpset() addsimps [not_zless_iff_zle RS iff_sym, 
                                  znegative_iff_zless_0 RS iff_sym]) 1); 
qed "zero_zle_int_of";
AddIffs [zero_zle_int_of];

Goal "nat_of(#0) = 0";
by (simp_tac (ZF_ss addsimps [natify_0, int_of_0 RS sym, nat_of_int_of]) 1);
qed "nat_of_0";
Addsimps [nat_of_0];

Goal "[| z $<= $#0; z: int |] ==> nat_of(z) = 0"; 
by (auto_tac (claset(), 
	      simpset() addsimps [znegative_iff_zless_0 RS iff_sym, 
				  zle_def, zneg_nat_of])); 
val lemma = result();

Goal "z $<= $#0 ==> nat_of(z) = 0"; 
by (subgoal_tac "nat_of(intify(z)) = 0" 1);
by (rtac lemma 2);
by Auto_tac;  
qed "nat_le_int0";

Goal "$# n = #0 ==> natify(n) = 0";
by (rtac not_znegative_imp_zero 1);
by Auto_tac;  
qed "int_of_eq_0_imp_natify_eq_0";

Goalw [nat_of_def, raw_nat_of_def] "nat_of($- $# n) = 0";
by (auto_tac((claset() addSDs [not_znegative_imp_zero, natify_int_of_eq], 
              simpset())     delIffs [int_of_eq]));
by (rtac the_equality 1);
by Auto_tac;  
by (blast_tac (claset() addIs [int_of_eq_0_imp_natify_eq_0, sym]) 1); 
qed "nat_of_zminus_int_of";

Goal "#0 $<= z ==> $# nat_of(z) = intify(z)";
by (rtac not_zneg_nat_of_intify 1);
by (asm_simp_tac (simpset() addsimps [znegative_iff_zless_0, 
                                      not_zless_iff_zle]) 1); 
qed "int_of_nat_of";

Addsimps [int_of_nat_of, nat_of_zminus_int_of];

Goal "$# nat_of(z) = (if #0 $<= z then intify(z) else #0)";
by (simp_tac (simpset() addsimps [int_of_nat_of,
                              znegative_iff_zless_0, not_zle_iff_zless]) 1);
qed "int_of_nat_of_if";

Goal "[| m: nat; z: int |] ==> (m < nat_of(z)) <-> ($#m $< z)";
by (case_tac "znegative(z)" 1);
by (etac (not_zneg_nat_of RS subst) 2);
by (auto_tac (claset() addDs [zless_trans]
		       addSDs [zero_zle_int_of RS zle_zless_trans], 
	      simpset() addsimps [znegative_iff_zless_0])); 
qed "zless_nat_iff_int_zless";


(** nat_of and zless **)

(*An alternative condition is  $#0 <= w  *)
Goal "$#0 $< z ==> (nat_of(w) < nat_of(z)) <-> (w $< z)";
by (rtac iff_trans 1);
by (rtac (zless_int_of RS iff_sym) 1);
by (auto_tac (claset(), 
       simpset() addsimps [int_of_nat_of_if] delsimps [zless_int_of]));  
by (auto_tac (claset() addEs [zless_asym],
              simpset() addsimps [not_zle_iff_zless]));  
by (blast_tac (claset() addIs [zless_zle_trans]) 1); 
val lemma = result();

Goal "(nat_of(w) < nat_of(z)) <-> ($#0 $< z & w $< z)";
by (case_tac "$#0 $< z" 1);
by (auto_tac (claset(), 
	      simpset() addsimps [lemma, nat_le_int0, not_zless_iff_zle])); 
qed "zless_nat_conj";

