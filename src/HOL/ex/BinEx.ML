(*  Title:      HOL/ex/BinEx.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Examples of performing binary arithmetic by simplification

Also a proof that binary arithmetic on normalized operands 
yields normalized results. 
*)

set proof_timing;

(**** The Integers ****)

(*** Addition ***)

Goal "(#13::int)  +  #19 = #32";
by (Simp_tac 1);
result();

Goal "(#1234::int)  +  #5678 = #6912";
by (Simp_tac 1);
result();

Goal "(#1359::int)  +  #-2468 = #-1109";
by (Simp_tac 1);
result();

Goal "(#93746::int) +  #-46375 = #47371";
by (Simp_tac 1);
result();

(*** Negation ***)

Goal "- (#65745::int) = #-65745";
by (Simp_tac 1);
result();

Goal "- (#-54321::int) = #54321";
by (Simp_tac 1);
result();


(*** Multiplication ***)

Goal "(#13::int)  *  #19 = #247";
by (Simp_tac 1);
result();

Goal "(#-84::int)  *  #51 = #-4284";
by (Simp_tac 1);
result();

Goal "(#255::int)  *  #255 = #65025";
by (Simp_tac 1);
result();

Goal "(#1359::int)  *  #-2468 = #-3354012";
by (Simp_tac 1);
result();

Goal "(#89::int) * #10 ~= #889";  
by (Simp_tac 1); 
result();

Goal "(#13::int) < #18 - #4";  
by (Simp_tac 1); 
result();

Goal "(#-345::int) < #-242 + #-100";  
by (Simp_tac 1); 
result();

Goal "(#13557456::int) < #18678654";  
by (Simp_tac 1); 
result();

Goal "(#999999::int) <= (#1000001 + #1)-#2";  
by (Simp_tac 1); 
result();

Goal "(#1234567::int) <= #1234567";  
by (Simp_tac 1); 
result();


(*** Quotient and Remainder ***)

Goal "(#10::int) div #3 = #3";
by (Simp_tac 1);
result();

Goal "(#10::int) mod #3 = #1";
by (Simp_tac 1);
result();

(** A negative divisor **)

Goal "(#10::int) div #-3 = #-4";
by (Simp_tac 1);
result();

Goal "(#10::int) mod #-3 = #-2";
by (Simp_tac 1);
result();

(** A negative dividend
    [ The definition agrees with mathematical convention but not with
      the hardware of most computers ]
**)

Goal "(#-10::int) div #3 = #-4";
by (Simp_tac 1);
result();

Goal "(#-10::int) mod #3 = #2";
by (Simp_tac 1);
result();

(** A negative dividend AND divisor **)

Goal "(#-10::int) div #-3 = #3";
by (Simp_tac 1);
result();

Goal "(#-10::int) mod #-3 = #-1";
by (Simp_tac 1);
result();

(** A few bigger examples **)

Goal "(#8452::int) mod #3 = #1";
by (Simp_tac 1);
result();

Goal "(#59485::int) div #434 = #137";
by (Simp_tac 1);
result();

Goal "(#1000006::int) mod #10 = #6";
by (Simp_tac 1);
result();


(** division by shifting **)

Goal "#10000000 div #2 = (#5000000::int)";
by (Simp_tac 1);
result();

Goal "#10000001 mod #2 = (#1::int)";
by (Simp_tac 1);
result();

Goal "#10000055 div #32 = (#312501::int)";
by (Simp_tac 1);

Goal "#10000055 mod #32 = (#23::int)";
by (Simp_tac 1);

Goal "#100094 div #144 = (#695::int)";
by (Simp_tac 1);
result();

Goal "#100094 mod #144 = (#14::int)";
by (Simp_tac 1);
result();



(**** The Natural Numbers ****)

(** Successor **)

Goal "Suc #99999 = #100000";
by (asm_simp_tac (simpset() addsimps [Suc_nat_number_of]) 1);
	(*not a default rewrite since sometimes we want to have Suc(#nnn)*)
result();


(** Addition **)

Goal "(#13::nat)  +  #19 = #32";
by (Simp_tac 1);
result();

Goal "(#1234::nat)  +  #5678 = #6912";
by (Simp_tac 1);
result();

Goal "(#973646::nat) +  #6475 = #980121";
by (Simp_tac 1);
result();


(** Subtraction **)

Goal "(#32::nat)  -  #14 = #18";
by (Simp_tac 1);
result();

Goal "(#14::nat)  -  #15 = #0";
by (Simp_tac 1);
result();

Goal "(#14::nat)  -  #1576644 = #0";
by (Simp_tac 1);
result();

Goal "(#48273776::nat)  -  #3873737 = #44400039";
by (Simp_tac 1);
result();


(** Multiplication **)

Goal "(#12::nat) * #11 = #132";
by (Simp_tac 1);
result();

Goal "(#647::nat) * #3643 = #2357021";
by (Simp_tac 1);
result();


(** Quotient and Remainder **)

Goal "(#10::nat) div #3 = #3";
by (Simp_tac 1);
result();

Goal "(#10::nat) mod #3 = #1";
by (Simp_tac 1);
result();

Goal "(#10000::nat) div #9 = #1111";
by (Simp_tac 1);
result();

Goal "(#10000::nat) mod #9 = #1";
by (Simp_tac 1);
result();

Goal "(#10000::nat) div #16 = #625";
by (Simp_tac 1);
result();

Goal "(#10000::nat) mod #16 = #0";
by (Simp_tac 1);
result();


(*** Testing the cancellation of complementary terms ***)

Goal "y + (x + -x) = (#0::int) + y";
by (Simp_tac 1);
result();

Goal "y + (-x + (- y + x)) = (#0::int)";
by (Simp_tac 1);
result();

Goal "-x + (y + (- y + x)) = (#0::int)";
by (Simp_tac 1);
result();

Goal "x + (x + (- x + (- x + (- y + - z)))) = (#0::int) - y - z";
by (Simp_tac 1);
result();

Goal "x + x - x - x - y - z = (#0::int) - y - z";
by (Simp_tac 1);
result();

Goal "x + y + z - (x + z) = y - (#0::int)";
by (Simp_tac 1);
result();

Goal "x+(y+(y+(y+ (-x + -x)))) = (#0::int) + y - x + y + y";
by (Simp_tac 1);
result();

Goal "x+(y+(y+(y+ (-y + -x)))) = y + (#0::int) + y";
by (Simp_tac 1);
result();

Goal "x + y - x + z - x - y - z + x < (#1::int)";
by (Simp_tac 1);
result();


Addsimps normal.intrs;

Goal "(w BIT b): normal ==> (w BIT b BIT c): normal";
by (case_tac "c" 1);
by Auto_tac;
qed "normal_BIT_I";

Addsimps [normal_BIT_I];

Goal "w BIT b: normal ==> w: normal";
by (etac normal.elim 1);
by Auto_tac;
qed "normal_BIT_D";

Goal "w : normal --> NCons w b : normal";
by (induct_tac "w" 1);
by (auto_tac (claset(), simpset() addsimps [NCons_Pls, NCons_Min]));
qed_spec_mp "NCons_normal";

Addsimps [NCons_normal];

Goal "NCons w True ~= Pls";
by (induct_tac "w" 1);
by Auto_tac;
qed "NCons_True";

Goal "NCons w False ~= Min";
by (induct_tac "w" 1);
by Auto_tac;
qed "NCons_False";

Goal "w: normal ==> bin_succ w : normal";
by (etac normal.induct 1);
by (cases_tac "w" 4);
by (auto_tac (claset(), simpset() addsimps [NCons_True, bin_succ_BIT]));
qed "bin_succ_normal";

Goal "w: normal ==> bin_pred w : normal";
by (etac normal.induct 1);
by (cases_tac "w" 3);
by (auto_tac (claset(), simpset() addsimps [NCons_False, bin_pred_BIT]));
qed "bin_pred_normal";

Addsimps [bin_succ_normal, bin_pred_normal];

Goal "w : normal --> (ALL z. z: normal --> bin_add w z : normal)";
by (induct_tac "w" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (rtac impI 1);
by (rtac allI 1);
by (induct_tac "z" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [bin_add_BIT])));
by (safe_tac (claset() addSDs [normal_BIT_D]));
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "bin_add_normal";

Goal "w: normal ==> (w = Pls) = (number_of w = (#0::int))";
by (etac normal.induct 1);
by Auto_tac;
qed "normal_Pls_eq_0";

Goal "w : normal ==> bin_minus w : normal";
by (etac normal.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [bin_minus_BIT])));
by (resolve_tac normal.intrs 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [normal_Pls_eq_0]) 1);
by (asm_full_simp_tac 
    (simpset_of Int.thy 
     addsimps [number_of_minus, iszero_def, 
	       read_instantiate [("y","int 0")] zminus_equation]) 1);
by (etac not_sym 1);
qed "bin_minus_normal";

Goal "w : normal ==> z: normal --> bin_mult w z : normal";
by (etac normal.induct 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [bin_minus_normal, bin_mult_BIT])));
by (safe_tac (claset() addSDs [normal_BIT_D]));
by (asm_simp_tac (simpset() addsimps [bin_add_normal]) 1);
qed_spec_mp "bin_mult_normal";

