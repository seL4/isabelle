(*  Title:      HOL/Integ/int_arith2.ML
    ID:         $Id$
    Authors:    Larry Paulson and Tobias Nipkow
*)

(** Simplification of inequalities involving numerical constants **)

Goal "(w <= z - (#1::int)) = (w<(z::int))";
by (arith_tac 1);
qed "zle_diff1_eq";
Addsimps [zle_diff1_eq];

Goal "(w < z + #1) = (w<=(z::int))";
by (arith_tac 1);
qed "zle_add1_eq_le";
Addsimps [zle_add1_eq_le];

Goal "(z = z + w) = (w = (#0::int))";
by (arith_tac 1);
qed "zadd_left_cancel0";
Addsimps [zadd_left_cancel0];


(* nat *)

Goal "#0 <= z ==> int (nat z) = z"; 
by (asm_full_simp_tac
    (simpset() addsimps [neg_eq_less_0, zle_def, not_neg_nat]) 1); 
qed "nat_0_le"; 

Goal "z <= #0 ==> nat z = 0"; 
by (case_tac "z = #0" 1);
by (asm_simp_tac (simpset() addsimps [nat_le_int0]) 1); 
by (asm_full_simp_tac 
    (simpset() addsimps [neg_eq_less_0, neg_nat, linorder_neq_iff]) 1);
qed "nat_le_0"; 

Addsimps [nat_0_le, nat_le_0];

val [major,minor] = Goal "[| #0 <= z;  !!m. z = int m ==> P |] ==> P"; 
by (rtac (major RS nat_0_le RS sym RS minor) 1);
qed "nonneg_eq_int"; 

Goal "(nat w = m) = (if #0 <= w then w = int m else m=0)";
by Auto_tac;
qed "nat_eq_iff";

Goal "(m = nat w) = (if #0 <= w then w = int m else m=0)";
by Auto_tac;
qed "nat_eq_iff2";

Goal "#0 <= w ==> (nat w < m) = (w < int m)";
by (rtac iffI 1);
by (asm_full_simp_tac 
    (simpset() delsimps [zless_int] addsimps [zless_int RS sym]) 2);
by (etac (nat_0_le RS subst) 1);
by (Simp_tac 1);
qed "nat_less_iff";

Goal "(int m = z) = (m = nat z & #0 <= z)";
by (auto_tac (claset(), simpset() addsimps [nat_eq_iff2]));  
qed "int_eq_iff";

Addsimps [inst "z" "number_of ?v" int_eq_iff];


(*Users don't want to see (int 0), int(Suc 0) or w + - z*)
Addsimps [int_0, int_Suc, symmetric zdiff_def];

Goal "nat #0 = 0";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_0";

Goal "nat #1 = 1";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_1";

Goal "nat #2 = 2";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_2";

Goal "#0 <= w ==> (nat w < nat z) = (w<z)";
by (case_tac "neg z" 1);
by (auto_tac (claset(), simpset() addsimps [nat_less_iff]));
by (auto_tac (claset() addIs [zless_trans], 
	      simpset() addsimps [neg_eq_less_0, zle_def]));
qed "nat_less_eq_zless";

Goal "#0 < w | #0 <= z ==> (nat w <= nat z) = (w<=z)";
by (auto_tac (claset(), 
	      simpset() addsimps [linorder_not_less RS sym, 
				  zless_nat_conj]));
qed "nat_le_eq_zle";

(*Analogous to zadd_int, but more easily provable using the arithmetic in Bin*)
Goal "n<=m --> int m - int n = int (m-n)";
by (induct_thm_tac diff_induct "m n" 1);
by Auto_tac;
qed_spec_mp "zdiff_int";


(*** abs: absolute value, as an integer ****)

(* Simpler: use zabs_def as rewrite rule;
   but arith_tac is not parameterized by such simp rules
*)

Goalw [zabs_def]
 "P(abs(i::int)) = ((#0 <= i --> P i) & (i < #0 --> P(-i)))";
by(Simp_tac 1);
qed "zabs_split";

Goal "#0 <= abs (z::int)";
by (simp_tac (simpset() addsimps [zabs_def]) 1); 
qed "zero_le_zabs";
AddIffs [zero_le_zabs];

(*continued in IntArith.ML ...*)
