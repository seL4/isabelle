(*  Title:      Integ.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Type "int" is a linear order
*)

Goal "(w<z) = znegative(w-z)";
by (simp_tac (simpset() addsimps [zless_def]) 1);
qed "zless_eq_znegative";

Goal "(w=z) = iszero(w-z)";
by (simp_tac (simpset() addsimps [iszero_def, zdiff_eq_eq]) 1);
qed "eq_eq_iszero";

Goal "(w<=z) = (~ znegative(z-w))";
by (simp_tac (simpset() addsimps [zle_def, zless_def]) 1);
qed "zle_eq_not_znegative";

(*This list of rewrites simplifies (in)equalities by subtracting the RHS
  from the LHS, then using the cancellation simproc.  Use with zadd_ac.*)
val zcompare_0_rls = 
    [zdiff_def, zless_eq_znegative, eq_eq_iszero, zle_eq_not_znegative];



(*** Monotonicity results ***)

Goal "(v+z < w+z) = (v < (w::int))";
by (full_simp_tac (simpset() addsimps (zcompare_0_rls @ zadd_ac)) 1);
qed "zadd_right_cancel_zless";

Goal "(z+v < z+w) = (v < (w::int))";
by (full_simp_tac (simpset() addsimps (zcompare_0_rls @ zadd_ac)) 1);
qed "zadd_left_cancel_zless";

Addsimps [zadd_right_cancel_zless, zadd_left_cancel_zless];

Goal "(v+z <= w+z) = (v <= (w::int))";
by (full_simp_tac (simpset() addsimps (zcompare_0_rls @ zadd_ac)) 1);
qed "zadd_right_cancel_zle";

Goal "(z+v <= z+w) = (v <= (w::int))";
by (full_simp_tac (simpset() addsimps (zcompare_0_rls @ zadd_ac)) 1);
qed "zadd_left_cancel_zle";

Addsimps [zadd_right_cancel_zle, zadd_left_cancel_zle];

(*"v<=w ==> v+z <= w+z"*)
bind_thm ("zadd_zless_mono1", zadd_right_cancel_zless RS iffD2);

(*"v<=w ==> v+z <= w+z"*)
bind_thm ("zadd_zle_mono1", zadd_right_cancel_zle RS iffD2);

Goal "!!z z'::int. [| w'<=w; z'<=z |] ==> w' + z' <= w + z";
by (etac (zadd_zle_mono1 RS zle_trans) 1);
by (Simp_tac 1);
qed "zadd_zle_mono";

Goal "!!z z'::int. [| w'<w; z'<=z |] ==> w' + z' < w + z";
by (etac (zadd_zless_mono1 RS zless_zle_trans) 1);
by (Simp_tac 1);
qed "zadd_zless_mono";


(*** Comparison laws ***)

Goal "(- x < - y) = (y < (x::int))";
by (simp_tac (simpset() addsimps (zcompare_0_rls @ zadd_ac)) 1);
qed "zminus_zless_zminus"; 
Addsimps [zminus_zless_zminus];

Goal "(- x <= - y) = (y <= (x::int))";
by (simp_tac (simpset() addsimps (zcompare_0_rls @ zadd_ac)) 1);
qed "zminus_zle_zminus"; 
Addsimps [zminus_zle_zminus];

(** The next several equations can make the simplifier loop! **)

Goal "(x < - y) = (y < - (x::int))";
by (simp_tac (simpset() addsimps (zcompare_0_rls @ zadd_ac)) 1);
qed "zless_zminus"; 

Goal "(- x < y) = (- y < (x::int))";
by (simp_tac (simpset() addsimps (zcompare_0_rls @ zadd_ac)) 1);
qed "zminus_zless"; 

Goal "(x <= - y) = (y <= - (x::int))";
by (simp_tac (simpset() addsimps (zcompare_0_rls @ zadd_ac)) 1);
qed "zle_zminus"; 

Goal "(- x <= y) = (- y <= (x::int))";
by (simp_tac (simpset() addsimps (zcompare_0_rls @ zadd_ac)) 1);
qed "zminus_zle"; 

Goal "$#0 < $# Suc n"; 
by (Simp_tac 1);
qed "zero_zless_Suc"; 

Goal "- $# Suc n < $# 0";
by (simp_tac (simpset() addsimps (zcompare_0_rls @ zadd_ac)) 1);
qed "negative_zless_0"; 

Goal "- $# Suc n < $# m";
by (rtac (negative_zless_0 RS zless_zle_trans) 1);
by (Simp_tac 1); 
qed "negative_zless"; 
AddIffs [negative_zless]; 

Goal "- $# n <= $#0";
by (simp_tac (simpset() addsimps (zcompare_0_rls @ zadd_ac)) 1);
qed "negative_zle_0"; 

Goal "- $# n <= $# m";
by (simp_tac (simpset() addsimps (add_znat::(zcompare_0_rls @ zadd_ac))) 1);
qed "negative_zle"; 
AddIffs [negative_zle]; 

Goal "~($# 0 <= - $# Suc n)";
by (stac zle_zminus 1);
by (Simp_tac 1);
qed "not_zle_0_negative"; 
Addsimps [not_zle_0_negative]; 

Goal "($# n <= - $# m) = (n = 0 & m = 0)"; 
by Safe_tac; 
by (Simp_tac 3); 
by (dtac (zle_zminus RS iffD1) 2); 
by (ALLGOALS (dtac (negative_zle_0 RSN(2,zle_trans)))); 
by (ALLGOALS Asm_full_simp_tac); 
qed "znat_zle_znegative"; 

Goal "~($# n < - $# m)";
by (simp_tac (simpset() addsimps [symmetric zle_def]) 1); 
qed "not_znat_zless_negative"; 

Goal "(- $# n = $# m) = (n = 0 & m = 0)"; 
by (rtac iffI 1);
by (rtac (znat_zle_znegative RS iffD1) 1); 
by (dtac sym 1); 
by (ALLGOALS Asm_simp_tac); 
qed "negative_eq_positive"; 

Addsimps [negative_eq_positive, not_znat_zless_negative]; 



Goalw [zdiff_def,zless_def] "znegative x = (x < $# 0)";
by Auto_tac; 
qed "znegative_eq_less_nat0"; 

Goalw [zle_def] "(~znegative x) = ($# 0 <= x)";
by (simp_tac (simpset() addsimps [znegative_eq_less_nat0]) 1); 
qed "not_znegative_eq_ge_nat0"; 

(**** zmagnitude: magnitide of an integer, as a natural number ****)

Goalw [zmagnitude_def] "zmagnitude($# n) = n";
by Auto_tac;
qed "zmagnitude_znat";

Goalw [zmagnitude_def] "zmagnitude(- $# n) = n";
by Auto_tac;
qed "zmagnitude_zminus_znat";

Addsimps [zmagnitude_znat, zmagnitude_zminus_znat];

Goal "~ znegative z ==> $# (zmagnitude z) = z"; 
by (dtac (not_znegative_eq_ge_nat0 RS iffD1) 1); 
by (dtac zle_imp_zless_or_eq 1); 
by (auto_tac (claset(), simpset() addsimps [zless_iff_Suc_zadd])); 
qed "not_zneg_mag"; 

Goal "znegative x ==> ? n. x = - $# Suc n"; 
by (auto_tac (claset(), 
	      simpset() addsimps [znegative_eq_less_nat0, zless_iff_Suc_zadd,
				  zdiff_eq_eq RS sym, zdiff_def])); 
qed "znegativeD"; 

Goal "znegative z ==> $# (zmagnitude z) = -z"; 
bd znegativeD 1;
by Auto_tac; 
qed "zneg_mag"; 

(* a case theorem distinguishing positive and negative int *)  

val prems = Goal "[|!! n. P ($# n); !! n. P (- $# Suc n) |] ==> P z"; 
by (case_tac "znegative z" 1); 
by (blast_tac (claset() addSDs [znegativeD] addSIs prems) 1); 
be (not_zneg_mag RS subst) 1;
brs prems 1;
qed "int_cases"; 

fun int_case_tac x = res_inst_tac [("z",x)] int_cases; 

