(*  Title       : HRealAbs.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Absolute value function for the hyperreals
                  Similar to RealAbs.thy
*) 

(*------------------------------------------------------------
  absolute value on hyperreals as pointwise operation on 
  equivalence class representative
 ------------------------------------------------------------*)

Goalw [hrabs_def]
     "abs (number_of v :: hypreal) = \
\       (if neg (number_of v) then number_of (bin_minus v) \
\        else number_of v)";
by (Simp_tac 1); 
qed "hrabs_number_of";
Addsimps [hrabs_number_of];

(*------------------------------------------------------------
   Properties of the absolute value function over the reals
   (adapted version of previously proved theorems about abs)
 ------------------------------------------------------------*)

Goal "(0::hypreal)<=x ==> abs x = x";
by (asm_simp_tac (simpset() addsimps [hrabs_def]) 1); 
qed "hrabs_eqI1";

Goal "(0::hypreal)<x ==> abs x = x";
by (asm_simp_tac (simpset() addsimps [order_less_imp_le, hrabs_eqI1]) 1);
qed "hrabs_eqI2";

Goal "x<(0::hypreal) ==> abs x = -x";
by (asm_simp_tac (simpset() addsimps [hypreal_le_def, hrabs_def]) 1); 
qed "hrabs_minus_eqI2";

Goal "x<=(0::hypreal) ==> abs x = -x";
by (auto_tac (claset() addDs [order_antisym], simpset() addsimps [hrabs_def]));qed "hrabs_minus_eqI1";

Addsimps [abs_mult];

Goalw [hrabs_def] "[| abs x < r; abs y < s |] ==> abs(x+y) < r + (s::hypreal)";
by (asm_full_simp_tac (simpset() addsplits [split_if_asm]) 1); 
qed "hrabs_add_less";

Goal "abs x < r ==> (0::hypreal) < r";
by (blast_tac (claset() addSIs [order_le_less_trans, abs_ge_zero]) 1);
qed "hrabs_less_gt_zero";

Goal "abs x = (x::hypreal) | abs x = -x";
by (simp_tac (simpset() addsimps [hrabs_def]) 1); 
qed "hrabs_disj";

Goal "abs x = (y::hypreal) ==> x = y | -x = y";
by (asm_full_simp_tac (simpset() addsimps [hrabs_def] 
                                 addsplits [split_if_asm]) 1); 
qed "hrabs_eq_disj";

(* Needed in Geom.ML *)
Goal "(y::hypreal) + - x + (y + - z) = abs (x + - z) ==> y = z | x = y";
by (asm_full_simp_tac (simpset() addsimps [hrabs_def] 
                                 addsplits [split_if_asm]) 1); 
qed "hrabs_add_lemma_disj";

(* Needed in Geom.ML?? *)
Goal "(x::hypreal) + - y + (z + - y) = abs (x + - z) ==> y = z | x = y";
by (asm_full_simp_tac (simpset() addsimps [hrabs_def] 
                                 addsplits [split_if_asm]) 1); 
qed "hrabs_add_lemma_disj2";

 
(*----------------------------------------------------------
    Relating hrabs to abs through embedding of IR into IR*
 ----------------------------------------------------------*)
Goalw [hypreal_of_real_def] 
    "abs (hypreal_of_real r) = hypreal_of_real (abs r)";
by (auto_tac (claset(), simpset() addsimps [hypreal_hrabs]));
qed "hypreal_of_real_hrabs";


(*----------------------------------------------------------------------------
             Embedding of the naturals in the hyperreals
 ----------------------------------------------------------------------------*)

Goal "hypreal_of_nat (m + n) = hypreal_of_nat m + hypreal_of_nat n";
by (simp_tac (simpset() addsimps [hypreal_of_nat_def]) 1);
qed "hypreal_of_nat_add";
Addsimps [hypreal_of_nat_add];

Goal "hypreal_of_nat (m * n) = hypreal_of_nat m * hypreal_of_nat n";
by (simp_tac (simpset() addsimps [hypreal_of_nat_def]) 1);
qed "hypreal_of_nat_mult";
Addsimps [hypreal_of_nat_mult];

Goalw [hypreal_of_nat_def] 
      "(n < m) = (hypreal_of_nat n < hypreal_of_nat m)";
by (auto_tac (claset() addIs [hypreal_add_less_mono1], simpset()));
qed "hypreal_of_nat_less_iff";
Addsimps [hypreal_of_nat_less_iff RS sym];

(*------------------------------------------------------------*)
(* naturals embedded in hyperreals                            *)
(* is a hyperreal c.f. NS extension                           *)
(*------------------------------------------------------------*)

Goalw [hypreal_of_nat_def, hypreal_of_real_def, real_of_nat_def] 
     "hypreal_of_nat  m = Abs_hypreal(hyprel``{%n. real m})";
by Auto_tac;
qed "hypreal_of_nat_iff";

Goal "inj hypreal_of_nat";
by (simp_tac (simpset() addsimps [inj_on_def, hypreal_of_nat_def]) 1);
qed "inj_hypreal_of_nat";

Goalw [hypreal_of_nat_def] 
     "hypreal_of_nat (Suc n) = hypreal_of_nat n + (1::hypreal)";
by (simp_tac (simpset() addsimps [real_of_nat_Suc]) 1);
qed "hypreal_of_nat_Suc";

(*"neg" is used in rewrite rules for binary comparisons*)
Goal "hypreal_of_nat (number_of v :: nat) = \
\        (if neg (number_of v) then 0 \
\         else (number_of v :: hypreal))";
by (simp_tac (simpset() addsimps [hypreal_of_nat_def]) 1);
qed "hypreal_of_nat_number_of";
Addsimps [hypreal_of_nat_number_of];

Goal "hypreal_of_nat 0 = 0";
by (simp_tac (simpset() delsimps [numeral_0_eq_0]
                        addsimps [numeral_0_eq_0 RS sym]) 1);
qed "hypreal_of_nat_zero";
Addsimps [hypreal_of_nat_zero];

Goal "hypreal_of_nat 1 = 1";
by (simp_tac (simpset() addsimps [hypreal_of_nat_Suc]) 1); 
qed "hypreal_of_nat_one";
Addsimps [hypreal_of_nat_one];
