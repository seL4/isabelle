(*  Title:      HOL/Integ/Bin.ML
    Authors:    Lawrence C Paulson, Cambridge University Computer Laboratory
                David Spelt, University of Twente 
    Copyright   1994  University of Cambridge
    Copyright   1996 University of Twente

Arithmetic on binary integers.
*)

open Bin;

(** extra rules for bin_succ, bin_pred, bin_add, bin_mult **)

qed_goal "norm_Bcons_Plus_0" Bin.thy
    "norm_Bcons PlusSign False = PlusSign"
 (fn _ => [(Simp_tac 1)]);

qed_goal "norm_Bcons_Plus_1" Bin.thy
    "norm_Bcons PlusSign True = Bcons PlusSign True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "norm_Bcons_Minus_0" Bin.thy
    "norm_Bcons MinusSign False = Bcons MinusSign False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "norm_Bcons_Minus_1" Bin.thy
    "norm_Bcons MinusSign True = MinusSign"
 (fn _ => [(Simp_tac 1)]);

qed_goal "norm_Bcons_Bcons" Bin.thy
    "norm_Bcons (Bcons w x) b = Bcons (Bcons w x) b"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_succ_Bcons1" Bin.thy
    "bin_succ(Bcons w True) = Bcons (bin_succ w) False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_succ_Bcons0" Bin.thy
    "bin_succ(Bcons w False) =  norm_Bcons w True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_pred_Bcons1" Bin.thy
    "bin_pred(Bcons w True) = norm_Bcons w False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_pred_Bcons0" Bin.thy
    "bin_pred(Bcons w False) = Bcons (bin_pred w) True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_minus_Bcons1" Bin.thy
    "bin_minus(Bcons w True) = bin_pred (Bcons(bin_minus w) False)"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_minus_Bcons0" Bin.thy
    "bin_minus(Bcons w False) = Bcons (bin_minus w) False"
 (fn _ => [(Simp_tac 1)]);

(*** bin_add: binary addition ***)

qed_goal "bin_add_Bcons_Bcons11" Bin.thy
    "bin_add (Bcons v True) (Bcons w True) = \
\    norm_Bcons (bin_add v (bin_succ w)) False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_add_Bcons_Bcons10" Bin.thy
    "bin_add (Bcons v True) (Bcons w False) = norm_Bcons (bin_add v w) True"
 (fn _ => [(Simp_tac 1)]);

val lemma = prove_goal HOL.thy "(False = (~P)) = P"
 (fn _ => [(Fast_tac 1)]);

qed_goal "bin_add_Bcons_Bcons0" Bin.thy
    "bin_add (Bcons v False) (Bcons w y) = norm_Bcons (bin_add v w) y"
 (fn _ => [(simp_tac (!simpset addsimps [lemma]) 1)]);

qed_goal "bin_add_Bcons_Plus" Bin.thy
    "bin_add (Bcons v x) PlusSign = Bcons v x"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_add_Bcons_Minus" Bin.thy
    "bin_add (Bcons v x) MinusSign = bin_pred (Bcons v x)"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_add_Bcons_Bcons" Bin.thy
    "bin_add (Bcons v x) (Bcons w y) = \
\    norm_Bcons(bin_add v (if x & y then (bin_succ w) else w)) (x~= y)"
 (fn _ => [(Simp_tac 1)]);


(*** bin_add: binary multiplication ***)

qed_goal "bin_mult_Bcons1" Bin.thy
    "bin_mult (Bcons v True) w = bin_add (norm_Bcons (bin_mult v w) False) w"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_mult_Bcons0" Bin.thy
    "bin_mult (Bcons v False) w = norm_Bcons (bin_mult v w) False"
 (fn _ => [(Simp_tac 1)]);


(**** The carry/borrow functions, bin_succ and bin_pred ****)

val if_ss = !simpset addsplits [expand_if];


(**** integ_of_bin ****)


qed_goal "integ_of_bin_norm_Bcons" Bin.thy
    "integ_of_bin(norm_Bcons w b) = integ_of_bin(Bcons w b)"
 (fn _ =>[(bin.induct_tac "w" 1),
          (ALLGOALS(simp_tac if_ss)) ]);

qed_goal "integ_of_bin_succ" Bin.thy
    "integ_of_bin(bin_succ w) = $#1 + integ_of_bin w"
 (fn _ =>[(rtac bin.induct 1),
          (ALLGOALS(asm_simp_tac 
                    (if_ss addsimps (integ_of_bin_norm_Bcons::zadd_ac)))) ]);

qed_goal "integ_of_bin_pred" Bin.thy
    "integ_of_bin(bin_pred w) = $~ ($#1) + integ_of_bin w"
 (fn _ =>[(rtac bin.induct 1),
          (ALLGOALS(asm_simp_tac
                  (if_ss addsimps (integ_of_bin_norm_Bcons::zadd_ac)))) ]);

qed_goal "integ_of_bin_minus" Bin.thy
    "integ_of_bin(bin_minus w) = $~ (integ_of_bin w)"
 (fn _ =>[(rtac bin.induct 1),
          (Simp_tac 1),
          (Simp_tac 1),
          (asm_simp_tac (if_ss
                         delsimps [pred_Plus,pred_Minus,pred_Bcons]
                         addsimps [integ_of_bin_succ,integ_of_bin_pred,
                                   zadd_assoc]) 1)]);

 
val bin_add_simps = [add_Plus,add_Minus,bin_add_Bcons_Plus,
                     bin_add_Bcons_Minus,bin_add_Bcons_Bcons,
                     integ_of_bin_succ, integ_of_bin_pred,
                     integ_of_bin_norm_Bcons];
val bin_simps = [iob_Plus,iob_Minus,iob_Bcons];

goal Bin.thy
    "! w. integ_of_bin(bin_add v w) = integ_of_bin v + integ_of_bin w";
by (bin.induct_tac "v" 1);
by (simp_tac (if_ss addsimps bin_add_simps) 1);
by (simp_tac (if_ss addsimps bin_add_simps) 1);
by (rtac allI 1);
by (bin.induct_tac "w" 1);
by (asm_simp_tac (if_ss addsimps (bin_add_simps)) 1);
by (asm_simp_tac (if_ss addsimps (bin_add_simps @ zadd_ac)) 1);
by (cut_inst_tac [("P","bool")] True_or_False 1);
by (etac disjE 1);
by (asm_simp_tac (if_ss addsimps (bin_add_simps @ zadd_ac)) 1);
by (asm_simp_tac (if_ss addsimps (bin_add_simps @ zadd_ac)) 1);
val integ_of_bin_add_lemma = result();

goal Bin.thy "integ_of_bin(bin_add v w) = integ_of_bin v + integ_of_bin w";
by (cut_facts_tac [integ_of_bin_add_lemma] 1);
by (Fast_tac 1);
qed "integ_of_bin_add";

val bin_mult_simps = [integ_of_bin_minus, integ_of_bin_add,
                      integ_of_bin_norm_Bcons];

goal Bin.thy "integ_of_bin(bin_mult v w) = integ_of_bin v * integ_of_bin w";
by (bin.induct_tac "v" 1);
by (simp_tac (if_ss addsimps bin_mult_simps) 1);
by (simp_tac (if_ss addsimps bin_mult_simps) 1);
by (cut_inst_tac [("P","bool")] True_or_False 1);
by (etac disjE 1);
by (asm_simp_tac (if_ss addsimps (bin_mult_simps @ [zadd_zmult_distrib])) 2);
by (asm_simp_tac (if_ss addsimps (bin_mult_simps @ [zadd_zmult_distrib] @ 
                                  zadd_ac)) 1);
qed "integ_of_bin_mult";


Delsimps [succ_Bcons,pred_Bcons,min_Bcons,add_Bcons,mult_Bcons,
          iob_Plus,iob_Minus,iob_Bcons,
          norm_Plus,norm_Minus,norm_Bcons];

Addsimps [integ_of_bin_add RS sym,
          integ_of_bin_minus RS sym,
          integ_of_bin_mult RS sym,
          bin_succ_Bcons1,bin_succ_Bcons0,
          bin_pred_Bcons1,bin_pred_Bcons0,
          bin_minus_Bcons1,bin_minus_Bcons0, 
          bin_add_Bcons_Plus,bin_add_Bcons_Minus,
          bin_add_Bcons_Bcons0,bin_add_Bcons_Bcons10,bin_add_Bcons_Bcons11,
          bin_mult_Bcons1,bin_mult_Bcons0,
          norm_Bcons_Plus_0,norm_Bcons_Plus_1,
          norm_Bcons_Minus_0,norm_Bcons_Minus_1,
          norm_Bcons_Bcons];


(** Simplification rules for comparison of binary numbers (Norbert Völker) **) 

Addsimps [zadd_assoc];

goal Bin.thy  
    "(integ_of_bin x = integ_of_bin y) \ 
\   = (integ_of_bin (bin_add x (bin_minus y)) = $# 0)"; 
  by (simp_tac (HOL_ss addsimps
                [integ_of_bin_add, integ_of_bin_minus,zdiff_def]) 1); 
  by (rtac iffI 1); 
  by (etac ssubst 1);
  by (rtac zadd_zminus_inverse 1); 
  by (dres_inst_tac [("f","(% z. z + integ_of_bin y)")] arg_cong 1); 
  by (asm_full_simp_tac 
      (HOL_ss addsimps[zadd_assoc,zadd_0,zadd_0_right, 
                       zadd_zminus_inverse2]) 1); 
val iob_eq_eq_diff_0 = result(); 

goal Bin.thy "(integ_of_bin PlusSign = $# 0) = True"; 
  by (stac iob_Plus 1); by (Simp_tac 1); 
val iob_Plus_eq_0 = result(); 

goal Bin.thy "(integ_of_bin MinusSign = $# 0) = False"; 
  by (stac iob_Minus 1); 
  by (Simp_tac 1);
val iob_Minus_not_eq_0 = result(); 

goal Bin.thy 
    "(integ_of_bin (Bcons w x) = $# 0) = (~x & integ_of_bin w = $# 0)"; 
  by (stac iob_Bcons 1);
  by (case_tac "x" 1); 
  by (ALLGOALS Asm_simp_tac); 
  by (ALLGOALS(asm_simp_tac (HOL_ss addsimps [integ_of_bin_add]))); 
  by (ALLGOALS(int_case_tac "integ_of_bin w")); 
  by (ALLGOALS(asm_simp_tac 
               (!simpset addsimps[zminus_zadd_distrib RS sym, 
                                znat_add RS sym]))); 
  by (stac eq_False_conv 1); 
  by (rtac notI 1); 
  by (dres_inst_tac [("f","(% z. z +  $# Suc (Suc (n + n)))")] arg_cong 1); 
  by (Asm_full_simp_tac 1); 
val iob_Bcons_eq_0 = result(); 

goalw Bin.thy [zless_def,zdiff_def] 
    "integ_of_bin x < integ_of_bin y \
\    = (integ_of_bin (bin_add x (bin_minus y)) < $# 0)";
  by (Simp_tac 1); 
val iob_less_eq_diff_lt_0 = result(); 

goal Bin.thy "(integ_of_bin PlusSign < $# 0) = False"; 
  by (stac iob_Plus 1); by (Simp_tac 1); 
val iob_Plus_not_lt_0 = result(); 

goal Bin.thy "(integ_of_bin MinusSign < $# 0) = True"; 
  by (stac iob_Minus 1); by (Simp_tac 1);
val iob_Minus_lt_0 = result(); 

goal Bin.thy 
    "(integ_of_bin (Bcons w x) < $# 0) = (integ_of_bin w < $# 0)"; 
  by (stac iob_Bcons 1);
  by (case_tac "x" 1); 
  by (ALLGOALS Asm_simp_tac); 
  by (ALLGOALS(asm_simp_tac (HOL_ss addsimps [integ_of_bin_add]))); 
  by (ALLGOALS(int_case_tac "integ_of_bin w")); 
  by (ALLGOALS(asm_simp_tac 
               (!simpset addsimps[zminus_zadd_distrib RS sym, 
                                znat_add RS sym]))); 
  by (stac (zadd_zminus_inverse RS sym) 1); 
  by (rtac zadd_zless_mono1 1); 
  by (Simp_tac 1); 
val iob_Bcons_lt_0 = result(); 

goal Bin.thy
  "integ_of_bin x <= integ_of_bin y \
\  = ( integ_of_bin (bin_add x (bin_minus y)) < $# 0 \
\    | integ_of_bin (bin_add x (bin_minus y)) = $# 0)";
by (simp_tac (HOL_ss addsimps 
              [zle_eq_zless_or_eq,iob_less_eq_diff_lt_0,zdiff_def
               ,iob_eq_eq_diff_0,integ_of_bin_minus,integ_of_bin_add]) 1);
val iob_le_diff_lt_0_or_eq_0 = result(); 

Delsimps [zless_eq_less, zle_eq_le, zadd_assoc, znegative_zminus_znat, 
          not_znegative_znat, zero_zless_Suc_pos, negative_zless_0, 
          negative_zle_0, not_zle_0_negative, not_znat_zless_negative, 
          zminus_zless_zminus, zminus_zle_zminus, negative_eq_positive]; 

Addsimps [zdiff_def, iob_eq_eq_diff_0, iob_less_eq_diff_lt_0, 
          iob_le_diff_lt_0_or_eq_0, iob_Plus_eq_0, iob_Minus_not_eq_0, 
          iob_Bcons_eq_0, iob_Plus_not_lt_0, iob_Minus_lt_0, iob_Bcons_lt_0];


(*** Examples of performing binary arithmetic by simplification ***)

goal Bin.thy "#13  +  #19 = #32";
by (Simp_tac 1);
result();

goal Bin.thy "#1234  +  #5678 = #6912";
by (Simp_tac 1);
result();

goal Bin.thy "#1359  +  #~2468 = #~1109";
by (Simp_tac 1);
result();

goal Bin.thy "#93746 +  #~46375 = #47371";
by (Simp_tac 1);
result();

goal Bin.thy "$~ #65745 = #~65745";
by (Simp_tac 1);
result();

goal Bin.thy "$~ #~54321 = #54321";
by (Simp_tac 1);
result();

goal Bin.thy "#13  *  #19 = #247";
by (Simp_tac 1);
result();

goal Bin.thy "#~84  *  #51 = #~4284";
by (Simp_tac 1);
result();

goal Bin.thy "#255  *  #255 = #65025";
by (Simp_tac 1);
result();

goal Bin.thy "#1359  *  #~2468 = #~3354012";
by (Simp_tac 1);
result();

goal Bin.thy "#89 * #10 ~= #889";  
by (Simp_tac 1); 
result();

goal Bin.thy "#13 < #18 - #4";  
by (Simp_tac 1); 
result();

goal Bin.thy "#~345 < #~242 + #~100";  
by (Simp_tac 1); 
result();

goal Bin.thy "#13557456 < #18678654";  
by (Simp_tac 1); 
result();

goal Bin.thy "#999999 <= (#1000001 + #1)-#2";  
by (Simp_tac 1); 
result();

goal Bin.thy "#1234567 <= #1234567";  
by (Simp_tac 1); 
result();
