(*  Title:	HOL/Integ/Bin.ML
    Authors:	Lawrence C Paulson, Cambridge University Computer Laboratory
		David Spelt, University of Twente 
    Copyright   1994  University of Cambridge
    Copyright   1996 University of Twente

Arithmetic on binary integers.
*)

open Bin;

(** extra rules for bin_succ, bin_pred, bin_add, bin_mult **)

qed_goal "norm_Bcons_Plus_0" Bin.thy "norm_Bcons Plus False = Plus"
	(fn prem => [(Simp_tac 1)]);

qed_goal "norm_Bcons_Plus_1" Bin.thy "norm_Bcons Plus True = Bcons Plus True"
	(fn prem => [(Simp_tac 1)]);

qed_goal "norm_Bcons_Minus_0" Bin.thy "norm_Bcons Minus False = Bcons Minus False"
	(fn prem => [(Simp_tac 1)]);

qed_goal "norm_Bcons_Minus_1" Bin.thy "norm_Bcons Minus True = Minus"
	(fn prem => [(Simp_tac 1)]);

qed_goal "norm_Bcons_Bcons" Bin.thy "norm_Bcons (Bcons w x) b = Bcons (Bcons w x) b"
	(fn prem => [(Simp_tac 1)]);

qed_goal "bin_succ_Bcons1" Bin.thy "bin_succ(Bcons w True) = Bcons (bin_succ w) False"
	(fn prem => [(Simp_tac 1)]);

qed_goal "bin_succ_Bcons0" Bin.thy "bin_succ(Bcons w False) =  norm_Bcons w True"
	(fn prem => [(Simp_tac 1)]);

qed_goal "bin_pred_Bcons1" Bin.thy "bin_pred(Bcons w True) = norm_Bcons w False"
	(fn prem => [(Simp_tac 1)]);

qed_goal "bin_pred_Bcons0" Bin.thy "bin_pred(Bcons w False) = Bcons (bin_pred w) True"
	(fn prem => [(Simp_tac 1)]);

qed_goal "bin_minus_Bcons1" Bin.thy "bin_minus(Bcons w True) = bin_pred (Bcons(bin_minus w) False)"
	(fn prem => [(Simp_tac 1)]);

qed_goal "bin_minus_Bcons0" Bin.thy "bin_minus(Bcons w False) = Bcons (bin_minus w) False"
	(fn prem => [(Simp_tac 1)]);

(*** bin_add: binary addition ***)

qed_goal "bin_add_Bcons_Bcons11" Bin.thy "bin_add (Bcons v True) (Bcons w True) = norm_Bcons (bin_add v (bin_succ w)) False"
	(fn prem => [(Simp_tac 1)]);

qed_goal "bin_add_Bcons_Bcons10" Bin.thy "bin_add (Bcons v True) (Bcons w False) = norm_Bcons (bin_add v w) True"
	(fn prem => [(Simp_tac 1)]);

(* SHOULD THIS THEOREM BE ADDED TO HOL_SS ? *)
val my = prove_goal HOL.thy "(False = (~P)) = P"
	(fn prem => [(Fast_tac 1)]);

qed_goal "bin_add_Bcons_Bcons0" Bin.thy "bin_add (Bcons v False) (Bcons w y) = norm_Bcons (bin_add v w) y"
	(fn prem => [(simp_tac (!simpset addsimps [my]) 1)]);

qed_goal "bin_add_Bcons_Plus" Bin.thy "bin_add (Bcons v x) Plus = Bcons v x"
	(fn prems => [(Simp_tac 1)]);

qed_goal "bin_add_Bcons_Minus" Bin.thy "bin_add (Bcons v x) Minus = bin_pred (Bcons v x)"
	(fn prems => [(Simp_tac 1)]);

qed_goal "bin_add_Bcons_Bcons" Bin.thy "bin_add (Bcons v x) (Bcons w y) = norm_Bcons(bin_add v (if x & y then (bin_succ w) else w)) (x~= y)"
	(fn prems => [(Simp_tac 1)]);


(*** bin_add: binary multiplication ***)

qed_goal "bin_mult_Bcons1" Bin.thy "bin_mult (Bcons v True) w = bin_add (norm_Bcons (bin_mult v w) False) w"
	(fn prem => [(Simp_tac 1)]);

qed_goal "bin_mult_Bcons0" Bin.thy "bin_mult (Bcons v False) w = norm_Bcons (bin_mult v w) False"
	(fn prem => [(Simp_tac 1)]);


(**** The carry/borrow functions, bin_succ and bin_pred ****)

(** Lemmas **)

qed_goal "zadd_assoc_cong" Integ.thy "(z::int) + v = z' + v' ==> z + (v + w) = z' + (v' + w)"
  (fn prems => [(asm_simp_tac (!simpset addsimps (prems @ [zadd_assoc RS sym])) 1)]);

qed_goal "zadd_assoc_swap" Integ.thy "(z::int) + (v + w) = v + (z + w)"
   (fn prems => [(REPEAT (ares_tac [zadd_commute RS zadd_assoc_cong] 1))]);


val my_ss = !simpset setloop (split_tac [expand_if]) ;


(**** integ_of_bin ****)


qed_goal "integ_of_bin_norm_Bcons" Bin.thy "integ_of_bin(norm_Bcons w b) = integ_of_bin(Bcons w b)"
   (fn prems=>[	(bin.induct_tac "w" 1),
		(REPEAT(simp_tac (!simpset setloop (split_tac [expand_if])) 1)) ]);

qed_goal "integ_of_bin_succ" Bin.thy "integ_of_bin(bin_succ w) = $#1 + integ_of_bin w"
   (fn prems=>[	(rtac bin.induct 1),
		(REPEAT(asm_simp_tac (!simpset addsimps (integ_of_bin_norm_Bcons::zadd_ac)
					       setloop (split_tac [expand_if])) 1)) ]);

qed_goal "integ_of_bin_pred" Bin.thy "integ_of_bin(bin_pred w) = $~ ($#1) + integ_of_bin w"
   (fn prems=>[	(rtac bin.induct 1),
		(REPEAT(asm_simp_tac (!simpset addsimps (integ_of_bin_norm_Bcons::zadd_ac)
					       setloop (split_tac [expand_if])) 1)) ]);

qed_goal "integ_of_bin_minus" Bin.thy "integ_of_bin(bin_minus w) = $~ (integ_of_bin w)"
   (fn prems=>[	(rtac bin.induct 1),
		(Simp_tac 1),
		(Simp_tac 1),
		(asm_simp_tac (!simpset
				delsimps [pred_Plus,pred_Minus,pred_Bcons]
				addsimps [integ_of_bin_succ,integ_of_bin_pred,
					  zadd_assoc]
				setloop (split_tac [expand_if])) 1)]);

 
val bin_add_simps = [add_Plus,add_Minus,bin_add_Bcons_Plus,bin_add_Bcons_Minus,bin_add_Bcons_Bcons,
		     integ_of_bin_succ, integ_of_bin_pred,
		     integ_of_bin_norm_Bcons];
val bin_simps = [iob_Plus,iob_Minus,iob_Bcons];

goal Bin.thy "! w. integ_of_bin(bin_add v w) = integ_of_bin v + integ_of_bin w";
by (bin.induct_tac "v" 1);
by (simp_tac (my_ss addsimps bin_add_simps) 1);
by (simp_tac (my_ss addsimps bin_add_simps) 1);
by (rtac allI 1);
by (bin.induct_tac "w" 1);
by (asm_simp_tac (my_ss addsimps (bin_add_simps)) 1);
by (asm_simp_tac (my_ss addsimps (bin_add_simps @ zadd_ac)) 1);
by (cut_inst_tac [("P","bool")] True_or_False 1);
by (etac disjE 1);
by (asm_simp_tac (my_ss addsimps (bin_add_simps @ zadd_ac)) 1);
by (asm_simp_tac (my_ss addsimps (bin_add_simps @ zadd_ac)) 1);
val integ_of_bin_add_lemma = result();

goal Bin.thy "integ_of_bin(bin_add v w) = integ_of_bin v + integ_of_bin w";
by (cut_facts_tac [integ_of_bin_add_lemma] 1);
by (Fast_tac 1);
qed "integ_of_bin_add";

val bin_mult_simps = [integ_of_bin_minus, integ_of_bin_add,integ_of_bin_norm_Bcons];

goal Bin.thy "integ_of_bin(bin_mult v w) = integ_of_bin v * integ_of_bin w";
by (bin.induct_tac "v" 1);
by (simp_tac (my_ss addsimps bin_mult_simps) 1);
by (simp_tac (my_ss addsimps bin_mult_simps) 1);
by (cut_inst_tac [("P","bool")] True_or_False 1);
by (etac disjE 1);
by (asm_simp_tac (my_ss addsimps (bin_mult_simps @ [zadd_zmult_distrib])) 2);
by (asm_simp_tac (my_ss addsimps (bin_mult_simps @ [zadd_zmult_distrib] @ zadd_ac)) 1);
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
