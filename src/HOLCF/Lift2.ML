 (* Lift2.ML *)

open Lift2;
Addsimps [less_lift_def];


(* -------------------------------------------------------------------------*)
(* type ('a)lift is pointed                                                *)
(* ------------------------------------------------------------------------ *)
 

goal Lift2.thy  "Undef << x";
by (simp_tac (!simpset addsimps [inst_lift_po]) 1);
qed"minimal_lift";


(* ------------------------------------------------------------------------ *)
(* ('a)lift is a cpo                                                       *)
(* ------------------------------------------------------------------------ *)

(* The following Lemmata have already been proved in Pcpo.ML and Fix.ML, 
   but there class pcpo is assumed, although only po is necessary and a
   least element. Therefore they are redone here for the po lift with 
   least element Undef.   *)

(* Tailoring notUU_I of Pcpo.ML to Undef *)

goal Lift2.thy "!!x. [| x<<y; ~x=Undef |] ==> ~y=Undef";
by (etac contrapos 1);
by (hyp_subst_tac 1);
by (rtac antisym_less 1);
by (atac 1);
by (rtac minimal_lift 1);
qed"notUndef_I";


(* Tailoring chain_mono2 of Pcpo.ML to Undef *)

goal Lift2.thy
"!!Y. [|? j.~Y(j)=Undef;is_chain(Y::nat=>('a)lift)|] \
\ ==> ? j.!i.j<i-->~Y(i)=Undef";
by (safe_tac HOL_cs);
by (step_tac HOL_cs 1);
by (strip_tac 1);
by (rtac notUndef_I 1);
by (atac 2);
by (etac (chain_mono RS mp) 1);
by (atac 1);
qed"chain_mono2_po";


(* Tailoring flat_imp_chain_finite of Fix.ML to lift *)

goal Lift2.thy
        "(! Y. is_chain(Y::nat=>('a)lift)-->(? n. max_in_chain n Y))";
by (rewtac max_in_chain_def);  
by (strip_tac 1);
by (res_inst_tac [("P","!i.Y(i)=Undef")] case_split_thm  1);
by (res_inst_tac [("x","0")] exI 1);
by (strip_tac 1);
by (rtac trans 1);
by (etac spec 1);
by (rtac sym 1);
by (etac spec 1); 

by (subgoal_tac "!x y.x<<(y::('a)lift) --> x=Undef | x=y" 1);
by (simp_tac (!simpset addsimps [inst_lift_po]) 2);
by (rtac (chain_mono2_po RS exE) 1); 
by (fast_tac HOL_cs 1); 
by (atac 1); 
by (res_inst_tac [("x","Suc(x)")] exI 1); 
by (strip_tac 1); 
by (rtac disjE 1); 
by (atac 3); 
by (rtac mp 1); 
by (dtac spec 1);
by (etac spec 1); 
by (etac (le_imp_less_or_eq RS disjE) 1); 
by (etac (chain_mono RS mp) 1); 
by (atac 1); 
by (hyp_subst_tac 1); 
by (rtac refl_less 1); 
by (res_inst_tac [("P","Y(Suc(x)) = Undef")] notE 1); 
by (atac 2); 
by (rtac mp 1); 
by (etac spec 1); 
by (Asm_simp_tac 1);
qed"flat_imp_chain_finite_poo";


(* Main Lemma: cpo_lift *)

goal Lift2.thy  
  "!!Y. is_chain(Y::nat=>('a)lift) ==> ? x.range(Y) <<|x";
by (cut_inst_tac [] flat_imp_chain_finite_poo 1);
by (step_tac HOL_cs 1);
by (safe_tac HOL_cs);
by (step_tac HOL_cs 1); 
by (rtac exI 1);
by (rtac lub_finch1 1);
by (atac 1);
by (atac 1);
qed"cpo_lift";



