(*  Title: 	HOL/WF.ML
    ID:         $Id$
    Author: 	Konrad Slind
    Copyright   1996  TU Munich

For WF1.thy.  
*)

open WF1;

(* TFL variants *)
goal WF.thy
    "!R. wf R --> (!P. (!x. (!y. (y,x):R --> P y) --> P x) --> (!x. P x))";
by (strip_tac 1);
by (res_inst_tac [("r","R"),("P","P"), ("a","x")] wf_induct 1);
by (assume_tac 1);
by (fast_tac HOL_cs 1);
qed"tfl_wf_induct";

goal WF.thy "!f R. (x,a):R --> (cut f R a)(x) = f(x)";
by (strip_tac 1);
by (rtac cut_apply 1);
by (assume_tac 1);
qed"tfl_cut_apply";

goal WF.thy "!M R f. (f=wfrec R M) --> wf R --> (!x. f x = M (cut f R x) x)";
by (strip_tac 1);
by (res_inst_tac [("r","R"), ("H","M"),
                  ("a","x"), ("f","f")] (eq_reflection RS def_wfrec) 1);
by (assume_tac 1);
by (assume_tac 1);
qed "tfl_wfrec";

(*----------------------------------------------------------------------------
 * Proof that the inverse image into a wellfounded relation is wellfounded.
 * The proof is relatively sloppy - I map to another version of 
 * wellfoundedness (every n.e. set has an R-minimal element) and transport 
 * the proof for that formulation over. I also didn't remember the existence
 *  of "set_cs" so no doubt the proof can be dramatically shortened!
 *---------------------------------------------------------------------------*)
goal HOL.thy "(~(!x. P x)) = (? x. ~(P x))";
by (fast_tac HOL_cs 1);
val th1 = result();

goal HOL.thy "(~(? x. P x)) = (!x. ~(P x))";
by (fast_tac HOL_cs 1);
val th2 = result();

goal HOL.thy "(~(x-->y)) = (x & (~ y))";
by (fast_tac HOL_cs 1);
val th3 = result();

goal HOL.thy "((~ x) | y) = (x --> y)";
by (fast_tac HOL_cs 1);
val th4 = result();

goal HOL.thy "(~(x & y)) = ((~ x) | (~ y))";
by (fast_tac HOL_cs 1);
val th5 = result();

goal HOL.thy "(~(x | y)) = ((~ x) & (~ y))";
by (fast_tac HOL_cs 1);
val th6 = result();

goal HOL.thy "(~(~x)) = x";
by (fast_tac HOL_cs 1);
val th7 = result();

(* Using [th1,th2,th3,th4,th5,th6,th7] as rewrites drives negation inwards. *)
val NNF_rews = map (fn th => th RS eq_reflection)[th1,th2,th3,th4,th5,th6,th7];

(* The name "contrapos" is already taken. *)
goal HOL.thy "(P --> Q) = ((~ Q) --> (~ P))";
by (fast_tac HOL_cs 1);
val ol_contrapos = result();

(* Maps to another version of wellfoundedness *)
val [p1] = goalw WF.thy [wf_def]
"wf(R) ==> (!Q. (? x. Q x) --> (? min. Q min & (!b. (b,min):R --> (~ Q b))))";
by (rtac allI 1);
by (rtac (ol_contrapos RS ssubst) 1);
by (rewrite_tac NNF_rews);
by (rtac impI 1);
by (rtac ((p1 RS spec) RS mp) 1);
by (fast_tac HOL_cs 1);
val wf_minimal = result();

goalw WF.thy [wf_def]
"(!Q. (? x. Q x) --> (? min. Q min & (!b. (b,min):R --> (~ Q b)))) --> wf R";
by (rtac impI 1);
by (rtac allI 1);
by (rtac (ol_contrapos RS ssubst) 1);
by (rewrite_tac NNF_rews);
by (rtac impI 1);
by (etac allE 1);
by (dtac mp 1);
by (assume_tac 1);
by (fast_tac HOL_cs 1);
val minimal_wf = result();

val wf_eq_minimal = 
  standard ((wf_minimal COMP ((minimal_wf RS mp) COMP iffI)) RS sym);

goalw WF1.thy [inv_image_def,wf_eq_minimal RS eq_reflection] 
"wf(R) --> wf(inv_image R (f::'a=>'b))"; 
by (strip_tac 1);
by (etac exE 1);
by (subgoal_tac "? (w::'b). ? (x::'a). Q x & (f x = w)" 1);
by (rtac exI 2);
by (rtac exI 2);
by (rtac conjI 2);
by (assume_tac 2);
by (rtac refl 2);

by (etac allE 1);
by (dtac mp 1);
by (assume_tac 1);
by (eres_inst_tac [("P","? min. (? x. Q x & f x = min) & \
                \ (! b. (b, min) : R --> ~ (? x. Q x & f x = b))")] rev_mp 1);
by (etac thin_rl 1);
by (etac thin_rl 1);
by (rewrite_tac NNF_rews);
by (rtac impI 1);
by (etac exE 1);
by (etac conjE 1);
by (etac exE 1);
by (rtac exI 1);
by (etac conjE 1);
by (rtac conjI 1);
by (assume_tac 1);
by (hyp_subst_tac 1);
by (rtac allI 1);
by (rtac impI 1);
by (etac CollectE 1);
by (etac allE 1);
by (dtac mp 1);
by (rewrite_tac[fst_conv RS eq_reflection,snd_conv RS eq_reflection]);
by (assume_tac 1);
by (fast_tac HOL_cs 1);
val wf_inv_image = result() RS mp;

(* from Nat.ML *)
goalw WF1.thy [wf_def] "wf(pred_nat)";
by (strip_tac 1);
by (nat_ind_tac "x" 1);
by (fast_tac (HOL_cs addSEs [mp, pred_natE, Pair_inject, 
                             make_elim Suc_inject]) 2);
by (fast_tac (HOL_cs addSEs [mp, pred_natE, Pair_inject, Zero_neq_Suc]) 1);
val wf_pred_nat = result();

goalw WF1.thy [wf_def,pred_list_def] "wf(pred_list)";
by (strip_tac 1);
by (List.list.induct_tac "x" 1);
by (etac allE 1);
by (etac impE 1);
by (assume_tac 2);
by (strip_tac 1);
by (etac CollectE 1);
by (asm_full_simp_tac (!simpset) 1);

by (etac allE 1);
by (etac impE 1);
by (assume_tac 2);
by (strip_tac 1);
by (etac CollectE 1);
by (etac exE 1);
by (asm_full_simp_tac (!simpset) 1);
by (etac conjE 1);
by (hyp_subst_tac 1);
by (assume_tac 1);
qed "wf_pred_list";

(*----------------------------------------------------------------------------
 * All measures are wellfounded.
 *---------------------------------------------------------------------------*)

goalw WF1.thy [measure_def] "wf (measure f)";
by (rtac wf_inv_image 1);
by (rtac wf_trancl 1);
by (rtac wf_pred_nat 1);
qed "wf_measure";

(*----------------------------------------------------------------------------
 * Wellfoundedness of lexicographic combinations
 *---------------------------------------------------------------------------*)

val prems = goal Prod.thy "!a b. P((a,b)) ==> !p. P(p)";
by (cut_facts_tac prems 1);
by (rtac allI 1);
by (rtac (surjective_pairing RS ssubst) 1);
by (fast_tac HOL_cs 1);
qed "split_all_pair";

val [wfa,wfb] = goalw WF1.thy [wf_def,lex_prod_def]
 "[| wf(ra); wf(rb) |] ==> wf(ra**rb)";
by (EVERY1 [rtac allI,rtac impI, rtac split_all_pair]);
by (rtac (wfa RS spec RS mp) 1);
by (EVERY1 [rtac allI,rtac impI]);
by (rtac (wfb RS spec RS mp) 1);
by (fast_tac (set_cs addSEs [Pair_inject]) 1);
qed "wf_lex_prod";

(*----------------------------------------------------------------------------
 * Wellfoundedness of relational product
 *---------------------------------------------------------------------------*)
val [wfa,wfb] = goalw WF1.thy [wf_def,rprod_def]
 "[| wf(ra); wf(rb) |] ==> wf(rprod ra rb)";
by (EVERY1 [rtac allI,rtac impI, rtac split_all_pair]);
by (rtac (wfa RS spec RS mp) 1);
by (EVERY1 [rtac allI,rtac impI]);
by (rtac (wfb RS spec RS mp) 1);
by (fast_tac (set_cs addSEs [Pair_inject]) 1);
qed "wf_rel_prod";


(*---------------------------------------------------------------------------
 * Wellfoundedness of subsets
 *---------------------------------------------------------------------------*)

goalw WF1.thy [wf_eq_minimal RS eq_reflection] 
     "wf(r) --> (!x y. (x,y):p --> (x,y):r) --> wf(p)";
by (fast_tac set_cs 1);
qed "wf_subset";

(*---------------------------------------------------------------------------
 * Wellfoundedness of the empty relation.
 *---------------------------------------------------------------------------*)

goalw WF1.thy [wf_eq_minimal RS eq_reflection,emptyr_def] 
     "wf(emptyr)";
by (fast_tac set_cs 1);
qed "wf_emptyr";
