(*  Title: 	HOL/WF_Rel
    ID:         $Id$
    Author: 	Konrad Slind
    Copyright   1996  TU Munich

Derived wellfounded relations: inverse image, relational product, measure, ...
*)

open WF_Rel;


(*----------------------------------------------------------------------------
 * "Less than" on the natural numbers
 *---------------------------------------------------------------------------*)

goalw thy [less_than_def] "wf less_than"; 
by (rtac (wf_pred_nat RS wf_trancl) 1);
qed "wf_less_than";
AddIffs [wf_less_than];

goalw thy [less_than_def] "trans less_than"; 
by (rtac trans_trancl 1);
qed "trans_less_than";
AddIffs [trans_less_than];

goalw thy [less_than_def, less_def] "((x,y): less_than) = (x<y)"; 
by (Simp_tac 1);
qed "less_than_iff";
AddIffs [less_than_iff];

(*----------------------------------------------------------------------------
 * The inverse image into a wellfounded relation is wellfounded.
 *---------------------------------------------------------------------------*)

goal thy "!!r. wf(r) ==> wf(inv_image r (f::'a=>'b))"; 
by (full_simp_tac (!simpset addsimps [inv_image_def, wf_eq_minimal]) 1);
by (Step_tac 1);
by (subgoal_tac "? (w::'b). w : {w. ? (x::'a). x: Q & (f x = w)}" 1);
by (blast_tac (!claset delrules [allE]) 2);
by (etac allE 1);
by (mp_tac 1);
by (Blast_tac 1);
qed "wf_inv_image";
AddSIs [wf_inv_image];

goalw thy [trans_def,inv_image_def]
    "!!r. trans r ==> trans (inv_image r f)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "trans_inv_image";


(*----------------------------------------------------------------------------
 * All measures are wellfounded.
 *---------------------------------------------------------------------------*)

goalw thy [measure_def] "wf (measure f)";
by (rtac (wf_less_than RS wf_inv_image) 1);
qed "wf_measure";
AddIffs [wf_measure];

(*----------------------------------------------------------------------------
 * Wellfoundedness of lexicographic combinations
 *---------------------------------------------------------------------------*)

goal Prod.thy "!!P. !a b. P((a,b)) ==> !p. P(p)";
by (rtac allI 1);
by (rtac (surjective_pairing RS ssubst) 1);
by (Blast_tac 1);
qed "split_all_pair";

val [wfa,wfb] = goalw thy [wf_def,lex_prod_def]
 "[| wf(ra); wf(rb) |] ==> wf(ra**rb)";
by (EVERY1 [rtac allI,rtac impI, rtac split_all_pair]);
by (rtac (wfa RS spec RS mp) 1);
by (EVERY1 [rtac allI,rtac impI]);
by (rtac (wfb RS spec RS mp) 1);
by (Blast_tac 1);
qed "wf_lex_prod";
AddSIs [wf_lex_prod];

(*----------------------------------------------------------------------------
 * Wellfoundedness of relational product
 *---------------------------------------------------------------------------*)
val [wfa,wfb] = goalw thy [wf_def,rprod_def]
 "[| wf(ra); wf(rb) |] ==> wf(rprod ra rb)";
by (EVERY1 [rtac allI,rtac impI, rtac split_all_pair]);
by (rtac (wfa RS spec RS mp) 1);
by (EVERY1 [rtac allI,rtac impI]);
by (rtac (wfb RS spec RS mp) 1);
by (Blast_tac 1);
qed "wf_rel_prod";
AddSIs [wf_rel_prod];


(*---------------------------------------------------------------------------
 * Wellfoundedness of subsets
 *---------------------------------------------------------------------------*)

goal thy "!!r. [| wf(r);  p<=r |] ==> wf(p)";
by (full_simp_tac (!simpset addsimps [wf_eq_minimal]) 1);
by (Fast_tac 1);
qed "wf_subset";

(*---------------------------------------------------------------------------
 * Wellfoundedness of the empty relation.
 *---------------------------------------------------------------------------*)

goal thy "wf({})";
by (simp_tac (!simpset addsimps [wf_def]) 1);
qed "wf_empty";
AddSIs [wf_empty];


(*---------------------------------------------------------------------------
 * Transitivity of WF combinators.
 *---------------------------------------------------------------------------*)
goalw thy [trans_def, lex_prod_def]
    "!!R1 R2. [| trans R1; trans R2 |] ==> trans (R1 ** R2)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "trans_lex_prod";
AddSIs [trans_lex_prod];

goalw thy [trans_def, rprod_def]
    "!!R1 R2. [| trans R1; trans R2 |] ==> trans (rprod R1 R2)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "trans_rprod";
AddSIs [trans_rprod];


(*---------------------------------------------------------------------------
 * Wellfoundedness of proper subset on finite sets.
 *---------------------------------------------------------------------------*)
goalw thy [finite_psubset_def] "wf(finite_psubset)";
by (rtac (wf_measure RS wf_subset) 1);
by (simp_tac (!simpset addsimps [measure_def, inv_image_def, less_than_def,
				 symmetric less_def])1);
by (fast_tac (!claset addIs [psubset_card]) 1);
qed "wf_finite_psubset";

goalw thy [finite_psubset_def, trans_def] "trans finite_psubset";
by (simp_tac (!simpset addsimps [psubset_def]) 1);
by (Blast_tac 1);
qed "trans_finite_psubset";

