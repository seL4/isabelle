(*  Title: 	HOL/WF_Rel
    ID:         $Id$
    Author: 	Konrad Slind
    Copyright   1996  TU Munich

Derived WF relations: inverse image, lexicographic product, measure, ...
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

val [wfa,wfb] = goalw thy [wf_def,lex_prod_def]
 "[| wf(ra); wf(rb) |] ==> wf(ra**rb)";
by (EVERY1 [rtac allI,rtac impI]);
by (simp_tac (HOL_basic_ss addsimps [split_paired_All]) 1);
by (rtac (wfa RS spec RS mp) 1);
by (EVERY1 [rtac allI,rtac impI]);
by (rtac (wfb RS spec RS mp) 1);
by (Blast_tac 1);
qed "wf_lex_prod";
AddSIs [wf_lex_prod];

(*---------------------------------------------------------------------------
 * Transitivity of WF combinators.
 *---------------------------------------------------------------------------*)
goalw thy [trans_def, lex_prod_def]
    "!!R1 R2. [| trans R1; trans R2 |] ==> trans (R1 ** R2)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "trans_lex_prod";
AddSIs [trans_lex_prod];


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

(*---------------------------------------------------------------------------
 * Wellfoundedness of finite acyclic relations
 * Cannot go into WF because it needs Finite
 *---------------------------------------------------------------------------*)

goal thy "!!r. finite r ==> acyclic r --> wf r";
be finite_induct 1;
 by(Blast_tac 1);
by(split_all_tac 1);
by(Asm_full_simp_tac 1);
qed_spec_mp "finite_acyclic_wf";

goal thy "!!r. finite r ==> wf r = acyclic r";
by(blast_tac (!claset addIs [finite_acyclic_wf,wf_acyclic]) 1);
qed "wf_iff_acyclic_if_finite";


(*---------------------------------------------------------------------------
 * A relation is wellfounded iff it has no infinite descending chain
 *---------------------------------------------------------------------------*)

goalw thy [wf_eq_minimal RS eq_reflection]
  "wf r = (~(? f. !i. (f(Suc i),f i) : r))";
br iffI 1;
 br notI 1;
 be exE 1;
 by(eres_inst_tac [("x","{w. ? i. w=f i}")] allE 1);
 by(Blast_tac 1);
be swap 1;
by(Asm_full_simp_tac 1);
be exE 1;
be swap 1;
br impI 1;
be swap 1;
be exE 1;
by(rename_tac "x" 1);
by(subgoal_tac
 "!i. nat_rec x (%i y. @z. z:Q & (z,y):r) (Suc i) : Q & \
\     (nat_rec x (%i y. @z. z:Q & (z,y):r) (Suc i),\
\      nat_rec x (%i y. @z. z:Q & (z,y):r) i): r" 1);
 by(Blast_tac 1);
br allI 1;
by(induct_tac "i" 1);
 by(Asm_simp_tac 1);
 by(subgoal_tac "? y. y : Q & (y,x):r" 1);
  by(Blast_tac 2);
 be exE 1;
 be selectI 1;
by(subgoal_tac "? y.y:Q & (y,nat_rec x (%i y. @z. z:Q & (z,y):r)(Suc i)):r" 1);
 by(Blast_tac 2);
by(Asm_full_simp_tac 1);
be exE 1;
(* `be selectI 1' takes a long time; hence the instantiation: *)
by (eres_inst_tac[("P","%u.u:Q & (u,?v):r")]selectI 1);
qed "wf_iff_no_infinite_down_chain";
