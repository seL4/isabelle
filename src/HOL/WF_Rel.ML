(*  Title: 	HOL/WF_Rel
    ID:         $Id$
    Author: 	Konrad Slind
    Copyright   1996  TU Munich

Derived WF relations: inverse image, lexicographic product, measure, ...
*)


(*----------------------------------------------------------------------------
 * "Less than" on the natural numbers
 *---------------------------------------------------------------------------*)

Goalw [less_than_def] "wf less_than"; 
by (rtac (wf_pred_nat RS wf_trancl) 1);
qed "wf_less_than";
AddIffs [wf_less_than];

Goalw [less_than_def] "trans less_than"; 
by (rtac trans_trancl 1);
qed "trans_less_than";
AddIffs [trans_less_than];

Goalw [less_than_def, less_def] "((x,y): less_than) = (x<y)"; 
by (Simp_tac 1);
qed "less_than_iff";
AddIffs [less_than_iff];

Goal "(!!n. (!m. Suc m <= n --> P m) ==> P n) ==> P n";
br (wf_less_than RS wf_induct) 1;
by (resolve_tac (premises()) 1);
by Auto_tac;
qed_spec_mp "full_nat_induct";

(*----------------------------------------------------------------------------
 * The inverse image into a wellfounded relation is wellfounded.
 *---------------------------------------------------------------------------*)

Goal "wf(r) ==> wf(inv_image r (f::'a=>'b))"; 
by (full_simp_tac (simpset() addsimps [inv_image_def, wf_eq_minimal]) 1);
by (Clarify_tac 1);
by (subgoal_tac "? (w::'b). w : {w. ? (x::'a). x: Q & (f x = w)}" 1);
by (blast_tac (claset() delrules [allE]) 2);
by (etac allE 1);
by (mp_tac 1);
by (Blast_tac 1);
qed "wf_inv_image";
AddSIs [wf_inv_image];

Goalw [trans_def,inv_image_def]
    "!!r. trans r ==> trans (inv_image r f)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "trans_inv_image";


(*----------------------------------------------------------------------------
 * All measures are wellfounded.
 *---------------------------------------------------------------------------*)

Goalw [measure_def] "wf (measure f)";
by (rtac (wf_less_than RS wf_inv_image) 1);
qed "wf_measure";
AddIffs [wf_measure];

val measure_induct = standard
    (asm_full_simplify (simpset() addsimps [measure_def,inv_image_def])
      (wf_measure RS wf_induct));
store_thm("measure_induct",measure_induct);

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
Goalw [trans_def, lex_prod_def]
    "!!R1 R2. [| trans R1; trans R2 |] ==> trans (R1 ** R2)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "trans_lex_prod";
AddSIs [trans_lex_prod];


(*---------------------------------------------------------------------------
 * Wellfoundedness of proper subset on finite sets.
 *---------------------------------------------------------------------------*)
Goalw [finite_psubset_def] "wf(finite_psubset)";
by (rtac (wf_measure RS wf_subset) 1);
by (simp_tac (simpset() addsimps [measure_def, inv_image_def, less_than_def,
				 symmetric less_def])1);
by (fast_tac (claset() addSIs [psubset_card]) 1);
qed "wf_finite_psubset";

Goalw [finite_psubset_def, trans_def] "trans finite_psubset";
by (simp_tac (simpset() addsimps [psubset_def]) 1);
by (Blast_tac 1);
qed "trans_finite_psubset";

(*---------------------------------------------------------------------------
 * Wellfoundedness of finite acyclic relations
 * Cannot go into WF because it needs Finite.
 *---------------------------------------------------------------------------*)

Goal "finite r ==> acyclic r --> wf r";
by (etac finite_induct 1);
 by (Blast_tac 1);
by (split_all_tac 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "finite_acyclic_wf";

Goal "[|finite r; acyclic r|] ==> wf (r^-1)";
by (etac (finite_converse RS iffD2 RS finite_acyclic_wf) 1);
by (etac (acyclic_converse RS iffD2) 1);
qed "finite_acyclic_wf_converse";

Goal "finite r ==> wf r = acyclic r";
by (blast_tac (claset() addIs [finite_acyclic_wf,wf_acyclic]) 1);
qed "wf_iff_acyclic_if_finite";


(*---------------------------------------------------------------------------
 * A relation is wellfounded iff it has no infinite descending chain
 * Cannot go into WF because it needs type nat.
 *---------------------------------------------------------------------------*)

Goalw [wf_eq_minimal RS eq_reflection]
  "wf r = (~(? f. !i. (f(Suc i),f i) : r))";
by (rtac iffI 1);
 by (rtac notI 1);
 by (etac exE 1);
 by (eres_inst_tac [("x","{w. ? i. w=f i}")] allE 1);
 by (Blast_tac 1);
by (etac swap 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (subgoal_tac "!n. nat_rec x (%i y. @z. z:Q & (z,y):r) n : Q" 1);
 by (res_inst_tac[("x","nat_rec x (%i y. @z. z:Q & (z,y):r)")]exI 1);
 by (rtac allI 1);
 by (Simp_tac 1);
 by (rtac selectI2EX 1);
  by (Blast_tac 1);
 by (Blast_tac 1);
by (rtac allI 1);
by (induct_tac "n" 1);
 by (Asm_simp_tac 1);
by (Simp_tac 1);
by (rtac selectI2EX 1);
 by (Blast_tac 1);
by (Blast_tac 1);
qed "wf_iff_no_infinite_down_chain";

(*----------------------------------------------------------------------------
 * Weakly decreasing sequences (w.r.t. some well-founded order) stabilize.
 *---------------------------------------------------------------------------*)

Goal "[| ! i. (f (Suc i), f i) : r^* |] ==> (f (i+k), f i) : r^*";
by (induct_tac "k" 1);
 by (ALLGOALS Simp_tac);
by (blast_tac (claset() addIs [rtrancl_trans]) 1);
val lemma = result();

Goal "[| ! i. (f (Suc i), f i) : r^*; wf (r^+) |] \
\     ==> ! m. f m = x --> (? i. ! k. f (m+i+k) = f (m+i))";
by (etac wf_induct 1);
by (Clarify_tac 1);
by (case_tac "? j. (f (m+j), f m) : r^+" 1);
 by (Clarify_tac 1);
 by (subgoal_tac "? i. ! k. f ((m+j)+i+k) = f ((m+j)+i)" 1);
  by (Clarify_tac 1);
  by (res_inst_tac [("x","j+i")] exI 1);
  by (asm_full_simp_tac (simpset() addsimps add_ac) 1);
 by (Blast_tac 1);
by (res_inst_tac [("x","0")] exI 1);
by (Clarsimp_tac 1);
by (dres_inst_tac [("i","m"), ("k","k")] lemma 1);
by (fast_tac (claset() addDs [rtranclE,rtrancl_into_trancl1]) 1);
val lemma = result();

Goal "[| ! i. (f (Suc i), f i) : r^*; wf (r^+) |] \
\     ==> ? i. ! k. f (i+k) = f i";
by (dres_inst_tac [("x","0")] (lemma RS spec) 1);
by Auto_tac;
qed "wf_weak_decr_stable";

(* special case: <= *)

Goal "(m, n) : pred_nat^* = (m <= n)";
by (simp_tac (simpset() addsimps [less_eq, reflcl_trancl RS sym] 
                        delsimps [reflcl_trancl]) 1);
by (arith_tac 1);
qed "le_eq";

Goal "[| ! i. f (Suc i) <= ((f i)::nat) |] ==> ? i. ! k. f (i+k) = f i";
by (res_inst_tac [("r","pred_nat")] wf_weak_decr_stable 1);
by (asm_simp_tac (simpset() addsimps [le_eq]) 1);
by (REPEAT (resolve_tac [wf_trancl,wf_pred_nat] 1));
qed "weak_decr_stable";
