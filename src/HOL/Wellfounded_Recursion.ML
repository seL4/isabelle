(*  Title:      HOL/Wellfounded_Recursion.ML
    ID:         $Id$
    Author:     Tobias Nipkow, with minor changes by Konrad Slind
    Copyright   1992  University of Cambridge/1995 TU Munich

Wellfoundedness, induction, and  recursion
*)

Goal "x = y ==> H x z = H y z";
by (Asm_simp_tac 1);
val H_cong2 = (*freeze H!*)
	      read_instantiate [("H","H")] (result());

val [prem] = Goalw [wf_def]
 "(!!P x. (ALL x. (ALL y. (y,x) : r --> P(y)) --> P(x)) ==> P(x)) ==> wf(r)";
by (Clarify_tac 1);
by (rtac prem 1);
by (assume_tac 1);
qed "wfUNIVI";

(*Restriction to domain A.  If r is well-founded over A then wf(r)*)
val [prem1,prem2] = Goalw [wf_def]
 "[| r <= A <*> A;  \
\    !!x P. [| ALL x. (ALL y. (y,x) : r --> P y) --> P x;  x:A |] ==> P x |]  \
\ ==>  wf r";
by (cut_facts_tac [prem1] 1);
by (blast_tac (claset() addIs [prem2]) 1);
qed "wfI";

val major::prems = Goalw [wf_def]
    "[| wf(r);          \
\       !!x.[| ALL y. (y,x): r --> P(y) |] ==> P(x) \
\    |]  ==>  P(a)";
by (rtac (major RS spec RS mp RS spec) 1);
by (blast_tac (claset() addIs prems) 1);
qed "wf_induct";

(*Perform induction on i, then prove the wf(r) subgoal using prems. *)
fun wf_ind_tac a prems i = 
    EVERY [res_inst_tac [("a",a)] wf_induct i,
           rename_last_tac a ["1"] (i+1),
           ares_tac prems i];

Goal "wf(r) ==> ALL x. (a,x):r --> (x,a)~:r";
by (wf_ind_tac "a" [] 1);
by (Blast_tac 1);
qed_spec_mp "wf_not_sym";

(* [| wf r;  ~Z ==> (a,x) : r;  (x,a) ~: r ==> Z |] ==> Z *)
bind_thm ("wf_asym", cla_make_elim wf_not_sym);

Goal "wf(r) ==> (a,a) ~: r";
by (blast_tac (claset() addEs [wf_asym]) 1);
qed "wf_not_refl";

(* [| wf r;  (a,a) ~: r ==> PROP W |] ==> PROP W *)
bind_thm ("wf_irrefl", make_elim wf_not_refl);

(*transitive closure of a wf relation is wf! *)
Goal "wf(r) ==> wf(r^+)";
by (stac wf_def 1);
by (Clarify_tac 1);
(*must retain the universal formula for later use!*)
by (rtac allE 1 THEN assume_tac 1);
by (etac mp 1);
by (eres_inst_tac [("a","x")] wf_induct 1);
by (blast_tac (claset() addEs [tranclE]) 1);
qed "wf_trancl";

Goal "wf (r^-1) ==> wf ((r^+)^-1)";
by (stac (trancl_converse RS sym) 1);
by (etac wf_trancl 1);
qed "wf_converse_trancl";


(*----------------------------------------------------------------------------
 * Minimal-element characterization of well-foundedness
 *---------------------------------------------------------------------------*)

Goalw [wf_def] "wf r ==> x:Q --> (EX z:Q. ALL y. (y,z):r --> y~:Q)";
by (dtac spec 1);
by (etac (mp RS spec) 1);
by (Blast_tac 1);
val lemma1 = result();

Goalw [wf_def] "(ALL Q x. x:Q --> (EX z:Q. ALL y. (y,z):r --> y~:Q)) ==> wf r";
by (Clarify_tac 1);
by (dres_inst_tac [("x", "{x. ~ P x}")] spec 1);
by (Blast_tac 1);
val lemma2 = result();

Goal "wf r = (ALL Q x. x:Q --> (EX z:Q. ALL y. (y,z):r --> y~:Q))";
by (blast_tac (claset() addSIs [lemma1, lemma2]) 1);
qed "wf_eq_minimal";

(*---------------------------------------------------------------------------
 * Wellfoundedness of subsets
 *---------------------------------------------------------------------------*)

Goal "[| wf(r);  p<=r |] ==> wf(p)";
by (full_simp_tac (simpset() addsimps [wf_eq_minimal]) 1);
by (Fast_tac 1);
qed "wf_subset";

(*---------------------------------------------------------------------------
 * Wellfoundedness of the empty relation.
 *---------------------------------------------------------------------------*)

Goal "wf({})";
by (simp_tac (simpset() addsimps [wf_def]) 1);
qed "wf_empty";
AddIffs [wf_empty];

(*---------------------------------------------------------------------------
 * Wellfoundedness of `insert'
 *---------------------------------------------------------------------------*)

Goal "wf(insert (y,x) r) = (wf(r) & (x,y) ~: r^*)";
by (rtac iffI 1);
 by (blast_tac (claset() addEs [wf_trancl RS wf_irrefl] 
	addIs [rtrancl_into_trancl1,wf_subset,impOfSubs rtrancl_mono]) 1);
by (asm_full_simp_tac (simpset() addsimps [wf_eq_minimal]) 1);
by Safe_tac;
by (EVERY1[rtac allE, assume_tac, etac impE, Blast_tac]);
by (etac bexE 1);
by (rename_tac "a" 1 THEN case_tac "a = x" 1);
 by (res_inst_tac [("x","a")]bexI 2);
  by (assume_tac 3);
 by (Blast_tac 2);
by (case_tac "y:Q" 1);
 by (Blast_tac 2);
by (res_inst_tac [("x","{z. z:Q & (z,y) : r^*}")] allE 1);
 by (assume_tac 1);
by (thin_tac "ALL Q. (EX x. x : Q) --> ?P Q" 1);	(*essential for speed*)
(*Blast_tac with new substOccur fails*)
by (best_tac (claset() addIs [rtrancl_into_rtrancl2]) 1);
qed "wf_insert";
AddIffs [wf_insert];

(*---------------------------------------------------------------------------
 * Wellfoundedness of `disjoint union'
 *---------------------------------------------------------------------------*)

(*Intuition behind this proof for the case of binary union:

  Goal: find an (R u S)-min element of a nonempty subset A.
  by case distinction:
  1. There is a step a -R-> b with a,b : A.
     Pick an R-min element z of the (nonempty) set {a:A | EX b:A. a -R-> b}.
     By definition, there is z':A s.t. z -R-> z'. Because z is R-min in the
     subset, z' must be R-min in A. Because z' has an R-predecessor, it cannot
     have an S-successor and is thus S-min in A as well.
  2. There is no such step.
     Pick an S-min element of A. In this case it must be an R-min
     element of A as well.

*)

Goal "[| ALL i:I. wf(r i); \
\        ALL i:I. ALL j:I. r i ~= r j --> Domain(r i) Int Range(r j) = {} & \
\                                         Domain(r j) Int Range(r i) = {} \
\     |] ==> wf(UN i:I. r i)";
by (asm_full_simp_tac (HOL_basic_ss addsimps [wf_eq_minimal]) 1);
by (Clarify_tac 1);
by (rename_tac "A a" 1 THEN case_tac "EX i:I. EX a:A. EX b:A. (b,a) : r i" 1);
 by (Asm_full_simp_tac 2);
 by (Best_tac 2);  (*much faster than Blast_tac*)
by (Clarify_tac 1);
by (EVERY1[dtac bspec, assume_tac,
	   eres_inst_tac [("x","{a. a:A & (EX b:A. (b,a) : r i)}")] allE]);
by (EVERY1[etac allE, etac impE]);
 by (ALLGOALS Blast_tac);
qed "wf_UN";

Goalw [Union_def]
 "[| ALL r:R. wf r; \
\    ALL r:R. ALL s:R. r ~= s --> Domain r Int Range s = {} & \
\                                 Domain s Int Range r = {} \
\ |] ==> wf(Union R)";
by (blast_tac (claset() addIs [wf_UN]) 1);
qed "wf_Union";

Goal "[| wf r; wf s; Domain r Int Range s = {}; Domain s Int Range r = {} \
\     |] ==> wf(r Un s)";
by (rtac (simplify (simpset()) (read_instantiate[("R","{r,s}")]wf_Union)) 1);
by (Blast_tac 1);
by (Blast_tac 1);
qed "wf_Un";

(*---------------------------------------------------------------------------
 * Wellfoundedness of `image'
 *---------------------------------------------------------------------------*)

Goal "[| wf r; inj f |] ==> wf(prod_fun f f ` r)";
by (asm_full_simp_tac (HOL_basic_ss addsimps [wf_eq_minimal]) 1);
by (Clarify_tac 1);
by (case_tac "EX p. f p : Q" 1);
by (eres_inst_tac [("x","{p. f p : Q}")]allE 1);
by (fast_tac (claset() addDs [injD]) 1);
by (Blast_tac 1);
qed "wf_prod_fun_image";

(*** acyclic ***)

Goalw [acyclic_def] "ALL x. (x, x) ~: r^+ ==> acyclic r";
by (assume_tac 1);
qed "acyclicI";

Goalw [acyclic_def] "wf r ==> acyclic r";
by (blast_tac (claset() addEs [wf_trancl RS wf_irrefl]) 1);
qed "wf_acyclic";

Goalw [acyclic_def] "acyclic(insert (y,x) r) = (acyclic r & (x,y) ~: r^*)";
by (simp_tac (simpset() addsimps [trancl_insert]) 1);
by (blast_tac (claset() addIs [rtrancl_trans]) 1);
qed "acyclic_insert";
AddIffs [acyclic_insert];

Goalw [acyclic_def] "acyclic(r^-1) = acyclic r";
by (simp_tac (simpset() addsimps [trancl_converse]) 1);
qed "acyclic_converse";
AddIffs [acyclic_converse];

Goalw [acyclic_def,antisym_def] "acyclic r ==> antisym(r^*)";
by (blast_tac (claset() addEs [rtranclE]
     addIs [rtrancl_into_trancl1,rtrancl_trancl_trancl]) 1);
qed "acyclic_impl_antisym_rtrancl";

(* Other direction:
acyclic = no loops
antisym = only self loops
Goalw [acyclic_def,antisym_def] "antisym(r^* ) ==> acyclic(r - Id)";
==> "antisym(r^* ) = acyclic(r - Id)";
*)

Goalw [acyclic_def] "[| acyclic s; r <= s |] ==> acyclic r";
by (blast_tac (claset() addIs [trancl_mono]) 1);
qed "acyclic_subset";

(** cut **)

(*This rewrite rule works upon formulae; thus it requires explicit use of
  H_cong to expose the equality*)
Goalw [cut_def] "(cut f r x = cut g r x) = (ALL y. (y,x):r --> f(y)=g(y))";
by (simp_tac (HOL_ss addsimps [expand_fun_eq]) 1);
qed "cuts_eq";

Goalw [cut_def] "(x,a):r ==> (cut f r a)(x) = f(x)";
by (asm_simp_tac HOL_ss 1);
qed "cut_apply";

(*** Inductive characterization of wfrec combinator; for details see:   ***)
(*** John Harrison, "Inductive definitions: automation and application" ***)

Goalw [adm_wf_def]
  "[| adm_wf R F; wf R |] ==> EX! y. (x, y) : wfrec_rel R F";
by (wf_ind_tac "x" [] 1);
by (rtac ex1I 1);
by (res_inst_tac [("g","%x. THE y. (x, y) : wfrec_rel R F")] wfrec_rel.wfrecI 1);
by (fast_tac (claset() addSDs [theI']) 1); 
by (etac wfrec_rel.elim 1);
by (Asm_full_simp_tac 1);
byev [etac allE 1, etac allE 1, etac allE 1, etac mp 1];
by (fast_tac (claset() addIs [the_equality RS sym]) 1);
qed "wfrec_unique";

Goalw [adm_wf_def] "adm_wf R (%f x. F (cut f R x) x)";
by (strip_tac 1);
by (rtac (cuts_eq RS iffD2 RS subst) 1);
by (atac 1);
by (rtac refl 1);
qed "adm_lemma";

Goalw [wfrec_def]
    "wf(r) ==> wfrec r H a = H (cut (wfrec r H) r a) a";
by (rtac (adm_lemma RS wfrec_unique RS the1_equality) 1);
by (atac 1);
by (rtac wfrec_rel.wfrecI 1);
by (strip_tac 1);
by (etac (adm_lemma RS wfrec_unique RS theI') 1);
qed "wfrec";


(*---------------------------------------------------------------------------
 * This form avoids giant explosions in proofs.  NOTE USE OF == 
 *---------------------------------------------------------------------------*)
Goal "[| f==wfrec r H;  wf(r) |] ==> f(a) = H (cut f r a) a";
by Auto_tac;
by (blast_tac (claset() addIs [wfrec]) 1);   
qed "def_wfrec";


(**** TFL variants ****)

Goal "ALL R. wf R --> \
\      (ALL P. (ALL x. (ALL y. (y,x):R --> P y) --> P x) --> (ALL x. P x))";
by (Clarify_tac 1);
by (res_inst_tac [("r","R"),("P","P"), ("a","x")] wf_induct 1);
by (assume_tac 1);
by (Blast_tac 1);
qed"tfl_wf_induct";

Goal "ALL f R. (x,a):R --> (cut f R a)(x) = f(x)";
by (Clarify_tac 1);
by (rtac cut_apply 1);
by (assume_tac 1);
qed"tfl_cut_apply";

Goal "ALL M R f. (f=wfrec R M) --> wf R --> (ALL x. f x = M (cut f R x) x)";
by (Clarify_tac 1);
by (etac wfrec 1);
qed "tfl_wfrec";

(*LEAST and wellorderings*)
(* ### see also wf_linord_ex_has_least and its consequences in Wellfounded_Relations.ML *)

Goal "P (k::'a::wellorder) --> P (LEAST x. P(x)) & (LEAST x. P(x)) <= k";
by (res_inst_tac [("a","k")] (wf RS wf_induct) 1);
by (rtac impI 1);
by (rtac classical 1);
by (res_inst_tac [("s","x")] (Least_equality RS ssubst) 1);
by Auto_tac;
by (auto_tac (claset(), simpset() addsimps [linorder_not_less RS sym]));  
by (blast_tac (claset() addIs [order_less_trans]) 1);
bind_thm("wellorder_LeastI",   result() RS mp RS conjunct1);
bind_thm("wellorder_Least_le", result() RS mp RS conjunct2);

Goal "[| k < (LEAST x. P x) |] ==> ~P (k::'a::wellorder)";
by (full_simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (etac contrapos_nn 1);
by (etac wellorder_Least_le 1);
qed "wellorder_not_less_Least";

