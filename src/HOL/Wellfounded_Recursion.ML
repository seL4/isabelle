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
by (rename_tac "a" 1);
by (case_tac "a = x" 1);
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
by (rename_tac "A a" 1);
by (case_tac "EX i:I. EX a:A. EX b:A. (b,a) : r i" 1);
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
by(blast_tac (claset() addEs [rtranclE]
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

(*** is_recfun ***)

Goalw [is_recfun_def,cut_def]
    "[| is_recfun r H a f;  ~(b,a):r |] ==> f(b) = arbitrary";
by (etac ssubst 1);
by (asm_simp_tac HOL_ss 1);
qed "is_recfun_undef";

(*** NOTE! some simplifications need a different Solver!! ***)
fun indhyp_tac hyps =
    (cut_facts_tac hyps THEN'
       DEPTH_SOLVE_1 o (ares_tac [TrueI] ORELSE'
                        eresolve_tac [transD, mp, allE]));
val wf_super_ss = HOL_ss addSolver (mk_solver "WF" indhyp_tac);

Goalw [is_recfun_def,cut_def]
    "[| wf(r);  trans(r);  is_recfun r H a f;  is_recfun r H b g |] ==> \
    \ (x,a):r --> (x,b):r --> f(x)=g(x)";
by (etac wf_induct 1);
by (REPEAT (rtac impI 1 ORELSE etac ssubst 1));
by (asm_simp_tac (wf_super_ss addcongs [if_cong]) 1);
qed_spec_mp "is_recfun_equal";


val prems as [wfr,transr,recfa,recgb,_] = goalw (the_context ()) [cut_def]
    "[| wf(r);  trans(r); \
\       is_recfun r H a f;  is_recfun r H b g;  (b,a):r |] ==> \
\    cut f r b = g";
val gundef = recgb RS is_recfun_undef
and fisg   = recgb RS (recfa RS (transr RS (wfr RS is_recfun_equal)));
by (cut_facts_tac prems 1);
by (rtac ext 1);
by (asm_simp_tac (wf_super_ss addsimps [gundef,fisg]) 1);
qed "is_recfun_cut";

(*** Main Existence Lemma -- Basic Properties of the_recfun ***)

Goalw [the_recfun_def]
    "is_recfun r H a f ==> is_recfun r H a (the_recfun r H a)";
by (eres_inst_tac [("P", "is_recfun r H a")] someI 1);
qed "is_the_recfun";

Goal "[| wf(r);  trans(r) |] ==> is_recfun r H a (the_recfun r H a)";
by (wf_ind_tac "a" [] 1);
by (res_inst_tac [("f","cut (%y. H (the_recfun r H y) y) r a1")]
                 is_the_recfun 1);
by (rewtac is_recfun_def);
by (stac cuts_eq 1);
by (Clarify_tac 1);
by (rtac H_cong2 1);
by (subgoal_tac
         "the_recfun r H y = cut(%x. H(cut(the_recfun r H y) r x) x) r y" 1);
 by (Blast_tac 2);
by (etac ssubst 1);
by (simp_tac (HOL_ss addsimps [cuts_eq]) 1);
by (Clarify_tac 1);
by (stac cut_apply 1);
 by (fast_tac (claset() addDs [transD]) 1);
by (fold_tac [is_recfun_def]);
by (asm_simp_tac (wf_super_ss addsimps[is_recfun_cut]) 1);
qed "unfold_the_recfun";

Goal "[| wf r; trans r; (x,a) : r; (x,b) : r |] \
\     ==> the_recfun r H a x = the_recfun r H b x";
by (best_tac (claset() addIs [is_recfun_equal, unfold_the_recfun]) 1);
qed "the_recfun_equal";

(** Removal of the premise trans(r) **)
val th = rewrite_rule[is_recfun_def]
                     (trans_trancl RSN (2,(wf_trancl RS unfold_the_recfun)));

Goalw [wfrec_def]
    "wf(r) ==> wfrec r H a = H (cut (wfrec r H) r a) a";
by (rtac H_cong2 1);
by (simp_tac (HOL_ss addsimps [cuts_eq]) 1);
by (rtac allI 1);
by (rtac impI 1);
by (res_inst_tac [("a1","a")] (th RS ssubst) 1);
by (assume_tac 1);
by (ftac wf_trancl 1);
by (ftac r_into_trancl 1);
by (asm_simp_tac (HOL_ss addsimps [cut_apply]) 1);
by (rtac H_cong2 1);    (*expose the equality of cuts*)
by (simp_tac (HOL_ss addsimps [cuts_eq, cut_apply, r_into_trancl]) 1);
by (blast_tac (claset() addIs [the_recfun_equal, transD, trans_trancl, 
			       r_into_trancl]) 1);
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
