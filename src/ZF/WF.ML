(*  Title:      ZF/WF.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Lawrence C Paulson
    Copyright   1998  University of Cambridge

Well-founded Recursion

Derived first for transitive relations, and finally for arbitrary WF relations
via wf_trancl and trans_trancl.

It is difficult to derive this general case directly, using r^+ instead of
r.  In is_recfun, the two occurrences of the relation must have the same
form.  Inserting r^+ in the_recfun or wftrec yields a recursion rule with
r^+ -`` {a} instead of r-``{a}.  This recursion rule is stronger in
principle, but harder to use, especially to prove wfrec_eclose_eq in
epsilon.ML.  Expanding out the definition of wftrec in wfrec would yield
a mess.
*)


(*** Well-founded relations ***)

(** Equivalences between wf and wf_on **)

Goalw [wf_def, wf_on_def] "wf(r) ==> wf[A](r)";
by (Clarify_tac 1);  (*essential for Blast_tac's efficiency*)
by (Blast_tac 1);
qed "wf_imp_wf_on";

Goalw [wf_def, wf_on_def] "wf[field(r)](r) ==> wf(r)";
by (Fast_tac 1);
qed "wf_on_field_imp_wf";

Goal "wf(r) <-> wf[field(r)](r)";
by (blast_tac (claset() addIs [wf_imp_wf_on, wf_on_field_imp_wf]) 1);
qed "wf_iff_wf_on_field";

Goalw [wf_on_def, wf_def] "[| wf[A](r);  B<=A |] ==> wf[B](r)";
by (Fast_tac 1);
qed "wf_on_subset_A";

Goalw [wf_on_def, wf_def] "[| wf[A](r);  s<=r |] ==> wf[A](s)";
by (Fast_tac 1);
qed "wf_on_subset_r";

(** Introduction rules for wf_on **)

(*If every non-empty subset of A has an r-minimal element then wf[A](r).*)
val [prem] = Goalw [wf_on_def, wf_def]
    "[| !!Z u. [| Z<=A;  u:Z;  ALL x:Z. EX y:Z. <y,x>:r |] ==> False |] \
\    ==>  wf[A](r)";
by (rtac (equals0I RS disjCI RS allI) 1);
by (res_inst_tac [ ("Z", "Z") ] prem 1);
by (ALLGOALS Blast_tac);
qed "wf_onI";

(*If r allows well-founded induction over A then wf[A](r)
  Premise is equivalent to 
  !!B. ALL x:A. (ALL y. <y,x>: r --> y:B) --> x:B ==> A<=B  *)
val [prem] = Goal
    "[| !!y B. [| ALL x:A. (ALL y:A. <y,x>:r --> y:B) --> x:B;   y:A |]   \
\              ==> y:B |] \
\    ==>  wf[A](r)";
by (rtac wf_onI 1);
by (res_inst_tac [ ("c", "u") ] (prem RS DiffE) 1);
by (contr_tac 3);
by (Blast_tac 2);
by (Fast_tac 1);
qed "wf_onI2";


(** Well-founded Induction **)

(*Consider the least z in domain(r) Un {a} such that P(z) does not hold...*)
val [major,minor] = Goalw [wf_def]
    "[| wf(r);          \
\       !!x.[| ALL y. <y,x>: r --> P(y) |] ==> P(x) \
\    |]  ==>  P(a)";
by (res_inst_tac [ ("x", "{z:domain(r) Un {a}. ~P(z)}") ]  (major RS allE) 1);
by (etac disjE 1);
by (blast_tac (claset() addEs [equalityE]) 1);
by (asm_full_simp_tac (simpset() addsimps [domainI]) 1);
by (blast_tac (claset() addSDs [minor]) 1);
qed "wf_induct";

(*Perform induction on i, then prove the wf(r) subgoal using prems. *)
fun wf_ind_tac a prems i = 
    EVERY [res_inst_tac [("a",a)] wf_induct i,
           rename_last_tac a ["1"] (i+1),
           ares_tac prems i];

(*The form of this rule is designed to match wfI*)
val wfr::amem::prems = Goal
    "[| wf(r);  a:A;  field(r)<=A;  \
\       !!x.[| x: A;  ALL y. <y,x>: r --> P(y) |] ==> P(x) \
\    |]  ==>  P(a)";
by (rtac (amem RS rev_mp) 1);
by (wf_ind_tac "a" [wfr] 1);
by (rtac impI 1);
by (eresolve_tac prems 1);
by (blast_tac (claset() addIs (prems RL [subsetD])) 1);
qed "wf_induct2";

Goal "field(r Int A*A) <= A";
by (Blast_tac 1);
qed "field_Int_square";

val wfr::amem::prems = Goalw [wf_on_def]
    "[| wf[A](r);  a:A;                                         \
\       !!x.[| x: A;  ALL y:A. <y,x>: r --> P(y) |] ==> P(x)    \
\    |]  ==>  P(a)";
by (rtac ([wfr, amem, field_Int_square] MRS wf_induct2) 1);
by (REPEAT (ares_tac prems 1));
by (Blast_tac 1);
qed "wf_on_induct";

fun wf_on_ind_tac a prems i = 
    EVERY [res_inst_tac [("a",a)] wf_on_induct i,
           rename_last_tac a ["1"] (i+2),
           REPEAT (ares_tac prems i)];

(*If r allows well-founded induction then wf(r)*)
val [subs,indhyp] = Goal
    "[| field(r)<=A;  \
\       !!y B. [| ALL x:A. (ALL y:A. <y,x>:r --> y:B) --> x:B;  y:A|]  \
\              ==> y:B |] \
\    ==>  wf(r)";
by (rtac ([wf_onI2, subs] MRS (wf_on_subset_A RS wf_on_field_imp_wf)) 1);
by (REPEAT (ares_tac [indhyp] 1));
qed "wfI";


(*** Properties of well-founded relations ***)

Goal "wf(r) ==> <a,a> ~: r";
by (wf_ind_tac "a" [] 1);
by (Blast_tac 1);
qed "wf_not_refl";

Goal "wf(r) ==> ALL x. <a,x>:r --> <x,a> ~: r";
by (wf_ind_tac "a" [] 1);
by (Blast_tac 1);
qed_spec_mp "wf_not_sym";

(* [| wf(r);  <a,x> : r;  ~P ==> <x,a> : r |] ==> P *)
bind_thm ("wf_asym", wf_not_sym RS swap);

Goal "[| wf[A](r); a: A |] ==> <a,a> ~: r";
by (wf_on_ind_tac "a" [] 1);
by (Blast_tac 1);
qed "wf_on_not_refl";

Goal "[| wf[A](r);  a:A;  b:A |] ==> <a,b>:r --> <b,a>~:r";
by (res_inst_tac [("x","b")] bspec 1);
by (assume_tac 2);
by (wf_on_ind_tac "a" [] 1);
by (Blast_tac 1);
qed_spec_mp "wf_on_not_sym";

(* [| wf[A](r); ~Z ==> <a,b> : r;
      <b,a> ~: r ==> Z; ~Z ==> a : A; ~Z ==> b : A |] ==> Z *)
bind_thm ("wf_on_asym", permute_prems 1 2 (cla_make_elim wf_on_not_sym));

(*Needed to prove well_ordI.  Could also reason that wf[A](r) means
  wf(r Int A*A);  thus wf( (r Int A*A)^+ ) and use wf_not_refl *)
Goal "[| wf[A](r); <a,b>:r; <b,c>:r; <c,a>:r; a:A; b:A; c:A |] ==> P";
by (subgoal_tac "ALL y:A. ALL z:A. <a,y>:r --> <y,z>:r --> <z,a>:r --> P" 1);
by (wf_on_ind_tac "a" [] 2);
by (Blast_tac 2);
by (Blast_tac 1);
qed "wf_on_chain3";


(*retains the universal formula for later use!*)
val bchain_tac = EVERY' [rtac (bspec RS mp), assume_tac, assume_tac ];

(*transitive closure of a WF relation is WF provided A is downwards closed*)
val [wfr,subs] = goal (the_context ())
    "[| wf[A](r);  r-``A <= A |] ==> wf[A](r^+)";
by (rtac wf_onI2 1);
by (bchain_tac 1);
by (eres_inst_tac [("a","y")] (wfr RS wf_on_induct) 1);
by (cut_facts_tac [subs] 1);
by (blast_tac (claset() addEs [tranclE]) 1);
qed "wf_on_trancl";

Goal "wf(r) ==> wf(r^+)";
by (asm_full_simp_tac (simpset() addsimps [wf_iff_wf_on_field]) 1);
by (rtac (trancl_type RS field_rel_subset RSN (2, wf_on_subset_A)) 1);
by (etac wf_on_trancl 1);
by (Blast_tac 1);
qed "wf_trancl";



(** r-``{a} is the set of everything under a in r **)

bind_thm ("underI", vimage_singleton_iff RS iffD2);
bind_thm ("underD", vimage_singleton_iff RS iffD1);

(** is_recfun **)

Goalw [is_recfun_def] "is_recfun(r,a,H,f) ==> f: r-``{a} -> range(f)";
by (etac ssubst 1);
by (rtac (lamI RS rangeI RS lam_type) 1);
by (assume_tac 1);
qed "is_recfun_type";

val [isrec,rel] = goalw (the_context ()) [is_recfun_def]
    "[| is_recfun(r,a,H,f); <x,a>:r |] ==> f`x = H(x, restrict(f,r-``{x}))";
by (res_inst_tac [("P", "%x.?t(x) = (?u::i)")] (isrec RS ssubst) 1);
by (rtac (rel RS underI RS beta) 1);
qed "apply_recfun";

Goal "[| wf(r);  trans(r);  is_recfun(r,a,H,f);  is_recfun(r,b,H,g) |]  \
\     ==> <x,a>:r --> <x,b>:r --> f`x=g`x";
by (forw_inst_tac [("f","f")] is_recfun_type 1); 
by (forw_inst_tac [("f","g")] is_recfun_type 1); 
by (asm_full_simp_tac (simpset() addsimps [is_recfun_def]) 1); 
by (wf_ind_tac "x" [] 1);
by (REPEAT (rtac impI 1 ORELSE etac ssubst 1));
by (asm_simp_tac (simpset() addsimps [vimage_singleton_iff, restrict_def]) 1); 
by (res_inst_tac [("t","%z. H(?x,z)")] subst_context 1); 
by (subgoal_tac "ALL y : r-``{x1}. ALL z. <y,z>:f <-> <y,z>:g" 1);
 by (blast_tac (claset() addDs [transD]) 1); 
by (asm_full_simp_tac (simpset() addsimps [apply_iff]) 1); 
by (blast_tac (claset() addDs [transD] addIs [sym]) 1); 
qed_spec_mp "is_recfun_equal";

Goal "[| wf(r);  trans(r);       \
\        is_recfun(r,a,H,f);  is_recfun(r,b,H,g);  <b,a>:r |]  \
\     ==> restrict(f, r-``{b}) = g";
by (forw_inst_tac [("f","f")] is_recfun_type 1); 
by (rtac fun_extension 1);
  by (blast_tac (claset() addDs [transD] addIs [restrict_type2]) 1); 
 by (etac is_recfun_type 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addDs [transD]
			addIs [is_recfun_equal]) 1);
qed "is_recfun_cut";

(*** Main Existence Lemma ***)

Goal "[| wf(r); trans(r); is_recfun(r,a,H,f); is_recfun(r,a,H,g) |]  ==>  f=g";
by (blast_tac (claset() addIs [fun_extension, is_recfun_type, 
                               is_recfun_equal]) 1); 
qed "is_recfun_functional";

(*If some f satisfies is_recfun(r,a,H,-) then so does the_recfun(r,a,H) *)
Goalw [the_recfun_def]
    "[| is_recfun(r,a,H,f);  wf(r);  trans(r) |]  \
\    ==> is_recfun(r, a, H, the_recfun(r,a,H))";
by (rtac (ex1I RS theI) 1);
by (REPEAT (ares_tac [is_recfun_functional] 1));
qed "is_the_recfun";

Goal "[| wf(r);  trans(r) |] ==> is_recfun(r, a, H, the_recfun(r,a,H))";
by (wf_ind_tac "a" [] 1);
by (res_inst_tac [("f", "lam y: r-``{a1}. wftrec(r,y,H)")] is_the_recfun 1);
by (REPEAT (assume_tac 2));
by (rewrite_goals_tac [is_recfun_def, wftrec_def]);
(*Applying the substitution: must keep the quantified assumption!!*)
by (REPEAT (dtac underD 1 ORELSE resolve_tac [refl, lam_cong] 1));
by (fold_tac [is_recfun_def]);
by (res_inst_tac [("t","%z. H(?x,z)")] subst_context 1); 
by (rtac fun_extension 1);
  by (blast_tac (claset() addIs [is_recfun_type]) 1);
 by (rtac (lam_type RS restrict_type2) 1); 
  by (Blast_tac 1); 
 by (blast_tac (claset() addDs [transD]) 1); 
by (ftac (spec RS mp) 1 THEN assume_tac 1);
by (subgoal_tac "<xa,a1> : r" 1);
by (dres_inst_tac [("x1","xa")] (spec RS mp) 1 THEN assume_tac 1);
by (asm_full_simp_tac
     (simpset() addsimps [vimage_singleton_iff, underI RS beta, apply_recfun, 
                          is_recfun_cut]) 1);
by (blast_tac (claset() addDs [transD]) 1);
qed "unfold_the_recfun";


(*** Unfolding wftrec ***)

Goal "[| wf(r);  trans(r);  <b,a>:r |] ==> \
\     restrict(the_recfun(r,a,H), r-``{b}) = the_recfun(r,b,H)";
by (REPEAT (ares_tac [is_recfun_cut, unfold_the_recfun] 1));
qed "the_recfun_cut";

(*NOT SUITABLE FOR REWRITING: it is recursive!*)
Goalw [wftrec_def]
    "[| wf(r);  trans(r) |] ==> \
\         wftrec(r,a,H) = H(a, lam x: r-``{a}. wftrec(r,x,H))";
by (stac (rewrite_rule [is_recfun_def] unfold_the_recfun) 1);
by (ALLGOALS 
    (asm_simp_tac
     (simpset() addsimps [vimage_singleton_iff RS iff_sym, the_recfun_cut])));
qed "wftrec";

(** Removal of the premise trans(r) **)

(*NOT SUITABLE FOR REWRITING: it is recursive!*)
val [wfr] = goalw (the_context ()) [wfrec_def]
    "wf(r) ==> wfrec(r,a,H) = H(a, lam x:r-``{a}. wfrec(r,x,H))";
by (stac (wfr RS wf_trancl RS wftrec) 1);
by (rtac trans_trancl 1);
by (rtac (vimage_pair_mono RS restrict_lam_eq RS subst_context) 1);
by (etac r_into_trancl 1);
by (rtac subset_refl 1);
qed "wfrec";

(*This form avoids giant explosions in proofs.  NOTE USE OF == *)
val rew::prems = Goal
    "[| !!x. h(x)==wfrec(r,x,H);  wf(r) |] ==> \
\    h(a) = H(a, lam x: r-``{a}. h(x))";
by (rewtac rew);
by (REPEAT (resolve_tac (prems@[wfrec]) 1));
qed "def_wfrec";

val prems = Goal
    "[| wf(r);  a:A;  field(r)<=A;  \
\       !!x u. [| x: A;  u: Pi(r-``{x}, B) |] ==> H(x,u) : B(x)   \
\    |] ==> wfrec(r,a,H) : B(a)";
by (res_inst_tac [("a","a")] wf_induct2 1);
by (stac wfrec 4);
by (REPEAT (ares_tac (prems@[lam_type]) 1
     ORELSE eresolve_tac [spec RS mp, underD] 1));
qed "wfrec_type";


Goalw [wf_on_def, wfrec_on_def]
 "[| wf[A](r);  a: A |] ==> \
\        wfrec[A](r,a,H) = H(a, lam x: (r-``{a}) Int A. wfrec[A](r,x,H))";
by (etac (wfrec RS trans) 1);
by (asm_simp_tac (simpset() addsimps [vimage_Int_square, cons_subset_iff]) 1);
qed "wfrec_on";

(*Minimal-element characterization of well-foundedness*)
Goalw [wf_def] 
     "wf(r) <-> (ALL Q x. x:Q --> (EX z:Q. ALL y. <y,z>:r --> y~:Q))";
by (Blast_tac 1);
qed "wf_eq_minimal";

