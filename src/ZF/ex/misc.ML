(*  Title: 	ZF/ex/misc
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Miscellaneous examples for Zermelo-Fraenkel Set Theory 
Cantor's Theorem; Schroeder-Bernstein Theorem; Composition of homomorphisms...
*)

writeln"ZF/ex/misc";


(*Example 12 (credited to Peter Andrews) from
 W. Bledsoe.  A Maximal Method for Set Variables in Automatic Theorem-proving.
 In: J. Hayes and D. Michie and L. Mikulich, eds.  Machine Intelligence 9.
 Ellis Horwood, 53-100 (1979). *)
goal ZF.thy "(ALL F. {x}: F --> {y}:F) --> (ALL A. x:A --> y:A)";
by (best_tac ZF_cs 1);
result();


(*** Cantor's Theorem: There is no surjection from a set to its powerset. ***)

val cantor_cs = FOL_cs   (*precisely the rules needed for the proof*)
  addSIs [ballI, CollectI, PowI, subsetI] addIs [bexI]
  addSEs [CollectE, equalityCE];

(*The search is undirected and similar proof attempts fail*)
goal ZF.thy "ALL f: A->Pow(A). EX S: Pow(A). ALL x:A. f`x ~= S";
by (best_tac cantor_cs 1);
result();

(*This form displays the diagonal term, {x: A . x ~: f`x} *)
val [prem] = goal ZF.thy
    "f: A->Pow(A) ==> (ALL x:A. f`x ~= ?S) & ?S: Pow(A)";
by (best_tac cantor_cs 1);
result();

(*yet another version...*)
goalw Perm.thy [surj_def] "f ~: surj(A,Pow(A))";
by (safe_tac ZF_cs);
by (etac ballE 1);
by (best_tac (cantor_cs addSEs [bexE]) 1);
by (fast_tac ZF_cs 1);
result();


(**** The Schroeder-Bernstein Theorem -- see Davey & Priestly, page 106 ****)

val SB_thy = merge_theories (Fixedpt.thy, Perm.thy);

(** Lemma: Banach's Decomposition Theorem **)

goal SB_thy "bnd_mono(X, %W. X - g``(Y - f``W))";
by (rtac bnd_monoI 1);
by (REPEAT (ares_tac [Diff_subset, subset_refl, Diff_mono, image_mono] 1));
val decomp_bnd_mono = result();

val [gfun] = goal SB_thy
    "g: Y->X ==>   					\
\    g``(Y - f`` lfp(X, %W. X - g``(Y - f``W))) = 	\
\    X - lfp(X, %W. X - g``(Y - f``W)) ";
by (res_inst_tac [("P", "%u. ?v = X-u")] 
     (decomp_bnd_mono RS lfp_Tarski RS ssubst) 1);
by (simp_tac (ZF_ss addsimps [subset_refl, double_complement,
			     gfun RS fun_is_rel RS image_subset]) 1);
val Banach_last_equation = result();

val prems = goal SB_thy
    "[| f: X->Y;  g: Y->X |] ==>   \
\    EX XA XB YA YB. (XA Int XB = 0) & (XA Un XB = X) &    \
\                    (YA Int YB = 0) & (YA Un YB = Y) &    \
\                    f``XA=YA & g``YB=XB";
by (REPEAT 
    (FIRSTGOAL
     (resolve_tac [refl, exI, conjI, Diff_disjoint, Diff_partition])));
by (rtac Banach_last_equation 3);
by (REPEAT (resolve_tac (prems@[fun_is_rel, image_subset, lfp_subset]) 1));
val decomposition = result();

val prems = goal SB_thy
    "[| f: inj(X,Y);  g: inj(Y,X) |] ==> EX h. h: bij(X,Y)";
by (cut_facts_tac prems 1);
by (cut_facts_tac [(prems RL [inj_is_fun]) MRS decomposition] 1);
by (fast_tac (ZF_cs addSIs [restrict_bij,bij_disjoint_Un]
                    addIs [bij_converse_bij]) 1);
(* The instantiation of exI to "restrict(f,XA) Un converse(restrict(g,YB))"
   is forced by the context!! *)
val schroeder_bernstein = result();


(*** Composition of homomorphisms is a homomorphism ***)

(*Given as a challenge problem in
  R. Boyer et al.,
  Set Theory in First-Order Logic: Clauses for G\"odel's Axioms,
  JAR 2 (1986), 287-327 
*)

(*collecting the relevant lemmas*)
val hom_ss = ZF_ss addsimps [comp_func,comp_func_apply,SigmaI,apply_funtype];

(*The problem below is proving conditions of rewrites such as comp_func_apply;
  rewriting does not instantiate Vars; we must prove the conditions
  explicitly.*)
fun hom_tac hyps =
    resolve_tac (TrueI::refl::iff_refl::hyps) ORELSE' 
    (cut_facts_tac hyps THEN' fast_tac prop_cs);

(*This version uses a super application of simp_tac*)
goal Perm.thy
    "(ALL A f B g. hom(A,f,B,g) = \
\          {H: A->B. f:A*A->A & g:B*B->B & \
\                    (ALL x:A. ALL y:A. H`(f`<x,y>) = g`<H`x,H`y>)}) --> \
\    J : hom(A,f,B,g) & K : hom(B,g,C,h) -->  \
\    (K O J) : hom(A,f,C,h)";
by (simp_tac (hom_ss setsolver hom_tac) 1);
(*Also works but slower:
    by (asm_simp_tac (hom_ss setloop (K (safe_tac FOL_cs))) 1); *)
val comp_homs = result();

(*This version uses meta-level rewriting, safe_tac and asm_simp_tac*)
val [hom_def] = goal Perm.thy
    "(!! A f B g. hom(A,f,B,g) == \
\          {H: A->B. f:A*A->A & g:B*B->B & \
\                    (ALL x:A. ALL y:A. H`(f`<x,y>) = g`<H`x,H`y>)}) ==> \
\    J : hom(A,f,B,g) & K : hom(B,g,C,h) -->  \
\    (K O J) : hom(A,f,C,h)";
by (rewtac hom_def);
by (safe_tac ZF_cs);
by (asm_simp_tac hom_ss 1);
by (asm_simp_tac hom_ss 1);
val comp_homs = result();


(** A characterization of functions, suggested by Tobias Nipkow **)

goalw ZF.thy [Pi_def]
    "r: domain(r)->B  <->  r <= domain(r)*B & (ALL X. r `` (r -`` X) <= X)";
by (safe_tac ZF_cs);
by (fast_tac (ZF_cs addSDs [bspec RS ex1_equalsE]) 1);
by (eres_inst_tac [("x", "{y}")] allE 1);
by (fast_tac ZF_cs 1);
result();


(**** From D Pastre.  Automatic theorem proving in set theory. 
         Artificial Intelligence, 10:1--27, 1978.
             These examples require forward reasoning! ****)

(*reduce the clauses to units by type checking -- beware of nontermination*)
fun forw_typechk tyrls [] = []
  | forw_typechk tyrls clauses =
    let val (units, others) = partition (has_fewer_prems 1) clauses
    in  gen_union eq_thm (units, forw_typechk tyrls (tyrls RL others))
    end;

(*A crude form of forward reasoning*)
fun forw_iterate tyrls rls facts 0 = facts
  | forw_iterate tyrls rls facts n =
      let val facts' = 
	  gen_union eq_thm (forw_typechk (tyrls@facts) (facts RL rls), facts);
      in  forw_iterate tyrls rls facts' (n-1)  end;

val pastre_rls =
    [comp_mem_injD1, comp_mem_surjD1, comp_mem_injD2, comp_mem_surjD2];

fun pastre_facts (fact1::fact2::fact3::prems) = 
    forw_iterate (prems @ [comp_surj, comp_inj, comp_func])
               pastre_rls [fact1,fact2,fact3] 4;

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): inj(A,A);		\
\       (f O h O g): surj(B,B); 	\
\       (g O f O h): surj(C,C); 	\
\       f: A->B;  g: B->C;  h: C->A |] ==> h: bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
val pastre1 = result();

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): surj(A,A);		\
\       (f O h O g): inj(B,B); 		\
\       (g O f O h): surj(C,C); 	\
\       f: A->B;  g: B->C;  h: C->A |] ==> h: bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
val pastre2 = result();

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): surj(A,A);		\
\       (f O h O g): surj(B,B); 	\
\       (g O f O h): inj(C,C); 		\
\       f: A->B;  g: B->C;  h: C->A |] ==> h: bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
val pastre3 = result();

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): surj(A,A);		\
\       (f O h O g): inj(B,B); 		\
\       (g O f O h): inj(C,C); 		\
\       f: A->B;  g: B->C;  h: C->A |] ==> h: bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
val pastre4 = result();

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): inj(A,A);		\
\       (f O h O g): surj(B,B); 	\
\       (g O f O h): inj(C,C); 		\
\       f: A->B;  g: B->C;  h: C->A |] ==> h: bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
val pastre5 = result();

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): inj(A,A);		\
\       (f O h O g): inj(B,B); 		\
\       (g O f O h): surj(C,C); 	\
\       f: A->B;  g: B->C;  h: C->A |] ==> h: bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
val pastre6 = result();

(** Yet another example... **)

goalw (merge_theories(Sum.thy,Perm.thy)) [bij_def,inj_def,surj_def]
    "(lam Z:Pow(A+B). <{x:A. Inl(x):Z}, {y:B. Inr(y):Z}>) \
\    : bij(Pow(A+B), Pow(A)*Pow(B))";
by (DO_GOAL
      [rtac IntI,
       DO_GOAL
	 [rtac CollectI,
	  fast_tac (ZF_cs addSIs [lam_type]),
	  simp_tac ZF_ss,
	  fast_tac (eq_cs addSEs [sumE]
			  addEs  [equalityD1 RS subsetD RS CollectD2,
				  equalityD2 RS subsetD RS CollectD2])],
       DO_GOAL
	 [rtac CollectI,
	  fast_tac (ZF_cs addSIs [lam_type]),
	  simp_tac ZF_ss,
	  K(safe_tac ZF_cs),
	  res_inst_tac [("x", "{Inl(u). u: ?U} Un {Inr(v). v: ?V}")] bexI,
	  DO_GOAL
	    [res_inst_tac [("t", "Pair")] subst_context2,
	    fast_tac (sum_cs addSIs [equalityI]),
	    fast_tac (sum_cs addSIs [equalityI])],
	  DO_GOAL [fast_tac sum_cs]]] 1);
val Pow_bij = result();

writeln"Reached end of file.";
