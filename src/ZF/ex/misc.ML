(*  Title:      ZF/ex/misc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Miscellaneous examples for Zermelo-Fraenkel Set Theory 
Composition of homomorphisms, Pastre's examples, ...
*)

writeln"ZF/ex/misc";

set_current_thy"Perm";

(*Example 12 (credited to Peter Andrews) from
 W. Bledsoe.  A Maximal Method for Set Variables in Automatic Theorem-proving.
 In: J. Hayes and D. Michie and L. Mikulich, eds.  Machine Intelligence 9.
 Ellis Horwood, 53-100 (1979). *)
goal thy "(ALL F. {x}: F --> {y}:F) --> (ALL A. x:A --> y:A)";
by (Best_tac 1);
result();


(*** Composition of homomorphisms is a homomorphism ***)

(*Given as a challenge problem in
  R. Boyer et al.,
  Set Theory in First-Order Logic: Clauses for G\"odel's Axioms,
  JAR 2 (1986), 287-327 
*)

(*collecting the relevant lemmas*)
Addsimps [comp_fun, SigmaI, apply_funtype];

(*This version uses a super application of simp_tac.  Needs setloop to help
  proving conditions of rewrites such as comp_fun_apply;
  rewriting does not instantiate Vars*)
goal Perm.thy
    "(ALL A f B g. hom(A,f,B,g) = \
\          {H: A->B. f:A*A->A & g:B*B->B & \
\                    (ALL x:A. ALL y:A. H`(f`<x,y>) = g`<H`x,H`y>)}) --> \
\    J : hom(A,f,B,g) & K : hom(B,g,C,h) -->  \
\    (K O J) : hom(A,f,C,h)";
by (asm_simp_tac (!simpset setloop (K (safe_tac (!claset)))) 1);
val comp_homs = result();

(*This version uses meta-level rewriting, safe_tac and asm_simp_tac*)
val [hom_def] = goal Perm.thy
    "(!! A f B g. hom(A,f,B,g) == \
\          {H: A->B. f:A*A->A & g:B*B->B & \
\                    (ALL x:A. ALL y:A. H`(f`<x,y>) = g`<H`x,H`y>)}) ==> \
\    J : hom(A,f,B,g) & K : hom(B,g,C,h) -->  \
\    (K O J) : hom(A,f,C,h)";
by (rewtac hom_def);
by (safe_tac (!claset));
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
qed "comp_homs";


(** A characterization of functions, suggested by Tobias Nipkow **)

goalw thy [Pi_def, function_def]
    "r: domain(r)->B  <->  r <= domain(r)*B & (ALL X. r `` (r -`` X) <= X)";
by (Best_tac 1);
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
    forw_iterate (prems @ [comp_surj, comp_inj, comp_fun])
               pastre_rls [fact1,fact2,fact3] 4;

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): inj(A,A);          \
\       (f O h O g): surj(B,B);         \
\       (g O f O h): surj(C,C);         \
\       f: A->B;  g: B->C;  h: C->A |] ==> h: bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
qed "pastre1";

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): surj(A,A);         \
\       (f O h O g): inj(B,B);          \
\       (g O f O h): surj(C,C);         \
\       f: A->B;  g: B->C;  h: C->A |] ==> h: bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
qed "pastre2";

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): surj(A,A);         \
\       (f O h O g): surj(B,B);         \
\       (g O f O h): inj(C,C);          \
\       f: A->B;  g: B->C;  h: C->A |] ==> h: bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
qed "pastre3";

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): surj(A,A);         \
\       (f O h O g): inj(B,B);          \
\       (g O f O h): inj(C,C);          \
\       f: A->B;  g: B->C;  h: C->A |] ==> h: bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
qed "pastre4";

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): inj(A,A);          \
\       (f O h O g): surj(B,B);         \
\       (g O f O h): inj(C,C);          \
\       f: A->B;  g: B->C;  h: C->A |] ==> h: bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
qed "pastre5";

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): inj(A,A);          \
\       (f O h O g): inj(B,B);          \
\       (g O f O h): surj(C,C);         \
\       f: A->B;  g: B->C;  h: C->A |] ==> h: bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
qed "pastre6";

(** Yet another example... **)

goal Perm.thy
    "(lam Z:Pow(A+B). <{x:A. Inl(x):Z}, {y:B. Inr(y):Z}>) \
\    : bij(Pow(A+B), Pow(A)*Pow(B))";
by (res_inst_tac [("d", "%<X,Y>.{Inl(x).x:X} Un {Inr(y).y:Y}")] 
    lam_bijective 1);
by (TRYALL (etac SigmaE));
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (fast_tac (!claset addSIs [equalityI])));
val Pow_bij = result();

writeln"Reached end of file.";
