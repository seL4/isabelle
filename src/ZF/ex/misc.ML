(*  Title:      ZF/ex/misc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Miscellaneous examples for Zermelo-Fraenkel Set Theory 
Composition of homomorphisms, Pastre's examples, ...
*)

writeln"ZF/ex/misc";

(*These two are cited in Benzmueller and Kohlhash's system description of LEO,
  CADE-15, 1998 (page 139-143) as theorems LEO could not prove.*)

Goal "(X = Y Un Z) <-> (Y<=X & Z<=X & (ALL V. Y<=V & Z<=V --> X<=V))";
by (blast_tac (claset() addSIs [equalityI]) 1);
result();

(*the dual of the previous one*)
Goal "(X = Y Int Z) <-> (X<=Y & X<=Z & (ALL V. V<=Y & V<=Z --> V<=X))";
by (blast_tac (claset() addSIs [equalityI]) 1);
result();

(*trivial example of term synthesis: apparently hard for some provers!*)
Goal "a ~= b ==> a:?X & b ~: ?X";
by (Blast_tac 1);
result();

(*Nice Blast_tac benchmark.  Proved in 0.3s; old tactics can't manage it!*)
Goal "ALL x:S. ALL y:S. x<=y ==> EX z. S <= {z}";
by (Blast_tac 1);
result();

(*variant of the benchmark above*)
Goal "ALL x:S. Union(S) <= x ==> EX z. S <= {z}";
by (Blast_tac 1);
result();

context Perm.thy;

(*Example 12 (credited to Peter Andrews) from
 W. Bledsoe.  A Maximal Method for Set Variables in Automatic Theorem-proving.
 In: J. Hayes and D. Michie and L. Mikulich, eds.  Machine Intelligence 9.
 Ellis Horwood, 53-100 (1979). *)
Goal "(ALL F. {x}: F --> {y}:F) --> (ALL A. x:A --> y:A)";
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
by (asm_simp_tac (simpset() setloop (K Safe_tac)) 1);
val comp_homs = result();

(*This version uses meta-level rewriting, safe_tac and asm_simp_tac*)
val [hom_def] = goal Perm.thy
    "(!! A f B g. hom(A,f,B,g) == \
\          {H: A->B. f:A*A->A & g:B*B->B & \
\                    (ALL x:A. ALL y:A. H`(f`<x,y>) = g`<H`x,H`y>)}) ==> \
\    J : hom(A,f,B,g) & K : hom(B,g,C,h) -->  \
\    (K O J) : hom(A,f,C,h)";
by (rewtac hom_def);
by Safe_tac;
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
qed "comp_homs";


(** A characterization of functions, suggested by Tobias Nipkow **)

Goalw [Pi_def, function_def]
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
(*Auto_tac no longer proves it*)
by (REPEAT (fast_tac (claset() addss (simpset())) 1));
qed "Pow_sum_bij";

(*As a special case, we have  bij(Pow(A*B), A -> Pow B)  *)
goal Perm.thy
    "(lam r:Pow(Sigma(A,B)). lam x:A. r``{x}) \
\    : bij(Pow(Sigma(A,B)), PROD x:A. Pow(B(x)))";
by (res_inst_tac [("d", "%f. UN x:A. UN y:f`x. {<x,y>}")] lam_bijective 1);
by (blast_tac (claset() addDs [apply_type]) 2);
by (blast_tac (claset() addIs [lam_type]) 1);
by (ALLGOALS Asm_simp_tac);
by (Fast_tac 1);
by (rtac fun_extension 1);
by (assume_tac 2);
by (rtac (singletonI RS lam_type) 1);
by (Asm_simp_tac 1);
by (Blast_tac 1);
qed "Pow_Sigma_bij";

writeln"Reached end of file.";
