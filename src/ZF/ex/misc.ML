(*  Title:      ZF/ex/misc.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Miscellaneous examples for Zermelo-Fraenkel Set Theory 
Composition of homomorphisms, Pastre's examples, ...
*)

(*These two are cited in Benzmueller and Kohlhase's system description of LEO,
  CADE-15, 1998 (page 139-143) as theorems LEO could not prove.*)

Goal "(X = Y Un Z) <-> (Y \\<subseteq> X & Z \\<subseteq> X & (\\<forall>V. Y \\<subseteq> V & Z \\<subseteq> V --> X \\<subseteq> V))";
by (blast_tac (claset() addSIs [equalityI]) 1);
qed "";

(*the dual of the previous one*)
Goal "(X = Y Int Z) <-> (X \\<subseteq> Y & X \\<subseteq> Z & (\\<forall>V. V \\<subseteq> Y & V \\<subseteq> Z --> V \\<subseteq> X))";
by (blast_tac (claset() addSIs [equalityI]) 1);
qed "";

(*trivial example of term synthesis: apparently hard for some provers!*)
Goal "a \\<noteq> b ==> a:?X & b \\<notin> ?X";
by (Blast_tac 1);
qed "";

(*Nice Blast_tac benchmark.  Proved in 0.3s; old tactics can't manage it!*)
Goal "\\<forall>x \\<in> S. \\<forall>y \\<in> S. x \\<subseteq> y ==> \\<exists>z. S \\<subseteq> {z}";
by (Blast_tac 1);
qed "";

(*variant of the benchmark above*)
Goal "\\<forall>x \\<in> S. Union(S) \\<subseteq> x ==> \\<exists>z. S \\<subseteq> {z}";
by (Blast_tac 1);
qed "";

context Perm.thy;

(*Example 12 (credited to Peter Andrews) from
 W. Bledsoe.  A Maximal Method for Set Variables in Automatic Theorem-proving.
 In: J. Hayes and D. Michie and L. Mikulich, eds.  Machine Intelligence 9.
 Ellis Horwood, 53-100 (1979). *)
Goal "(\\<forall>F. {x}: F --> {y}:F) --> (\\<forall>A. x \\<in> A --> y \\<in> A)";
by (Best_tac 1);
qed "";


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
    "(\\<forall>A f B g. hom(A,f,B,g) = \
\          {H \\<in> A->B. f \\<in> A*A->A & g \\<in> B*B->B & \
\                    (\\<forall>x \\<in> A. \\<forall>y \\<in> A. H`(f`<x,y>) = g`<H`x,H`y>)}) --> \
\    J \\<in> hom(A,f,B,g) & K \\<in> hom(B,g,C,h) -->  \
\    (K O J) \\<in> hom(A,f,C,h)";
by (asm_simp_tac (simpset() setloop (K Safe_tac)) 1);
qed "";

(*This version uses meta-level rewriting, safe_tac and asm_simp_tac*)
val [hom_def] = goal Perm.thy
    "(!! A f B g. hom(A,f,B,g) == \
\          {H \\<in> A->B. f \\<in> A*A->A & g \\<in> B*B->B & \
\                    (\\<forall>x \\<in> A. \\<forall>y \\<in> A. H`(f`<x,y>) = g`<H`x,H`y>)}) ==> \
\    J \\<in> hom(A,f,B,g) & K \\<in> hom(B,g,C,h) -->  \
\    (K O J) \\<in> hom(A,f,C,h)";
by (rewtac hom_def);
by Safe_tac;
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
qed "comp_homs";


(** A characterization of functions, suggested by Tobias Nipkow **)

Goalw [Pi_def, function_def]
    "r \\<in> domain(r)->B  <->  r \\<subseteq> domain(r)*B & (\\<forall>X. r `` (r -`` X) \\<subseteq> X)";
by (Best_tac 1);
qed "";


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
          gen_union eq_thm (forw_typechk (tyrls@facts) (facts RL rls), facts)
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
\       f \\<in> A->B;  g \\<in> B->C;  h \\<in> C->A |] ==> h \\<in> bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
qed "pastre1";

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): surj(A,A);         \
\       (f O h O g): inj(B,B);          \
\       (g O f O h): surj(C,C);         \
\       f \\<in> A->B;  g \\<in> B->C;  h \\<in> C->A |] ==> h \\<in> bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
qed "pastre2";

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): surj(A,A);         \
\       (f O h O g): surj(B,B);         \
\       (g O f O h): inj(C,C);          \
\       f \\<in> A->B;  g \\<in> B->C;  h \\<in> C->A |] ==> h \\<in> bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
qed "pastre3";

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): surj(A,A);         \
\       (f O h O g): inj(B,B);          \
\       (g O f O h): inj(C,C);          \
\       f \\<in> A->B;  g \\<in> B->C;  h \\<in> C->A |] ==> h \\<in> bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
qed "pastre4";

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): inj(A,A);          \
\       (f O h O g): surj(B,B);         \
\       (g O f O h): inj(C,C);          \
\       f \\<in> A->B;  g \\<in> B->C;  h \\<in> C->A |] ==> h \\<in> bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
qed "pastre5";

val prems = goalw Perm.thy [bij_def]
    "[| (h O g O f): inj(A,A);          \
\       (f O h O g): inj(B,B);          \
\       (g O f O h): surj(C,C);         \
\       f \\<in> A->B;  g \\<in> B->C;  h \\<in> C->A |] ==> h \\<in> bij(C,A)";
by (REPEAT (resolve_tac (IntI :: pastre_facts prems) 1));
qed "pastre6";

(** Yet another example... **)

goal Perm.thy
    "(\\<lambda>Z \\<in> Pow(A+B). <{x \\<in> A. Inl(x):Z}, {y \\<in> B. Inr(y):Z}>) \
\    \\<in> bij(Pow(A+B), Pow(A)*Pow(B))";
by (res_inst_tac [("d", "%<X,Y>.{Inl(x).x \\<in> X} Un {Inr(y).y \\<in> Y}")] 
    lam_bijective 1);
(*Auto_tac no longer proves it*)
by Auto_tac;
by (ALLGOALS Blast_tac);  
qed "Pow_sum_bij";

(*As a special case, we have  bij(Pow(A*B), A -> Pow B)  *)
goal Perm.thy
    "(\\<lambda>r \\<in> Pow(Sigma(A,B)). \\<lambda>x \\<in> A. r``{x}) \
\    \\<in> bij(Pow(Sigma(A,B)), \\<Pi>x \\<in> A. Pow(B(x)))";
by (res_inst_tac [("d", "%f. \\<Union>x \\<in> A. \\<Union>y \\<in> f`x. {<x,y>}")] lam_bijective 1);
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
