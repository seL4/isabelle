(*  Title:      ZF/ex/misc.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Miscellaneous examples for Zermelo-Fraenkel Set Theory 
Composition of homomorphisms, Pastre's examples, ...
*)

theory misc = Main:



(*These two are cited in Benzmueller and Kohlhase's system description of LEO,
  CADE-15, 1998 (page 139-143) as theorems LEO could not prove.*)
lemma "(X = Y Un Z) <-> (Y \<subseteq> X & Z \<subseteq> X & (\<forall>V. Y \<subseteq> V & Z \<subseteq> V --> X \<subseteq> V))"
by (blast intro!: equalityI)

(*the dual of the previous one*)
lemma "(X = Y Int Z) <-> (X \<subseteq> Y & X \<subseteq> Z & (\<forall>V. V \<subseteq> Y & V \<subseteq> Z --> V \<subseteq> X))"
by (blast intro!: equalityI)

(*trivial example of term synthesis: apparently hard for some provers!*)
lemma "a \<noteq> b ==> a:?X & b \<notin> ?X"
by blast

(*Nice Blast_tac benchmark.  Proved in 0.3s; old tactics can't manage it!*)
lemma "\<forall>x \<in> S. \<forall>y \<in> S. x \<subseteq> y ==> \<exists>z. S \<subseteq> {z}"
by blast

(*variant of the benchmark above*)
lemma "\<forall>x \<in> S. Union(S) \<subseteq> x ==> \<exists>z. S \<subseteq> {z}"
by blast

(*Example 12 (credited to Peter Andrews) from
 W. Bledsoe.  A Maximal Method for Set Variables in Automatic Theorem-proving.
 In: J. Hayes and D. Michie and L. Mikulich, eds.  Machine Intelligence 9.
 Ellis Horwood, 53-100 (1979). *)
lemma "(\<forall>F. {x} \<in> F --> {y} \<in> F) --> (\<forall>A. x \<in> A --> y \<in> A)"
by best


(*** Composition of homomorphisms is a homomorphism ***)

(*Given as a challenge problem in
  R. Boyer et al.,
  Set Theory in First-Order Logic: Clauses for G\"odel's Axioms,
  JAR 2 (1986), 287-327 
*)

(*collecting the relevant lemmas*)
declare comp_fun [simp] SigmaI [simp] apply_funtype [simp]

(*Force helps prove conditions of rewrites such as comp_fun_apply, since
  rewriting does not instantiate Vars.*)
lemma "(\<forall>A f B g. hom(A,f,B,g) =  
           {H \<in> A->B. f \<in> A*A->A & g \<in> B*B->B &  
                     (\<forall>x \<in> A. \<forall>y \<in> A. H`(f`<x,y>) = g`<H`x,H`y>)}) -->  
       J \<in> hom(A,f,B,g) & K \<in> hom(B,g,C,h) -->   
       (K O J) \<in> hom(A,f,C,h)"
by force

(*Another version, with meta-level rewriting*)
lemma "(!! A f B g. hom(A,f,B,g) ==  
           {H \<in> A->B. f \<in> A*A->A & g \<in> B*B->B &  
                     (\<forall>x \<in> A. \<forall>y \<in> A. H`(f`<x,y>) = g`<H`x,H`y>)}) 
       ==> J \<in> hom(A,f,B,g) & K \<in> hom(B,g,C,h) --> (K O J) \<in> hom(A,f,C,h)"
by force



(** A characterization of functions suggested by Tobias Nipkow **)

lemma "r \<in> domain(r)->B  <->  r \<subseteq> domain(r)*B & (\<forall>X. r `` (r -`` X) \<subseteq> X)"
by (unfold Pi_def function_def, best)

(**** From D Pastre.  Automatic theorem proving in set theory. 
         Artificial Intelligence, 10:1--27, 1978.

      Previously, these were done using ML code, but blast manages fine.
****)

lemmas compIs [intro] = comp_surj comp_inj comp_fun [intro]
lemmas compDs [dest] =  comp_mem_injD1 comp_mem_surjD1 
                        comp_mem_injD2 comp_mem_surjD2

lemma pastre1: 
    "[| (h O g O f) \<in> inj(A,A);           
        (f O h O g) \<in> surj(B,B);          
        (g O f O h) \<in> surj(C,C);          
        f \<in> A->B;  g \<in> B->C;  h \<in> C->A |] ==> h \<in> bij(C,A)";
by (unfold bij_def, blast)

lemma pastre3: 
    "[| (h O g O f) \<in> surj(A,A);          
        (f O h O g) \<in> surj(B,B);          
        (g O f O h) \<in> inj(C,C);           
        f \<in> A->B;  g \<in> B->C;  h \<in> C->A |] ==> h \<in> bij(C,A)"
by (unfold bij_def, blast)

lemma pastre4: 
    "[| (h O g O f) \<in> surj(A,A);          
        (f O h O g) \<in> inj(B,B);           
        (g O f O h) \<in> inj(C,C);           
        f \<in> A->B;  g \<in> B->C;  h \<in> C->A |] ==> h \<in> bij(C,A)"
by (unfold bij_def, blast)

lemma pastre5: 
    "[| (h O g O f) \<in> inj(A,A);           
        (f O h O g) \<in> surj(B,B);          
        (g O f O h) \<in> inj(C,C);           
        f \<in> A->B;  g \<in> B->C;  h \<in> C->A |] ==> h \<in> bij(C,A)"
by (unfold bij_def, blast)

lemma pastre6: 
    "[| (h O g O f) \<in> inj(A,A);           
        (f O h O g) \<in> inj(B,B);           
        (g O f O h) \<in> surj(C,C);          
        f \<in> A->B;  g \<in> B->C;  h \<in> C->A |] ==> h \<in> bij(C,A)"
by (unfold bij_def, blast)


(** Yet another example... **)

lemma Pow_sum_bij:
    "(\<lambda>Z \<in> Pow(A+B). <{x \<in> A. Inl(x) \<in> Z}, {y \<in> B. Inr(y) \<in> Z}>)  
     \<in> bij(Pow(A+B), Pow(A)*Pow(B))"
apply (rule_tac d = "%<X,Y>. {Inl (x). x \<in> X} Un {Inr (y). y \<in> Y}" 
       in lam_bijective)
apply force+
done

(*As a special case, we have  bij(Pow(A*B), A -> Pow B)  *)
lemma Pow_Sigma_bij:
    "(\<lambda>r \<in> Pow(Sigma(A,B)). \<lambda>x \<in> A. r``{x})  
     \<in> bij(Pow(Sigma(A,B)), \<Pi>x \<in> A. Pow(B(x)))"
apply (rule_tac d = "%f. \<Union>x \<in> A. \<Union>y \<in> f`x. {<x,y>}" in lam_bijective)
apply (blast intro: lam_type)
apply (blast dest: apply_type, simp_all)
apply fast (*strange, but blast can't do it*)
apply (rule fun_extension, auto)
by blast

end

