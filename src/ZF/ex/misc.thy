(*  Title:      ZF/ex/misc.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Composition of homomorphisms, Pastre's examples, ...
*)

header{*Miscellaneous ZF Examples*}

theory misc imports Main begin


subsection{*Various Small Problems*}

text{*The singleton problems are much harder in HOL.*}
lemma singleton_example_1:
     "\<forall>x \<in> S. \<forall>y \<in> S. x \<subseteq> y \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
  by blast

lemma singleton_example_2:
     "\<forall>x \<in> S. \<Union>S \<subseteq> x \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
  -- {*Variant of the problem above. *}
  by blast

lemma "\<exists>!x. f (g(x)) = x \<Longrightarrow> \<exists>!y. g (f(y)) = y"
  -- {* A unique fixpoint theorem --- @{text fast}/@{text best}/@{text auto} all fail. *} 
  apply (erule ex1E, rule ex1I, erule subst_context)
  apply (rule subst, assumption, erule allE, rule subst_context, erule mp)
  apply (erule subst_context)
  done


text{*A weird property of ordered pairs.*}
lemma "b\<noteq>c ==> <a,b> \<inter> <a,c> = <a,a>"
by (simp add: Pair_def Int_cons_left Int_cons_right doubleton_eq_iff, blast)

text{*These two are cited in Benzmueller and Kohlhase's system description of
 LEO, CADE-15, 1998 (page 139-143) as theorems LEO could not prove.*}
lemma "(X = Y \<union> Z) \<longleftrightarrow> (Y \<subseteq> X & Z \<subseteq> X & (\<forall>V. Y \<subseteq> V & Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
by (blast intro!: equalityI)

text{*the dual of the previous one*}
lemma "(X = Y \<inter> Z) \<longleftrightarrow> (X \<subseteq> Y & X \<subseteq> Z & (\<forall>V. V \<subseteq> Y & V \<subseteq> Z \<longrightarrow> V \<subseteq> X))"
by (blast intro!: equalityI)

text{*trivial example of term synthesis: apparently hard for some provers!*}
schematic_lemma "a \<noteq> b ==> a:?X & b \<notin> ?X"
by blast

text{*Nice blast benchmark.  Proved in 0.3s; old tactics can't manage it!*}
lemma "\<forall>x \<in> S. \<forall>y \<in> S. x \<subseteq> y ==> \<exists>z. S \<subseteq> {z}"
by blast

text{*variant of the benchmark above*}
lemma "\<forall>x \<in> S. \<Union>(S) \<subseteq> x ==> \<exists>z. S \<subseteq> {z}"
by blast

(*Example 12 (credited to Peter Andrews) from
 W. Bledsoe.  A Maximal Method for Set Variables in Automatic Theorem-proving.
 In: J. Hayes and D. Michie and L. Mikulich, eds.  Machine Intelligence 9.
 Ellis Horwood, 53-100 (1979). *)
lemma "(\<forall>F. {x} \<in> F \<longrightarrow> {y} \<in> F) \<longrightarrow> (\<forall>A. x \<in> A \<longrightarrow> y \<in> A)"
by best

text{*A characterization of functions suggested by Tobias Nipkow*}
lemma "r \<in> domain(r)->B  \<longleftrightarrow>  r \<subseteq> domain(r)*B & (\<forall>X. r `` (r -`` X) \<subseteq> X)"
by (unfold Pi_def function_def, best)


subsection{*Composition of homomorphisms is a Homomorphism*}

text{*Given as a challenge problem in
  R. Boyer et al.,
  Set Theory in First-Order Logic: Clauses for G\"odel's Axioms,
  JAR 2 (1986), 287-327 *}

text{*collecting the relevant lemmas*}
declare comp_fun [simp] SigmaI [simp] apply_funtype [simp]

(*Force helps prove conditions of rewrites such as comp_fun_apply, since
  rewriting does not instantiate Vars.*)
lemma "(\<forall>A f B g. hom(A,f,B,g) =  
           {H \<in> A->B. f \<in> A*A->A & g \<in> B*B->B &  
                     (\<forall>x \<in> A. \<forall>y \<in> A. H`(f`<x,y>) = g`<H`x,H`y>)}) \<longrightarrow>  
       J \<in> hom(A,f,B,g) & K \<in> hom(B,g,C,h) \<longrightarrow>   
       (K O J) \<in> hom(A,f,C,h)"
by force

text{*Another version, with meta-level rewriting*}
lemma "(!! A f B g. hom(A,f,B,g) ==  
           {H \<in> A->B. f \<in> A*A->A & g \<in> B*B->B &  
                     (\<forall>x \<in> A. \<forall>y \<in> A. H`(f`<x,y>) = g`<H`x,H`y>)}) 
       ==> J \<in> hom(A,f,B,g) & K \<in> hom(B,g,C,h) \<longrightarrow> (K O J) \<in> hom(A,f,C,h)"
by force


subsection{*Pastre's Examples*}

text{*D Pastre.  Automatic theorem proving in set theory. 
        Artificial Intelligence, 10:1--27, 1978.
Previously, these were done using ML code, but blast manages fine.*}

lemmas compIs [intro] = comp_surj comp_inj comp_fun [intro]
lemmas compDs [dest] =  comp_mem_injD1 comp_mem_surjD1 
                        comp_mem_injD2 comp_mem_surjD2

lemma pastre1: 
    "[| (h O g O f) \<in> inj(A,A);           
        (f O h O g) \<in> surj(B,B);          
        (g O f O h) \<in> surj(C,C);          
        f \<in> A->B;  g \<in> B->C;  h \<in> C->A |] ==> h \<in> bij(C,A)"
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


end

