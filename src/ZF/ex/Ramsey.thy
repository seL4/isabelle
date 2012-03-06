(*  Title:      ZF/ex/Ramsey.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Ramsey's Theorem (finite exponent 2 version)

Based upon the article
    D Basin and M Kaufmann,
    The Boyer-Moore Prover and Nuprl: An Experimental Comparison.
    In G Huet and G Plotkin, editors, Logical Frameworks.
    (CUP, 1991), pages 89-119

See also
    M Kaufmann,
    An example in NQTHM: Ramsey's Theorem
    Internal Note, Computational Logic, Inc., Austin, Texas 78703
    Available from the author: kaufmann@cli.com

This function compute Ramsey numbers according to the proof given below
(which, does not constrain the base case values at all.

fun ram 0 j = 1
  | ram i 0 = 1
  | ram i j = ram (i-1) j + ram i (j-1)
*)

theory Ramsey imports Main begin

definition
  Symmetric :: "i=>o" where
    "Symmetric(E) == (\<forall>x y. <x,y>:E \<longrightarrow> <y,x>:E)"

definition
  Atleast :: "[i,i]=>o" where -- "not really necessary: ZF defines cardinality"
    "Atleast(n,S) == (\<exists>f. f \<in> inj(n,S))"

definition
  Clique  :: "[i,i,i]=>o" where
    "Clique(C,V,E) == (C \<subseteq> V) & (\<forall>x \<in> C. \<forall>y \<in> C. x\<noteq>y \<longrightarrow> <x,y> \<in> E)"

definition
  Indept  :: "[i,i,i]=>o" where
    "Indept(I,V,E) == (I \<subseteq> V) & (\<forall>x \<in> I. \<forall>y \<in> I. x\<noteq>y \<longrightarrow> <x,y> \<notin> E)"
  
definition
  Ramsey  :: "[i,i,i]=>o" where
    "Ramsey(n,i,j) == \<forall>V E. Symmetric(E) & Atleast(n,V) \<longrightarrow>  
         (\<exists>C. Clique(C,V,E) & Atleast(i,C)) |       
         (\<exists>I. Indept(I,V,E) & Atleast(j,I))"

(*** Cliques and Independent sets ***)

lemma Clique0 [intro]: "Clique(0,V,E)"
by (unfold Clique_def, blast)

lemma Clique_superset: "[| Clique(C,V',E);  V'<=V |] ==> Clique(C,V,E)"
by (unfold Clique_def, blast)

lemma Indept0 [intro]: "Indept(0,V,E)"
by (unfold Indept_def, blast)

lemma Indept_superset: "[| Indept(I,V',E);  V'<=V |] ==> Indept(I,V,E)"
by (unfold Indept_def, blast)

(*** Atleast ***)

lemma Atleast0 [intro]: "Atleast(0,A)"
by (unfold Atleast_def inj_def Pi_def function_def, blast)

lemma Atleast_succD: 
    "Atleast(succ(m),A) ==> \<exists>x \<in> A. Atleast(m, A-{x})"
apply (unfold Atleast_def)
apply (blast dest: inj_is_fun [THEN apply_type] inj_succ_restrict)
done

lemma Atleast_superset: 
    "[| Atleast(n,A);  A \<subseteq> B |] ==> Atleast(n,B)"
by (unfold Atleast_def, blast intro: inj_weaken_type)

lemma Atleast_succI: 
    "[| Atleast(m,B);  b\<notin> B |] ==> Atleast(succ(m), cons(b,B))"
apply (unfold Atleast_def succ_def)
apply (blast intro: inj_extend elim: mem_irrefl) 
done

lemma Atleast_Diff_succI:
     "[| Atleast(m, B-{x});  x \<in> B |] ==> Atleast(succ(m), B)"
by (blast intro: Atleast_succI [THEN Atleast_superset]) 

(*** Main Cardinality Lemma ***)

(*The #-succ(0) strengthens the original theorem statement, but precisely
  the same proof could be used!!*)
lemma pigeon2 [rule_format]:
     "m \<in> nat ==>  
          \<forall>n \<in> nat. \<forall>A B. Atleast((m#+n) #- succ(0), A \<union> B) \<longrightarrow>    
                           Atleast(m,A) | Atleast(n,B)"
apply (induct_tac "m")
apply (blast intro!: Atleast0, simp)
apply (rule ballI)
apply (rename_tac m' n) (*simplifier does NOT preserve bound names!*)
apply (induct_tac "n", auto)
apply (erule Atleast_succD [THEN bexE])
apply (rename_tac n' A B z)
apply (erule UnE)
(**case z \<in> B.  Instantiate the '\<forall>A B' induction hypothesis. **)
apply (drule_tac [2] x1 = A and x = "B-{z}" in spec [THEN spec])
apply (erule_tac [2] mp [THEN disjE])
(*cases Atleast(succ(m1),A) and Atleast(succ(k),B)*)
apply (erule_tac [3] asm_rl notE Atleast_Diff_succI)+
(*proving the condition*)
prefer 2 apply (blast intro: Atleast_superset)
(**case z \<in> A.  Instantiate the '\<forall>n \<in> nat. \<forall>A B' induction hypothesis. **)
apply (drule_tac x2="succ(n')" and x1="A-{z}" and x=B
       in bspec [THEN spec, THEN spec])
apply (erule nat_succI)
apply (erule mp [THEN disjE])
(*cases Atleast(succ(m1),A) and Atleast(succ(k),B)*)
apply (erule_tac [2] asm_rl Atleast_Diff_succI notE)+
(*proving the condition*)
apply simp
apply (blast intro: Atleast_superset)
done


(**** Ramsey's Theorem ****)

(** Base cases of induction; they now admit ANY Ramsey number **)

lemma Ramsey0j: "Ramsey(n,0,j)"
by (unfold Ramsey_def, blast)

lemma Ramseyi0: "Ramsey(n,i,0)"
by (unfold Ramsey_def, blast)

(** Lemmas for induction step **)

(*The use of succ(m) here, rather than #-succ(0), simplifies the proof of 
  Ramsey_step_lemma.*)
lemma Atleast_partition: "[| Atleast(m #+ n, A);  m \<in> nat;  n \<in> nat |]   
      ==> Atleast(succ(m), {x \<in> A. ~P(x)}) | Atleast(n, {x \<in> A. P(x)})"
apply (rule nat_succI [THEN pigeon2], assumption+)
apply (rule Atleast_superset, auto)
done

(*For the Atleast part, proves ~(a \<in> I) from the second premise!*)
lemma Indept_succ: 
    "[| Indept(I, {z \<in> V-{a}. <a,z> \<notin> E}, E);  Symmetric(E);  a \<in> V;   
        Atleast(j,I) |] ==>    
     Indept(cons(a,I), V, E) & Atleast(succ(j), cons(a,I))"
apply (unfold Symmetric_def Indept_def)
apply (blast intro!: Atleast_succI)
done


lemma Clique_succ: 
    "[| Clique(C, {z \<in> V-{a}. <a,z>:E}, E);  Symmetric(E);  a \<in> V;   
        Atleast(j,C) |] ==>    
     Clique(cons(a,C), V, E) & Atleast(succ(j), cons(a,C))"
apply (unfold Symmetric_def Clique_def)
apply (blast intro!: Atleast_succI)
done

(** Induction step **)

(*Published proofs gloss over the need for Ramsey numbers to be POSITIVE.*)
lemma Ramsey_step_lemma:
   "[| Ramsey(succ(m), succ(i), j);  Ramsey(n, i, succ(j));   
       m \<in> nat;  n \<in> nat |] ==> Ramsey(succ(m#+n), succ(i), succ(j))"
apply (unfold Ramsey_def, clarify)
apply (erule Atleast_succD [THEN bexE])
apply (erule_tac P1 = "%z.<x,z>:E" in Atleast_partition [THEN disjE],
       assumption+)
(*case m*)
apply (fast dest!: Indept_succ elim: Clique_superset)
(*case n*)
apply (fast dest!: Clique_succ elim: Indept_superset)
done


(** The actual proof **)

(*Again, the induction requires Ramsey numbers to be positive.*)
lemma ramsey_lemma: "i \<in> nat ==> \<forall>j \<in> nat. \<exists>n \<in> nat. Ramsey(succ(n), i, j)"
apply (induct_tac "i")
apply (blast intro!: Ramsey0j)
apply (rule ballI)
apply (induct_tac "j")
apply (blast intro!: Ramseyi0)
apply (blast intro!: add_type Ramsey_step_lemma)
done

(*Final statement in a tidy form, without succ(...) *)
lemma ramsey: "[| i \<in> nat;  j \<in> nat |] ==> \<exists>n \<in> nat. Ramsey(n,i,j)"
by (blast dest: ramsey_lemma)

end
