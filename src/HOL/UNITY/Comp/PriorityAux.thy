(*  Title:      HOL/UNITY/PriorityAux
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

Auxiliary definitions needed in Priority.thy
*)

theory PriorityAux = UNITY_Main:

typedecl vertex
arities vertex :: type
  
constdefs
  (* symmetric closure: removes the orientation of a relation *)
  symcl :: "(vertex*vertex)set=>(vertex*vertex)set"
  "symcl r == r \<union> (r^-1)"

  (* Neighbors of a vertex i *)
  neighbors :: "[vertex, (vertex*vertex)set]=>vertex set"
 "neighbors i r == ((r \<union> r^-1)``{i}) - {i}"

  R :: "[vertex, (vertex*vertex)set]=>vertex set"
  "R i r == r``{i}"

  A :: "[vertex, (vertex*vertex)set]=>vertex set"
  "A i r == (r^-1)``{i}"

  (* reachable and above vertices: the original notation was R* and A* *)  
  reach :: "[vertex, (vertex*vertex)set]=> vertex set"
  "reach i r == (r^+)``{i}"

  above :: "[vertex, (vertex*vertex)set]=> vertex set"
  "above i r == ((r^-1)^+)``{i}"  

  reverse :: "[vertex, (vertex*vertex) set]=>(vertex*vertex)set"
  "reverse i r == (r - {(x,y). x=i | y=i} \<inter> r) \<union> ({(x,y). x=i|y=i} \<inter> r)^-1"

  (* The original definition *)
  derive1 :: "[vertex, (vertex*vertex)set, (vertex*vertex)set]=>bool"
  "derive1 i r q == symcl r = symcl q &
                    (\<forall>k k'. k\<noteq>i & k'\<noteq>i -->((k,k'):r) = ((k,k'):q)) &
                    A i r = {} & R i q = {}"

  (* Our alternative definition *)
  derive :: "[vertex, (vertex*vertex)set, (vertex*vertex)set]=>bool"
  "derive i r q == A i r = {} & (q = reverse i r)"

axioms
  (* we assume that the universe of vertices is finite  *)
  finite_vertex_univ:  "finite (UNIV :: vertex set)"

declare derive_def [simp] derive1_def [simp] symcl_def [simp] 
        A_def [simp] R_def [simp] 
        above_def [simp] reach_def [simp] 
        reverse_def [simp] neighbors_def [simp]

text{*All vertex sets are finite*}
declare finite_subset [OF subset_UNIV finite_vertex_univ, iff]

text{* and relatons over vertex are finite too *}

lemmas finite_UNIV_Prod =
       finite_Prod_UNIV [OF finite_vertex_univ finite_vertex_univ] 

declare finite_subset [OF subset_UNIV finite_UNIV_Prod, iff]


(* The equalities (above i r = {}) = (A i r = {}) 
   and (reach i r = {}) = (R i r) rely on the following theorem  *)

lemma image0_trancl_iff_image0_r: "((r^+)``{i} = {}) = (r``{i} = {})"
apply auto
apply (erule trancl_induct, auto)
done

(* Another form usefull in some situation *)
lemma image0_r_iff_image0_trancl: "(r``{i}={}) = (ALL x. ((i,x):r^+) = False)"
apply auto
apply (drule image0_trancl_iff_image0_r [THEN ssubst], auto)
done


(* In finite universe acyclic coincides with wf *)
lemma acyclic_eq_wf: "!!r::(vertex*vertex)set. acyclic r = wf r"
by (auto simp add: wf_iff_acyclic_if_finite)

(* derive and derive1 are equivalent *)
lemma derive_derive1_eq: "derive i r q = derive1 i r q"
by auto

(* Lemma 1 *)
lemma lemma1_a: 
     "[| x \<in> reach i q; derive1 k r q |] ==> x\<noteq>k --> x \<in> reach i r"
apply (unfold reach_def)
apply (erule ImageE)
apply (erule trancl_induct) 
 apply (case_tac "i=k", simp_all) 
  apply (blast intro: r_into_trancl, blast, clarify) 
apply (drule_tac x = y in spec)
apply (drule_tac x = z in spec)
apply (blast dest: r_into_trancl intro: trancl_trans)
done

lemma reach_lemma: "derive k r q ==> reach i q \<subseteq> (reach i r \<union> {k})"
apply clarify 
apply (drule lemma1_a)
apply (auto simp add: derive_derive1_eq 
            simp del: reach_def derive_def derive1_def)
done

(* An other possible formulation of the above theorem based on
   the equivalence x \<in> reach y r = y \<in> above x r                  *)
lemma reach_above_lemma:
      "(\<forall>i. reach i q \<subseteq> (reach i r \<union> {k})) = 
       (\<forall>x. x\<noteq>k --> (\<forall>i. i \<notin> above x r --> i \<notin> above x q))"
by (auto simp add: trancl_converse)

(* Lemma 2 *)
lemma maximal_converse_image0: 
     "(z, i):r^+ ==> (\<forall>y. (y, z):r --> (y,i) \<notin> r^+) = ((r^-1)``{z}={})"
apply auto
apply (frule_tac r = r in trancl_into_trancl2, auto)
done

lemma above_lemma_a: 
     "acyclic r ==> A i r\<noteq>{}-->(\<exists>j \<in> above i r. A j r = {})"
apply (simp add: acyclic_eq_wf wf_eq_minimal) 
apply (drule_tac x = " ((r^-1) ^+) ``{i}" in spec)
apply auto
apply (simp add: maximal_converse_image0 trancl_converse)
done

lemma above_lemma_b: 
     "acyclic r ==> above i r\<noteq>{}-->(\<exists>j \<in> above i r. above j r = {})";
apply (drule above_lemma_a)
apply (auto simp add: image0_trancl_iff_image0_r)
done

end
