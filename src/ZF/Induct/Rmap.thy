(*  Title:      ZF/ex/Rmap
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Inductive definition of an operator to "map" a relation over a list
*)

theory Rmap = Main:

consts
  rmap :: "i=>i"

inductive
  domains "rmap(r)" <= "list(domain(r))*list(range(r))"
  intros
    NilI:  "<Nil,Nil> \<in> rmap(r)"

    ConsI: "[| <x,y>: r;  <xs,ys> \<in> rmap(r) |] 
            ==> <Cons(x,xs), Cons(y,ys)> \<in> rmap(r)"

  type_intros domainI rangeI list.intros

lemma rmap_mono: "r \<subseteq> s ==> rmap(r) \<subseteq> rmap(s)"
apply (unfold rmap.defs )
apply (rule lfp_mono)
apply (rule rmap.bnd_mono)+
apply (assumption | 
       rule Sigma_mono list_mono domain_mono range_mono basic_monos)+
done

inductive_cases Nil_rmap_case  [elim!]: "<Nil,zs> \<in> rmap(r)"
inductive_cases Cons_rmap_case [elim!]: "<Cons(x,xs),zs> \<in> rmap(r)"

declare rmap.intros [intro]

lemma rmap_rel_type: "r \<subseteq> A*B ==> rmap(r) \<subseteq> list(A)*list(B)"
apply (rule rmap.dom_subset [THEN subset_trans])
apply (assumption | 
       rule domain_rel_subset range_rel_subset Sigma_mono list_mono)+
done

lemma rmap_total: "A \<subseteq> domain(r) ==> list(A) \<subseteq> domain(rmap(r))"
apply (rule subsetI)
apply (erule list.induct)
apply blast+
done

lemma rmap_functional: "function(r) ==> function(rmap(r))"
apply (unfold function_def)
apply (rule impI [THEN allI, THEN allI])
apply (erule rmap.induct)
apply blast+
done


(** If f is a function then rmap(f) behaves as expected. **)

lemma rmap_fun_type: "f \<in> A->B ==> rmap(f): list(A)->list(B)"
by (simp add: Pi_iff rmap_rel_type rmap_functional rmap_total)

lemma rmap_Nil: "rmap(f)`Nil = Nil"
by (unfold apply_def, blast)

lemma rmap_Cons: "[| f \<in> A->B;  x \<in> A;  xs: list(A) |]   
      ==> rmap(f) ` Cons(x,xs) = Cons(f`x, rmap(f)`xs)"
by (blast intro: apply_equality apply_Pair rmap_fun_type rmap.intros)


end
  
