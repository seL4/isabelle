(*  Title:      ZF/Induct/ListN
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Inductive definition of lists of n elements

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

theory ListN = Main:

consts  listn :: "i=>i"
inductive
  domains   "listn(A)" <= "nat*list(A)"
  intros
    NilI:  "<0,Nil> \<in> listn(A)"
    ConsI: "[| a \<in> A; <n,l> \<in> listn(A) |] ==> <succ(n), Cons(a,l)> \<in> listn(A)"
  type_intros  nat_typechecks list.intros


lemma list_into_listn: "l \<in> list(A) ==> <length(l),l> \<in> listn(A)"
by (erule list.induct, simp_all add: listn.intros)

lemma listn_iff: "<n,l> \<in> listn(A) <-> l \<in> list(A) & length(l)=n"
apply (rule iffI)
apply (erule listn.induct)
apply auto
apply (blast intro: list_into_listn)
done

lemma listn_image_eq: "listn(A)``{n} = {l \<in> list(A). length(l)=n}"
apply (rule equality_iffI)
apply (simp (no_asm) add: listn_iff separation image_singleton_iff)
done

lemma listn_mono: "A \<subseteq> B ==> listn(A) \<subseteq> listn(B)"
apply (unfold listn.defs )
apply (rule lfp_mono)
apply (rule listn.bnd_mono)+
apply (assumption | rule univ_mono Sigma_mono list_mono basic_monos)+
done

lemma listn_append:
     "[| <n,l> \<in> listn(A); <n',l'> \<in> listn(A) |] ==> <n#+n', l@l'> \<in> listn(A)"
apply (erule listn.induct)
apply (frule listn.dom_subset [THEN subsetD])
apply (simp_all add: listn.intros)
done

inductive_cases Nil_listn_case: "<i,Nil> \<in> listn(A)"
inductive_cases Cons_listn_case: "<i,Cons(x,l)> \<in> listn(A)"

inductive_cases zero_listn_case: "<0,l> \<in> listn(A)"
inductive_cases succ_listn_case: "<succ(i),l> \<in> listn(A)"

end
