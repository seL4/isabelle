(*  Title:      ZF/Induct/ListN.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

header {* Lists of n elements *}

theory ListN imports Main begin

text {*
  Inductive definition of lists of @{text n} elements; see
  \cite{paulin-tlca}.
*}

consts listn :: "i=>i"
inductive
  domains "listn(A)" \<subseteq> "nat \<times> list(A)"
  intros
    NilI: "<0,Nil> \<in> listn(A)"
    ConsI: "[| a \<in> A; <n,l> \<in> listn(A) |] ==> <succ(n), Cons(a,l)> \<in> listn(A)"
  type_intros nat_typechecks list.intros


lemma list_into_listn: "l \<in> list(A) ==> <length(l),l> \<in> listn(A)"
  by (induct set: list) (simp_all add: listn.intros)

lemma listn_iff: "<n,l> \<in> listn(A) \<longleftrightarrow> l \<in> list(A) & length(l)=n"
  apply (rule iffI)
   apply (erule listn.induct)
    apply auto
  apply (blast intro: list_into_listn)
  done

lemma listn_image_eq: "listn(A)``{n} = {l \<in> list(A). length(l)=n}"
  apply (rule equality_iffI)
  apply (simp add: listn_iff separation image_singleton_iff)
  done

lemma listn_mono: "A \<subseteq> B ==> listn(A) \<subseteq> listn(B)"
  apply (unfold listn.defs)
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

inductive_cases
      Nil_listn_case: "<i,Nil> \<in> listn(A)"
  and Cons_listn_case: "<i,Cons(x,l)> \<in> listn(A)"

inductive_cases
      zero_listn_case: "<0,l> \<in> listn(A)"
  and succ_listn_case: "<succ(i),l> \<in> listn(A)"

end
