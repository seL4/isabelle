(*  Title:      ZF/ex/ListN
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Inductive definition of lists of n elements

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

Goal "l:list(A) ==> <length(l),l> : listn(A)";
by (etac list.induct 1);
by (ALLGOALS Asm_simp_tac);
by (REPEAT (ares_tac listn.intrs 1));
qed "list_into_listn";

Goal "<n,l> : listn(A) <-> l:list(A) & length(l)=n";
by (rtac iffI 1);
by (blast_tac (claset() addIs [list_into_listn]) 2);
by (etac listn.induct 1);
by Auto_tac;
qed "listn_iff";

Goal "listn(A)``{n} = {l:list(A). length(l)=n}";
by (rtac equality_iffI 1);
by (simp_tac (simpset() addsimps [listn_iff,separation,image_singleton_iff]) 1);
qed "listn_image_eq";

Goalw listn.defs "A<=B ==> listn(A) <= listn(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac listn.bnd_mono 1));
by (REPEAT (ares_tac ([univ_mono,Sigma_mono,list_mono] @ basic_monos) 1));
qed "listn_mono";

Goal "[| <n,l> : listn(A); <n',l'> : listn(A) |] ==> <n#+n', l@l'> : listn(A)";
by (etac listn.induct 1);
by (ftac (impOfSubs listn.dom_subset) 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps listn.intrs)));
qed "listn_append";

val Nil_listn_case  = listn.mk_cases "<i,Nil> : listn(A)"
and Cons_listn_case = listn.mk_cases "<i,Cons(x,l)> : listn(A)";

val zero_listn_case = listn.mk_cases "<0,l> : listn(A)"
and succ_listn_case = listn.mk_cases "<succ(i),l> : listn(A)";
