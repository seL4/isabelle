(*  Title: 	ZF/ex/listn
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Inductive definition of lists of n elements

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

open ListN;

val listn_induct = standard 
    (listn.mutual_induct RS spec RS spec RSN (2,rev_mp));

goal ListN.thy "!!l. l:list(A) ==> <length(l),l> : listn(A)";
by (etac list.induct 1);
by (ALLGOALS (asm_simp_tac list_ss));
by (REPEAT (ares_tac listn.intrs 1));
qed "list_into_listn";

goal ListN.thy "<n,l> : listn(A) <-> l:list(A) & length(l)=n";
by (rtac iffI 1);
by (etac listn_induct 1);
by (safe_tac (ZF_cs addSIs (list_typechecks @
			    [length_Nil, length_Cons, list_into_listn])));
qed "listn_iff";

goal ListN.thy "listn(A)``{n} = {l:list(A). length(l)=n}";
by (rtac equality_iffI 1);
by (simp_tac (list_ss addsimps [listn_iff,separation,image_singleton_iff]) 1);
qed "listn_image_eq";

goalw ListN.thy listn.defs "!!A B. A<=B ==> listn(A) <= listn(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac listn.bnd_mono 1));
by (REPEAT (ares_tac ([univ_mono,Sigma_mono,list_mono] @ basic_monos) 1));
qed "listn_mono";

goal ListN.thy
    "!!n l. [| <n,l> : listn(A);  <n',l'> : listn(A) |] ==> \
\           <n#+n', l@l'> : listn(A)";
by (etac listn_induct 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps listn.intrs)));
qed "listn_append";

val Nil_listn_case = listn.mk_cases list.con_defs "<i,Nil> : listn(A)"
and Cons_listn_case = listn.mk_cases list.con_defs "<i,Cons(x,l)> : listn(A)";

val zero_listn_case = listn.mk_cases list.con_defs "<0,l> : listn(A)"
and succ_listn_case = listn.mk_cases list.con_defs "<succ(i),l> : listn(A)";
