(*  Title: 	ZF/ex/listn
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Inductive definition of lists of n elements

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

structure ListN = Inductive_Fun
 (val thy        = ListFn.thy |> add_consts [("listn","i=>i",NoSyn)]
  val thy_name   = "ListN"
  val rec_doms   = [("listn", "nat*list(A)")]
  val sintrs     = 
          ["<0,Nil> : listn(A)",
           "[| a: A;  <n,l> : listn(A) |] ==> <succ(n), Cons(a,l)> : listn(A)"]
  val monos      = []
  val con_defs   = []
  val type_intrs = nat_typechecks @ List.intrs @ [SigmaI]
  val type_elims = [SigmaE2]);

val listn_induct = standard 
    (ListN.mutual_induct RS spec RS spec RSN (2,rev_mp));

goal ListN.thy "!!l. l:list(A) ==> <length(l),l> : listn(A)";
by (etac List.induct 1);
by (ALLGOALS (asm_simp_tac list_ss));
by (REPEAT (ares_tac ListN.intrs 1));
val list_into_listn = result();

goal ListN.thy "<n,l> : listn(A) <-> l:list(A) & length(l)=n";
by (rtac iffI 1);
by (etac listn_induct 1);
by (safe_tac (ZF_cs addSIs (list_typechecks @
			    [length_Nil, length_Cons, list_into_listn])));
val listn_iff = result();

goal ListN.thy "listn(A)``{n} = {l:list(A). length(l)=n}";
by (rtac equality_iffI 1);
by (simp_tac (list_ss addsimps [listn_iff,separation,image_singleton_iff]) 1);
val listn_image_eq = result();

goalw ListN.thy ListN.defs "!!A B. A<=B ==> listn(A) <= listn(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac ListN.bnd_mono 1));
by (REPEAT (ares_tac ([univ_mono,Sigma_mono,list_mono] @ basic_monos) 1));
val listn_mono = result();

goal ListN.thy
    "!!n l. [| <n,l> : listn(A);  <n',l'> : listn(A) |] ==> \
\           <n#+n', l@l'> : listn(A)";
by (etac listn_induct 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps ListN.intrs)));
val listn_append = result();

val Nil_listn_case = ListN.mk_cases List.con_defs "<i,Nil> : listn(A)"
and Cons_listn_case = ListN.mk_cases List.con_defs "<i,Cons(x,l)> : listn(A)";

val zero_listn_case = ListN.mk_cases List.con_defs "<0,l> : listn(A)"
and succ_listn_case = ListN.mk_cases List.con_defs "<succ(i),l> : listn(A)";
