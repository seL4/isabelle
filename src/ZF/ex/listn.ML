(*  Title: 	ZF/ex/listn
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Inductive definition of lists of n elements

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

structure ListN = Inductive_Fun
 (val thy = ListFn.thy addconsts [(["listn"],"i=>i")];
  val rec_doms = [("listn", "nat*list(A)")];
  val sintrs = 
      ["<0,Nil> : listn(A)",
       "[| a: A;  <n,l> : listn(A) |] ==> <succ(n), Cons(a,l)> : listn(A)"];
  val monos = [];
  val con_defs = [];
  val type_intrs = nat_typechecks@List.intrs@[SigmaI]
  val type_elims = [SigmaE2]);

(*Could be generated automatically; requires use of fsplitD*)
val listn_induct = standard
 (fsplitI RSN 
  (2, fsplitI RSN 
      (3, (read_instantiate [("P", "fsplit(R)")] ListN.induct) RS fsplitD)));

val [major] = goal ListN.thy "l:list(A) ==> <length(l),l> : listn(A)";
by (rtac (major RS List.induct) 1);
by (ALLGOALS (ASM_SIMP_TAC list_ss));
by (REPEAT (ares_tac ListN.intrs 1));
val list_into_listn = result();

goal ListN.thy "<n,l> : listn(A) <-> l:list(A) & length(l)=n";
by (rtac iffI 1);
by (etac listn_induct 1);
by (dtac fsplitD 2);
by (ALLGOALS (ASM_SIMP_TAC (list_ss addrews [Pair_iff])));
by (fast_tac (ZF_cs addSIs [list_into_listn]) 1);
val listn_iff = result();

goal ListN.thy "listn(A)``{n} = {l:list(A). length(l)=n}";
by (rtac equality_iffI 1);
by (SIMP_TAC (list_ss addrews [listn_iff,separation,image_singleton_iff]) 1);
val listn_image_eq = result();

