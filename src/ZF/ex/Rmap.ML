(*  Title: 	ZF/ex/rmap
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Inductive definition of an operator to "map" a relation over a list
*)

structure Rmap = Inductive_Fun
 (val thy = List.thy |> add_consts [("rmap","i=>i",NoSyn)];
  val rec_doms = [("rmap", "list(domain(r))*list(range(r))")];
  val sintrs = 
      ["<Nil,Nil> : rmap(r)",

       "[| <x,y>: r;  <xs,ys> : rmap(r) |] ==> \
\       <Cons(x,xs), Cons(y,ys)> : rmap(r)"];
  val monos = [];
  val con_defs = [];
  val type_intrs = [domainI,rangeI] @ List.intrs @ [SigmaI]
  val type_elims = [SigmaE2]);

goalw Rmap.thy Rmap.defs "!!r s. r<=s ==> rmap(r) <= rmap(s)";
by (rtac lfp_mono 1);
by (REPEAT (rtac Rmap.bnd_mono 1));
by (REPEAT (ares_tac ([Sigma_mono, list_mono, domain_mono, range_mono] @ 
		      basic_monos) 1));
val rmap_mono = result();

val rmap_induct = standard 
    (Rmap.mutual_induct RS spec RS spec RSN (2,rev_mp));

val Nil_rmap_case = Rmap.mk_cases List.con_defs "<Nil,zs> : rmap(r)"
and Cons_rmap_case = Rmap.mk_cases List.con_defs "<Cons(x,xs),zs> : rmap(r)";

val rmap_cs = ZF_cs addIs  Rmap.intrs
		    addSEs [Nil_rmap_case, Cons_rmap_case];

goal Rmap.thy "!!r. r <= A*B ==> rmap(r) <= list(A)*list(B)";
by (rtac (Rmap.dom_subset RS subset_trans) 1);
by (REPEAT (ares_tac [domain_rel_subset, range_rel_subset,
		      Sigma_mono, list_mono] 1));
val rmap_rel_type = result();

goal Rmap.thy
    "!!r. [| ALL x:A. EX y. <x,y>: r;  xs: list(A) |] ==> \
\         EX y. <xs, y> : rmap(r)";
by (etac List.induct 1);
by (ALLGOALS (fast_tac rmap_cs));
val rmap_total = result();

goal Rmap.thy
    "!!r. [| ALL x y z. <x,y>: r --> <x,z>: r --> y=z;    \
\            <xs, ys> : rmap(r) |] ==>                    \
\          ALL zs. <xs, zs> : rmap(r) --> ys=zs";
by (etac rmap_induct 1);
by (ALLGOALS (fast_tac rmap_cs));
val rmap_functional_lemma = result();
val rmap_functional = standard (rmap_functional_lemma RS spec RS mp);

(** If f is a function then rmap(f) behaves as expected. **)

goal Rmap.thy "!!f. f: A->B ==> rmap(f): list(A)->list(B)";
by (etac PiE 1);
by (rtac PiI 1);
by (etac rmap_rel_type 1);
by (rtac (rmap_total RS ex_ex1I) 1);
by (assume_tac 2);
by (fast_tac (ZF_cs addSEs [bspec RS ex1E]) 1);
by (rtac rmap_functional 1);
by (REPEAT (assume_tac 2));
by (fast_tac (ZF_cs addSEs [bspec RS ex1_equalsE]) 1);
val rmap_fun_type = result();

goalw Rmap.thy [apply_def] "rmap(f)`Nil = Nil";
by (fast_tac (rmap_cs addIs [the_equality]) 1);
val rmap_Nil = result();

goal Rmap.thy "!!f. [| f: A->B;  x: A;  xs: list(A) |] ==> \
\                   rmap(f) ` Cons(x,xs) = Cons(f`x, rmap(f)`xs)";
by (rtac apply_equality 1);
by (REPEAT (ares_tac ([apply_Pair, rmap_fun_type] @ Rmap.intrs) 1));
val rmap_Cons = result();
