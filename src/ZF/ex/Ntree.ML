(*  Title: 	ZF/ex/Ntree.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype definition n-ary branching trees
Demonstrates a simple use of function space in a datatype definition

Based upon ex/Term.ML
*)

structure Ntree = Datatype_Fun
 (val thy	= Univ.thy;
  val thy_name 	= "Ntree";
  val rec_specs = 
      [("ntree", "univ(A)",
	  [(["Branch"], "[i,i]=>i", NoSyn)])];
  val rec_styp 	= "i=>i";
  val sintrs 	= 
	["[| a: A;  n: nat;  h: n -> ntree(A) |] ==> Branch(a,h) : ntree(A)"];
  val monos 	= [Pi_mono];
  val type_intrs = (nat_fun_univ RS subsetD) :: datatype_intrs;
  val type_elims = []);

val [BranchI] = Ntree.intrs;

goal Ntree.thy "ntree(A) = A * (UN n: nat. n -> ntree(A))";
by (rtac (Ntree.unfold RS trans) 1);
bws Ntree.con_defs;
by (fast_tac (sum_cs addIs ([equalityI] @ datatype_intrs)
 	             addDs [Ntree.dom_subset RS subsetD]
 	             addEs [A_into_univ, nat_fun_into_univ]) 1);
val ntree_unfold = result();

(*A nicer induction rule than the standard one*)
val major::prems = goal Ntree.thy
    "[| t: ntree(A);  \
\       !!x n h. [| x: A;  n: nat;  h: n -> ntree(A);  ALL i:n. P(h`i)  \
\                |] ==> P(Branch(x,h))  \
\    |] ==> P(t)";
by (rtac (major RS Ntree.induct) 1);
by (REPEAT_SOME (ares_tac prems));
by (fast_tac (ZF_cs addEs [fun_weaken_type]) 1);
by (fast_tac (ZF_cs addDs [apply_type]) 1);
val ntree_induct2 = result();

(*Induction on ntree(A) to prove an equation*)
val major::prems = goal Ntree.thy
  "[| t: ntree(A);  f: ntree(A)->B;  g: ntree(A)->B;		\
\     !!x n h. [| x: A;  n: nat;  h: n -> ntree(A);  f O h = g O h |] ==> \
\              f ` Branch(x,h) = g ` Branch(x,h)  		\
\  |] ==> f`t=g`t";
by (rtac (major RS ntree_induct2) 1);
by (REPEAT_SOME (ares_tac prems));
by (cut_facts_tac prems 1);
br fun_extension 1;
by (REPEAT_SOME (ares_tac [comp_fun]));
by (asm_simp_tac (ZF_ss addsimps [comp_fun_apply]) 1);
val ntree_induct_eqn = result();

(**  Lemmas to justify using "Ntree" in other recursive type definitions **)

goalw Ntree.thy Ntree.defs "!!A B. A<=B ==> ntree(A) <= ntree(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac Ntree.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::basic_monos) 1));
val ntree_mono = result();

(*Easily provable by induction also*)
goalw Ntree.thy (Ntree.defs@Ntree.con_defs) "ntree(univ(A)) <= univ(A)";
by (rtac lfp_lowerbound 1);
by (rtac (A_subset_univ RS univ_mono) 2);
by (safe_tac ZF_cs);
by (REPEAT (ares_tac [Pair_in_univ, nat_fun_univ RS subsetD] 1));
val ntree_univ = result();

val ntree_subset_univ = 
    [ntree_mono, ntree_univ] MRS subset_trans |> standard;

goal Ntree.thy "!!t A B. [| t: ntree(A);  A <= univ(B) |] ==> t: univ(B)";
by (REPEAT (ares_tac [ntree_subset_univ RS subsetD] 1));
val ntree_into_univ = result();
