(*  Title: 	ZF/pair
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Ordered pairs in Zermelo-Fraenkel Set Theory 
*)

(** Lemmas for showing that <a,b> uniquely determines a and b **)

val doubleton_iff = prove_goal ZF.thy
    "{a,b} = {c,d} <-> (a=c & b=d) | (a=d & b=c)"
 (fn _=> [ (resolve_tac [extension RS iff_trans] 1),
           (fast_tac upair_cs 1) ]);

val Pair_iff = prove_goalw ZF.thy [Pair_def]
    "<a,b> = <c,d> <-> a=c & b=d"
 (fn _=> [ (simp_tac (FOL_ss addsimps [doubleton_iff]) 1),
           (fast_tac FOL_cs 1) ]);

val Pair_inject = standard (Pair_iff RS iffD1 RS conjE);

val Pair_inject1 = prove_goal ZF.thy "<a,b> = <c,d> ==> a=c"
 (fn [major]=>
  [ (rtac (major RS Pair_inject) 1), (assume_tac 1) ]);

val Pair_inject2 = prove_goal ZF.thy "<a,b> = <c,d> ==> b=d"
 (fn [major]=>
  [ (rtac (major RS Pair_inject) 1), (assume_tac 1) ]);

val Pair_neq_0 = prove_goalw ZF.thy [Pair_def] "<a,b>=0 ==> P"
 (fn [major]=>
  [ (rtac (major RS equalityD1 RS subsetD RS emptyE) 1),
    (rtac consI1 1) ]);

val Pair_neq_fst = prove_goalw ZF.thy [Pair_def] "<a,b>=a ==> P"
 (fn [major]=>
  [ (rtac (consI1 RS mem_asym RS FalseE) 1),
    (rtac (major RS subst) 1),
    (rtac consI1 1) ]);

val Pair_neq_snd = prove_goalw ZF.thy [Pair_def] "<a,b>=b ==> P"
 (fn [major]=>
  [ (rtac (consI1 RS consI2 RS mem_asym RS FalseE) 1),
    (rtac (major RS subst) 1),
    (rtac (consI1 RS consI2) 1) ]);


(*** Sigma: Disjoint union of a family of sets
     Generalizes Cartesian product ***)

val SigmaI = prove_goalw ZF.thy [Sigma_def]
    "[| a:A;  b:B(a) |] ==> <a,b> : Sigma(A,B)"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[singletonI,UN_I]) 1)) ]);

(*The general elimination rule*)
val SigmaE = prove_goalw ZF.thy [Sigma_def]
    "[| c: Sigma(A,B);  \
\       !!x y.[| x:A;  y:B(x);  c=<x,y> |] ==> P \
\    |] ==> P"
 (fn major::prems=>
  [ (cut_facts_tac [major] 1),
    (REPEAT (eresolve_tac [UN_E, singletonE] 1 ORELSE ares_tac prems 1)) ]);

(** Elimination of <a,b>:A*B -- introduces no eigenvariables **)
val SigmaD1 = prove_goal ZF.thy "<a,b> : Sigma(A,B) ==> a : A"
 (fn [major]=>
  [ (rtac (major RS SigmaE) 1),
    (REPEAT (eresolve_tac [asm_rl,Pair_inject,ssubst] 1)) ]);

val SigmaD2 = prove_goal ZF.thy "<a,b> : Sigma(A,B) ==> b : B(a)"
 (fn [major]=>
  [ (rtac (major RS SigmaE) 1),
    (REPEAT (eresolve_tac [asm_rl,Pair_inject,ssubst] 1)) ]);

(*Also provable via 
  rule_by_tactic (REPEAT_FIRST (etac Pair_inject ORELSE' bound_hyp_subst_tac)
		  THEN prune_params_tac)
      (read_instantiate [("c","<a,b>")] SigmaE);  *)
val SigmaE2 = prove_goal ZF.thy
    "[| <a,b> : Sigma(A,B);    \
\       [| a:A;  b:B(a) |] ==> P   \
\    |] ==> P"
 (fn [major,minor]=>
  [ (rtac minor 1),
    (rtac (major RS SigmaD1) 1),
    (rtac (major RS SigmaD2) 1) ]);

val Sigma_cong = prove_goalw ZF.thy [Sigma_def]
    "[| A=A';  !!x. x:A' ==> B(x)=B'(x) |] ==> \
\    Sigma(A,B) = Sigma(A',B')"
 (fn prems=> [ (simp_tac (FOL_ss addsimps prems addcongs [RepFun_cong]) 1) ]);

val Sigma_empty1 = prove_goal ZF.thy "Sigma(0,B) = 0"
 (fn _ => [ (fast_tac (lemmas_cs addIs [equalityI] addSEs [SigmaE]) 1) ]);

val Sigma_empty2 = prove_goal ZF.thy "A*0 = 0"
 (fn _ => [ (fast_tac (lemmas_cs addIs [equalityI] addSEs [SigmaE]) 1) ]);


(*** Eliminator - split ***)

val split = prove_goalw ZF.thy [split_def]
    "split(%x y.c(x,y), <a,b>) = c(a,b)"
 (fn _ =>
  [ (fast_tac (upair_cs addIs [the_equality] addSEs [Pair_inject]) 1) ]);

val split_type = prove_goal ZF.thy
    "[|  p:Sigma(A,B);   \
\        !!x y.[| x:A; y:B(x) |] ==> c(x,y):C(<x,y>) \
\    |] ==> split(%x y.c(x,y), p) : C(p)"
 (fn major::prems=>
  [ (rtac (major RS SigmaE) 1),
    (etac ssubst 1),
    (REPEAT (ares_tac (prems @ [split RS ssubst]) 1)) ]);


goal ZF.thy
  "!!u. u: A*B ==>   \
\       R(split(c,u)) <-> (ALL x:A. ALL y:B. u = <x,y> --> R(c(x,y)))";
by (etac SigmaE 1);
by (asm_simp_tac (FOL_ss addsimps [split]) 1);
by (fast_tac (upair_cs addSEs [Pair_inject]) 1);
val expand_split = result();


(*** conversions for fst and snd ***)

val fst_conv = prove_goalw ZF.thy [fst_def] "fst(<a,b>) = a"
 (fn _=> [ (rtac split 1) ]);

val snd_conv = prove_goalw ZF.thy [snd_def] "snd(<a,b>) = b"
 (fn _=> [ (rtac split 1) ]);


(*** split for predicates: result type o ***)

goalw ZF.thy [fsplit_def] "!!R a b. R(a,b) ==> fsplit(R, <a,b>)";
by (REPEAT (ares_tac [refl,exI,conjI] 1));
val fsplitI = result();

val major::prems = goalw ZF.thy [fsplit_def]
    "[| fsplit(R,z);  !!x y. [| z = <x,y>;  R(x,y) |] ==> P |] ==> P";
by (cut_facts_tac [major] 1);
by (REPEAT (eresolve_tac (prems@[asm_rl,exE,conjE]) 1));
val fsplitE = result();

goal ZF.thy "!!R a b. fsplit(R,<a,b>) ==> R(a,b)";
by (REPEAT (eresolve_tac [asm_rl,fsplitE,Pair_inject,ssubst] 1));
val fsplitD = result();

val pair_cs = upair_cs 
    addSIs [SigmaI]
    addSEs [SigmaE2, SigmaE, Pair_inject, make_elim succ_inject,
	    Pair_neq_0, sym RS Pair_neq_0, succ_neq_0, sym RS succ_neq_0];

