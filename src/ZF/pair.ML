(*  Title: 	ZF/pair
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Ordered pairs in Zermelo-Fraenkel Set Theory 
*)

(** Lemmas for showing that <a,b> uniquely determines a and b **)

qed_goal "doubleton_iff" ZF.thy
    "{a,b} = {c,d} <-> (a=c & b=d) | (a=d & b=c)"
 (fn _=> [ (resolve_tac [extension RS iff_trans] 1),
           (fast_tac upair_cs 1) ]);

qed_goalw "Pair_iff" ZF.thy [Pair_def]
    "<a,b> = <c,d> <-> a=c & b=d"
 (fn _=> [ (simp_tac (FOL_ss addsimps [doubleton_iff]) 1),
           (fast_tac FOL_cs 1) ]);

val Pair_inject = standard (Pair_iff RS iffD1 RS conjE);

qed_goal "Pair_inject1" ZF.thy "<a,b> = <c,d> ==> a=c"
 (fn [major]=>
  [ (rtac (major RS Pair_inject) 1), (assume_tac 1) ]);

qed_goal "Pair_inject2" ZF.thy "<a,b> = <c,d> ==> b=d"
 (fn [major]=>
  [ (rtac (major RS Pair_inject) 1), (assume_tac 1) ]);

qed_goalw "Pair_neq_0" ZF.thy [Pair_def] "<a,b>=0 ==> P"
 (fn [major]=>
  [ (rtac (major RS equalityD1 RS subsetD RS emptyE) 1),
    (rtac consI1 1) ]);

qed_goalw "Pair_neq_fst" ZF.thy [Pair_def] "<a,b>=a ==> P"
 (fn [major]=>
  [ (rtac (consI1 RS mem_asym RS FalseE) 1),
    (rtac (major RS subst) 1),
    (rtac consI1 1) ]);

qed_goalw "Pair_neq_snd" ZF.thy [Pair_def] "<a,b>=b ==> P"
 (fn [major]=>
  [ (rtac (consI1 RS consI2 RS mem_asym RS FalseE) 1),
    (rtac (major RS subst) 1),
    (rtac (consI1 RS consI2) 1) ]);


(*** Sigma: Disjoint union of a family of sets
     Generalizes Cartesian product ***)

qed_goalw "SigmaI" ZF.thy [Sigma_def]
    "[| a:A;  b:B(a) |] ==> <a,b> : Sigma(A,B)"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[singletonI,UN_I]) 1)) ]);

(*The general elimination rule*)
qed_goalw "SigmaE" ZF.thy [Sigma_def]
    "[| c: Sigma(A,B);  \
\       !!x y.[| x:A;  y:B(x);  c=<x,y> |] ==> P \
\    |] ==> P"
 (fn major::prems=>
  [ (cut_facts_tac [major] 1),
    (REPEAT (eresolve_tac [UN_E, singletonE] 1 ORELSE ares_tac prems 1)) ]);

(** Elimination of <a,b>:A*B -- introduces no eigenvariables **)
qed_goal "SigmaD1" ZF.thy "<a,b> : Sigma(A,B) ==> a : A"
 (fn [major]=>
  [ (rtac (major RS SigmaE) 1),
    (REPEAT (eresolve_tac [asm_rl,Pair_inject,ssubst] 1)) ]);

qed_goal "SigmaD2" ZF.thy "<a,b> : Sigma(A,B) ==> b : B(a)"
 (fn [major]=>
  [ (rtac (major RS SigmaE) 1),
    (REPEAT (eresolve_tac [asm_rl,Pair_inject,ssubst] 1)) ]);

(*Also provable via 
  rule_by_tactic (REPEAT_FIRST (etac Pair_inject ORELSE' bound_hyp_subst_tac)
		  THEN prune_params_tac)
      (read_instantiate [("c","<a,b>")] SigmaE);  *)
qed_goal "SigmaE2" ZF.thy
    "[| <a,b> : Sigma(A,B);    \
\       [| a:A;  b:B(a) |] ==> P   \
\    |] ==> P"
 (fn [major,minor]=>
  [ (rtac minor 1),
    (rtac (major RS SigmaD1) 1),
    (rtac (major RS SigmaD2) 1) ]);

qed_goalw "Sigma_cong" ZF.thy [Sigma_def]
    "[| A=A';  !!x. x:A' ==> B(x)=B'(x) |] ==> \
\    Sigma(A,B) = Sigma(A',B')"
 (fn prems=> [ (simp_tac (FOL_ss addsimps prems addcongs [RepFun_cong]) 1) ]);

qed_goal "Sigma_empty1" ZF.thy "Sigma(0,B) = 0"
 (fn _ => [ (fast_tac (lemmas_cs addIs [equalityI] addSEs [SigmaE]) 1) ]);

qed_goal "Sigma_empty2" ZF.thy "A*0 = 0"
 (fn _ => [ (fast_tac (lemmas_cs addIs [equalityI] addSEs [SigmaE]) 1) ]);


(*** Eliminator - split ***)

qed_goalw "split" ZF.thy [split_def]
    "split(%x y.c(x,y), <a,b>) = c(a,b)"
 (fn _ =>
  [ (fast_tac (upair_cs addIs [the_equality] addSEs [Pair_inject]) 1) ]);

qed_goal "split_type" ZF.thy
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
qed "expand_split";


(*** conversions for fst and snd ***)

qed_goalw "fst_conv" ZF.thy [fst_def] "fst(<a,b>) = a"
 (fn _=> [ (rtac split 1) ]);

qed_goalw "snd_conv" ZF.thy [snd_def] "snd(<a,b>) = b"
 (fn _=> [ (rtac split 1) ]);


(*** split for predicates: result type o ***)

goalw ZF.thy [fsplit_def] "!!R a b. R(a,b) ==> fsplit(R, <a,b>)";
by (REPEAT (ares_tac [refl,exI,conjI] 1));
qed "fsplitI";

val major::prems = goalw ZF.thy [fsplit_def]
    "[| fsplit(R,z);  !!x y. [| z = <x,y>;  R(x,y) |] ==> P |] ==> P";
by (cut_facts_tac [major] 1);
by (REPEAT (eresolve_tac (prems@[asm_rl,exE,conjE]) 1));
qed "fsplitE";

goal ZF.thy "!!R a b. fsplit(R,<a,b>) ==> R(a,b)";
by (REPEAT (eresolve_tac [asm_rl,fsplitE,Pair_inject,ssubst] 1));
qed "fsplitD";

val pair_cs = upair_cs 
    addSIs [SigmaI]
    addSEs [SigmaE2, SigmaE, Pair_inject, make_elim succ_inject,
	    Pair_neq_0, sym RS Pair_neq_0, succ_neq_0, sym RS succ_neq_0];


(*** Basic simplification for ZF; see simpdata.ML for full version ***)

fun prove_fun s = 
    (writeln s;  prove_goal ZF.thy s
       (fn prems => [ (cut_facts_tac prems 1), (fast_tac pair_cs 1) ]));

(*INCLUDED IN ZF_ss*)
val mem_simps = map prove_fun
 [ "a : 0             <-> False",
   "a : A Un B        <-> a:A | a:B",
   "a : A Int B       <-> a:A & a:B",
   "a : A-B           <-> a:A & ~a:B",
   "<a,b>: Sigma(A,B) <-> a:A & b:B(a)",
   "a : Collect(A,P)  <-> a:A & P(a)" ];

goal ZF.thy "{x.x:A} = A";
by (fast_tac (pair_cs addSIs [equalityI]) 1);
qed "triv_RepFun";

(*INCLUDED: should be??*)
val bquant_simps = map prove_fun
 [ "(ALL x:0.P(x)) <-> True",
   "(EX  x:0.P(x)) <-> False",
   "(ALL x:succ(i).P(x)) <-> P(i) & (ALL x:i.P(x))",
   "(EX  x:succ(i).P(x)) <-> P(i) | (EX  x:i.P(x))" ];

