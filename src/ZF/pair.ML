(*  Title: 	ZF/pair
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Ordered pairs in Zermelo-Fraenkel Set Theory 
*)

(** Lemmas for showing that <a,b> uniquely determines a and b **)

qed_goal "singleton_eq_iff" ZF.thy
    "{a} = {b} <-> a=b"
 (fn _=> [ (resolve_tac [extension RS iff_trans] 1),
           (fast_tac upair_cs 1) ]);

qed_goal "doubleton_eq_iff" ZF.thy
    "{a,b} = {c,d} <-> (a=c & b=d) | (a=d & b=c)"
 (fn _=> [ (resolve_tac [extension RS iff_trans] 1),
           (fast_tac upair_cs 1) ]);

qed_goalw "Pair_iff" ZF.thy [Pair_def]
    "<a,b> = <c,d> <-> a=c & b=d"
 (fn _=> [ (simp_tac (FOL_ss addsimps [doubleton_eq_iff]) 1),
           (fast_tac FOL_cs 1) ]);

bind_thm ("Pair_inject", (Pair_iff RS iffD1 RS conjE));

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

val pair_cs = upair_cs 
    addSIs [SigmaI]
    addSEs [SigmaE2, SigmaE, Pair_inject, make_elim succ_inject,
	    Pair_neq_0, sym RS Pair_neq_0, succ_neq_0, sym RS succ_neq_0];


(*** Projections: fst, snd ***)

qed_goalw "fst_conv" ZF.thy [fst_def] "fst(<a,b>) = a"
 (fn _=> 
  [ (fast_tac (pair_cs addIs [the_equality]) 1) ]);

qed_goalw "snd_conv" ZF.thy [snd_def] "snd(<a,b>) = b"
 (fn _=> 
  [ (fast_tac (pair_cs addIs [the_equality]) 1) ]);

val pair_ss = FOL_ss addsimps [fst_conv,snd_conv];

qed_goal "fst_type" ZF.thy
    "!!p. p:Sigma(A,B) ==> fst(p) : A"
 (fn _=> [ (fast_tac (pair_cs addss pair_ss) 1) ]);

qed_goal "snd_type" ZF.thy
    "!!p. p:Sigma(A,B) ==> snd(p) : B(fst(p))"
 (fn _=> [ (fast_tac (pair_cs addss pair_ss) 1) ]);

goal ZF.thy "!!a A B. a: Sigma(A,B) ==> <fst(a),snd(a)> = a";
by (etac SigmaE 1);
by (asm_simp_tac pair_ss 1);
qed "Pair_fst_snd_eq";


(*** Eliminator - split ***)

(*A META-equality, so that it applies to higher types as well...*)
qed_goalw "split" ZF.thy [split_def]
    "split(%x y.c(x,y), <a,b>) == c(a,b)"
 (fn _ => [ (simp_tac pair_ss 1),
            (rtac reflexive_thm 1) ]);

qed_goal "split_type" ZF.thy
    "[|  p:Sigma(A,B);   \
\        !!x y.[| x:A; y:B(x) |] ==> c(x,y):C(<x,y>) \
\    |] ==> split(%x y.c(x,y), p) : C(p)"
 (fn major::prems=>
  [ (rtac (major RS SigmaE) 1),
    (asm_simp_tac (pair_ss addsimps (split::prems)) 1) ]);

goalw ZF.thy [split_def]
  "!!u. u: A*B ==>   \
\       R(split(c,u)) <-> (ALL x:A. ALL y:B. u = <x,y> --> R(c(x,y)))";
by (etac SigmaE 1);
by (asm_simp_tac pair_ss 1);
by (fast_tac pair_cs 1);
qed "expand_split";


(*** split for predicates: result type o ***)

goalw ZF.thy [split_def] "!!R a b. R(a,b) ==> split(R, <a,b>)";
by (asm_simp_tac pair_ss 1);
qed "splitI";

val major::sigma::prems = goalw ZF.thy [split_def]
    "[| split(R,z);  z:Sigma(A,B);  			\
\       !!x y. [| z = <x,y>;  R(x,y) |] ==> P 		\
\    |] ==> P";
by (rtac (sigma RS SigmaE) 1);
by (cut_facts_tac [major] 1);
by (asm_full_simp_tac (pair_ss addsimps prems) 1);
qed "splitE";

goalw ZF.thy [split_def] "!!R a b. split(R,<a,b>) ==> R(a,b)";
by (asm_full_simp_tac pair_ss 1);
qed "splitD";


(*** Basic simplification for ZF; see simpdata.ML for full version ***)

fun prove_fun s = 
    (writeln s;  prove_goal ZF.thy s
       (fn prems => [ (cut_facts_tac prems 1), 
		      (fast_tac (pair_cs addSIs [equalityI]) 1) ]));

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

(*INCLUDED: should be?  And what about cons(a,b)?*)
val bquant_simps = map prove_fun
 [ "(ALL x:0.P(x)) <-> True",
   "(EX  x:0.P(x)) <-> False",
   "(ALL x:succ(i).P(x)) <-> P(i) & (ALL x:i.P(x))",
   "(EX  x:succ(i).P(x)) <-> P(i) | (EX  x:i.P(x))",
   "(ALL x:cons(a,B).P(x)) <-> P(a) & (ALL x:B.P(x))",
   "(EX  x:cons(a,B).P(x)) <-> P(a) | (EX  x:B.P(x))" ];

val Collect_simps = map prove_fun
 [ "{x:0. P(x)} = 0",
   "{x:A. False} = 0",
   "{x:A. True} = A",
   "RepFun(0,f) = 0",
   "RepFun(succ(i),f) = cons(f(i), RepFun(i,f))",
   "RepFun(cons(a,B),f) = cons(f(a), RepFun(B,f))" ];

val UnInt_simps = map prove_fun
 [ "0 Un A = A",  "A Un 0 = A",
   "0 Int A = 0", "A Int 0 = 0",
   "0-A = 0",     "A-0 = A",
   "Union(0) = 0",
   "Union(cons(b,A)) = b Un Union(A)",
   "Inter({b}) = b"];

