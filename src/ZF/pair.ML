(*  Title:      ZF/pair
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Ordered pairs in Zermelo-Fraenkel Set Theory 
*)

(** Lemmas for showing that <a,b> uniquely determines a and b **)

qed_goal "singleton_eq_iff" ZF.thy
    "{a} = {b} <-> a=b"
 (fn _=> [ (resolve_tac [extension RS iff_trans] 1),
           (Blast_tac 1) ]);

qed_goal "doubleton_eq_iff" ZF.thy
    "{a,b} = {c,d} <-> (a=c & b=d) | (a=d & b=c)"
 (fn _=> [ (resolve_tac [extension RS iff_trans] 1),
           (Blast_tac 1) ]);

qed_goalw "Pair_iff" ZF.thy [Pair_def]
    "<a,b> = <c,d> <-> a=c & b=d"
 (fn _=> [ (simp_tac (!simpset addsimps [doubleton_eq_iff]) 1),
           (Blast_tac 1) ]);

Addsimps [Pair_iff];

bind_thm ("Pair_inject", Pair_iff RS iffD1 RS conjE);

AddSEs [Pair_inject];

bind_thm ("Pair_inject1", Pair_iff RS iffD1 RS conjunct1);
bind_thm ("Pair_inject2", Pair_iff RS iffD1 RS conjunct2);

qed_goalw "Pair_not_0" ZF.thy [Pair_def] "<a,b> ~= 0"
 (fn _ => [ (blast_tac (!claset addEs [equalityE]) 1) ]);

bind_thm ("Pair_neq_0", Pair_not_0 RS notE);

AddSEs [Pair_neq_0, sym RS Pair_neq_0];

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

qed_goalw "Sigma_iff" ZF.thy [Sigma_def] "<a,b>: Sigma(A,B) <-> a:A & b:B(a)"
 (fn _ => [ Blast_tac 1 ]);

Addsimps [Sigma_iff];

qed_goal "SigmaI" ZF.thy
    "!!a b. [| a:A;  b:B(a) |] ==> <a,b> : Sigma(A,B)"
 (fn _ => [ Asm_simp_tac 1 ]);

bind_thm ("SigmaD1", Sigma_iff RS iffD1 RS conjunct1);
bind_thm ("SigmaD2", Sigma_iff RS iffD1 RS conjunct2);

(*The general elimination rule*)
qed_goalw "SigmaE" ZF.thy [Sigma_def]
    "[| c: Sigma(A,B);  \
\       !!x y.[| x:A;  y:B(x);  c=<x,y> |] ==> P \
\    |] ==> P"
 (fn major::prems=>
  [ (cut_facts_tac [major] 1),
    (REPEAT (eresolve_tac [UN_E, singletonE] 1 ORELSE ares_tac prems 1)) ]);

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
 (fn prems=> [ (simp_tac (!simpset addsimps prems) 1) ]);


(*Sigma_cong, Pi_cong NOT given to Addcongs: they cause
  flex-flex pairs and the "Check your prover" error.  Most
  Sigmas and Pis are abbreviated as * or -> *)

AddSIs [SigmaI];
AddSEs [SigmaE2, SigmaE];

qed_goal "Sigma_empty1" ZF.thy "Sigma(0,B) = 0"
 (fn _ => [ (Blast_tac 1) ]);

qed_goal "Sigma_empty2" ZF.thy "A*0 = 0"
 (fn _ => [ (Blast_tac 1) ]);

Addsimps [Sigma_empty1, Sigma_empty2];


(*** Projections: fst, snd ***)

qed_goalw "fst_conv" ZF.thy [fst_def] "fst(<a,b>) = a"
 (fn _=> [ (blast_tac (!claset addIs [the_equality]) 1) ]);

qed_goalw "snd_conv" ZF.thy [snd_def] "snd(<a,b>) = b"
 (fn _=> [ (blast_tac (!claset addIs [the_equality]) 1) ]);

Addsimps [fst_conv,snd_conv];

qed_goal "fst_type" ZF.thy "!!p. p:Sigma(A,B) ==> fst(p) : A"
 (fn _=> [ Auto_tac() ]);

qed_goal "snd_type" ZF.thy "!!p. p:Sigma(A,B) ==> snd(p) : B(fst(p))"
 (fn _=> [ Auto_tac() ]);

qed_goal "Pair_fst_snd_eq" ZF.thy
    "!!a A B. a: Sigma(A,B) ==> <fst(a),snd(a)> = a"
 (fn _=> [ Auto_tac() ]);


(*** Eliminator - split ***)

(*A META-equality, so that it applies to higher types as well...*)
qed_goalw "split" ZF.thy [split_def] "split(%x y. c(x,y), <a,b>) == c(a,b)"
 (fn _ => [ (Simp_tac 1),
            (rtac reflexive_thm 1) ]);

Addsimps [split];

qed_goal "split_type" ZF.thy
    "[|  p:Sigma(A,B);   \
\        !!x y.[| x:A; y:B(x) |] ==> c(x,y):C(<x,y>) \
\    |] ==> split(%x y. c(x,y), p) : C(p)"
 (fn major::prems=>
  [ (rtac (major RS SigmaE) 1),
    (asm_simp_tac (!simpset addsimps prems) 1) ]);

goalw ZF.thy [split_def]
  "!!u. u: A*B ==>   \
\       R(split(c,u)) <-> (ALL x:A. ALL y:B. u = <x,y> --> R(c(x,y)))";
by (Auto_tac());
qed "expand_split";


(*** split for predicates: result type o ***)

goalw ZF.thy [split_def] "!!R a b. R(a,b) ==> split(R, <a,b>)";
by (Asm_simp_tac 1);
qed "splitI";

val major::sigma::prems = goalw ZF.thy [split_def]
    "[| split(R,z);  z:Sigma(A,B);                      \
\       !!x y. [| z = <x,y>;  R(x,y) |] ==> P           \
\    |] ==> P";
by (rtac (sigma RS SigmaE) 1);
by (cut_facts_tac [major] 1);
by (REPEAT (ares_tac prems 1));
by (Asm_full_simp_tac 1);
qed "splitE";

goalw ZF.thy [split_def] "!!R a b. split(R,<a,b>) ==> R(a,b)";
by (Full_simp_tac 1);
qed "splitD";



