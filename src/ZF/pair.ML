(*  Title:      ZF/pair
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Ordered pairs in Zermelo-Fraenkel Set Theory 
*)

(** Lemmas for showing that <a,b> uniquely determines a and b **)

Goal "{a} = {b} <-> a=b";
by (resolve_tac [extension RS iff_trans] 1);
by (Blast_tac 1) ;
qed "singleton_eq_iff";
AddIffs [singleton_eq_iff];

Goal "{a,b} = {c,d} <-> (a=c & b=d) | (a=d & b=c)";
by (resolve_tac [extension RS iff_trans] 1);
by (Blast_tac 1) ;
qed "doubleton_eq_iff";

Goalw [Pair_def] "<a,b> = <c,d> <-> a=c & b=d";
by (simp_tac (simpset() addsimps [doubleton_eq_iff]) 1);
by (Blast_tac 1) ;
qed "Pair_iff";

Addsimps [Pair_iff];

bind_thm ("Pair_inject", Pair_iff RS iffD1 RS conjE);

AddSEs [Pair_inject];

bind_thm ("Pair_inject1", Pair_iff RS iffD1 RS conjunct1);
bind_thm ("Pair_inject2", Pair_iff RS iffD1 RS conjunct2);

Goalw [Pair_def]  "<a,b> ~= 0";
by (blast_tac (claset() addEs [equalityE]) 1) ;
qed "Pair_not_0";

bind_thm ("Pair_neq_0", Pair_not_0 RS notE);

AddSEs [Pair_neq_0, sym RS Pair_neq_0];

Goalw [Pair_def]  "<a,b>=a ==> P";
by (rtac (consI1 RS mem_asym RS FalseE) 1);
by (etac subst 1);
by (rtac consI1 1) ;
qed "Pair_neq_fst";

Goalw [Pair_def]  "<a,b>=b ==> P";
by (rtac (consI1 RS consI2 RS mem_asym RS FalseE) 1);
by (etac subst 1);
by (rtac (consI1 RS consI2) 1) ;
qed "Pair_neq_snd";


(*** Sigma: Disjoint union of a family of sets
     Generalizes Cartesian product ***)

Goalw [Sigma_def]  "<a,b>: Sigma(A,B) <-> a:A & b:B(a)";
by (Blast_tac 1) ;
qed "Sigma_iff";

Addsimps [Sigma_iff];

Goal "[| a:A;  b:B(a) |] ==> <a,b> : Sigma(A,B)";
by (Asm_simp_tac 1);
qed "SigmaI";

AddTCs [SigmaI];

bind_thm ("SigmaD1", Sigma_iff RS iffD1 RS conjunct1);
bind_thm ("SigmaD2", Sigma_iff RS iffD1 RS conjunct2);

(*The general elimination rule*)
val major::prems= Goalw [Sigma_def] 
    "[| c: Sigma(A,B);  \
\       !!x y.[| x:A;  y:B(x);  c=<x,y> |] ==> P \
\    |] ==> P";
by (cut_facts_tac [major] 1);
by (REPEAT (eresolve_tac [UN_E, singletonE] 1 ORELSE ares_tac prems 1)) ;
qed "SigmaE";

val [major,minor]= Goal
    "[| <a,b> : Sigma(A,B);    \
\       [| a:A;  b:B(a) |] ==> P   \
\    |] ==> P";
by (rtac minor 1);
by (rtac (major RS SigmaD1) 1);
by (rtac (major RS SigmaD2) 1) ;
qed "SigmaE2";

val prems= Goalw [Sigma_def] 
    "[| A=A';  !!x. x:A' ==> B(x)=B'(x) |] ==> \
\    Sigma(A,B) = Sigma(A',B')";
by (simp_tac (simpset() addsimps prems) 1) ;
qed "Sigma_cong";


(*Sigma_cong, Pi_cong NOT given to Addcongs: they cause
  flex-flex pairs and the "Check your prover" error.  Most
  Sigmas and Pis are abbreviated as * or -> *)

AddSIs [SigmaI];
AddSEs [SigmaE2, SigmaE];

Goal "Sigma(0,B) = 0";
by (Blast_tac 1) ;
qed "Sigma_empty1";

Goal "A*0 = 0";
by (Blast_tac 1) ;
qed "Sigma_empty2";

Addsimps [Sigma_empty1, Sigma_empty2];

Goal "A*B=0 <-> A=0 | B=0";
by (Blast_tac 1);
qed "Sigma_empty_iff";


(*** Projections: fst, snd ***)

Goalw [fst_def]  "fst(<a,b>) = a";
by (Blast_tac 1) ;
qed "fst_conv";

Goalw [snd_def]  "snd(<a,b>) = b";
by (Blast_tac 1) ;
qed "snd_conv";

Addsimps [fst_conv,snd_conv];

Goal "p:Sigma(A,B) ==> fst(p) : A";
by (Auto_tac) ;
qed "fst_type";
AddTCs [fst_type];

Goal "p:Sigma(A,B) ==> snd(p) : B(fst(p))";
by (Auto_tac) ;
qed "snd_type";
AddTCs [snd_type];

Goal "a: Sigma(A,B) ==> <fst(a),snd(a)> = a";
by (Auto_tac) ;
qed "Pair_fst_snd_eq";


(*** Eliminator - split ***)

(*A META-equality, so that it applies to higher types as well...*)
Goalw [split_def] "split(%x y. c(x,y), <a,b>) == c(a,b)";
by (Simp_tac 1);
qed "split";
Addsimps [split];

val major::prems= Goal
    "[|  p:Sigma(A,B);   \
\        !!x y.[| x:A; y:B(x) |] ==> c(x,y):C(<x,y>) \
\    |] ==> split(%x y. c(x,y), p) : C(p)";
by (rtac (major RS SigmaE) 1);
by (asm_simp_tac (simpset() addsimps prems) 1);
qed "split_type";
AddTCs [split_type];

Goalw [split_def]
  "u: A*B ==>   \
\       R(split(c,u)) <-> (ALL x:A. ALL y:B. u = <x,y> --> R(c(x,y)))";
by Auto_tac;
qed "expand_split";


(*** split for predicates: result type o ***)

Goalw [split_def] "R(a,b) ==> split(R, <a,b>)";
by (Asm_simp_tac 1);
qed "splitI";

val major::sigma::prems = Goalw [split_def]
    "[| split(R,z);  z:Sigma(A,B);                      \
\       !!x y. [| z = <x,y>;  R(x,y) |] ==> P           \
\    |] ==> P";
by (rtac (sigma RS SigmaE) 1);
by (cut_facts_tac [major] 1);
by (REPEAT (ares_tac prems 1));
by (Asm_full_simp_tac 1);
qed "splitE";

Goalw [split_def] "split(R,<a,b>) ==> R(a,b)";
by (Full_simp_tac 1);
qed "splitD";
