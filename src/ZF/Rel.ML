(*  Title:      ZF/Rel.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Relations in Zermelo-Fraenkel Set Theory 
*)

(*** Some properties of relations -- useful? ***)

(* irreflexivity *)

val prems = Goalw [irrefl_def]
    "[| !!x. x:A ==> <x,x> ~: r |] ==> irrefl(A,r)";
by (REPEAT (ares_tac (prems @ [ballI]) 1));
qed "irreflI";

Goalw [irrefl_def] "[| irrefl(A,r);  x:A |] ==>  <x,x> ~: r";
by (Blast_tac 1);
qed "irreflE";

(* symmetry *)

val prems = Goalw [sym_def]
     "[| !!x y.<x,y>: r ==> <y,x>: r |] ==> sym(r)";
by (REPEAT (ares_tac (prems @ [allI,impI]) 1));
qed "symI";

Goalw [sym_def] "[| sym(r); <x,y>: r |]  ==>  <y,x>: r";
by (Blast_tac 1);
qed "symE";

(* antisymmetry *)

val prems = Goalw [antisym_def]
     "[| !!x y.[| <x,y>: r;  <y,x>: r |] ==> x=y |] ==> \
\     antisym(r)";
by (REPEAT (ares_tac (prems @ [allI,impI]) 1));
qed "antisymI";

Goalw [antisym_def] "[| antisym(r); <x,y>: r;  <y,x>: r |]  ==>  x=y";
by (Blast_tac 1);
qed "antisymE";

(* transitivity *)

Goalw [trans_def] "[| trans(r);  <a,b>:r;  <b,c>:r |] ==> <a,c>:r";
by (Blast_tac 1);
qed "transD";

Goalw [trans_on_def]
    "[| trans[A](r);  <a,b>:r;  <b,c>:r;  a:A;  b:A;  c:A |] ==> <a,c>:r";
by (Blast_tac 1);
qed "trans_onD";

