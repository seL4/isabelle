(*  Title:      ZF/Rel.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

For Rel.thy.  Relations in Zermelo-Fraenkel Set Theory 
*)

open Rel;

(*** Some properties of relations -- useful? ***)

(* irreflexivity *)

val prems = goalw Rel.thy [irrefl_def]
    "[| !!x. x:A ==> <x,x> ~: r |] ==> irrefl(A,r)";
by (REPEAT (ares_tac (prems @ [ballI]) 1));
qed "irreflI";

val prems = goalw Rel.thy [irrefl_def]
    "[| irrefl(A,r);  x:A |] ==>  <x,x> ~: r";
by (rtac (prems MRS bspec) 1);
qed "irreflE";

(* symmetry *)

val prems = goalw Rel.thy [sym_def]
     "[| !!x y.<x,y>: r ==> <y,x>: r |] ==> sym(r)";
by (REPEAT (ares_tac (prems @ [allI,impI]) 1));
qed "symI";

goalw Rel.thy [sym_def] "!!r. [| sym(r); <x,y>: r |]  ==>  <y,x>: r";
by (fast_tac ZF_cs 1);
qed "symE";

(* antisymmetry *)

val prems = goalw Rel.thy [antisym_def]
     "[| !!x y.[| <x,y>: r;  <y,x>: r |] ==> x=y |] ==> \
\     antisym(r)";
by (REPEAT (ares_tac (prems @ [allI,impI]) 1));
qed "antisymI";

val prems = goalw Rel.thy [antisym_def]
     "!!r. [| antisym(r); <x,y>: r;  <y,x>: r |]  ==>  x=y";
by (fast_tac ZF_cs 1);
qed "antisymE";

(* transitivity *)

goalw Rel.thy [trans_def]
    "!!r. [| trans(r);  <a,b>:r;  <b,c>:r |] ==> <a,c>:r";
by (fast_tac ZF_cs 1);
qed "transD";

goalw Rel.thy [trans_on_def]
    "!!r. [| trans[A](r);  <a,b>:r;  <b,c>:r;  a:A;  b:A;  c:A |] ==> <a,c>:r";
by (fast_tac ZF_cs 1);
qed "trans_onD";

