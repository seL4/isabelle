(*  Title:      HOL/Vimage
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Inverse image of a function
*)

(** Basic rules **)

Goalw [vimage_def] "(a : f-``B) = (f a : B)";
by (Blast_tac 1) ;
qed "vimage_eq";

Addsimps [vimage_eq];

Goal "(a : f-``{b}) = (f a = b)";
by (simp_tac (simpset() addsimps [vimage_eq]) 1) ;
qed "vimage_singleton_eq";

Goalw [vimage_def]
    "!!A B f. [| f a = b;  b:B |] ==> a : f-``B";
by (Blast_tac 1) ;
qed "vimageI";

Goalw [vimage_def] "f a : A ==> a : f -`` A";
by (Fast_tac 1);
qed "vimageI2";

val major::prems = Goalw [vimage_def]
    "[| a: f-``B;  !!x.[| f a = x;  x:B |] ==> P |] ==> P";
by (rtac (major RS CollectE) 1);
by (blast_tac (claset() addIs prems) 1) ;
qed "vimageE";

Goalw [vimage_def] "a : f -`` A ==> f a : A";
by (Fast_tac 1);
qed "vimageD";

AddIs  [vimageI];
AddSEs [vimageE];


(*** Equations ***)

Goal "f-``{} = {}";
by (Blast_tac 1);
qed "vimage_empty";

Goal "f-``(-A) = -(f-``A)";
by (Blast_tac 1);
qed "vimage_Compl";

Goal "f-``(A Un B) = (f-``A) Un (f-``B)";
by (Blast_tac 1);
qed "vimage_Un";

Goal "f -`` (A Int B) = (f -`` A) Int (f -`` B)";
by (Fast_tac 1);
qed "vimage_Int";

Goal "f -`` (Union A) = (UN X:A. f -`` X)";
by (Blast_tac 1);
qed "vimage_Union";

Goal "f-``(UN x:A. B x) = (UN x:A. f -`` B x)";
by (Blast_tac 1);
qed "vimage_UN";

Goal "f-``(INT x:A. B x) = (INT x:A. f -`` B x)";
by (Blast_tac 1);
qed "vimage_INT";

Goal "f -`` Collect P = {y. P (f y)}";
by (Blast_tac 1);
qed "vimage_Collect_eq";
Addsimps [vimage_Collect_eq];

(*A strange result used in Tools/inductive_package*)
bind_thm ("vimage_Collect", 
	  allI RS 
	  prove_goalw (the_context ()) [vimage_def]
	  "! x. P (f x) = Q x ==> f -`` (Collect P) = Collect Q"
	      (fn prems => [cut_facts_tac prems 1, Fast_tac 1]));

Addsimps [vimage_empty, vimage_Un, vimage_Int];

(*NOT suitable for rewriting because of the recurrence of {a}*)
Goal "f-``(insert a B) = (f-``{a}) Un (f-``B)";
by (Blast_tac 1);
qed "vimage_insert";

Goal "f-``(A-B) = (f-``A) - (f-``B)";
by (Blast_tac 1);
qed "vimage_Diff";

Goal "f-``UNIV = UNIV";
by (Blast_tac 1);
qed "vimage_UNIV";
Addsimps [vimage_UNIV];

(*NOT suitable for rewriting*)
Goal "f-``B = (UN y: B. f-``{y})";
by (Blast_tac 1);
qed "vimage_eq_UN";

(*monotonicity*)
Goal "A<=B ==> f-``A <= f-``B";
by (Blast_tac 1);
qed "vimage_mono";
