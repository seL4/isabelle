(*  Title:      HOL/Vimage
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Inverse image of a function
*)

open Vimage;

(** Basic rules **)

qed_goalw "vimage_eq" thy [vimage_def]
    "(a : f-``B) = (f a : B)"
 (fn _ => [ (Blast_tac 1) ]);

Addsimps [vimage_eq];

qed_goal "vimage_singleton_eq" thy
    "(a : f-``{b}) = (f a = b)"
 (fn _ => [ simp_tac (simpset() addsimps [vimage_eq]) 1 ]);

qed_goalw "vimageI" thy [vimage_def]
    "!!A B f. [| f a = b;  b:B |] ==> a : f-``B"
 (fn _ => [ (Blast_tac 1) ]);

qed_goalw "vimageE" thy [vimage_def]
    "[| a: f-``B;  !!x.[| f a = x;  x:B |] ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS CollectE) 1),
    (blast_tac (claset() addIs prems) 1) ]);

AddIs  [vimageI];
AddSEs [vimageE];


(*** Simple equalities ***)

Goal "(%x. x) -`` B = B";
by (Blast_tac 1);
qed "ident_vimage";
Addsimps [ident_vimage];

Goal "f-``{} = {}";
by (Blast_tac 1);
qed "vimage_empty";

Goal "f-``(Compl A) = Compl (f-``A)";
by (Blast_tac 1);
qed "vimage_Compl";

Goal "f-``(A Un B) = (f-``A) Un (f-``B)";
by (Blast_tac 1);
qed "vimage_Un";

Goal "f-``(UN x:A. B x) = (UN x:A. f -`` B x)";
by (Blast_tac 1);
qed "vimage_UN";

Addsimps [vimage_empty, vimage_Un];

(*NOT suitable for rewriting because of the recurrence of {a}*)
Goal "f-``(insert a B) = (f-``{a}) Un (f-``B)";
by (Blast_tac 1);
qed "vimage_insert";

Goal "f-``(A Int B) = (f-``A) Int (f-``B)";
by (Blast_tac 1);
qed "vimage_Int";

Goal "f-``(A-B) = (f-``A) - (f-``B)";
by (Blast_tac 1);
qed "vimage_Diff";

Goal "f-``UNIV = UNIV";
by (Blast_tac 1);
qed "vimage_UNIV";
Addsimps [vimage_UNIV];

Goal "(UN x:A. f -`` B x) = f -`` (UN x:A. B x)";
by (Blast_tac 1);
qed "UN_vimage";
Addsimps [UN_vimage];

(*NOT suitable for rewriting*)
Goal "f-``B = (UN y: B. f-``{y})";
by (Blast_tac 1);
qed "vimage_eq_UN";


(** monotonicity **)

Goal "!!f. A<=B ==> f-``A <= f-``B";
by (Blast_tac 1);
qed "vimage_mono";
