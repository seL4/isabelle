(*  Title:      Relation.ML
    ID:         $Id$
    Authors:    Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

open Relation;

(** Identity relation **)

goalw Relation.thy [id_def] "(a,a) : id";  
by (Blast_tac 1);
qed "idI";

val major::prems = goalw Relation.thy [id_def]
    "[| p: id;  !!x.[| p = (x,x) |] ==> P  \
\    |] ==>  P";  
by (rtac (major RS CollectE) 1);
by (etac exE 1);
by (eresolve_tac prems 1);
qed "idE";

goalw Relation.thy [id_def] "(a,b):id = (a=b)";
by (Blast_tac 1);
qed "pair_in_id_conv";
Addsimps [pair_in_id_conv];


(** Composition of two relations **)

goalw Relation.thy [comp_def]
    "!!r s. [| (a,b):s; (b,c):r |] ==> (a,c) : r O s";
by (Blast_tac 1);
qed "compI";

(*proof requires higher-level assumptions or a delaying of hyp_subst_tac*)
val prems = goalw Relation.thy [comp_def]
    "[| xz : r O s;  \
\       !!x y z. [| xz = (x,z);  (x,y):s;  (y,z):r |] ==> P \
\    |] ==> P";
by (cut_facts_tac prems 1);
by (REPEAT (eresolve_tac [CollectE, splitE, exE, conjE] 1 
     ORELSE ares_tac prems 1));
qed "compE";

val prems = goal Relation.thy
    "[| (a,c) : r O s;  \
\       !!y. [| (a,y):s;  (y,c):r |] ==> P \
\    |] ==> P";
by (rtac compE 1);
by (REPEAT (ares_tac prems 1 ORELSE eresolve_tac [Pair_inject,ssubst] 1));
qed "compEpair";

AddIs [compI, idI];
AddSEs [compE, idE];

goal Relation.thy "!!r s. [| r'<=r; s'<=s |] ==> (r' O s') <= (r O s)";
by (Blast_tac 1);
qed "comp_mono";

goal Relation.thy
    "!!r s. [| s <= A Times B;  r <= B Times C |] ==> (r O s) <= A Times C";
by (Blast_tac 1);
qed "comp_subset_Sigma";

(** Natural deduction for trans(r) **)

val prems = goalw Relation.thy [trans_def]
    "(!! x y z. [| (x,y):r;  (y,z):r |] ==> (x,z):r) ==> trans(r)";
by (REPEAT (ares_tac (prems@[allI,impI]) 1));
qed "transI";

goalw Relation.thy [trans_def]
    "!!r. [| trans(r);  (a,b):r;  (b,c):r |] ==> (a,c):r";
by (Blast_tac 1);
qed "transD";

(** Natural deduction for r^-1 **)

goalw Relation.thy [inverse_def] "!!a b r. ((a,b): r^-1) = ((b,a):r)";
by (Simp_tac 1);
qed "inverse_iff";

AddIffs [inverse_iff];

goalw Relation.thy [inverse_def] "!!a b r. (a,b):r ==> (b,a): r^-1";
by (Simp_tac 1);
qed "inverseI";

goalw Relation.thy [inverse_def] "!!a b r. (a,b) : r^-1 ==> (b,a) : r";
by (Blast_tac 1);
qed "inverseD";

(*More general than inverseD, as it "splits" the member of the relation*)
qed_goalw "inverseE" Relation.thy [inverse_def]
    "[| yx : r^-1;  \
\       !!x y. [| yx=(y,x);  (x,y):r |] ==> P \
\    |] ==> P"
 (fn [major,minor]=>
  [ (rtac (major RS CollectE) 1),
    (REPEAT (eresolve_tac [splitE, bexE,exE, conjE, minor] 1)),
    (assume_tac 1) ]);

AddSEs [inverseE];

goalw Relation.thy [inverse_def] "(r^-1)^-1 = r";
by (Blast_tac 1);
qed "inverse_inverse";
Addsimps [inverse_inverse];

goal Relation.thy "(r O s)^-1 = s^-1 O r^-1";
by (Blast_tac 1);
qed "inverse_comp";

goal Relation.thy "id^-1 = id";
by (Blast_tac 1);
qed "inverse_id";
Addsimps [inverse_id];

(** Domain **)

qed_goalw "Domain_iff" Relation.thy [Domain_def]
    "a: Domain(r) = (EX y. (a,y): r)"
 (fn _=> [ (Blast_tac 1) ]);

qed_goal "DomainI" Relation.thy "!!a b r. (a,b): r ==> a: Domain(r)"
 (fn _ => [ (etac (exI RS (Domain_iff RS iffD2)) 1) ]);

qed_goal "DomainE" Relation.thy
    "[| a : Domain(r);  !!y. (a,y): r ==> P |] ==> P"
 (fn prems=>
  [ (rtac (Domain_iff RS iffD1 RS exE) 1),
    (REPEAT (ares_tac prems 1)) ]);

AddIs  [DomainI];
AddSEs [DomainE];

goal thy "Domain id = UNIV";
by (Blast_tac 1);
qed "Domain_id";
Addsimps [Domain_id];

(** Range **)

qed_goalw "RangeI" Relation.thy [Range_def] "!!a b r.(a,b): r ==> b : Range(r)"
 (fn _ => [ (etac (inverseI RS DomainI) 1) ]);

qed_goalw "RangeE" Relation.thy [Range_def]
    "[| b : Range(r);  !!x. (x,b): r ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS DomainE) 1),
    (resolve_tac prems 1),
    (etac inverseD 1) ]);

AddIs  [RangeI];
AddSEs [RangeE];

goal thy "Range id = UNIV";
by (Blast_tac 1);
qed "Range_id";
Addsimps [Range_id];

(*** Image of a set under a relation ***)

qed_goalw "Image_iff" Relation.thy [Image_def]
    "b : r^^A = (? x:A. (x,b):r)"
 (fn _ => [ Blast_tac 1 ]);

qed_goal "Image_singleton_iff" Relation.thy
    "(b : r^^{a}) = ((a,b):r)"
 (fn _ => [ rtac (Image_iff RS trans) 1,
            Blast_tac 1 ]);

qed_goalw "ImageI" Relation.thy [Image_def]
    "!!a b r. [| (a,b): r;  a:A |] ==> b : r^^A"
 (fn _ => [ (Blast_tac 1)]);

qed_goalw "ImageE" Relation.thy [Image_def]
    "[| b: r^^A;  !!x.[| (x,b): r;  x:A |] ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS CollectE) 1),
    (Clarify_tac 1),
    (rtac (hd prems) 1),
    (REPEAT (etac bexE 1 ORELSE ares_tac prems 1)) ]);

AddIs  [ImageI];
AddSEs [ImageE];


qed_goal "Image_empty" Relation.thy
    "R^^{} = {}"
 (fn _ => [ Blast_tac 1 ]);

Addsimps [Image_empty];

goal thy "id ^^ A = A";
by (Blast_tac 1);
qed "Image_id";

Addsimps [Image_id];

qed_goal "Image_Int_subset" Relation.thy
    "R ^^ (A Int B) <= R ^^ A Int R ^^ B"
 (fn _ => [ Blast_tac 1 ]);

qed_goal "Image_Un" Relation.thy
    "R ^^ (A Un B) = R ^^ A Un R ^^ B"
 (fn _ => [ Blast_tac 1 ]);


qed_goal "Image_subset" Relation.thy
    "!!A B r. r <= A Times B ==> r^^C <= B"
 (fn _ =>
  [ (rtac subsetI 1),
    (REPEAT (eresolve_tac [asm_rl, ImageE, subsetD RS SigmaD2] 1)) ]);

goal Relation.thy "R O id = R";
by (fast_tac (claset() addbefore split_all_tac) 1);
qed "R_O_id";

goal Relation.thy "id O R = R";
by (fast_tac (claset() addbefore split_all_tac) 1);
qed "id_O_R";

Addsimps [R_O_id,id_O_R];
