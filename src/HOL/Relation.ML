(*  Title:      Relation.ML
    ID:         $Id$
    Authors:    Riccardo Mattolini, Dip. Sistemi e Informatica
                Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994 Universita' di Firenze
    Copyright   1993  University of Cambridge
*)

val RSLIST = curry (op MRS);

open Relation;

(** Identity relation **)

goalw Relation.thy [id_def] "(a,a) : id";  
by (rtac CollectI 1);
by (rtac exI 1);
by (rtac refl 1);
qed "idI";

val major::prems = goalw Relation.thy [id_def]
    "[| p: id;  !!x.[| p = (x,x) |] ==> P  \
\    |] ==>  P";  
by (rtac (major RS CollectE) 1);
by (etac exE 1);
by (eresolve_tac prems 1);
qed "idE";

goalw Relation.thy [id_def] "(a,b):id = (a=b)";
by (Fast_tac 1);
qed "pair_in_id_conv";
Addsimps [pair_in_id_conv];


(** Composition of two relations **)

val prems = goalw Relation.thy [comp_def]
    "[| (a,b):s; (b,c):r |] ==> (a,c) : r O s";
by (fast_tac (!claset addIs prems) 1);
qed "compI";

(*proof requires higher-level assumptions or a delaying of hyp_subst_tac*)
val prems = goalw Relation.thy [comp_def]
    "[| xz : r O s;  \
\       !!x y z. [| xz = (x,z);  (x,y):s;  (y,z):r |] ==> P \
\    |] ==> P";
by (cut_facts_tac prems 1);
by (REPEAT (eresolve_tac [CollectE, splitE, exE, conjE] 1 ORELSE ares_tac prems 1));
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

val comp_cs = prod_cs addIs [compI, idI] addSEs [compE, idE];

goal Relation.thy "!!r s. [| r'<=r; s'<=s |] ==> (r' O s') <= (r O s)";
by (Fast_tac 1);
qed "comp_mono";

goal Relation.thy
    "!!r s. [| s <= A Times B;  r <= B Times C |] ==> \
\           (r O s) <= A Times C";
by (Fast_tac 1);
qed "comp_subset_Sigma";

(** Natural deduction for trans(r) **)

val prems = goalw Relation.thy [trans_def]
    "(!! x y z. [| (x,y):r;  (y,z):r |] ==> (x,z):r) ==> trans(r)";
by (REPEAT (ares_tac (prems@[allI,impI]) 1));
qed "transI";

val major::prems = goalw Relation.thy [trans_def]
    "[| trans(r);  (a,b):r;  (b,c):r |] ==> (a,c):r";
by (cut_facts_tac [major] 1);
by (fast_tac (!claset addIs prems) 1);
qed "transD";

(** Natural deduction for converse(r) **)

goalw Relation.thy [converse_def] "!!a b r. (a,b):r ==> (b,a):converse(r)";
by (Simp_tac 1);
qed "converseI";

goalw Relation.thy [converse_def] "!!a b r. (a,b) : converse(r) ==> (b,a) : r";
by (Fast_tac 1);
qed "converseD";

qed_goalw "converseE" Relation.thy [converse_def]
    "[| yx : converse(r);  \
\       !!x y. [| yx=(y,x);  (x,y):r |] ==> P \
\    |] ==> P"
 (fn [major,minor]=>
  [ (rtac (major RS CollectE) 1),
    (REPEAT (eresolve_tac [splitE, bexE,exE, conjE, minor] 1)),
    (assume_tac 1) ]);

AddSIs [converseI];
AddSEs [converseD,converseE];

val converse_cs = comp_cs addSIs [converseI]
                          addSEs [converseD,converseE];

goalw Relation.thy [converse_def] "converse(converse R) = R";
by(Fast_tac 1);
qed "converse_converse";

(** Domain **)

qed_goalw "Domain_iff" Relation.thy [Domain_def]
    "a: Domain(r) = (EX y. (a,y): r)"
 (fn _=> [ (Fast_tac 1) ]);

qed_goal "DomainI" Relation.thy "!!a b r. (a,b): r ==> a: Domain(r)"
 (fn _ => [ (etac (exI RS (Domain_iff RS iffD2)) 1) ]);

qed_goal "DomainE" Relation.thy
    "[| a : Domain(r);  !!y. (a,y): r ==> P |] ==> P"
 (fn prems=>
  [ (rtac (Domain_iff RS iffD1 RS exE) 1),
    (REPEAT (ares_tac prems 1)) ]);

(** Range **)

qed_goalw "RangeI" Relation.thy [Range_def] "!!a b r.(a,b): r ==> b : Range(r)"
 (fn _ => [ (etac (converseI RS DomainI) 1) ]);

qed_goalw "RangeE" Relation.thy [Range_def]
    "[| b : Range(r);  !!x. (x,b): r ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS DomainE) 1),
    (resolve_tac prems 1),
    (etac converseD 1) ]);

(*** Image of a set under a relation ***)

qed_goalw "Image_iff" Relation.thy [Image_def]
    "b : r^^A = (? x:A. (x,b):r)"
 (fn _ => [ fast_tac (!claset addIs [RangeI]) 1 ]);

qed_goal "Image_singleton_iff" Relation.thy
    "(b : r^^{a}) = ((a,b):r)"
 (fn _ => [ rtac (Image_iff RS trans) 1,
            Fast_tac 1 ]);

qed_goalw "ImageI" Relation.thy [Image_def]
    "!!a b r. [| (a,b): r;  a:A |] ==> b : r^^A"
 (fn _ => [ (REPEAT (ares_tac [CollectI,RangeI,bexI] 1)),
            (resolve_tac [conjI ] 1),
            (rtac RangeI 1),
            (REPEAT (Fast_tac 1))]);

qed_goalw "ImageE" Relation.thy [Image_def]
    "[| b: r^^A;  !!x.[| (x,b): r;  x:A |] ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS CollectE) 1),
    (safe_tac (!claset)),
    (etac RangeE 1),
    (rtac (hd prems) 1),
    (REPEAT (etac bexE 1 ORELSE ares_tac prems 1)) ]);

qed_goal "Image_subset" Relation.thy
    "!!A B r. r <= A Times B ==> r^^C <= B"
 (fn _ =>
  [ (rtac subsetI 1),
    (REPEAT (eresolve_tac [asm_rl, ImageE, subsetD RS SigmaD2] 1)) ]);

AddSIs [converseI]; 
AddIs  [ImageI, DomainI, RangeI];
AddSEs [ImageE, DomainE, RangeE];

val rel_cs = converse_cs addSIs [converseI] 
                         addIs  [ImageI, DomainI, RangeI]
                         addSEs [ImageE, DomainE, RangeE];

AddSIs [equalityI];

val rel_eq_cs = rel_cs addSIs [equalityI];

goal Relation.thy "R O id = R";
by(fast_tac (!claset addIs [set_ext] addbefore (split_all_tac 1)) 1);
qed "R_O_id";

goal Relation.thy "id O R = R";
by(fast_tac (!claset addIs [set_ext] addbefore (split_all_tac 1)) 1);
qed "id_O_R";

Addsimps [R_O_id,id_O_R];
