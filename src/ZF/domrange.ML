(*  Title:      ZF/domrange
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Converse, domain, range of a relation or function
*)

(*** converse ***)

qed_goalw "converse_iff" thy [converse_def]
    "<a,b>: converse(r) <-> <b,a>:r"
 (fn _ => [ (Blast_tac 1) ]);

qed_goalw "converseI" thy [converse_def]
    "!!a b r. <a,b>:r ==> <b,a>:converse(r)"
 (fn _ => [ (Blast_tac 1) ]);

qed_goalw "converseD" thy [converse_def]
    "!!a b r. <a,b> : converse(r) ==> <b,a> : r"
 (fn _ => [ (Blast_tac 1) ]);

qed_goalw "converseE" thy [converse_def]
    "[| yx : converse(r);  \
\       !!x y. [| yx=<y,x>;  <x,y>:r |] ==> P \
\    |] ==> P"
 (fn [major,minor]=>
  [ (rtac (major RS ReplaceE) 1),
    (REPEAT (eresolve_tac [exE, conjE, minor] 1)),
    (hyp_subst_tac 1),
    (assume_tac 1) ]);

Addsimps [converse_iff];
AddSIs [converseI];
AddSEs [converseD,converseE];

Goal "r<=Sigma(A,B) ==> converse(converse(r)) = r";
by (Blast_tac 1) ;
qed "converse_converse";

Goal "r<=A*B ==> converse(r)<=B*A";
by (Blast_tac 1) ;
qed "converse_type";

Goal "converse(A*B) = B*A";
by (Blast_tac 1) ;
qed "converse_prod";

Goal "converse(0) = 0";
by (Blast_tac 1) ;
qed "converse_empty";

Addsimps [converse_prod, converse_empty];

val converse_subset_iff = prove_goal thy
  "!!z. A <= Sigma(X,Y) ==> converse(A) <= converse(B) <-> A <= B"
 (fn _=> [ (Blast_tac 1) ]);


(*** domain ***)

qed_goalw "domain_iff" thy [domain_def]
    "a: domain(r) <-> (EX y. <a,y>: r)"
 (fn _=> [ (Blast_tac 1) ]);

Goal "<a,b>: r ==> a: domain(r)";
by (etac (exI RS (domain_iff RS iffD2)) 1) ;
qed "domainI";

val prems= Goal
    "[| a : domain(r);  !!y. <a,y>: r ==> P |] ==> P";
by (rtac (domain_iff RS iffD1 RS exE) 1);
by (REPEAT (ares_tac prems 1)) ;
qed "domainE";

AddIs  [domainI];
AddSEs [domainE];

Goal "domain(Sigma(A,B)) <= A";
by (Blast_tac 1) ;
qed "domain_subset";

(*** range ***)

qed_goalw "rangeI" thy [range_def] "!!a b r.<a,b>: r ==> b : range(r)"
 (fn _ => [ (etac (converseI RS domainI) 1) ]);

qed_goalw "rangeE" thy [range_def]
    "[| b : range(r);  !!x. <x,b>: r ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS domainE) 1),
    (resolve_tac prems 1),
    (etac converseD 1) ]);

AddIs  [rangeI];
AddSEs [rangeE];

qed_goalw "range_subset" thy [range_def] "range(A*B) <= B"
 (fn _ =>
  [ (stac converse_prod 1),
    (rtac domain_subset 1) ]);


(*** field ***)

qed_goalw "fieldI1" thy [field_def] "!!r. <a,b>: r ==> a : field(r)"
 (fn _ => [ (Blast_tac 1) ]);

qed_goalw "fieldI2" thy [field_def] "!!r. <a,b>: r ==> b : field(r)"
 (fn _ => [ (Blast_tac 1) ]);

qed_goalw "fieldCI" thy [field_def]
    "(~ <c,a>:r ==> <a,b>: r) ==> a : field(r)"
 (fn [prem]=> [ (blast_tac (claset() addIs [prem]) 1) ]);

qed_goalw "fieldE" thy [field_def]
     "[| a : field(r);  \
\        !!x. <a,x>: r ==> P;  \
\        !!x. <x,a>: r ==> P        |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS UnE) 1),
    (REPEAT (eresolve_tac (prems@[domainE,rangeE]) 1)) ]);

AddIs  [fieldCI];
AddSEs [fieldE];

Goal "field(A*B) <= A Un B";
by (Blast_tac 1) ;
qed "field_subset";

qed_goalw "domain_subset_field" thy [field_def]
    "domain(r) <= field(r)"
 (fn _ => [ (rtac Un_upper1 1) ]);

qed_goalw "range_subset_field" thy [field_def]
    "range(r) <= field(r)"
 (fn _ => [ (rtac Un_upper2 1) ]);

Goal "r <= Sigma(A,B) ==> r <= domain(r)*range(r)";
by (Blast_tac 1) ;
qed "domain_times_range";

Goal "r <= Sigma(A,B) ==> r <= field(r)*field(r)";
by (Blast_tac 1) ;
qed "field_times_field";


(*** Image of a set under a function/relation ***)

Goalw [image_def] "b : r``A <-> (EX x:A. <x,b>:r)";
by (Blast_tac 1);
qed "image_iff";

Goal "b : r``{a} <-> <a,b>:r";
by (rtac (image_iff RS iff_trans) 1);
by (Blast_tac 1) ;
qed "image_singleton_iff";

qed_goalw "imageI" thy [image_def]
    "!!a b r. [| <a,b>: r;  a:A |] ==> b : r``A"
 (fn _ => [ (Blast_tac 1) ]);

qed_goalw "imageE" thy [image_def]
    "[| b: r``A;  !!x.[| <x,b>: r;  x:A |] ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS CollectE) 1),
    (REPEAT (etac bexE 1 ORELSE ares_tac prems 1)) ]);

AddIs  [imageI];
AddSEs [imageE];

Goal "r <= A*B ==> r``C <= B";
by (Blast_tac 1) ;
qed "image_subset";


(*** Inverse image of a set under a function/relation ***)

qed_goalw "vimage_iff" thy [vimage_def,image_def,converse_def]
    "a : r-``B <-> (EX y:B. <a,y>:r)"
 (fn _ => [ (Blast_tac 1) ]);

Goal "a : r-``{b} <-> <a,b>:r";
by (rtac (vimage_iff RS iff_trans) 1);
by (Blast_tac 1) ;
qed "vimage_singleton_iff";

qed_goalw "vimageI" thy [vimage_def]
    "!!A B r. [| <a,b>: r;  b:B |] ==> a : r-``B"
 (fn _ => [ (Blast_tac 1) ]);

qed_goalw "vimageE" thy [vimage_def]
    "[| a: r-``B;  !!x.[| <a,x>: r;  x:B |] ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS imageE) 1),
    (REPEAT (etac converseD 1 ORELSE ares_tac prems 1)) ]);

qed_goalw "vimage_subset" thy [vimage_def]
    "!!A B r. r <= A*B ==> r-``C <= A"
 (fn _ => [ (etac (converse_type RS image_subset) 1) ]);


(** Theorem-proving for ZF set theory **)

AddIs  [vimageI];
AddSEs [vimageE];

val ZF_cs = claset() delrules [equalityI];

(** The Union of a set of relations is a relation -- Lemma for fun_Union **)
Goal "(ALL x:S. EX A B. x <= A*B) ==>  \
\                 Union(S) <= domain(Union(S)) * range(Union(S))";
by (Blast_tac 1);
qed "rel_Union";

(** The Union of 2 relations is a relation (Lemma for fun_Un)  **)
Goal "[| r <= A*B;  s <= C*D |] ==> (r Un s) <= (A Un C) * (B Un D)";
by (Blast_tac 1) ;
qed "rel_Un";

Goal "[| <a,c> : r; c~=b |] ==> domain(r-{<a,b>}) = domain(r)";
by (Blast_tac 1);
qed "domain_Diff_eq";

Goal "[| <c,b> : r; c~=a |] ==> range(r-{<a,b>}) = range(r)";
by (Blast_tac 1);
qed "range_Diff_eq";

