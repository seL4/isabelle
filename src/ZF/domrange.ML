(*  Title:      ZF/domrange
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Converse, domain, range of a relation or function
*)

(*** converse ***)

qed_goalw "converse_iff" thy [converse_def]
    "<a,b>: converse(r) <-> <b,a>:r"
 (fn _ => [ (Fast_tac 1) ]);

qed_goalw "converseI" thy [converse_def]
    "!!a b r. <a,b>:r ==> <b,a>:converse(r)"
 (fn _ => [ (Fast_tac 1) ]);

qed_goalw "converseD" thy [converse_def]
    "!!a b r. <a,b> : converse(r) ==> <b,a> : r"
 (fn _ => [ (Fast_tac 1) ]);

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

qed_goal "converse_converse" thy
    "!!A B r. r<=Sigma(A,B) ==> converse(converse(r)) = r"
 (fn _ => [ (Fast_tac 1) ]);

qed_goal "converse_type" thy "!!A B r. r<=A*B ==> converse(r)<=B*A"
 (fn _ => [ (Fast_tac 1) ]);

qed_goal "converse_prod" thy "converse(A*B) = B*A"
 (fn _ => [ (Fast_tac 1) ]);

qed_goal "converse_empty" thy "converse(0) = 0"
 (fn _ => [ (Fast_tac 1) ]);

Addsimps [converse_prod, converse_empty];

(*** domain ***)

qed_goalw "domain_iff" thy [domain_def]
    "a: domain(r) <-> (EX y. <a,y>: r)"
 (fn _=> [ (Fast_tac 1) ]);

qed_goal "domainI" thy "!!a b r. <a,b>: r ==> a: domain(r)"
 (fn _=> [ (etac (exI RS (domain_iff RS iffD2)) 1) ]);

qed_goal "domainE" thy
    "[| a : domain(r);  !!y. <a,y>: r ==> P |] ==> P"
 (fn prems=>
  [ (rtac (domain_iff RS iffD1 RS exE) 1),
    (REPEAT (ares_tac prems 1)) ]);

AddIs  [domainI];
AddSEs [domainE];

qed_goal "domain_subset" thy "domain(Sigma(A,B)) <= A"
 (fn _=> [ (Fast_tac 1) ]);

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
 (fn _ => [ (Fast_tac 1) ]);

qed_goalw "fieldI2" thy [field_def] "!!r. <a,b>: r ==> b : field(r)"
 (fn _ => [ (Fast_tac 1) ]);

qed_goalw "fieldCI" thy [field_def]
    "(~ <c,a>:r ==> <a,b>: r) ==> a : field(r)"
 (fn [prem]=> [ (fast_tac (!claset addIs [prem]) 1) ]);

qed_goalw "fieldE" thy [field_def]
     "[| a : field(r);  \
\        !!x. <a,x>: r ==> P;  \
\        !!x. <x,a>: r ==> P        |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS UnE) 1),
    (REPEAT (eresolve_tac (prems@[domainE,rangeE]) 1)) ]);

AddIs  [fieldCI];
AddSEs [fieldE];

qed_goal "field_subset" thy "field(A*B) <= A Un B"
 (fn _ => [ (Fast_tac 1) ]);

qed_goalw "domain_subset_field" thy [field_def]
    "domain(r) <= field(r)"
 (fn _ => [ (rtac Un_upper1 1) ]);

qed_goalw "range_subset_field" thy [field_def]
    "range(r) <= field(r)"
 (fn _ => [ (rtac Un_upper2 1) ]);

qed_goal "domain_times_range" thy
    "!!A B r. r <= Sigma(A,B) ==> r <= domain(r)*range(r)"
 (fn _ => [ (Fast_tac 1) ]);

qed_goal "field_times_field" thy
    "!!A B r. r <= Sigma(A,B) ==> r <= field(r)*field(r)"
 (fn _ => [ (Fast_tac 1) ]);


(*** Image of a set under a function/relation ***)

qed_goalw "image_iff" thy [image_def] "b : r``A <-> (EX x:A. <x,b>:r)"
 (fn _ => [ (Fast_tac 1) ]);

qed_goal "image_singleton_iff" thy    "b : r``{a} <-> <a,b>:r"
 (fn _ => [ rtac (image_iff RS iff_trans) 1,
            Fast_tac 1 ]);

qed_goalw "imageI" thy [image_def]
    "!!a b r. [| <a,b>: r;  a:A |] ==> b : r``A"
 (fn _ => [ (Fast_tac 1) ]);

qed_goalw "imageE" thy [image_def]
    "[| b: r``A;  !!x.[| <x,b>: r;  x:A |] ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS CollectE) 1),
    (REPEAT (etac bexE 1 ORELSE ares_tac prems 1)) ]);

AddIs  [imageI];
AddSEs [imageE];

qed_goal "image_subset" thy "!!A B r. r <= A*B ==> r``C <= B"
 (fn _ => [ (Fast_tac 1) ]);


(*** Inverse image of a set under a function/relation ***)

qed_goalw "vimage_iff" thy [vimage_def,image_def,converse_def]
    "a : r-``B <-> (EX y:B. <a,y>:r)"
 (fn _ => [ (Fast_tac 1) ]);

qed_goal "vimage_singleton_iff" thy
    "a : r-``{b} <-> <a,b>:r"
 (fn _ => [ rtac (vimage_iff RS iff_trans) 1,
            Fast_tac 1 ]);

qed_goalw "vimageI" thy [vimage_def]
    "!!A B r. [| <a,b>: r;  b:B |] ==> a : r-``B"
 (fn _ => [ (Fast_tac 1) ]);

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

val ZF_cs = !claset delrules [equalityI];

(** The Union of a set of relations is a relation -- Lemma for fun_Union **)
goal thy "!!S. (ALL x:S. EX A B. x <= A*B) ==>  \
\                 Union(S) <= domain(Union(S)) * range(Union(S))";
by (Fast_tac 1);
qed "rel_Union";

(** The Union of 2 relations is a relation (Lemma for fun_Un)  **)
qed_goal "rel_Un" thy
    "!!r s. [| r <= A*B;  s <= C*D |] ==> (r Un s) <= (A Un C) * (B Un D)"
 (fn _ => [ (Fast_tac 1) ]);


goal thy "!!r. [| <a,c> : r; c~=b |] ==> domain(r-{<a,b>}) = domain(r)";
by (Deepen_tac 0 1);
qed "domain_Diff_eq";

goal thy "!!r. [| <c,b> : r; c~=a |] ==> range(r-{<a,b>}) = range(r)";
by (Deepen_tac 0 1);
qed "range_Diff_eq";

