(*  Title: 	ZF/domrange
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Converse, domain, range of a relation or function
*)

(*** converse ***)

qed_goalw "converse_iff" ZF.thy [converse_def]
    "<a,b>: converse(r) <-> <b,a>:r"
 (fn _ => [ (fast_tac pair_cs 1) ]);

qed_goalw "converseI" ZF.thy [converse_def]
    "!!a b r. <a,b>:r ==> <b,a>:converse(r)"
 (fn _ => [ (fast_tac pair_cs 1) ]);

qed_goalw "converseD" ZF.thy [converse_def]
    "!!a b r. <a,b> : converse(r) ==> <b,a> : r"
 (fn _ => [ (fast_tac pair_cs 1) ]);

qed_goalw "converseE" ZF.thy [converse_def]
    "[| yx : converse(r);  \
\       !!x y. [| yx=<y,x>;  <x,y>:r |] ==> P \
\    |] ==> P"
 (fn [major,minor]=>
  [ (rtac (major RS ReplaceE) 1),
    (REPEAT (eresolve_tac [exE, conjE, minor] 1)),
    (hyp_subst_tac 1),
    (assume_tac 1) ]);

val converse_cs = pair_cs addSIs [converseI] 
			  addSEs [converseD,converseE];

qed_goal "converse_of_converse" ZF.thy
    "!!A B r. r<=Sigma(A,B) ==> converse(converse(r)) = r"
 (fn _ => [ (fast_tac (converse_cs addSIs [equalityI]) 1) ]);

qed_goal "converse_type" ZF.thy "!!A B r. r<=A*B ==> converse(r)<=B*A"
 (fn _ => [ (fast_tac converse_cs 1) ]);

qed_goal "converse_of_prod" ZF.thy "converse(A*B) = B*A"
 (fn _ => [ (fast_tac (converse_cs addSIs [equalityI]) 1) ]);

qed_goal "converse_empty" ZF.thy "converse(0) = 0"
 (fn _ => [ (fast_tac (converse_cs addSIs [equalityI]) 1) ]);

(*** domain ***)

qed_goalw "domain_iff" ZF.thy [domain_def]
    "a: domain(r) <-> (EX y. <a,y>: r)"
 (fn _=> [ (fast_tac pair_cs 1) ]);

qed_goal "domainI" ZF.thy "!!a b r. <a,b>: r ==> a: domain(r)"
 (fn _ => [ (etac (exI RS (domain_iff RS iffD2)) 1) ]);

qed_goal "domainE" ZF.thy
    "[| a : domain(r);  !!y. <a,y>: r ==> P |] ==> P"
 (fn prems=>
  [ (rtac (domain_iff RS iffD1 RS exE) 1),
    (REPEAT (ares_tac prems 1)) ]);

qed_goal "domain_subset" ZF.thy "domain(Sigma(A,B)) <= A"
 (fn _ => [ (rtac subsetI 1), (etac domainE 1), (etac SigmaD1 1) ]);


(*** range ***)

qed_goalw "rangeI" ZF.thy [range_def] "!!a b r.<a,b>: r ==> b : range(r)"
 (fn _ => [ (etac (converseI RS domainI) 1) ]);

qed_goalw "rangeE" ZF.thy [range_def]
    "[| b : range(r);  !!x. <x,b>: r ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS domainE) 1),
    (resolve_tac prems 1),
    (etac converseD 1) ]);

qed_goalw "range_subset" ZF.thy [range_def] "range(A*B) <= B"
 (fn _ =>
  [ (rtac (converse_of_prod RS ssubst) 1),
    (rtac domain_subset 1) ]);


(*** field ***)

qed_goalw "fieldI1" ZF.thy [field_def] "<a,b>: r ==> a : field(r)"
 (fn [prem]=>
  [ (rtac (prem RS domainI RS UnI1) 1) ]);

qed_goalw "fieldI2" ZF.thy [field_def] "<a,b>: r ==> b : field(r)"
 (fn [prem]=>
  [ (rtac (prem RS rangeI RS UnI2) 1) ]);

qed_goalw "fieldCI" ZF.thy [field_def]
    "(~ <c,a>:r ==> <a,b>: r) ==> a : field(r)"
 (fn [prem]=>
  [ (rtac (prem RS domainI RS UnCI) 1),
    (swap_res_tac [rangeI] 1),
    (etac notnotD 1) ]);

qed_goalw "fieldE" ZF.thy [field_def]
     "[| a : field(r);  \
\        !!x. <a,x>: r ==> P;  \
\        !!x. <x,a>: r ==> P        |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS UnE) 1),
    (REPEAT (eresolve_tac (prems@[domainE,rangeE]) 1)) ]);

qed_goal "field_subset" ZF.thy "field(A*B) <= A Un B"
 (fn _ => [ (fast_tac (pair_cs addIs  [fieldCI] addSEs [fieldE]) 1) ]);

qed_goalw "domain_subset_field" ZF.thy [field_def]
    "domain(r) <= field(r)"
 (fn _ => [ (rtac Un_upper1 1) ]);

qed_goalw "range_subset_field" ZF.thy [field_def]
    "range(r) <= field(r)"
 (fn _ => [ (rtac Un_upper2 1) ]);

qed_goal "domain_times_range" ZF.thy
    "!!A B r. r <= Sigma(A,B) ==> r <= domain(r)*range(r)"
 (fn _ => [ (fast_tac (pair_cs addIs [domainI,rangeI]) 1) ]);

qed_goal "field_times_field" ZF.thy
    "!!A B r. r <= Sigma(A,B) ==> r <= field(r)*field(r)"
 (fn _ => [ (fast_tac (pair_cs addIs [fieldI1,fieldI2]) 1) ]);


(*** Image of a set under a function/relation ***)

qed_goalw "image_iff" ZF.thy [image_def]
    "b : r``A <-> (EX x:A. <x,b>:r)"
 (fn _ => [ fast_tac (pair_cs addIs [rangeI]) 1 ]);

qed_goal "image_singleton_iff" ZF.thy
    "b : r``{a} <-> <a,b>:r"
 (fn _ => [ rtac (image_iff RS iff_trans) 1,
	    fast_tac pair_cs 1 ]);

qed_goalw "imageI" ZF.thy [image_def]
    "!!a b r. [| <a,b>: r;  a:A |] ==> b : r``A"
 (fn _ => [ (REPEAT (ares_tac [CollectI,rangeI,bexI] 1)) ]);

qed_goalw "imageE" ZF.thy [image_def]
    "[| b: r``A;  !!x.[| <x,b>: r;  x:A |] ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS CollectE) 1),
    (REPEAT (etac bexE 1 ORELSE ares_tac prems 1)) ]);

qed_goal "image_subset" ZF.thy
    "!!A B r. r <= A*B ==> r``C <= B"
 (fn _ => [ (fast_tac (pair_cs addSEs [imageE]) 1) ]);


(*** Inverse image of a set under a function/relation ***)

qed_goalw "vimage_iff" ZF.thy [vimage_def,image_def,converse_def]
    "a : r-``B <-> (EX y:B. <a,y>:r)"
 (fn _ => [ fast_tac (pair_cs addIs [rangeI]) 1 ]);

qed_goal "vimage_singleton_iff" ZF.thy
    "a : r-``{b} <-> <a,b>:r"
 (fn _ => [ rtac (vimage_iff RS iff_trans) 1,
	    fast_tac pair_cs 1 ]);

qed_goalw "vimageI" ZF.thy [vimage_def]
    "!!A B r. [| <a,b>: r;  b:B |] ==> a : r-``B"
 (fn _ => [ (REPEAT (ares_tac [converseI RS imageI] 1)) ]);

qed_goalw "vimageE" ZF.thy [vimage_def]
    "[| a: r-``B;  !!x.[| <a,x>: r;  x:B |] ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS imageE) 1),
    (REPEAT (etac converseD 1 ORELSE ares_tac prems 1)) ]);

qed_goalw "vimage_subset" ZF.thy [vimage_def]
    "!!A B r. r <= A*B ==> r-``C <= A"
 (fn _ => [ (etac (converse_type RS image_subset) 1) ]);


(** Theorem-proving for ZF set theory **)

val ZF_cs = pair_cs 
    addSIs [converseI]
    addIs  [imageI, vimageI, domainI, rangeI, fieldCI]
    addSEs [imageE, vimageE, domainE, rangeE, fieldE, converseD, converseE];

val eq_cs = ZF_cs addSIs [equalityI];

(** The Union of a set of relations is a relation -- Lemma for fun_Union **)
goal ZF.thy "!!S. (ALL x:S. EX A B. x <= A*B) ==>  \
\                 Union(S) <= domain(Union(S)) * range(Union(S))";
by (fast_tac ZF_cs 1);
qed "rel_Union";

(** The Union of 2 relations is a relation (Lemma for fun_Un)  **)
qed_goal "rel_Un" ZF.thy
    "!!r s. [| r <= A*B;  s <= C*D |] ==> (r Un s) <= (A Un C) * (B Un D)"
 (fn _ => [ (fast_tac ZF_cs 1) ]);


