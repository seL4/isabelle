(*  Title: 	ZF/domrange
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Converse, domain, range of a relation or function
*)

(*** converse ***)

val converseI = prove_goalw ZF.thy [converse_def]
    "!!a b r. <a,b>:r ==> <b,a>:converse(r)"
 (fn _ => [ (fast_tac pair_cs 1) ]);

val converseD = prove_goalw ZF.thy [converse_def]
    "!!a b r. <a,b> : converse(r) ==> <b,a> : r"
 (fn _ => [ (fast_tac pair_cs 1) ]);

val converseE = prove_goalw ZF.thy [converse_def]
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

val converse_of_converse = prove_goal ZF.thy
    "!!A B r. r<=Sigma(A,B) ==> converse(converse(r)) = r"
 (fn _ => [ (fast_tac (converse_cs addSIs [equalityI]) 1) ]);

val converse_type = prove_goal ZF.thy "!!A B r. r<=A*B ==> converse(r)<=B*A"
 (fn _ => [ (fast_tac converse_cs 1) ]);

val converse_of_prod = prove_goal ZF.thy "converse(A*B) = B*A"
 (fn _ => [ (fast_tac (converse_cs addSIs [equalityI]) 1) ]);

val converse_empty = prove_goal ZF.thy "converse(0) = 0"
 (fn _ => [ (fast_tac (converse_cs addSIs [equalityI]) 1) ]);

(*** domain ***)

val domain_iff = prove_goalw ZF.thy [domain_def]
    "a: domain(r) <-> (EX y. <a,y>: r)"
 (fn _=> [ (fast_tac pair_cs 1) ]);

val domainI = prove_goal ZF.thy "!!a b r. <a,b>: r ==> a: domain(r)"
 (fn _ => [ (etac (exI RS (domain_iff RS iffD2)) 1) ]);

val domainE = prove_goal ZF.thy
    "[| a : domain(r);  !!y. <a,y>: r ==> P |] ==> P"
 (fn prems=>
  [ (rtac (domain_iff RS iffD1 RS exE) 1),
    (REPEAT (ares_tac prems 1)) ]);

val domain_of_prod = prove_goal ZF.thy "!!A B. b:B ==> domain(A*B) = A"
 (fn _ =>
  [ (REPEAT (eresolve_tac [domainE,SigmaE2] 1
     ORELSE ares_tac [domainI,equalityI,subsetI,SigmaI] 1)) ]);

val domain_empty = prove_goal ZF.thy "domain(0) = 0"
 (fn _ =>
  [ (REPEAT (eresolve_tac [domainE,emptyE] 1
     ORELSE ares_tac [equalityI,subsetI] 1)) ]);

val domain_subset = prove_goal ZF.thy "domain(Sigma(A,B)) <= A"
 (fn _ =>
  [ (rtac subsetI 1),
    (etac domainE 1),
    (etac SigmaD1 1) ]);


(*** range ***)

val rangeI = prove_goalw ZF.thy [range_def] "!!a b r.<a,b>: r ==> b : range(r)"
 (fn _ => [ (etac (converseI RS domainI) 1) ]);

val rangeE = prove_goalw ZF.thy [range_def]
    "[| b : range(r);  !!x. <x,b>: r ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS domainE) 1),
    (resolve_tac prems 1),
    (etac converseD 1) ]);

val range_of_prod = prove_goalw ZF.thy [range_def]
    "!!a A B. a:A ==> range(A*B) = B"
 (fn _ =>
  [ (rtac (converse_of_prod RS ssubst) 1),
    (etac domain_of_prod 1) ]);

val range_empty = prove_goalw ZF.thy [range_def] "range(0) = 0"
 (fn _ =>
  [ (rtac (converse_empty RS ssubst) 1),
    (rtac domain_empty 1) ]);

val range_subset = prove_goalw ZF.thy [range_def] "range(A*B) <= B"
 (fn _ =>
  [ (rtac (converse_of_prod RS ssubst) 1),
    (rtac domain_subset 1) ]);


(*** field ***)

val fieldI1 = prove_goalw ZF.thy [field_def] "<a,b>: r ==> a : field(r)"
 (fn [prem]=>
  [ (rtac (prem RS domainI RS UnI1) 1) ]);

val fieldI2 = prove_goalw ZF.thy [field_def] "<a,b>: r ==> b : field(r)"
 (fn [prem]=>
  [ (rtac (prem RS rangeI RS UnI2) 1) ]);

val fieldCI = prove_goalw ZF.thy [field_def]
    "(~ <c,a>:r ==> <a,b>: r) ==> a : field(r)"
 (fn [prem]=>
  [ (rtac (prem RS domainI RS UnCI) 1),
    (swap_res_tac [rangeI] 1),
    (etac notnotD 1) ]);

val fieldE = prove_goalw ZF.thy [field_def]
     "[| a : field(r);  \
\        !!x. <a,x>: r ==> P;  \
\        !!x. <x,a>: r ==> P        |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS UnE) 1),
    (REPEAT (eresolve_tac (prems@[domainE,rangeE]) 1)) ]);

val field_of_prod = prove_goal ZF.thy "field(A*A) = A"
 (fn _ =>
  [ (fast_tac (pair_cs addIs  [fieldCI,equalityI] addSEs [fieldE]) 1) ]);

val field_subset = prove_goal ZF.thy "field(A*B) <= A Un B"
 (fn _ => [ (fast_tac (pair_cs addIs  [fieldCI] addSEs [fieldE]) 1) ]);

val domain_subset_field = prove_goalw ZF.thy [field_def]
    "domain(r) <= field(r)"
 (fn _ => [ (rtac Un_upper1 1) ]);

val range_subset_field = prove_goalw ZF.thy [field_def]
    "range(r) <= field(r)"
 (fn _ => [ (rtac Un_upper2 1) ]);

val domain_times_range = prove_goal ZF.thy
    "!!A B r. r <= Sigma(A,B) ==> r <= domain(r)*range(r)"
 (fn _ => [ (fast_tac (pair_cs addIs [domainI,rangeI]) 1) ]);

val field_times_field = prove_goal ZF.thy
    "!!A B r. r <= Sigma(A,B) ==> r <= field(r)*field(r)"
 (fn _ => [ (fast_tac (pair_cs addIs [fieldI1,fieldI2]) 1) ]);


(*** Image of a set under a function/relation ***)

val image_iff = prove_goalw ZF.thy [image_def]
    "b : r``A <-> (EX x:A. <x,b>:r)"
 (fn _ => [ fast_tac (pair_cs addIs [rangeI]) 1 ]);

val image_singleton_iff = prove_goal ZF.thy
    "b : r``{a} <-> <a,b>:r"
 (fn _ => [ rtac (image_iff RS iff_trans) 1,
	    fast_tac pair_cs 1 ]);

val imageI = prove_goalw ZF.thy [image_def]
    "!!a b r. [| <a,b>: r;  a:A |] ==> b : r``A"
 (fn _ => [ (REPEAT (ares_tac [CollectI,rangeI,bexI] 1)) ]);

val imageE = prove_goalw ZF.thy [image_def]
    "[| b: r``A;  !!x.[| <x,b>: r;  x:A |] ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS CollectE) 1),
    (REPEAT (etac bexE 1 ORELSE ares_tac prems 1)) ]);

val image_subset = prove_goal ZF.thy
    "!!A B r. r <= A*B ==> r``C <= B"
 (fn _ =>
  [ (rtac subsetI 1),
    (REPEAT (eresolve_tac [asm_rl, imageE, subsetD RS SigmaD2] 1)) ]);


(*** Inverse image of a set under a function/relation ***)

val vimage_iff = prove_goalw ZF.thy [vimage_def,image_def,converse_def]
    "a : r-``B <-> (EX y:B. <a,y>:r)"
 (fn _ => [ fast_tac (pair_cs addIs [rangeI]) 1 ]);

val vimage_singleton_iff = prove_goal ZF.thy
    "a : r-``{b} <-> <a,b>:r"
 (fn _ => [ rtac (vimage_iff RS iff_trans) 1,
	    fast_tac pair_cs 1 ]);

val vimageI = prove_goalw ZF.thy [vimage_def]
    "!!A B r. [| <a,b>: r;  b:B |] ==> a : r-``B"
 (fn _ => [ (REPEAT (ares_tac [converseI RS imageI] 1)) ]);

val vimageE = prove_goalw ZF.thy [vimage_def]
    "[| a: r-``B;  !!x.[| <a,x>: r;  x:B |] ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS imageE) 1),
    (REPEAT (etac converseD 1 ORELSE ares_tac prems 1)) ]);

val vimage_subset = prove_goalw ZF.thy [vimage_def]
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
val rel_Union = result();

(** The Union of 2 relations is a relation (Lemma for fun_Un)  **)
val rel_Un = prove_goal ZF.thy
    "!!r s. [| r <= A*B;  s <= C*D |] ==> (r Un s) <= (A Un C) * (B Un D)"
 (fn _ => [ (fast_tac ZF_cs 1) ]);


