(*  Title: 	Relation.ML
    ID:         $Id$
    Authors: 	Riccardo Mattolini, Dip. Sistemi e Informatica
        	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994 Universita' di Firenze
    Copyright   1993  University of Cambridge

Functions represented as relations in HOL Set Theory 
*)

val RSLIST = curry (op MRS);

open Relation;

goalw Relation.thy [converse_def] "!!a b r. <a,b>:r ==> <b,a>:converse(r)";
by (simp_tac prod_ss 1);
by (fast_tac set_cs 1);
qed "converseI";

goalw Relation.thy [converse_def] "!!a b r. <a,b> : converse(r) ==> <b,a> : r";
by (fast_tac comp_cs 1);
qed "converseD";

qed_goalw "converseE" Relation.thy [converse_def]
    "[| yx : converse(r);  \
\       !!x y. [| yx=<y,x>;  <x,y>:r |] ==> P \
\    |] ==> P"
 (fn [major,minor]=>
  [ (rtac (major RS CollectE) 1),
    (REPEAT (eresolve_tac [bexE,exE, conjE, minor] 1)),
    (hyp_subst_tac 1),
    (assume_tac 1) ]);

val converse_cs = comp_cs addSIs [converseI] 
			  addSEs [converseD,converseE];

qed_goalw "Domain_iff" Relation.thy [Domain_def]
    "a: Domain(r) = (EX y. <a,y>: r)"
 (fn _=> [ (fast_tac comp_cs 1) ]);

qed_goal "DomainI" Relation.thy "!!a b r. <a,b>: r ==> a: Domain(r)"
 (fn _ => [ (etac (exI RS (Domain_iff RS iffD2)) 1) ]);

qed_goal "DomainE" Relation.thy
    "[| a : Domain(r);  !!y. <a,y>: r ==> P |] ==> P"
 (fn prems=>
  [ (rtac (Domain_iff RS iffD1 RS exE) 1),
    (REPEAT (ares_tac prems 1)) ]);

qed_goalw "RangeI" Relation.thy [Range_def] "!!a b r.<a,b>: r ==> b : Range(r)"
 (fn _ => [ (etac (converseI RS DomainI) 1) ]);

qed_goalw "RangeE" Relation.thy [Range_def]
    "[| b : Range(r);  !!x. <x,b>: r ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS DomainE) 1),
    (resolve_tac prems 1),
    (etac converseD 1) ]);

(*** Image of a set under a function/relation ***)

qed_goalw "Image_iff" Relation.thy [Image_def]
    "b : r^^A = (? x:A. <x,b>:r)"
 (fn _ => [ fast_tac (comp_cs addIs [RangeI]) 1 ]);

qed_goal "Image_singleton_iff" Relation.thy
    "(b : r^^{a}) = (<a,b>:r)"
 (fn _ => [ rtac (Image_iff RS trans) 1,
	    fast_tac comp_cs 1 ]);

qed_goalw "ImageI" Relation.thy [Image_def]
    "!!a b r. [| <a,b>: r;  a:A |] ==> b : r^^A"
 (fn _ => [ (REPEAT (ares_tac [CollectI,RangeI,bexI] 1)),
            (resolve_tac [conjI ] 1),
            (resolve_tac [RangeI] 1),
            (REPEAT (fast_tac set_cs 1))]);

qed_goalw "ImageE" Relation.thy [Image_def]
    "[| b: r^^A;  !!x.[| <x,b>: r;  x:A |] ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS CollectE) 1),
    (safe_tac set_cs),
    (etac RangeE 1),
    (rtac (hd prems) 1),
    (REPEAT (etac bexE 1 ORELSE ares_tac prems 1)) ]);

qed_goal "Image_subset" Relation.thy
    "!!A B r. r <= Sigma A (%x.B) ==> r^^C <= B"
 (fn _ =>
  [ (rtac subsetI 1),
    (REPEAT (eresolve_tac [asm_rl, ImageE, subsetD RS SigmaD2] 1)) ]);

val rel_cs = converse_cs addSIs [converseI] 
                         addIs  [ImageI, DomainI, RangeI]
                         addSEs [ImageE, DomainE, RangeE];

val rel_eq_cs = rel_cs addSIs [equalityI];

