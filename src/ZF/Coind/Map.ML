(*  Title:      ZF/Coind/Map.ML
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

open Map;

(* ############################################################ *)
(* Lemmas                                                       *)
(* ############################################################ *)

goal Map.thy "!!A. a:A ==> Sigma(A,B)``{a} = B(a)";
by (fast_tac eq_cs 1);
qed "qbeta";

goal Map.thy "!!A. a~:A ==> Sigma(A,B)``{a} = 0";
by (fast_tac eq_cs 1);
qed "qbeta_emp";

goal Map.thy "!!A.a ~: A ==> Sigma(A,B)``{a}=0";
by (fast_tac eq_cs 1);
qed "image_Sigma1";

goal Map.thy "0``A = 0";
by (fast_tac eq_cs 1);
qed "image_02";

(* ############################################################ *)
(* Inclusion in Quine Universes                                 *)
(* ############################################################ *)

(* Lemmas *)

goalw Map.thy [quniv_def]
    "!!A. A <= univ(X) ==> Pow(A * Union(quniv(X))) <= quniv(X)";
by (rtac Pow_mono 1);
by (rtac ([Sigma_mono, product_univ] MRS subset_trans) 1);
by (etac subset_trans 1);
by (rtac (arg_subset_eclose RS univ_mono) 1);
by (simp_tac (!simpset addsimps [Union_Pow_eq]) 1);
qed "MapQU_lemma";

(* Theorems *)

val prems = goalw Map.thy [PMap_def,TMap_def]
  "[| m:PMap(A,quniv(B)); !!x.x:A ==> x:univ(B) |] ==> m:quniv(B)";
by (cut_facts_tac prems 1);
by (rtac (MapQU_lemma RS subsetD) 1);
by (rtac subsetI 1);
by (eresolve_tac prems 1);
by (Fast_tac 1);
qed "mapQU";

(* ############################################################ *)
(* Monotonicity                                                 *)
(* ############################################################ *)

goalw Map.thy [PMap_def,TMap_def] "!!A.B<=C ==> PMap(A,B)<=PMap(A,C)";
by (Fast_tac 1);
qed "map_mono";

(* Rename to pmap_mono *)

(* ############################################################ *)
(* Introduction Rules                                           *)
(* ############################################################ *)

(** map_emp **)

goalw Map.thy [map_emp_def,PMap_def,TMap_def] "map_emp:PMap(A,B)";
by (safe_tac (!claset));
by (rtac image_02 1);
qed "pmap_empI";

(** map_owr **)


goalw Map.thy [map_owr_def,PMap_def,TMap_def] 
  "!! A.[| m:PMap(A,B); a:A; b:B |]  ==> map_owr(m,a,b):PMap(A,B)";
by (Step_tac 1);
by (ALLGOALS (asm_full_simp_tac (!simpset addsimps [if_iff])));
by (Fast_tac 1);
by (Fast_tac 1);
by (Deepen_tac 2 1);
(*Remaining subgoal*)
by (rtac (excluded_middle RS disjE) 1);
by (etac image_Sigma1 1);
by (dres_inst_tac [("psi", "?uu ~: B")] asm_rl 1);
by (asm_full_simp_tac
    (!simpset addsimps [qbeta] setloop split_tac [expand_if]) 1);
by (safe_tac (!claset));
by (dres_inst_tac [("psi", "?uu ~: B")] asm_rl 3);
by (ALLGOALS Asm_full_simp_tac);
by (Fast_tac 1);
qed "pmap_owrI";

(** map_app **)

goalw Map.thy [TMap_def,map_app_def] 
  "!!m.[| m:TMap(A,B); a:domain(m) |] ==> map_app(m,a) ~=0";
by (etac domainE 1);
by (dtac imageI 1);
by (Fast_tac 1);
by (etac not_emptyI 1);
qed "tmap_app_notempty";

goalw Map.thy [TMap_def,map_app_def,domain_def] 
  "!!m.[| m:TMap(A,B); a:domain(m) |] ==> map_app(m,a):B";
by (fast_tac eq_cs 1);
qed "tmap_appI";

goalw Map.thy [PMap_def]
  "!!m.[| m:PMap(A,B); a:domain(m) |] ==> map_app(m,a):B";
by (forward_tac [tmap_app_notempty] 1); 
by (assume_tac 1);
by (dtac tmap_appI 1); 
by (assume_tac 1);
by (Fast_tac 1);
qed "pmap_appI";

(** domain **)

goalw Map.thy [TMap_def]
  "!!m.[| m:TMap(A,B); a:domain(m) |] ==> a:A";
by (fast_tac eq_cs 1);
qed "tmap_domainD";

goalw Map.thy [PMap_def,TMap_def]
  "!!m.[| m:PMap(A,B); a:domain(m) |] ==> a:A";
by (fast_tac eq_cs 1);
qed "pmap_domainD";

(* ############################################################ *)
(* Equalitites                                                  *)
(* ############################################################ *)

(** Domain **)

(* Lemmas *)

goal Map.thy  "domain(UN x:A.B(x)) = (UN x:A.domain(B(x)))";
by (fast_tac eq_cs 1);
qed "domain_UN";

goal Map.thy  "domain(Sigma(A,B)) = {x:A.EX y.y:B(x)}";
by (simp_tac (!simpset addsimps [domain_UN,domain_0,domain_cons]) 1);
by (fast_tac eq_cs 1);
qed "domain_Sigma";

(* Theorems *)

goalw Map.thy [map_emp_def] "domain(map_emp) = 0";
by (fast_tac eq_cs 1);
qed "map_domain_emp";

goalw Map.thy [map_owr_def] 
  "!!a.b ~= 0 ==> domain(map_owr(f,a,b)) = {a} Un domain(f)";
by (simp_tac (!simpset addsimps [domain_Sigma]) 1);
by (rtac equalityI 1);
by (fast_tac eq_cs 1);
by (rtac subsetI 1);
by (rtac CollectI 1);
by (assume_tac 1);
by (etac UnE' 1);
by (etac singletonE 1);
by (Asm_simp_tac 1);
by (fast_tac eq_cs 1);
by (fast_tac (eq_cs addss (!simpset)) 1);
qed "map_domain_owr";

(** Application **)

goalw Map.thy [map_app_def,map_owr_def] 
  "map_app(map_owr(f,a,b),a) = b";
by (stac qbeta 1);
by (Fast_tac 1);
by (Simp_tac 1);
qed "map_app_owr1";

goalw Map.thy [map_app_def,map_owr_def] 
  "!!a.c ~= a ==> map_app(map_owr(f,a,b),c)= map_app(f,c)";
by (rtac (excluded_middle RS disjE) 1);
by (stac qbeta_emp 1);
by (assume_tac 1);
by (fast_tac eq_cs 1);
by (etac (qbeta RS ssubst) 1);
by (Asm_simp_tac 1);
qed "map_app_owr2";









































