(*  Title:      ZF/Coind/Map.ML
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

open Map;

(** Some sample proofs of inclusions for the final coalgebra "U" (by lcp) **)

Goalw [TMap_def] "{0,1} <= {1} Un TMap(I, {0,1})";
by (Blast_tac 1);
result();

Goalw [TMap_def] "{0} Un TMap(I,1) <= {1} Un TMap(I, {0} Un TMap(I,1))";
by (Blast_tac 1);
result();

Goalw [TMap_def] "{0,1} Un TMap(I,2) <= {1} Un TMap(I, {0,1} Un TMap(I,2))";
by (Blast_tac 1);
result();

(*TOO SLOW
Goalw [TMap_def]
     "{0,1} Un TMap(I,TMap(I,2)) Un TMap(I,2) <= \
\     {1} Un TMap(I, {0,1} Un TMap(I,TMap(I,2)) Un TMap(I,2))";
by (Blast_tac 1);
result();
*)


(* ############################################################ *)
(* Lemmas                                                       *)
(* ############################################################ *)

Goal "Sigma(A,B)``{a} = (if a:A then B(a) else 0)";
by Auto_tac;
qed "qbeta_if";

Goal "a:A ==> Sigma(A,B)``{a} = B(a)";
by (Fast_tac 1);
qed "qbeta";

Goal "a~:A ==> Sigma(A,B)``{a} = 0";
by (Fast_tac 1);
qed "qbeta_emp";

Goal "a ~: A ==> Sigma(A,B)``{a}=0";
by (Fast_tac 1);
qed "image_Sigma1";


(* ############################################################ *)
(* Inclusion in Quine Universes                                 *)
(* ############################################################ *)

(* Lemmas *)

Goalw [quniv_def]
    "A <= univ(X) ==> Pow(A * Union(quniv(X))) <= quniv(X)";
by (rtac Pow_mono 1);
by (rtac ([Sigma_mono, product_univ] MRS subset_trans) 1);
by (etac subset_trans 1);
by (rtac (arg_subset_eclose RS univ_mono) 1);
by (simp_tac (simpset() addsimps [Union_Pow_eq]) 1);
qed "MapQU_lemma";

(* Theorems *)

val prems = goalw Map.thy [PMap_def,TMap_def]
  "[| m:PMap(A,quniv(B)); !!x. x:A ==> x:univ(B) |] ==> m:quniv(B)";
by (cut_facts_tac prems 1);
by (rtac (MapQU_lemma RS subsetD) 1);
by (rtac subsetI 1);
by (eresolve_tac prems 1);
by (Fast_tac 1);
qed "mapQU";

(* ############################################################ *)
(* Monotonicity                                                 *)
(* ############################################################ *)

Goalw [PMap_def,TMap_def] "B<=C ==> PMap(A,B)<=PMap(A,C)";
by (Fast_tac 1);
qed "map_mono";

(* Rename to pmap_mono *)

(* ############################################################ *)
(* Introduction Rules                                           *)
(* ############################################################ *)

(** map_emp **)

Goalw [map_emp_def,PMap_def,TMap_def] "map_emp:PMap(A,B)";
by Auto_tac;
qed "pmap_empI";

(** map_owr **)


Goalw [map_owr_def,PMap_def,TMap_def] 
  "[| m:PMap(A,B); a:A; b:B |]  ==> map_owr(m,a,b):PMap(A,B)";
by Safe_tac;
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [if_iff])));
by (Fast_tac 1);
by (Fast_tac 1);
by (Deepen_tac 2 1);
(*Remaining subgoal*)
by (rtac (excluded_middle RS disjE) 1);
by (etac image_Sigma1 1);
by (dres_inst_tac [("psi", "?uu ~: B")] asm_rl 1);
by (asm_full_simp_tac (simpset() addsimps [qbeta]) 1);
by Safe_tac;
by (dres_inst_tac [("psi", "?uu ~: B")] asm_rl 3);
by (ALLGOALS Asm_full_simp_tac);
by (Fast_tac 1);
qed "pmap_owrI";

(** map_app **)

Goalw [TMap_def,map_app_def] 
  "[| m:TMap(A,B); a:domain(m) |] ==> map_app(m,a) ~=0";
by (etac domainE 1);
by (dtac imageI 1);
by (Fast_tac 1);
by (etac not_emptyI 1);
qed "tmap_app_notempty";

Goalw [TMap_def,map_app_def,domain_def] 
  "[| m:TMap(A,B); a:domain(m) |] ==> map_app(m,a):B";
by (Fast_tac 1);
qed "tmap_appI";

Goalw [PMap_def]
  "[| m:PMap(A,B); a:domain(m) |] ==> map_app(m,a):B";
by (ftac tmap_app_notempty 1); 
by (assume_tac 1);
by (dtac tmap_appI 1); 
by (assume_tac 1);
by (Fast_tac 1);
qed "pmap_appI";

(** domain **)

Goalw [TMap_def]
  "[| m:TMap(A,B); a:domain(m) |] ==> a:A";
by (Fast_tac 1);
qed "tmap_domainD";

Goalw [PMap_def,TMap_def]
  "[| m:PMap(A,B); a:domain(m) |] ==> a:A";
by (Fast_tac 1);
qed "pmap_domainD";

(* ############################################################ *)
(* Equalities                                                   *)
(* ############################################################ *)

(** Domain **)

(* Lemmas *)

Goal  "domain(UN x:A. B(x)) = (UN x:A. domain(B(x)))";
by (Fast_tac 1);
qed "domain_UN";

Goal  "domain(Sigma(A,B)) = {x:A. EX y. y:B(x)}";
by (simp_tac (simpset() addsimps [domain_UN,domain_0,domain_cons]) 1);
by (Fast_tac 1);
qed "domain_Sigma";

(* Theorems *)

Goalw [map_emp_def] "domain(map_emp) = 0";
by (Fast_tac 1);
qed "map_domain_emp";

Goalw [map_owr_def] 
  "b ~= 0 ==> domain(map_owr(f,a,b)) = {a} Un domain(f)";
by (simp_tac (simpset() addsimps [domain_Sigma]) 1);
by (rtac equalityI 1);
by (Fast_tac 1);
by (rtac subsetI 1);
by (rtac CollectI 1);
by (assume_tac 1);
by (etac UnE' 1);
by (etac singletonE 1);
by (Asm_simp_tac 1);
by (Fast_tac 1);
by (fast_tac (claset() addss (simpset())) 1);
qed "map_domain_owr";

(** Application **)

Goalw [map_app_def,map_owr_def] 
  "map_app(map_owr(f,a,b),c) = (if c=a then b else map_app(f,c))";
by (asm_simp_tac (simpset() addsimps [qbeta_if]) 1);
by (Fast_tac 1);
qed "map_app_owr";

Goal "map_app(map_owr(f,a,b),a) = b";
by (asm_simp_tac (simpset() addsimps [map_app_owr]) 1);
qed "map_app_owr1";

Goal "c ~= a ==> map_app(map_owr(f,a,b),c)= map_app(f,c)";
by (asm_simp_tac (simpset() addsimps [map_app_owr]) 1);
qed "map_app_owr2";
