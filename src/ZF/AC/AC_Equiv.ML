(*  Title: 	ZF/AC/AC_Equiv.ML
    ID:         $Id$
    Author: 	Krzysztof Gr`abczewski

*)


open AC_Equiv;

val AC_aux_defs = [pairwise_disjoint_def, sets_of_size_between_def];

(* ******************************************** *)

(* Theorems analogous to ones presented in "ZF/Ordinal.ML" *)

(* lemma for nat_le_imp_lepoll *)
val [prem] = goalw Cardinal.thy [lepoll_def]
             "m:nat ==> ALL n: nat. m le n --> m lepoll n";
by (nat_ind_tac "m" [prem] 1);
by (fast_tac (ZF_cs addSIs [le_imp_subset RS id_subset_inj]) 1);
by (rtac ballI 1);
by (eres_inst_tac [("n","n")] natE 1);
by (asm_simp_tac (ZF_ss addsimps [inj_def, succI1 RS Pi_empty2]) 1);
by (fast_tac (ZF_cs addSDs [le0D]) 1);
by (fast_tac (ZF_cs addSIs [le_imp_subset RS id_subset_inj]) 1);
val nat_le_imp_lepoll_lemma = result();

(* used in : AC10-AC15.ML WO1-WO6.ML WO6WO1.ML*)
val nat_le_imp_lepoll = nat_le_imp_lepoll_lemma RS bspec RS mp |> standard;

(* ********************************************************************** *)
(*             lemmas concerning FOL and pure ZF theory                   *)
(* ********************************************************************** *)

(* The following two theorms are useful when rewriting only one instance  *) 
(* of a definition							  *)
(* first one for definitions of formulae and the second for terms	  *)

val prems = goal ZF.thy "(A == B) ==> A <-> B";
by (asm_simp_tac (ZF_ss addsimps prems) 1);
val def_imp_iff = result();

val prems = goal ZF.thy "(A == B) ==> P(A) <-> P(B)";
by (asm_simp_tac (ZF_ss addsimps prems) 1);
val def_imp_iff_P = result();

(* used only in lemmas4-7.ML *)
(*Note modified statement and proof*)
goal ZF.thy "!!X. X~=0 ==> (A->X)~=0";
by (fast_tac (ZF_cs addSIs [equals0I,lam_type] addSEs [equals0D]) 1);
val fun_space_not0I = result();

(* used only in WO1_DC.ML *)
(*Note simpler proof*)
goal ZF.thy "!!A f g. [| ALL x:A. f`x=g`x; f:Df->Cf; g:Dg->Cg;  \
\         A<=Df; A<=Dg |] ==> f``A=g``A";
by (asm_simp_tac (ZF_ss addsimps [image_fun]) 1);
val images_eq = result();

(* used in : AC10-AC15.ML AC16WO4.ML WO6WO1.ML *)
(*I don't know where to put this one.*)
goal Cardinal.thy
     "!!m A B. [| A lepoll succ(m); B<=A; B~=0 |] ==> A-B lepoll m";
by (resolve_tac [not_emptyE] 1 THEN (atac 1));
by (forward_tac [singleton_subsetI] 1);
by (forward_tac [subsetD] 1 THEN (atac 1));
by (res_inst_tac [("A2","A")] 
     (diff_sing_lepoll RSN (2, subset_imp_lepoll RS lepoll_trans)) 1 
    THEN (REPEAT (atac 2)));
by (fast_tac ZF_cs 1);
val Diff_lepoll = result();

(* ********************************************************************** *)
(*              lemmas concerning lepoll and eqpoll relations             *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(*                    Theorems concerning ordinals                        *)
(* ********************************************************************** *)

(* lemma for ordertype_Int *)
goalw Cardinal.thy [rvimage_def] "rvimage(A,id(A),r) = r Int A*A";
by (resolve_tac [equalityI] 1);
by (step_tac ZF_cs 1);
by (dres_inst_tac [("P","%a. <id(A)`xb,a>:r")] (id_conv RS subst) 1
    THEN (atac 1));
by (dres_inst_tac [("P","%a. <a,ya>:r")] (id_conv RS subst) 1
    THEN (REPEAT (atac 1)));
by (fast_tac (ZF_cs addIs [id_conv RS ssubst]) 1);
val rvimage_id = result();

(* used only in Hartog.ML *)
goal Cardinal.thy
	"!!A r. well_ord(A,r) ==> ordertype(A, r Int A*A) = ordertype(A,r)";
by (res_inst_tac [("P","%a. ordertype(A,a)=ordertype(A,r)")] 
    (rvimage_id RS subst) 1);
by (eresolve_tac [id_bij RS bij_ordertype_vimage] 1);
val ordertype_Int = result();

(* used only in AC16_lemmas.ML *)
goalw CardinalArith.thy [InfCard_def]
	"!!i. [| ~Finite(i); Card(i) |] ==> InfCard(i)";
by (asm_simp_tac (ZF_ss addsimps [Card_is_Ord RS nat_le_infinite_Ord]) 1);
val Inf_Card_is_InfCard = result();
