(*  Title:      ZF/AC/AC_Equiv.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

*)


open AC_Equiv;

val WO_defs = [WO1_def, WO2_def, WO3_def, WO4_def, WO5_def, WO6_def, WO8_def];
 
val AC_defs = [AC0_def, AC1_def, AC2_def, AC3_def, AC4_def, AC5_def, 
               AC6_def, AC7_def, AC8_def, AC9_def, AC10_def, AC11_def, 
               AC12_def, AC13_def, AC14_def, AC15_def, AC16_def, 
               AC17_def, AC18_def, AC19_def];
 
val AC_aux_defs = [pairwise_disjoint_def, sets_of_size_between_def];
 
(* ******************************************** *)

(* Theorems analogous to ones presented in "ZF/Ordinal.ML" *)

(* lemma for nat_le_imp_lepoll *)
val [prem] = goalw Cardinal.thy [lepoll_def]
             "m:nat ==> ALL n: nat. m le n --> m lepoll n";
by (nat_ind_tac "m" [prem] 1);
by (fast_tac (!claset addSIs [le_imp_subset RS id_subset_inj]) 1);
by (rtac ballI 1);
by (eres_inst_tac [("n","n")] natE 1);
by (asm_simp_tac (!simpset addsimps [inj_def, succI1 RS Pi_empty2]) 1);
by (fast_tac (!claset addSIs [le_imp_subset RS id_subset_inj]) 1);
val nat_le_imp_lepoll_lemma = result();

(* used in : AC10-AC15.ML WO1-WO6.ML WO6WO1.ML*)
val nat_le_imp_lepoll = nat_le_imp_lepoll_lemma RS bspec RS mp |> standard;

(* ********************************************************************** *)
(*             lemmas concerning FOL and pure ZF theory                   *)
(* ********************************************************************** *)

goal thy "!!X. (A->X)=0 ==> X=0";
by (fast_tac (!claset addSIs [equals0I] addEs [lam_type RSN (2, equals0D)]) 1);
val fun_space_emptyD = result();

(* used only in WO1_DC.ML *)
(*Note simpler proof*)
goal ZF.thy "!!A f g. [| ALL x:A. f`x=g`x; f:Df->Cf; g:Dg->Cg;  \
\         A<=Df; A<=Dg |] ==> f``A=g``A";
by (asm_simp_tac (!simpset addsimps [image_fun]) 1);
val images_eq = result();

(* used in : AC10-AC15.ML AC16WO4.ML WO6WO1.ML *)
(*I don't know where to put this one.*)
goal Cardinal.thy
     "!!m A B. [| A lepoll succ(m); B<=A; B~=0 |] ==> A-B lepoll m";
by (rtac not_emptyE 1 THEN (assume_tac 1));
by (forward_tac [singleton_subsetI] 1);
by (forward_tac [subsetD] 1 THEN (assume_tac 1));
by (res_inst_tac [("A2","A")] 
     (Diff_sing_lepoll RSN (2, subset_imp_lepoll RS lepoll_trans)) 1 
    THEN (REPEAT (assume_tac 2)));
by (Fast_tac 1);
val Diff_lepoll = result();

(* ********************************************************************** *)
(*              lemmas concerning lepoll and eqpoll relations             *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(*                    Theorems concerning ordinals                        *)
(* ********************************************************************** *)

(* lemma for ordertype_Int *)
goalw Cardinal.thy [rvimage_def] "rvimage(A,id(A),r) = r Int A*A";
by (rtac equalityI 1);
by (Step_tac 1);
by (dres_inst_tac [("P","%a. <id(A)`xb,a>:r")] (id_conv RS subst) 1
    THEN (assume_tac 1));
by (dres_inst_tac [("P","%a. <a,ya>:r")] (id_conv RS subst) 1
    THEN (REPEAT (assume_tac 1)));
by (fast_tac (!claset addIs [id_conv RS ssubst]) 1);
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
by (asm_simp_tac (!simpset addsimps [Card_is_Ord RS nat_le_infinite_Ord]) 1);
val Inf_Card_is_InfCard = result();

goal thy "(THE z. {x}={z}) = x";
by (fast_tac (!claset addSIs [the_equality]
                addSEs [singleton_eq_iff RS iffD1 RS sym]) 1);
val the_element = result();

goal thy "(lam x:A. {x}) : bij(A, {{x}. x:A})";
by (res_inst_tac [("d","%z. THE x. z={x}")] lam_bijective 1);
by (TRYALL (eresolve_tac [RepFunI, RepFunE]));
by (REPEAT (asm_full_simp_tac (!simpset addsimps [the_element]) 1));
val lam_sing_bij = result();

val [major,minor] = goal thy 
        "[| f : Pi(A,B); (!!x. x:A ==> B(x)<=C(x)) |] ==> f : Pi(A,C)";
by (fast_tac (!claset addSIs [major RS Pi_type, minor RS subsetD,
                major RS apply_type]) 1);
val Pi_weaken_type = result();

val [major, minor] = goalw thy [inj_def]
        "[| f:inj(A, B); (!!a. a:A ==> f`a : C) |] ==> f:inj(A,C)";
by (fast_tac (!claset addSEs [minor]
        addSIs [major RS CollectD1 RS Pi_type, major RS CollectD2]) 1);
val inj_strengthen_type = result();

goal thy "A*B=0 <-> A=0 | B=0";
by (fast_tac (!claset addSIs [equals0I] addEs [equals0D]) 1);
val Sigma_empty_iff = result();

goalw thy [Finite_def] "!!n. n:nat ==> Finite(n)";
by (fast_tac (!claset addSIs [eqpoll_refl]) 1);
val nat_into_Finite = result();

goalw thy [Finite_def] "~Finite(nat)";
by (fast_tac (!claset addSDs [eqpoll_imp_lepoll]
                addIs [Ord_nat RSN (2, ltI) RS lt_not_lepoll RS notE]) 1);
val nat_not_Finite = result();

val le_imp_lepoll = le_imp_subset RS subset_imp_lepoll;

(* ********************************************************************** *)
(* Another elimination rule for EX!                                       *)
(* ********************************************************************** *)

goal thy "!!x. [| EX! x. P(x); P(x); P(y) |] ==> x=y";
by (etac ex1E 1);
by (res_inst_tac [("b","xa")] (sym RSN (2, trans)) 1);
by (Fast_tac 1);
by (Fast_tac 1);
val ex1_two_eq = result();

(* ********************************************************************** *)
(* image of a surjection                                                  *)
(* ********************************************************************** *)

goalw thy [surj_def] "!!f. f : surj(A, B) ==> f``A = B";
by (etac CollectE 1);
by (resolve_tac [subset_refl RSN (2, image_fun) RS ssubst] 1 
    THEN (assume_tac 1));
by (fast_tac (!claset addSEs [apply_type] addIs [equalityI]) 1);
val surj_image_eq = result();


goal thy "!!y. succ(x) lepoll y ==> y ~= 0";
by (fast_tac (!claset addSDs [lepoll_0_is_0]) 1);
val succ_lepoll_imp_not_empty = result();

goal thy "!!x. x eqpoll succ(n) ==> x ~= 0";
by (fast_tac (!claset addSEs [eqpoll_sym RS eqpoll_0_is_0 RS succ_neq_0]) 1);
val eqpoll_succ_imp_not_empty = result();

