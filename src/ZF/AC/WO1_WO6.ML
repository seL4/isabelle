(*  Title:      ZF/AC/WO1_WO6.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

  Proofs needed to state that formulations WO1,...,WO6 are all equivalent.
  All but one WO6 ==> WO1 (placed in separate file WO6_WO1.ML)

  Every proof (exept one) presented in this file are referred as "clear"
  by Rubin & Rubin (page 2). 
  They refer reader to a book by Gödel to see the proof WO1 ==> WO2.
  Fortunately order types made this proof also very easy.
*)

(* ********************************************************************** *)

Goalw WO_defs "WO2 ==> WO3";
by (Fast_tac 1);
qed "WO2_WO3";

(* ********************************************************************** *)

Goalw (eqpoll_def::WO_defs) "WO3 ==> WO1";
by (fast_tac (claset() addSEs [bij_is_inj RS well_ord_rvimage, 
			      well_ord_Memrel RS well_ord_subset]) 1);
qed "WO3_WO1";

(* ********************************************************************** *)

Goalw (eqpoll_def::WO_defs) "WO1 ==> WO2";
by (fast_tac (claset() addSIs [Ord_ordertype, ordermap_bij]) 1);
qed "WO1_WO2";

(* ********************************************************************** *)

Goal "f \\<in> A->B ==> (\\<lambda>x \\<in> A. {f`x}): A -> {{b}. b \\<in> B}";
by (fast_tac (claset() addSIs [lam_type, apply_type]) 1);
qed "lam_sets";

Goalw [surj_def] "f \\<in> surj(A,B) ==> (\\<Union>a \\<in> A. {f`a}) = B";
by (fast_tac (claset() addSEs [apply_type]) 1);
qed "surj_imp_eq_";

Goal "[| f \\<in> surj(A,B); Ord(A) |] ==> (\\<Union>a<A. {f`a}) = B";
by (fast_tac (claset() addSDs [surj_imp_eq_]
                addSIs [ltI] addSEs [ltE]) 1);
qed "surj_imp_eq";

Goalw WO_defs "WO1 ==> WO4(1)";
by (rtac allI 1);
by (eres_inst_tac [("x","A")] allE 1);
by (etac exE 1);
by (REPEAT (resolve_tac [exI, conjI] 1));
by (etac Ord_ordertype 1);
by (rtac conjI 1);
by (eresolve_tac [ordermap_bij RS bij_converse_bij RS bij_is_fun RS
                lam_sets RS domain_of_fun] 1);
by (asm_simp_tac (simpset() addsimps [singleton_eqpoll_1 RS eqpoll_imp_lepoll,
                  Ord_ordertype RSN (2, ordermap_bij RS bij_converse_bij RS
                        bij_is_surj RS surj_imp_eq)]) 1);
qed "WO1_WO4";

(* ********************************************************************** *)

Goalw WO_defs "[| m le n; WO4(m) |] ==> WO4(n)";
by (blast_tac (claset() addSDs [spec] 
                        addIs [le_imp_lepoll RSN (2, lepoll_trans)]) 1);
qed "WO4_mono";

(* ********************************************************************** *)

Goalw WO_defs "[| m \\<in> nat; 1 le m; WO4(m) |] ==> WO5";
by (Blast_tac 1);
qed "WO4_WO5";

(* ********************************************************************** *)

Goalw WO_defs "WO5 ==> WO6";
by (Blast_tac 1);
qed "WO5_WO6";

