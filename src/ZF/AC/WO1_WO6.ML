(*  Title:      ZF/AC/WO1-WO6.ML
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

goalw thy WO_defs "!!Z. WO2 ==> WO3";
by (Fast_tac 1);
qed "WO2_WO3";

(* ********************************************************************** *)

goalw thy (eqpoll_def::WO_defs) "!!Z. WO3 ==> WO1";
by (fast_tac (!claset addSEs [bij_is_inj RS well_ord_rvimage, 
			      well_ord_Memrel RS well_ord_subset]) 1);
qed "WO3_WO1";

(* ********************************************************************** *)

goalw thy (eqpoll_def::WO_defs) "!!Z. WO1 ==> WO2";
by (fast_tac (!claset addSIs [Ord_ordertype, ordermap_bij]) 1);
qed "WO1_WO2";

(* ********************************************************************** *)

goal thy "!!f. f: A->B ==> (lam x:A. {f`x}): A -> {{b}. b:B}";
by (fast_tac (!claset addSIs [lam_type, apply_type]) 1);
qed "lam_sets";

goalw thy [surj_def] "!!f. f:surj(A,B) ==> (UN a:A. {f`a}) = B";
by (fast_tac (!claset addSEs [apply_type]) 1);
qed "surj_imp_eq_";

goal thy "!!f. [| f:surj(A,B); Ord(A) |] ==> (UN a<A. {f`a}) = B";
by (fast_tac (!claset addSDs [surj_imp_eq_]
                addSIs [ltI] addSEs [ltE]) 1);
qed "surj_imp_eq";

goalw thy WO_defs "!!Z. WO1 ==> WO4(1)";
by (rtac allI 1);
by (eres_inst_tac [("x","A")] allE 1);
by (etac exE 1);
by (REPEAT (resolve_tac [exI, conjI] 1));
by (etac Ord_ordertype 1);
by (rtac conjI 1);
by (eresolve_tac [ordermap_bij RS bij_converse_bij RS bij_is_fun RS
                lam_sets RS domain_of_fun] 1);
by (asm_simp_tac (!simpset addsimps [singleton_eqpoll_1 RS eqpoll_imp_lepoll,
                  Ord_ordertype RSN (2, ordermap_bij RS bij_converse_bij RS
                        bij_is_surj RS surj_imp_eq)]) 1);
qed "WO1_WO4";

(* ********************************************************************** *)

goalw thy WO_defs "!!Z. [| m:nat; n:nat; m le n; WO4(m) |] ==> WO4(n)";
by (fast_tac (!claset addIs [nat_le_imp_lepoll RSN (2, lepoll_trans)]) 1);
qed "WO4_mono";

(* ********************************************************************** *)

goalw thy WO_defs "!!Z. [| m:nat; 1 le m; WO4(m) |] ==> WO5";
    (*ZF_cs is essential: default claset's too slow*)
by (fast_tac ZF_cs 1);
qed "WO4_WO5";

(* ********************************************************************** *)

goalw thy WO_defs "!!Z. WO5 ==> WO6";
    (*ZF_cs is essential: default claset's too slow*)
by (fast_tac ZF_cs 1);
qed "WO5_WO6";

