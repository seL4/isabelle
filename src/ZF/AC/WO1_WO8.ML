(*  Title:      ZF/AC/WO1_WO8.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proof of WO8 <-> WO1 (Rubin & Rubin p. 6)
*)

(* ********************************************************************** *)
(* Trivial implication "WO1 ==> WO8"                                      *)
(* ********************************************************************** *)

Goalw WO_defs "WO1 ==> WO8";
by (Fast_tac 1);
qed "WO1_WO8";

(* ********************************************************************** *)
(* The proof of "WO8 ==> WO1" - faithful image of Rubin & Rubin's proof   *)
(* ********************************************************************** *)

Goalw WO_defs "WO8 ==> WO1";
by (rtac allI 1);
by (eres_inst_tac [("x","{{x}. x \\<in> A}")] allE 1);
by (etac impE 1);
by (fast_tac (claset() addSEs [lam_sing_bij RS bij_is_inj RS
                        well_ord_rvimage]) 2);
by (res_inst_tac [("x","\\<lambda>a \\<in> {{x}. x \\<in> A}. THE x. a={x}")] exI 1);
by (force_tac (claset() addSIs [lam_type],
               simpset() addsimps [singleton_eq_iff, the_equality]) 1);
qed "WO8_WO1";
