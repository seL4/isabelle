(*  Title:      HOLCF/holcfb.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Changed by: David von Oheimb
    Copyright   1993  Technische Universitaet Muenchen
*)


open Holcfb;

(* ------------------------------------------------------------------------ *)
(* Some lemmas in HOL.thy                                                   *)
(* ------------------------------------------------------------------------ *)


(* val de_morgan1 = de_Morgan_disj RS sym;   "(~a & ~b)=(~(a | b))" *)

(* val de_morgan2 = de_Morgan_conj RS sym;   "(~a | ~b)=(~(a & b))" *)


(* val notall2ex = not_all 		     "(~ (!x.P(x))) = (? x.~P(x))" *)

(* val notex2all = not_ex		     "(~ (? x.P(x))) = (!x.~P(x))" *)


(* val selectI3 =  select_eq_Ex RS iffD2   "(? x. P(x)) ==> P(@ x.P(x))" *)

(* val selectE =   select_eq_Ex RS iffD1   "P(@ x.P(x)) ==> (? x. P(x))" *)


(*
qed_goal "notnotI" HOL.thy "P ==> ~~P"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (fast_tac HOL_cs 1)
        ]);
*)

(* val classical2 = case_split_thm;        "[|Q ==> R; ~Q ==> R|]==>R" *)

(* fun case_tac s = res_inst_tac [("Q",s)] classical2; *)

val classical3 = (notE RS notI); (* [| ?P ==> ~ ?P1; ?P ==> ?P1 |] ==> ~ ?P *)
