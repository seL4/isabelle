(*  Title:      HOLCF/Tr.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for Tr.thy
*)

open Tr;

(* ------------------------------------------------------------------------ *)
(* Exhaustion and Elimination for type one                                  *)
(* ------------------------------------------------------------------------ *)
qed_goalw "Exh_tr" thy [FF_def,TT_def] "t=UU | t = TT | t = FF"
 (fn prems =>
        [
	(lift.induct_tac "t" 1),
	(fast_tac HOL_cs 1),
	(fast_tac (HOL_cs addss !simpset) 1)
	]);

qed_goal "trE" thy
        "[| p=UU ==> Q; p = TT ==>Q; p = FF ==>Q|] ==>Q"
 (fn prems =>
        [
        (rtac (Exh_tr RS disjE) 1),
        (eresolve_tac prems 1),
        (etac disjE 1),
        (eresolve_tac prems 1),
        (eresolve_tac prems 1)
        ]);

(* ------------------------------------------------------------------------ *) 
(* tactic for tr-thms with case split                                       *)
(* ------------------------------------------------------------------------ *)

val tr_defs = [andalso_def,orelse_def,neg_def,ifte_def,TT_def,FF_def];

fun prover t =  prove_goal thy t
 (fn prems =>
        [
        (res_inst_tac [("p","y")] trE 1),
	(REPEAT(asm_simp_tac (!simpset addsimps 
		[o_def,flift1_def,flift2_def,inst_lift_po]@tr_defs) 1))
	]);

(* ------------------------------------------------------------------------ *) 
(* distinctness for type tr                                                 *) 
(* ------------------------------------------------------------------------ *)

val dist_less_tr = map prover [
			"~TT << UU",
			"~FF << UU",
			"~TT << FF",
			"~FF << TT"
                        ];

val dist_eq_tr = map prover ["TT~=UU","FF~=UU","TT~=FF"];
val dist_eq_tr = dist_eq_tr @ (map (fn thm => (thm RS not_sym)) dist_eq_tr);

(* ------------------------------------------------------------------------ *) 
(* lemmas about andalso, orelse, neg and if                                 *) 
(* ------------------------------------------------------------------------ *)

val andalso_thms = map prover [
                        "(TT andalso y) = y",
                        "(FF andalso y) = FF",
                        "(UU andalso y) = UU",
			"(y andalso TT) = y",
		  	"(y andalso y) = y"
                        ];

val orelse_thms = map prover [
                        "(TT orelse y) = TT",
                        "(FF orelse y) = y",
                        "(UU orelse y) = UU",
                        "(y orelse FF) = y",
			"(y orelse y) = y"];

val neg_thms = map prover [
                        "neg`TT = FF",
                        "neg`FF = TT",
                        "neg`UU = UU"
                        ];

val ifte_thms = map prover [
                        "If UU then e1 else e2 fi = UU",
                        "If FF then e1 else e2 fi = e2",
                        "If TT then e1 else e2 fi = e1"];

Addsimps (dist_less_tr @ dist_eq_tr @ andalso_thms @ 
	  orelse_thms @ neg_thms @ ifte_thms);


                
(* --------------------------------------------------------- *)
(*                Theroems for the liftings                  *)
(* --------------------------------------------------------- *)


(* --------------------------------------------------------- *)
(*                Admissibility tactic and tricks            *)
(* --------------------------------------------------------- *)


goal thy "x~=FF = (x=TT|x=UU)";
by (res_inst_tac [("p","x")] trE 1);
  by (TRYALL (Asm_full_simp_tac));
qed"adm_trick_1";

goal thy "x~=TT = (x=FF|x=UU)";
by (res_inst_tac [("p","x")] trE 1);
  by (TRYALL (Asm_full_simp_tac));
qed"adm_trick_2";

val adm_tricks = [adm_trick_1,adm_trick_2];

(*val adm_tac = (fn i => ((resolve_tac adm_lemmas i)));*)
(*val adm_tacR = (fn i => (REPEAT (adm_tac i)));*)
(*val adm_cont_tac = (fn i => ((adm_tacR i) THEN (cont_tacR i)));*)

(* ----------------------------------------------------------------- *)
(*     Relations between domains and terms using lift constructs     *)
(* ----------------------------------------------------------------- *)

goal thy "!!t.[|t~=UU|]==> ((t andalso s)~=FF)=(t~=FF & s~=FF)";
by (rtac iffI 1);
(* 1 *)
by (res_inst_tac [("p","t")] trE 1);
by (fast_tac HOL_cs 1);
by (res_inst_tac [("p","s")] trE 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "(t andalso s) = FF" 1);
by (fast_tac HOL_cs 1);
by (Asm_full_simp_tac 1);
by (res_inst_tac [("p","s")] trE 1);
by (subgoal_tac "(t andalso s) = FF" 1);
by (fast_tac HOL_cs 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "(t andalso s) = FF" 1);
by (fast_tac HOL_cs 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "(t andalso s) = FF" 1);
by (fast_tac HOL_cs 1);
by (Asm_full_simp_tac 1);
(* 2*)
by (res_inst_tac [("p","t")] trE 1);
by (fast_tac HOL_cs 1);
by (Asm_full_simp_tac 1);
by (fast_tac HOL_cs 1);
qed"andalso_and";

goal thy "Def x ~=UU";
by (Simp_tac 1);
qed"blift_not_UU";

goal thy "(Def x ~=FF)= x";
by (simp_tac (!simpset addsimps [FF_def]) 1);
qed"blift_and_bool";

goal thy "(Def x = TT) = x";
by (simp_tac (!simpset addsimps [TT_def]) 1);
qed"blift_and_bool2";

goal thy "(Def x = FF) = (~x)";
by (simp_tac (!simpset addsimps [FF_def]) 1);
by (fast_tac HOL_cs 1);
qed"blift_and_bool3";

goal thy "plift P`(Def y) = Def (P y)";
by (simp_tac (!simpset addsimps [plift_def,flift1_def]) 1);
qed"plift2blift";

goal thy 
  "(If Def P then A else B fi)= (if P then A else B)";
by (res_inst_tac [("p","Def P")]  trE 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (!simpset addsimps tr_defs@[flift1_def,o_def]) 1);
by (asm_full_simp_tac (!simpset addsimps tr_defs@[flift1_def,o_def]) 1);
qed"If_and_if";

Addsimps [plift2blift,If_and_if,blift_not_UU,
	blift_and_bool,blift_and_bool2,blift_and_bool3];
