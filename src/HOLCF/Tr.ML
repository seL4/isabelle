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
	(fast_tac (HOL_cs addss simpset()) 1)
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
	(REPEAT(asm_simp_tac (simpset() addsimps 
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

(* ------------------------------------------------------------------- *)
(*  split-tac for If via If2 because the constant has to be a constant *)
(* ------------------------------------------------------------------- *)
  
goalw thy [If2_def] 
  "P (If2 Q x y ) = ((Q=UU --> P UU) & (Q=TT --> P x) & (Q=FF --> P y))";
by (res_inst_tac [("p","Q")] trE 1);
by (REPEAT (Asm_full_simp_tac 1));
qed"expand_If2";

val split_If_tac =
  simp_tac (HOL_basic_ss addsimps [symmetric If2_def]) THEN' (split_tac [expand_If2]);

 

(* ----------------------------------------------------------------- *)
        section"Rewriting of HOLCF operations to HOL functions";
(* ----------------------------------------------------------------- *)


goal thy
"!!t.[|t~=UU|]==> ((t andalso s)=FF)=(t=FF | s=FF)";
by (rtac iffI 1);
by (res_inst_tac [("p","t")] trE 1);
auto();
by (res_inst_tac [("p","t")] trE 1);
auto();
qed"andalso_or";

goal thy "!!t.[|t~=UU|]==> ((t andalso s)~=FF)=(t~=FF & s~=FF)";
by (rtac iffI 1);
by (res_inst_tac [("p","t")] trE 1);
auto();
by (res_inst_tac [("p","t")] trE 1);
auto();
qed"andalso_and";

goal thy "(Def x ~=FF)= x";
by (simp_tac (simpset() addsimps [FF_def]) 1);
qed"Def_bool1";

goal thy "(Def x = FF) = (~x)";
by (simp_tac (simpset() addsimps [FF_def]) 1);
by (fast_tac HOL_cs 1);
qed"Def_bool2";

goal thy "(Def x = TT) = x";
by (simp_tac (simpset() addsimps [TT_def]) 1);
qed"Def_bool3";

goal thy "(Def x ~= TT) = (~x)";
by (simp_tac (simpset() addsimps [TT_def]) 1);
qed"Def_bool4";

goal thy 
  "(If Def P then A else B fi)= (if P then A else B)";
by (res_inst_tac [("p","Def P")]  trE 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps tr_defs@[flift1_def,o_def]) 1);
by (asm_full_simp_tac (simpset() addsimps tr_defs@[flift1_def,o_def]) 1);
qed"If_and_if";

Addsimps [Def_bool1,Def_bool2,Def_bool3,Def_bool4];

(* ----------------------------------------------------------------- *)
        section"admissibility";
(* ----------------------------------------------------------------- *)


(* The following rewrite rules for admissibility should in the future be 
   replaced by a more general admissibility test that also checks 
   chain-finiteness, of which these lemmata are specific examples *)

goal thy "x~=FF = (x=TT|x=UU)";
by (res_inst_tac [("p","x")] trE 1);
by (TRYALL (Asm_full_simp_tac));
qed"adm_trick_1";

goal thy "x~=TT = (x=FF|x=UU)";
by (res_inst_tac [("p","x")] trE 1);
by (TRYALL (Asm_full_simp_tac));
qed"adm_trick_2";

val adm_tricks = [adm_trick_1,adm_trick_2];


goal thy "!!f. cont(f) ==> adm (%x. (f x)~=TT)";
by (simp_tac (HOL_basic_ss addsimps adm_tricks) 1);
by (REPEAT ((resolve_tac (adm_lemmas@cont_lemmas1) 1) ORELSE atac 1));
qed"adm_nTT";

goal thy "!!f. cont(f) ==> adm (%x. (f x)~=FF)";
by (simp_tac (HOL_basic_ss addsimps adm_tricks) 1);
by (REPEAT ((resolve_tac (adm_lemmas@cont_lemmas1) 1) ORELSE atac 1));
qed"adm_nFF";

Addsimps [adm_nTT,adm_nFF];