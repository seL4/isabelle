(*  Title:      HOLCF/tr2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for tr2.thy
*)

open Tr2;

(* ------------------------------------------------------------------------ *) 
(* lemmas about andalso                                                     *) 
(* ------------------------------------------------------------------------ *)

fun prover s =  prove_goalw Tr2.thy [andalso_def] s
 (fn prems =>
        [
        (simp_tac (!simpset addsimps tr_when) 1)
        ]);

val andalso_thms = map prover [
                        "(TT andalso y) = y",
                        "(FF andalso y) = FF",
                        "(UU andalso y) = UU"
                        ];

val andalso_thms = andalso_thms @ 
 [prove_goalw Tr2.thy [andalso_def] "(x andalso TT) =  x"
 (fn prems =>
        [
        (res_inst_tac [("p","x")] trE 1),
        (asm_simp_tac (!simpset addsimps tr_when) 1),
        (asm_simp_tac (!simpset addsimps tr_when) 1),
        (asm_simp_tac (!simpset addsimps tr_when) 1)
        ])];

(* ------------------------------------------------------------------------ *) 
(* lemmas about orelse                                                      *) 
(* ------------------------------------------------------------------------ *)

fun prover s =  prove_goalw Tr2.thy [orelse_def] s
 (fn prems =>
        [
        (simp_tac (!simpset addsimps tr_when) 1)
        ]);

val orelse_thms = map prover [
                        "(TT orelse y)  = TT",
                        "(FF orelse y) =  y",
                        "(UU orelse y) = UU"
                        ];

val orelse_thms = orelse_thms @ 
 [prove_goalw Tr2.thy [orelse_def] "(x orelse FF) =  x"
 (fn prems =>
        [
        (res_inst_tac [("p","x")] trE 1),
        (asm_simp_tac (!simpset addsimps tr_when) 1),
        (asm_simp_tac (!simpset addsimps tr_when) 1),
        (asm_simp_tac (!simpset addsimps tr_when) 1)
        ])];


(* ------------------------------------------------------------------------ *) 
(* lemmas about neg                                                         *) 
(* ------------------------------------------------------------------------ *)

fun prover s =  prove_goalw Tr2.thy [neg_def] s
 (fn prems =>
        [
        (simp_tac (!simpset addsimps tr_when) 1)
        ]);

val neg_thms = map prover [
                        "neg`TT = FF",
                        "neg`FF = TT",
                        "neg`UU = UU"
                        ];

(* ------------------------------------------------------------------------ *) 
(* lemmas about If_then_else_fi                                             *) 
(* ------------------------------------------------------------------------ *)

fun prover s =  prove_goalw Tr2.thy [ifte_def] s
 (fn prems =>
        [
        (simp_tac (!simpset addsimps tr_when) 1)
        ]);

val ifte_thms = map prover [
                        "If UU then e1 else e2 fi = UU",
                        "If FF then e1 else e2 fi = e2",
                        "If TT then e1 else e2 fi = e1"];




                
