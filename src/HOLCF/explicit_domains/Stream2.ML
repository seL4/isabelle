(*
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for theory Stream2.thy
*)

open Stream2;

(* ------------------------------------------------------------------------- *)
(* expand fixed point properties                                             *)
(* ------------------------------------------------------------------------- *)

val smap_def2 = fix_prover2 Stream2.thy smap_def 
        "smap = (LAM f s. stream_when`(LAM x l.scons`(f`x) `(smap`f`l)) `s)";


(* ------------------------------------------------------------------------- *)
(* recursive  properties                                                     *)
(* ------------------------------------------------------------------------- *)


qed_goal "smap1" Stream2.thy "smap`f`UU = UU"
 (fn prems =>
        [
        (stac smap_def2 1),
        (simp_tac (!simpset addsimps stream_when) 1)
        ]);

qed_goal "smap2" Stream2.thy 
        "x~=UU ==> smap`f`(scons`x`xs) = scons `(f`x) `(smap`f`xs)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac trans 1),
        (stac smap_def2 1),
        (asm_simp_tac (!simpset addsimps stream_rews) 1),
        (rtac refl 1)
        ]);


val stream2_rews = [smap1, smap2];
