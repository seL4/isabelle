open Dlist;

(* ------------------------------------------------------------------------- *)
(* expand fixed point properties of lmap                                     *)
(* ------------------------------------------------------------------------- *)

bind_thm ("lmap_def2", fix_prover2 Dlist.thy lmap_def 
        "lmap = (LAM f s.case s of dnil => dnil | x ## l => f`x ## lmap`f`l )");

(* ------------------------------------------------------------------------- *)
(* recursive  properties   of lmap                                           *)
(* ------------------------------------------------------------------------- *)

qed_goal "lmap1" Dlist.thy "lmap`f`UU = UU"
 (fn prems =>
	[
	(rtac (lmap_def2 RS ssubst) 1),
	(simp_tac (HOLCF_ss addsimps dlist.when_rews) 1)
	]);

qed_goal "lmap2" Dlist.thy "lmap`f`dnil = dnil"
 (fn prems =>
	[
	(rtac (lmap_def2 RS ssubst) 1),
	(simp_tac (HOLCF_ss addsimps dlist.when_rews) 1)
	]);

qed_goal "lmap3" Dlist.thy 
	"[|x~=UU; xs~=UU|] ==> lmap`f`(x##xs) = (f`x)##(lmap`f`xs)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac trans 1),
	(rtac (lmap_def2 RS ssubst) 1),
	(asm_simp_tac (HOLCF_ss addsimps dlist.rews) 1),
	(rtac refl 1)
	]);
