(*  Title:      LK/LK.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Tactics and lemmas for lk.thy (thanks also to Philippe de Groote)  
*)

open LK;

(*Higher precedence than := facilitates use of references*)
infix 4 add_safes add_unsafes;

(*Cut and thin, replacing the right-side formula*)
fun cutR_tac (sP: string) i = 
    res_inst_tac [ ("P",sP) ] cut i  THEN  rtac thinR i;

(*Cut and thin, replacing the left-side formula*)
fun cutL_tac (sP: string) i = 
    res_inst_tac [ ("P",sP) ] cut i  THEN  rtac thinL (i+1);


(** If-and-only-if rules **)
qed_goalw "iffR" LK.thy [iff_def]
    "[| $H,P |- $E,Q,$F;  $H,Q |- $E,P,$F |] ==> $H |- $E, P <-> Q, $F"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[conjR,impR]) 1)) ]);

qed_goalw "iffL" LK.thy [iff_def]
   "[| $H,$G |- $E,P,Q;  $H,Q,P,$G |- $E |] ==> $H, P <-> Q, $G |- $E"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[conjL,impL,basic]) 1)) ]);

qed_goalw "TrueR" LK.thy [True_def]
    "$H |- $E, True, $F"
 (fn _=> [ rtac impR 1, rtac basic 1 ]);


(** Weakened quantifier rules.  Incomplete, they let the search terminate.**)

qed_goal "allL_thin" LK.thy 
    "$H, P(x), $G |- $E ==> $H, ALL x. P(x), $G |- $E"
 (fn prems=> [ (rtac allL 1), (rtac thinL 1), (resolve_tac prems 1) ]);

qed_goal "exR_thin" LK.thy 
    "$H |- $E, P(x), $F ==> $H |- $E, EX x. P(x), $F"
 (fn prems=> [ (rtac exR 1), (rtac thinR 1), (resolve_tac prems 1) ]);

(* Symmetry of equality in hypotheses *)
qed_goal "symL" LK.thy 
    "$H, $G, B = A |- $E ==> $H, A = B, $G |- $E" 
 (fn prems=>
  [ (rtac cut 1),
    (rtac thinL 2),
    (resolve_tac prems 2),
    (resolve_tac [basic RS sym] 1) ]);




(*The rules of LK*)
val prop_pack = empty_pack add_safes 
                [basic, refl, conjL, conjR, disjL, disjR, impL, impR, 
                 notL, notR, iffL, iffR];

val LK_pack = prop_pack add_safes   [allR, exL] 
                        add_unsafes [allL_thin, exR_thin];

val LK_dup_pack = prop_pack add_safes   [allR, exL] 
                            add_unsafes [allL, exR];



(** Contraction.  Useful since some rules are not complete. **)

qed_goal "conR" LK.thy 
    "$H |- $E, P, $F, P ==> $H |- $E, P, $F"
 (fn prems=>
  [ (rtac cut 1), (REPEAT (resolve_tac (prems@[basic]) 1)) ]);

qed_goal "conL" LK.thy 
    "$H, P, $G, P |- $E ==> $H, P, $G |- $E"
 (fn prems=>
  [ (rtac cut 1), (REPEAT (resolve_tac (prems@[basic]) 1)) ]);
