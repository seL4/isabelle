(*  Title:      LK/LK0
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Tactics and lemmas for LK (thanks also to Philippe de Groote)  

Structural rules by Soren Heilmann
*)

(** Structural Rules on formulas **)

(*contraction*)

Goal "$H |- $E, P, P, $F ==> $H |- $E, P, $F";
by (etac contRS 1);
qed "contR";

Goal "$H, P, P, $G |- $E ==> $H, P, $G |- $E";
by (etac contLS 1);
qed "contL";

(*thinning*)

Goal "$H |- $E, $F ==> $H |- $E, P, $F";
by (etac thinRS 1);
qed "thinR";

Goal "$H, $G |- $E ==> $H, P, $G |- $E";
by (etac thinLS 1);
qed "thinL";

(*exchange*)

Goal "$H |- $E, Q, P, $F ==> $H |- $E, P, Q, $F";
by (etac exchRS 1);
qed "exchR";

Goal "$H, Q, P, $G |- $E ==> $H, P, Q, $G |- $E";
by (etac exchLS 1);
qed "exchL";

(*Cut and thin, replacing the right-side formula*)
fun cutR_tac (sP: string) i = 
    res_inst_tac [ ("P",sP) ] cut i  THEN  rtac thinR i;

(*Cut and thin, replacing the left-side formula*)
fun cutL_tac (sP: string) i = 
    res_inst_tac [ ("P",sP) ] cut i  THEN  rtac thinL (i+1);


(** If-and-only-if rules **)
Goalw [iff_def] 
    "[| $H,P |- $E,Q,$F;  $H,Q |- $E,P,$F |] ==> $H |- $E, P <-> Q, $F";
by (REPEAT (ares_tac [conjR,impR] 1));
qed "iffR";

Goalw [iff_def] 
    "[| $H,$G |- $E,P,Q;  $H,Q,P,$G |- $E |] ==> $H, P <-> Q, $G |- $E";
by (REPEAT (ares_tac [conjL,impL,basic] 1));
qed "iffL";

Goal "$H |- $E, (P <-> P), $F";
by (REPEAT (resolve_tac [iffR,basic] 1));
qed "iff_refl";

Goalw [True_def] "$H |- $E, True, $F";
by (rtac impR 1);
by (rtac basic 1);
qed "TrueR";

(*Descriptions*)
val [p1,p2] = Goal
    "[| $H |- $E, P(a), $F;  !!x. $H, P(x) |- $E, x=a, $F |] \
\    ==> $H |- $E, (THE x. P(x)) = a, $F";
by (rtac cut 1);
by (rtac p2 2);
by (rtac The 1 THEN rtac thinR 1 THEN rtac exchRS 1 THEN rtac p1 1);
by (rtac thinR 1 THEN rtac exchRS 1 THEN rtac p2 1);
qed "the_equality";

(** Weakened quantifier rules.  Incomplete, they let the search terminate.**)

Goal "$H, P(x), $G |- $E ==> $H, ALL x. P(x), $G |- $E";
by (rtac allL 1);
by (etac thinL 1);
qed "allL_thin";

Goal "$H |- $E, P(x), $F ==> $H |- $E, EX x. P(x), $F";
by (rtac exR 1);
by (etac thinR 1);
qed "exR_thin";


(*The rules of LK*)
val prop_pack = empty_pack add_safes 
                [basic, refl, TrueR, FalseL, 
		 conjL, conjR, disjL, disjR, impL, impR, 
                 notL, notR, iffL, iffR];

val LK_pack = prop_pack add_safes   [allR, exL] 
                        add_unsafes [allL_thin, exR_thin, the_equality];

val LK_dup_pack = prop_pack add_safes   [allR, exL] 
                            add_unsafes [allL, exR, the_equality];


pack_ref() := LK_pack;

fun lemma_tac th i = 
    rtac (thinR RS cut) i THEN REPEAT (rtac thinL i) THEN rtac th i;

val [major,minor] = goal thy 
    "[| $H |- $E, $F, P --> Q;  $H |- $E, $F, P |] ==> $H |- $E, Q, $F";
by (rtac (thinRS RS cut) 1 THEN rtac major 1);
by (Step_tac 1);
by (rtac thinR 1 THEN rtac minor 1);
qed "mp_R";

val [major,minor] = goal thy 
    "[| $H, $G |- $E, P --> Q;  $H, $G, Q |- $E |] ==> $H, P, $G |- $E";
by (rtac (thinL RS cut) 1 THEN rtac major 1);
by (Step_tac 1);
by (rtac thinL 1 THEN rtac minor 1);
qed "mp_L";


(** Two rules to generate left- and right- rules from implications **)

val [major,minor] = goal thy 
    "[| |- P --> Q;  $H |- $E, $F, P |] ==> $H |- $E, Q, $F";
by (rtac mp_R 1);
by (rtac minor 2);
by (rtac thinRS 1 THEN rtac (major RS thinLS) 1);
qed "R_of_imp";

val [major,minor] = goal thy 
    "[| |- P --> Q;  $H, $G, Q |- $E |] ==> $H, P, $G |- $E";
by (rtac mp_L 1);
by (rtac minor 2);
by (rtac thinRS 1 THEN rtac (major RS thinLS) 1);
qed "L_of_imp";

(*Can be used to create implications in a subgoal*)
val [prem] = goal thy 
    "[| $H, $G |- $E, $F, P --> Q |] ==> $H, P, $G |- $E, Q, $F";
by (rtac mp_L 1);
by (rtac basic 2);
by (rtac thinR 1 THEN rtac prem 1);
qed "backwards_impR";

Goal "|-P&Q ==> |-P";
by (etac (thinR RS cut) 1);
by (Fast_tac 1);		
qed "conjunct1";

Goal "|-P&Q ==> |-Q";
by (etac (thinR RS cut) 1);
by (Fast_tac 1);		
qed "conjunct2";

Goal "|- (ALL x. P(x)) ==> |- P(x)";
by (etac (thinR RS cut) 1);
by (Fast_tac 1);		
qed "spec";

(** Equality **)

Goal "|- a=b --> b=a";
by (safe_tac (LK_pack add_safes [subst]) 1);
qed "sym";

Goal "|- a=b --> b=c --> a=c";
by (safe_tac (LK_pack add_safes [subst]) 1);
qed "trans";

(* Symmetry of equality in hypotheses *)
bind_thm ("symL", sym RS L_of_imp);

(* Symmetry of equality in hypotheses *)
bind_thm ("symR", sym RS R_of_imp);

Goal "[| $H|- $E, $F, a=b;  $H|- $E, $F, b=c |] ==> $H|- $E, a=c, $F";
by (rtac (trans RS R_of_imp RS mp_R) 1);
by (ALLGOALS assume_tac);
qed "transR";


(* Two theorms for rewriting only one instance of a definition:
   the first for definitions of formulae and the second for terms *)

val prems = goal thy "(A == B) ==> |- A <-> B";
by (rewrite_goals_tac prems);
by (rtac iff_refl 1);
qed "def_imp_iff";

val prems = goal thy "(A == B) ==> |- A = B";
by (rewrite_goals_tac prems);
by (rtac refl 1);
qed "meta_eq_to_obj_eq";
