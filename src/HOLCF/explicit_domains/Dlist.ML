(*  Title:      HOLCF/Dlist.ML
    Author:     Franz Regensburger
    ID:         $ $
    Copyright   1994 Technische Universitaet Muenchen

Lemmas for dlist.thy
*)

open Dlist;

(* ------------------------------------------------------------------------*)
(* The isomorphisms dlist_rep_iso and dlist_abs_iso are strict             *)
(* ------------------------------------------------------------------------*)

val dlist_iso_strict= dlist_rep_iso RS (dlist_abs_iso RS 
        (allI  RSN (2,allI RS iso_strict)));

val dlist_rews = [dlist_iso_strict RS conjunct1,
                dlist_iso_strict RS conjunct2];

(* ------------------------------------------------------------------------*)
(* Properties of dlist_copy                                                *)
(* ------------------------------------------------------------------------*)

val temp = prove_goalw Dlist.thy  [dlist_copy_def] "dlist_copy`f`UU=UU"
 (fn prems =>
        [
        (asm_simp_tac (!simpset addsimps 
                (dlist_rews @ [dlist_abs_iso,dlist_rep_iso])) 1)
        ]);

val dlist_copy = [temp];


val temp = prove_goalw Dlist.thy  [dlist_copy_def,dnil_def] 
    "dlist_copy`f`dnil=dnil"
 (fn prems =>
        [
        (asm_simp_tac (!simpset addsimps 
                (dlist_rews @ [dlist_abs_iso,dlist_rep_iso])) 1)
        ]);

val dlist_copy = temp :: dlist_copy;


val temp = prove_goalw Dlist.thy  [dlist_copy_def,dcons_def] 
        "xl~=UU ==> dlist_copy`f`(dcons`x`xl)= dcons`x`(f`xl)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (asm_simp_tac (!simpset addsimps 
                (dlist_rews @ [dlist_abs_iso,dlist_rep_iso])) 1),
        (case_tac "x=UU" 1),
        (Asm_simp_tac  1),
        (asm_simp_tac (!simpset addsimps [defined_spair]) 1)
        ]);

val dlist_copy = temp :: dlist_copy;

val dlist_rews =  dlist_copy @ dlist_rews; 

(* ------------------------------------------------------------------------*)
(* Exhaustion and elimination for dlists                                   *)
(* ------------------------------------------------------------------------*)

qed_goalw "Exh_dlist" Dlist.thy [dcons_def,dnil_def]
        "l = UU | l = dnil | (? x xl. x~=UU &xl~=UU & l = dcons`x`xl)"
 (fn prems =>
        [
        (Simp_tac 1),
        (rtac (dlist_rep_iso RS subst) 1),
        (res_inst_tac [("p","dlist_rep`l")] ssumE 1),
        (rtac disjI1 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (rtac disjI2 1),
        (rtac disjI1 1),
        (res_inst_tac [("p","x")] oneE 1),
        (contr_tac 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (rtac disjI2 1),
        (rtac disjI2 1),
        (res_inst_tac [("p","y")] sprodE 1),
        (contr_tac 1),
        (rtac exI 1),
        (rtac exI 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (fast_tac HOL_cs 1)
        ]);


qed_goal "dlistE" Dlist.thy 
"[| l=UU ==> Q; l=dnil ==> Q;!!x xl.[|l=dcons`x`xl;x~=UU;xl~=UU|]==>Q|]==>Q"
 (fn prems =>
        [
        (rtac (Exh_dlist RS disjE) 1),
        (eresolve_tac prems 1),
        (etac disjE 1),
        (eresolve_tac prems 1),
        (etac exE 1),
        (etac exE 1),
        (resolve_tac prems 1),
        (fast_tac HOL_cs 1),
        (fast_tac HOL_cs 1),
        (fast_tac HOL_cs 1)
        ]);

(* ------------------------------------------------------------------------*)
(* Properties of dlist_when                                                *)
(* ------------------------------------------------------------------------*)

val temp = prove_goalw  Dlist.thy  [dlist_when_def] "dlist_when`f1`f2`UU=UU"
 (fn prems =>
        [
        (asm_simp_tac (!simpset addsimps [dlist_iso_strict]) 1)
        ]);

val dlist_when = [temp];

val temp = prove_goalw  Dlist.thy [dlist_when_def,dnil_def]
 "dlist_when`f1`f2`dnil= f1"
 (fn prems =>
        [
        (asm_simp_tac (!simpset addsimps [dlist_abs_iso]) 1)
        ]);

val dlist_when = temp::dlist_when;

val temp = prove_goalw  Dlist.thy [dlist_when_def,dcons_def]
 "[|x~=UU;xl~=UU|] ==> dlist_when`f1`f2`(dcons`x`xl)= f2`x`xl"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (asm_simp_tac (!simpset addsimps [dlist_abs_iso,defined_spair]) 1)
        ]);

val dlist_when = temp::dlist_when;

val dlist_rews = dlist_when @ dlist_rews;

(* ------------------------------------------------------------------------*)
(* Rewrites for  discriminators and  selectors                             *)
(* ------------------------------------------------------------------------*)

fun prover defs thm = prove_goalw Dlist.thy defs thm
 (fn prems =>
        [
        (simp_tac (!simpset addsimps dlist_rews) 1)
        ]);

val dlist_discsel = [
        prover [is_dnil_def] "is_dnil`UU=UU",
        prover [is_dcons_def] "is_dcons`UU=UU",
        prover [dhd_def] "dhd`UU=UU",
        prover [dtl_def] "dtl`UU=UU"
        ];

fun prover defs thm = prove_goalw Dlist.thy defs thm
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1)
        ]);

val dlist_discsel = [
prover [is_dnil_def,is_dcons_def,dhd_def,dtl_def]
  "is_dnil`dnil=TT",
prover [is_dnil_def,is_dcons_def,dhd_def,dtl_def]
  "[|x~=UU;xl~=UU|] ==> is_dnil`(dcons`x`xl)=FF",
prover [is_dnil_def,is_dcons_def,dhd_def,dtl_def]
  "is_dcons`dnil=FF",
prover [is_dnil_def,is_dcons_def,dhd_def,dtl_def]
  "[|x~=UU;xl~=UU|] ==> is_dcons`(dcons`x`xl)=TT",
prover [is_dnil_def,is_dcons_def,dhd_def,dtl_def]
  "dhd`dnil=UU",
prover [is_dnil_def,is_dcons_def,dhd_def,dtl_def]
  "[|x~=UU;xl~=UU|] ==> dhd`(dcons`x`xl)=x",
prover [is_dnil_def,is_dcons_def,dhd_def,dtl_def]
  "dtl`dnil=UU",
prover [is_dnil_def,is_dcons_def,dhd_def,dtl_def]
  "[|x~=UU;xl~=UU|] ==> dtl`(dcons`x`xl)=xl"] @ dlist_discsel;

val dlist_rews = dlist_discsel @ dlist_rews;

(* ------------------------------------------------------------------------*)
(* Definedness and strictness                                              *)
(* ------------------------------------------------------------------------*)

fun prover contr thm = prove_goal Dlist.thy thm
 (fn prems =>
        [
        (res_inst_tac [("P1",contr)] classical3 1),
        (simp_tac (!simpset addsimps dlist_rews) 1),
        (dtac sym 1),
        (Asm_simp_tac  1),
        (simp_tac (!simpset addsimps (prems @ dlist_rews)) 1)
        ]);


val dlist_constrdef = [
prover "is_dnil`(UU::'a dlist) ~= UU" "dnil~=(UU::'a dlist)",
prover "is_dcons`(UU::'a dlist) ~= UU" 
        "[|x~=UU;xl~=UU|]==>dcons`(x::'a)`xl ~= UU"
 ];


fun prover defs thm = prove_goalw Dlist.thy defs thm
 (fn prems =>
        [
        (simp_tac (!simpset addsimps dlist_rews) 1)
        ]);

val dlist_constrdef = [
        prover [dcons_def] "dcons`UU`xl=UU",
        prover [dcons_def] "dcons`x`UU=UU"
        ] @ dlist_constrdef;

val dlist_rews = dlist_constrdef @ dlist_rews;


(* ------------------------------------------------------------------------*)
(* Distinctness wrt. << and =                                              *)
(* ------------------------------------------------------------------------*)

val temp = prove_goal Dlist.thy  "~dnil << dcons`(x::'a)`xl"
 (fn prems =>
        [
        (res_inst_tac [("P1","TT << FF")] classical3 1),
        (resolve_tac dist_less_tr 1),
        (dres_inst_tac [("fo5","is_dnil")] monofun_cfun_arg 1),
        (etac box_less 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (case_tac "(x::'a)=UU" 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (case_tac "(xl ::'a dlist)=UU" 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1)
        ]);

val dlist_dist_less = [temp];

val temp = prove_goal Dlist.thy  "[|x~=UU;xl~=UU|]==>~ dcons`x`xl << dnil"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (res_inst_tac [("P1","TT << FF")] classical3 1),
        (resolve_tac dist_less_tr 1),
        (dres_inst_tac [("fo5","is_dcons")] monofun_cfun_arg 1),
        (etac box_less 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1)
        ]);

val dlist_dist_less = temp::dlist_dist_less;

val temp = prove_goal Dlist.thy  "dnil ~= dcons`x`xl"
 (fn prems =>
        [
        (case_tac "x=UU" 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (case_tac "xl=UU" 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (res_inst_tac [("P1","TT = FF")] classical3 1),
        (resolve_tac dist_eq_tr 1),
        (dres_inst_tac [("f","is_dnil")] cfun_arg_cong 1),
        (etac box_equals 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1)
        ]);

val dlist_dist_eq = [temp,temp RS not_sym];

val dlist_rews = dlist_dist_less @ dlist_dist_eq @ dlist_rews;

(* ------------------------------------------------------------------------*)
(* Invertibility                                                           *)
(* ------------------------------------------------------------------------*)

val temp = prove_goal Dlist.thy "[|x1~=UU; y1~=UU;x2~=UU; y2~=UU;\
\ dcons`x1`x2 << dcons`y1`y2 |] ==> x1<< y1 & x2 << y2"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac conjI 1),
        (dres_inst_tac [("fo5","dlist_when`UU`(LAM x l.x)")] monofun_cfun_arg 1),
        (etac box_less 1),
        (asm_simp_tac (!simpset addsimps dlist_when) 1),
        (asm_simp_tac (!simpset addsimps dlist_when) 1),
        (dres_inst_tac [("fo5","dlist_when`UU`(LAM x l.l)")] monofun_cfun_arg 1),
        (etac box_less 1),
        (asm_simp_tac (!simpset addsimps dlist_when) 1),
        (asm_simp_tac (!simpset addsimps dlist_when) 1)
        ]);

val dlist_invert =[temp];

(* ------------------------------------------------------------------------*)
(* Injectivity                                                             *)
(* ------------------------------------------------------------------------*)

val temp = prove_goal Dlist.thy "[|x1~=UU; y1~=UU;x2~=UU; y2~=UU;\
\ dcons`x1`x2 = dcons`y1`y2 |] ==> x1= y1 & x2 = y2"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac conjI 1),
        (dres_inst_tac [("f","dlist_when`UU`(LAM x l.x)")] cfun_arg_cong 1),
        (etac box_equals 1),
        (asm_simp_tac (!simpset addsimps dlist_when) 1),
        (asm_simp_tac (!simpset addsimps dlist_when) 1),
        (dres_inst_tac [("f","dlist_when`UU`(LAM x l.l)")] cfun_arg_cong 1),
        (etac box_equals 1),
        (asm_simp_tac (!simpset addsimps dlist_when) 1),
        (asm_simp_tac (!simpset addsimps dlist_when) 1)
        ]);

val dlist_inject = [temp];
 

(* ------------------------------------------------------------------------*)
(* definedness for  discriminators and  selectors                          *)
(* ------------------------------------------------------------------------*)

fun prover thm = prove_goal Dlist.thy thm
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac dlistE 1),
        (contr_tac 1),
        (REPEAT (asm_simp_tac (!simpset addsimps dlist_discsel) 1))
        ]);

val dlist_discsel_def = 
        [
        prover "l~=UU ==> is_dnil`l~=UU", 
        prover "l~=UU ==> is_dcons`l~=UU" 
        ];

val dlist_rews = dlist_discsel_def @ dlist_rews;

(* ------------------------------------------------------------------------*)
(* enhance the simplifier                                                  *)
(* ------------------------------------------------------------------------*)

qed_goal "dhd2" Dlist.thy "xl~=UU ==> dhd`(dcons`x`xl)=x"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (case_tac "x=UU" 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1)
        ]);

qed_goal "dtl2" Dlist.thy "x~=UU ==> dtl`(dcons`x`xl)=xl"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (case_tac "xl=UU" 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1)
        ]);

val dlist_rews = dhd2 :: dtl2 :: dlist_rews;

(* ------------------------------------------------------------------------*)
(* Properties dlist_take                                                   *)
(* ------------------------------------------------------------------------*)

val temp = prove_goalw Dlist.thy [dlist_take_def] "dlist_take n`UU=UU"
 (fn prems =>
        [
        (res_inst_tac [("n","n")] natE 1),
        (Asm_simp_tac 1),
        (Asm_simp_tac 1),
        (simp_tac (!simpset addsimps dlist_rews) 1)
        ]);

val dlist_take = [temp];

val temp = prove_goalw Dlist.thy [dlist_take_def] "dlist_take 0`xs=UU"
 (fn prems =>
        [
        (Asm_simp_tac 1)
        ]);

val dlist_take = temp::dlist_take;

val temp = prove_goalw Dlist.thy [dlist_take_def]
        "dlist_take (Suc n)`dnil=dnil"
 (fn prems =>
        [
        (Asm_simp_tac 1),
        (simp_tac (!simpset addsimps dlist_rews) 1)
        ]);

val dlist_take = temp::dlist_take;

val temp = prove_goalw Dlist.thy [dlist_take_def]
  "dlist_take (Suc n)`(dcons`x`xl)= dcons`x`(dlist_take n`xl)"
 (fn prems =>
        [
        (case_tac "x=UU" 1),
        (Asm_simp_tac 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (case_tac "xl=UU" 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (Asm_simp_tac 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (res_inst_tac [("n","n")] natE 1),
        (Asm_simp_tac 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (Asm_simp_tac 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (Asm_simp_tac 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1)
        ]);

val dlist_take = temp::dlist_take;

val dlist_rews = dlist_take @ dlist_rews;

(* ------------------------------------------------------------------------*)
(* take lemma for dlists                                                  *)
(* ------------------------------------------------------------------------*)

fun prover reach defs thm  = prove_goalw Dlist.thy defs thm
 (fn prems =>
        [
        (res_inst_tac [("t","l1")] (reach RS subst) 1),
        (res_inst_tac [("t","l2")] (reach RS subst) 1),
        (stac fix_def2 1),
        (stac contlub_cfun_fun 1),
        (rtac is_chain_iterate 1),
        (stac contlub_cfun_fun 1),
        (rtac is_chain_iterate 1),
        (rtac lub_equal 1),
        (rtac (is_chain_iterate RS ch2ch_fappL) 1),
        (rtac (is_chain_iterate RS ch2ch_fappL) 1),
        (rtac allI 1),
        (resolve_tac prems 1)
        ]);

val dlist_take_lemma = prover dlist_reach  [dlist_take_def]
        "(!!n.dlist_take n`l1 = dlist_take n`l2) ==> l1=l2";


(* ------------------------------------------------------------------------*)
(* Co -induction for dlists                                               *)
(* ------------------------------------------------------------------------*)

qed_goalw "dlist_coind_lemma" Dlist.thy [dlist_bisim_def] 
"dlist_bisim R ==> ! p q. R p q --> dlist_take n`p = dlist_take n`q"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (nat_ind_tac "n" 1),
        (simp_tac (!simpset addsimps dlist_rews) 1),
        (strip_tac 1),
        ((etac allE 1) THEN (etac allE 1) THEN (etac (mp RS disjE) 1)),
        (atac 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (etac disjE 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (etac exE 1),
        (etac exE 1),
        (etac exE 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (REPEAT (etac conjE 1)),
        (rtac cfun_arg_cong 1),
        (fast_tac HOL_cs 1)
        ]);

qed_goal "dlist_coind" Dlist.thy "[|dlist_bisim R ; R p q |] ==> p = q"
 (fn prems =>
        [
        (rtac dlist_take_lemma 1),
        (rtac (dlist_coind_lemma RS spec RS spec RS mp) 1),
        (resolve_tac prems 1),
        (resolve_tac prems 1)
        ]);

(* ------------------------------------------------------------------------*)
(* structural induction                                                    *)
(* ------------------------------------------------------------------------*)

qed_goal "dlist_finite_ind" Dlist.thy
"[|P(UU);P(dnil);\
\  !! x l1.[|x~=UU;l1~=UU;P(l1)|] ==> P(dcons`x`l1)\
\  |] ==> !l.P(dlist_take n`l)"
 (fn prems =>
        [
        (nat_ind_tac "n" 1),
        (simp_tac (!simpset addsimps dlist_rews) 1),
        (resolve_tac prems 1),
        (rtac allI 1),
        (res_inst_tac [("l","l")] dlistE 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (resolve_tac prems 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (resolve_tac prems 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (case_tac "dlist_take n1`xl=UU" 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (resolve_tac prems 1),
        (resolve_tac prems 1),
        (atac 1),
        (atac 1),
        (etac spec 1)
        ]);

qed_goal "dlist_all_finite_lemma1" Dlist.thy
"!l.dlist_take n`l=UU |dlist_take n`l=l"
 (fn prems =>
        [
        (nat_ind_tac "n" 1),
        (simp_tac (!simpset addsimps dlist_rews) 1),
        (rtac allI 1),
        (res_inst_tac [("l","l")] dlistE 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (eres_inst_tac [("x","xl")] allE 1),
        (etac disjE 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1)
        ]);

qed_goal "dlist_all_finite_lemma2" Dlist.thy "? n.dlist_take n`l=l"
 (fn prems =>
        [
        (case_tac "l=UU" 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (subgoal_tac "(!n.dlist_take n`l=UU) |(? n.dlist_take n`l = l)" 1),
        (etac disjE 1),
        (eres_inst_tac [("P","l=UU")] notE 1),
        (rtac dlist_take_lemma 1),
        (asm_simp_tac (!simpset addsimps dlist_rews) 1),
        (atac 1),
        (subgoal_tac "!n.!l.dlist_take n`l=UU |dlist_take n`l=l" 1),
        (fast_tac HOL_cs 1),
        (rtac allI 1),
        (rtac dlist_all_finite_lemma1 1)
        ]);

qed_goalw "dlist_all_finite" Dlist.thy [dlist_finite_def] "dlist_finite(l)"
 (fn prems =>
        [
        (rtac  dlist_all_finite_lemma2 1)
        ]);

qed_goal "dlist_ind" Dlist.thy
"[|P(UU);P(dnil);\
\  !! x l1.[|x~=UU;l1~=UU;P(l1)|] ==> P(dcons`x`l1)|] ==> P(l)"
 (fn prems =>
        [
        (rtac (dlist_all_finite_lemma2 RS exE) 1),
        (etac subst 1),
        (rtac (dlist_finite_ind RS spec) 1),
        (REPEAT (resolve_tac prems 1)),
        (REPEAT (atac 1))
        ]);




