(*  Title:      HOLCF/lift1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen
*)

open Lift1;

qed_goalw "Exh_Lift" Lift1.thy [UU_lift_def,Iup_def ]
        "z = UU_lift | (? x. z = Iup(x))"
 (fn prems =>
        [
        (rtac (Rep_Lift_inverse RS subst) 1),
        (res_inst_tac [("s","Rep_Lift(z)")] sumE 1),
        (rtac disjI1 1),
        (res_inst_tac [("f","Abs_Lift")] arg_cong 1),
        (rtac (unique_void2 RS subst) 1),
        (atac 1),
        (rtac disjI2 1),
        (rtac exI 1),
        (res_inst_tac [("f","Abs_Lift")] arg_cong 1),
        (atac 1)
        ]);

qed_goal "inj_Abs_Lift" Lift1.thy "inj(Abs_Lift)"
 (fn prems =>
        [
        (rtac inj_inverseI 1),
        (rtac Abs_Lift_inverse 1)
        ]);

qed_goal "inj_Rep_Lift" Lift1.thy "inj(Rep_Lift)"
 (fn prems =>
        [
        (rtac inj_inverseI 1),
        (rtac Rep_Lift_inverse 1)
        ]);

qed_goalw "inject_Iup" Lift1.thy [Iup_def] "Iup(x)=Iup(y) ==> x=y"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (inj_Inr RS injD) 1),
        (rtac (inj_Abs_Lift RS injD) 1),
        (atac 1)
        ]);

qed_goalw "defined_Iup" Lift1.thy [Iup_def,UU_lift_def] "Iup(x)~=UU_lift"
 (fn prems =>
        [
        (rtac notI 1),
        (rtac notE 1),
        (rtac Inl_not_Inr 1),
        (rtac sym 1),
        (etac (inj_Abs_Lift RS  injD) 1)
        ]);


qed_goal "liftE"  Lift1.thy
        "[| p=UU_lift ==> Q; !!x. p=Iup(x)==>Q|] ==>Q"
 (fn prems =>
        [
        (rtac (Exh_Lift RS disjE) 1),
        (eresolve_tac prems 1),
        (etac exE 1),
        (eresolve_tac prems 1)
        ]);

qed_goalw "Ilift1"  Lift1.thy [Ilift_def,UU_lift_def]
        "Ilift(f)(UU_lift)=UU"
 (fn prems =>
        [
        (stac Abs_Lift_inverse 1),
        (stac sum_case_Inl 1),
        (rtac refl 1)
        ]);

qed_goalw "Ilift2"  Lift1.thy [Ilift_def,Iup_def]
        "Ilift(f)(Iup(x))=f`x"
 (fn prems =>
        [
        (stac Abs_Lift_inverse 1),
        (stac sum_case_Inr 1),
        (rtac refl 1)
        ]);

val Lift0_ss = (simpset_of "Cfun3") addsimps [Ilift1,Ilift2];

qed_goalw "less_lift1a"  Lift1.thy [less_lift_def,UU_lift_def]
        "less_lift(UU_lift)(z)"
 (fn prems =>
        [
        (stac Abs_Lift_inverse 1),
        (stac sum_case_Inl 1),
        (rtac TrueI 1)
        ]);

qed_goalw "less_lift1b"  Lift1.thy [Iup_def,less_lift_def,UU_lift_def]
        "~less_lift (Iup x) UU_lift"
 (fn prems =>
        [
        (rtac notI 1),
        (rtac iffD1 1),
        (atac 2),
        (stac Abs_Lift_inverse 1),
        (stac Abs_Lift_inverse 1),
        (stac sum_case_Inr 1),
        (stac sum_case_Inl 1),
        (rtac refl 1)
        ]);

qed_goalw "less_lift1c"  Lift1.thy [Iup_def,less_lift_def,UU_lift_def]
        "less_lift (Iup x) (Iup y)=(x<<y)"
 (fn prems =>
        [
        (stac Abs_Lift_inverse 1),
        (stac Abs_Lift_inverse 1),
        (stac sum_case_Inr 1),
        (stac sum_case_Inr 1),
        (rtac refl 1)
        ]);


qed_goal "refl_less_lift"  Lift1.thy "less_lift p p"
 (fn prems =>
        [
        (res_inst_tac [("p","p")] liftE 1),
        (hyp_subst_tac 1),
        (rtac less_lift1a 1),
        (hyp_subst_tac 1),
        (rtac (less_lift1c RS iffD2) 1),
        (rtac refl_less 1)
        ]);

qed_goal "antisym_less_lift"  Lift1.thy 
        "!!p1. [|less_lift p1 p2;less_lift p2 p1|] ==> p1=p2"
 (fn _ =>
        [
        (res_inst_tac [("p","p1")] liftE 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("p","p2")] liftE 1),
        (etac sym 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("P","less_lift (Iup x) UU_lift")] notE 1),
        (rtac less_lift1b 1),
        (atac 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("p","p2")] liftE 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("P","less_lift (Iup x) UU_lift")] notE 1),
        (rtac less_lift1b 1),
        (atac 1),
        (hyp_subst_tac 1),
        (rtac arg_cong 1),
        (rtac antisym_less 1),
        (etac (less_lift1c RS iffD1) 1),
        (etac (less_lift1c RS iffD1) 1)
        ]);

qed_goal "trans_less_lift"  Lift1.thy 
        "[|less_lift p1 p2;less_lift p2 p3|] ==> less_lift p1 p3"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (res_inst_tac [("p","p1")] liftE 1),
        (hyp_subst_tac 1),
        (rtac less_lift1a 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("p","p2")] liftE 1),
        (hyp_subst_tac 1),
        (rtac notE 1),
        (rtac less_lift1b 1),
        (atac 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("p","p3")] liftE 1),
        (hyp_subst_tac 1),
        (rtac notE 1),
        (rtac less_lift1b 1),
        (atac 1),
        (hyp_subst_tac 1),
        (rtac (less_lift1c RS iffD2) 1),
        (rtac trans_less 1),
        (etac (less_lift1c RS iffD1) 1),
        (etac (less_lift1c RS iffD1) 1)
        ]);

