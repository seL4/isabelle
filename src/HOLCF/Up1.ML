(*  Title:      HOLCF/Up1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen
*)

open Up1;

qed_goalw "Exh_Up" Up1.thy [UU_up_def,Iup_def ]
        "z = UU_up | (? x. z = Iup(x))"
 (fn prems =>
        [
        (rtac (Rep_Up_inverse RS subst) 1),
        (res_inst_tac [("s","Rep_Up(z)")] sumE 1),
        (rtac disjI1 1),
        (res_inst_tac [("f","Abs_Up")] arg_cong 1),
        (rtac (unique_void2 RS subst) 1),
        (atac 1),
        (rtac disjI2 1),
        (rtac exI 1),
        (res_inst_tac [("f","Abs_Up")] arg_cong 1),
        (atac 1)
        ]);

qed_goal "inj_Abs_Up" Up1.thy "inj(Abs_Up)"
 (fn prems =>
        [
        (rtac inj_inverseI 1),
        (rtac Abs_Up_inverse 1)
        ]);

qed_goal "inj_Rep_Up" Up1.thy "inj(Rep_Up)"
 (fn prems =>
        [
        (rtac inj_inverseI 1),
        (rtac Rep_Up_inverse 1)
        ]);

qed_goalw "inject_Iup" Up1.thy [Iup_def] "Iup(x)=Iup(y) ==> x=y"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (inj_Inr RS injD) 1),
        (rtac (inj_Abs_Up RS injD) 1),
        (atac 1)
        ]);

qed_goalw "defined_Iup" Up1.thy [Iup_def,UU_up_def] "Iup(x)~=UU_up"
 (fn prems =>
        [
        (rtac notI 1),
        (rtac notE 1),
        (rtac Inl_not_Inr 1),
        (rtac sym 1),
        (etac (inj_Abs_Up RS  injD) 1)
        ]);


qed_goal "upE"  Up1.thy
        "[| p=UU_up ==> Q; !!x. p=Iup(x)==>Q|] ==>Q"
 (fn prems =>
        [
        (rtac (Exh_Up RS disjE) 1),
        (eresolve_tac prems 1),
        (etac exE 1),
        (eresolve_tac prems 1)
        ]);

qed_goalw "Ifup1"  Up1.thy [Ifup_def,UU_up_def]
        "Ifup(f)(UU_up)=UU"
 (fn prems =>
        [
        (stac Abs_Up_inverse 1),
        (stac sum_case_Inl 1),
        (rtac refl 1)
        ]);

qed_goalw "Ifup2"  Up1.thy [Ifup_def,Iup_def]
        "Ifup(f)(Iup(x))=f`x"
 (fn prems =>
        [
        (stac Abs_Up_inverse 1),
        (stac sum_case_Inr 1),
        (rtac refl 1)
        ]);

val Up0_ss = (simpset_of "Cfun3") addsimps [Ifup1,Ifup2];

qed_goalw "less_up1a"  Up1.thy [less_up_def,UU_up_def]
        "less_up(UU_up)(z)"
 (fn prems =>
        [
        (stac Abs_Up_inverse 1),
        (stac sum_case_Inl 1),
        (rtac TrueI 1)
        ]);

qed_goalw "less_up1b"  Up1.thy [Iup_def,less_up_def,UU_up_def]
        "~less_up (Iup x) UU_up"
 (fn prems =>
        [
        (rtac notI 1),
        (rtac iffD1 1),
        (atac 2),
        (stac Abs_Up_inverse 1),
        (stac Abs_Up_inverse 1),
        (stac sum_case_Inr 1),
        (stac sum_case_Inl 1),
        (rtac refl 1)
        ]);

qed_goalw "less_up1c"  Up1.thy [Iup_def,less_up_def,UU_up_def]
        "less_up (Iup x) (Iup y)=(x<<y)"
 (fn prems =>
        [
        (stac Abs_Up_inverse 1),
        (stac Abs_Up_inverse 1),
        (stac sum_case_Inr 1),
        (stac sum_case_Inr 1),
        (rtac refl 1)
        ]);


qed_goal "refl_less_up"  Up1.thy "less_up p p"
 (fn prems =>
        [
        (res_inst_tac [("p","p")] upE 1),
        (hyp_subst_tac 1),
        (rtac less_up1a 1),
        (hyp_subst_tac 1),
        (rtac (less_up1c RS iffD2) 1),
        (rtac refl_less 1)
        ]);

qed_goal "antisym_less_up"  Up1.thy 
        "!!p1. [|less_up p1 p2;less_up p2 p1|] ==> p1=p2"
 (fn _ =>
        [
        (res_inst_tac [("p","p1")] upE 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("p","p2")] upE 1),
        (etac sym 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("P","less_up (Iup x) UU_up")] notE 1),
        (rtac less_up1b 1),
        (atac 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("p","p2")] upE 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("P","less_up (Iup x) UU_up")] notE 1),
        (rtac less_up1b 1),
        (atac 1),
        (hyp_subst_tac 1),
        (rtac arg_cong 1),
        (rtac antisym_less 1),
        (etac (less_up1c RS iffD1) 1),
        (etac (less_up1c RS iffD1) 1)
        ]);

qed_goal "trans_less_up"  Up1.thy 
        "[|less_up p1 p2;less_up p2 p3|] ==> less_up p1 p3"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (res_inst_tac [("p","p1")] upE 1),
        (hyp_subst_tac 1),
        (rtac less_up1a 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("p","p2")] upE 1),
        (hyp_subst_tac 1),
        (rtac notE 1),
        (rtac less_up1b 1),
        (atac 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("p","p3")] upE 1),
        (hyp_subst_tac 1),
        (rtac notE 1),
        (rtac less_up1b 1),
        (atac 1),
        (hyp_subst_tac 1),
        (rtac (less_up1c RS iffD2) 1),
        (rtac trans_less 1),
        (etac (less_up1c RS iffD1) 1),
        (etac (less_up1c RS iffD1) 1)
        ]);

