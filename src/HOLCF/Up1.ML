(*  Title:      HOLCF/Up1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen
*)

Goal "Rep_Up (Abs_Up y) = y";
by (simp_tac (simpset() addsimps [Up_def,Abs_Up_inverse]) 1);
qed "Abs_Up_inverse2";

qed_goalw "Exh_Up" thy [Iup_def ]
        "z = Abs_Up(Inl ()) | (? x. z = Iup x)"
 (fn prems =>
        [
        (rtac (Rep_Up_inverse RS subst) 1),
        (res_inst_tac [("s","Rep_Up z")] sumE 1),
        (rtac disjI1 1),
        (res_inst_tac [("f","Abs_Up")] arg_cong 1),
        (rtac (unit_eq RS subst) 1),
        (atac 1),
        (rtac disjI2 1),
        (rtac exI 1),
        (res_inst_tac [("f","Abs_Up")] arg_cong 1),
        (atac 1)
        ]);

Goal "inj(Abs_Up)";
by (rtac inj_inverseI 1);
by (rtac Abs_Up_inverse2 1);
qed "inj_Abs_Up";

Goal "inj(Rep_Up)";
by (rtac inj_inverseI 1);
by (rtac Rep_Up_inverse 1);
qed "inj_Rep_Up";

qed_goalw "inject_Iup" thy [Iup_def] "Iup x=Iup y ==> x=y"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (inj_Inr RS injD) 1),
        (rtac (inj_Abs_Up RS injD) 1),
        (atac 1)
        ]);

AddSDs [inject_Iup];

qed_goalw "defined_Iup" thy [Iup_def] "Iup x~=Abs_Up(Inl ())"
 (fn prems =>
        [
        (rtac notI 1),
        (rtac notE 1),
        (rtac Inl_not_Inr 1),
        (rtac sym 1),
        (etac (inj_Abs_Up RS  injD) 1)
        ]);


val prems = Goal "[| p=Abs_Up(Inl ()) ==> Q; !!x. p=Iup(x)==>Q|] ==>Q";
by (rtac (Exh_Up RS disjE) 1);
by (eresolve_tac prems 1);
by (etac exE 1);
by (eresolve_tac prems 1);
qed "upE";

qed_goalw "Ifup1"  thy [Ifup_def]
        "Ifup(f)(Abs_Up(Inl ()))=UU"
 (fn prems =>
        [
        (stac Abs_Up_inverse2 1),
        (stac sum_case_Inl 1),
        (rtac refl 1)
        ]);

qed_goalw "Ifup2"  thy [Ifup_def,Iup_def]
        "Ifup(f)(Iup(x))=f`x"
 (fn prems =>
        [
        (stac Abs_Up_inverse2 1),
        (stac sum_case_Inr 1),
        (rtac refl 1)
        ]);

val Up0_ss = (simpset_of Cfun3.thy) delsimps [range_composition] 
	     addsimps [Ifup1,Ifup2];

Addsimps [Ifup1,Ifup2];

qed_goalw "less_up1a"  thy [less_up_def]
        "Abs_Up(Inl ())<< z"
 (fn prems =>
        [
        (stac Abs_Up_inverse2 1),
        (stac sum_case_Inl 1),
        (rtac TrueI 1)
        ]);

qed_goalw "less_up1b" thy [Iup_def,less_up_def]
        "~(Iup x) << (Abs_Up(Inl ()))"
 (fn prems =>
        [
        (rtac notI 1),
        (rtac iffD1 1),
        (atac 2),
        (stac Abs_Up_inverse2 1),
        (stac Abs_Up_inverse2 1),
        (stac sum_case_Inr 1),
        (stac sum_case_Inl 1),
        (rtac refl 1)
        ]);

qed_goalw "less_up1c"  thy [Iup_def,less_up_def]
        "(Iup x) << (Iup y)=(x<<y)"
 (fn prems =>
        [
        (stac Abs_Up_inverse2 1),
        (stac Abs_Up_inverse2 1),
        (stac sum_case_Inr 1),
        (stac sum_case_Inr 1),
        (rtac refl 1)
        ]);

AddIffs [less_up1a, less_up1b, less_up1c];

Goal "(p::'a u) << p";
by (res_inst_tac [("p","p")] upE 1);
by Auto_tac;
qed "refl_less_up";

Goal "[|(p1::'a u) << p2;p2 << p1|] ==> p1=p2";
by (res_inst_tac [("p","p1")] upE 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("p","p2")] upE 1);
by (etac sym 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("P","(Iup x) << (Abs_Up(Inl ()))")] notE 1);
by (rtac less_up1b 1);
by (atac 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("p","p2")] upE 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("P","(Iup x) << (Abs_Up(Inl ()))")] notE 1);
by (rtac less_up1b 1);
by (atac 1);
by (blast_tac (claset() addIs [arg_cong, antisym_less, less_up1c RS iffD1]) 1);
qed "antisym_less_up";

Goal "[|(p1::'a u) << p2;p2 << p3|] ==> p1 << p3";
by (res_inst_tac [("p","p1")] upE 1);
by (hyp_subst_tac 1);
by (rtac less_up1a 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("p","p2")] upE 1);
by (hyp_subst_tac 1);
by (rtac notE 1);
by (rtac less_up1b 1);
by (atac 1);
by (res_inst_tac [("p","p3")] upE 1);
by Auto_tac;
by (blast_tac (claset() addIs [trans_less]) 1);
qed "trans_less_up";

