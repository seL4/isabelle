(*  Title:      HOLCF/Up1.ML
    ID:         $Id$
    Author:     Franz Regensburger

Lifting.
*)

Goal "Rep_Up (Abs_Up y) = y";
by (simp_tac (simpset() addsimps [Up_def,Abs_Up_inverse]) 1);
qed "Abs_Up_inverse2";

Goalw [Iup_def] "z = Abs_Up(Inl ()) | (? x. z = Iup x)";
by (rtac (Rep_Up_inverse RS subst) 1);
by (res_inst_tac [("s","Rep_Up z")] sumE 1);
by (rtac disjI1 1);
by (res_inst_tac [("f","Abs_Up")] arg_cong 1);
by (rtac (unit_eq RS subst) 1);
by (atac 1);
by (rtac disjI2 1);
by (rtac exI 1);
by (res_inst_tac [("f","Abs_Up")] arg_cong 1);
by (atac 1);
qed "Exh_Up";

Goal "inj(Abs_Up)";
by (rtac inj_inverseI 1);
by (rtac Abs_Up_inverse2 1);
qed "inj_Abs_Up";

Goal "inj(Rep_Up)";
by (rtac inj_inverseI 1);
by (rtac Rep_Up_inverse 1);
qed "inj_Rep_Up";

Goalw [Iup_def] "Iup x=Iup y ==> x=y";
by (rtac (inj_Inr RS injD) 1);
by (rtac (inj_Abs_Up RS injD) 1);
by (atac 1);
qed "inject_Iup";

AddSDs [inject_Iup];

Goalw [Iup_def] "Iup x~=Abs_Up(Inl ())";
by (rtac notI 1);
by (rtac notE 1);
by (rtac Inl_not_Inr 1);
by (rtac sym 1);
by (etac (inj_Abs_Up RS  injD) 1);
qed "defined_Iup";


val prems = Goal "[| p=Abs_Up(Inl ()) ==> Q; !!x. p=Iup(x)==>Q|] ==>Q";
by (rtac (Exh_Up RS disjE) 1);
by (eresolve_tac prems 1);
by (etac exE 1);
by (eresolve_tac prems 1);
qed "upE";

Goalw [Ifup_def] "Ifup(f)(Abs_Up(Inl ()))=UU";
by (stac Abs_Up_inverse2 1);
by (stac sum_case_Inl 1);
by (rtac refl 1);
qed "Ifup1";

Goalw [Ifup_def,Iup_def]
        "Ifup(f)(Iup(x))=f$x";
by (stac Abs_Up_inverse2 1);
by (stac sum_case_Inr 1);
by (rtac refl 1);
qed "Ifup2";

val Up0_ss = (simpset_of Cfun3.thy) delsimps [range_composition] 
	     addsimps [Ifup1,Ifup2];

Addsimps [Ifup1,Ifup2];

Goalw [less_up_def]
        "Abs_Up(Inl ())<< z";
by (stac Abs_Up_inverse2 1);
by (stac sum_case_Inl 1);
by (rtac TrueI 1);
qed "less_up1a";

Goalw [Iup_def,less_up_def]
        "~(Iup x) << (Abs_Up(Inl ()))";
by (rtac notI 1);
by (rtac iffD1 1);
by (atac 2);
by (stac Abs_Up_inverse2 1);
by (stac Abs_Up_inverse2 1);
by (stac sum_case_Inr 1);
by (stac sum_case_Inl 1);
by (rtac refl 1);
qed "less_up1b";

Goalw [Iup_def,less_up_def]
        "(Iup x) << (Iup y)=(x<<y)";
by (stac Abs_Up_inverse2 1);
by (stac Abs_Up_inverse2 1);
by (stac sum_case_Inr 1);
by (stac sum_case_Inr 1);
by (rtac refl 1);
qed "less_up1c";

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

