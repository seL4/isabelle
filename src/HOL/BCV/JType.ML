(*  Title:      HOL/BCV/JType.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

Goalw [lesub_def,subtype_def] "T [=_S T";
by (Simp_tac 1);
qed "subtype_refl";
AddIffs [subtype_refl];

Goalw [lesub_def,subtype_def,is_Class_def]
 "(T [=_S Integer) = (T = Integer)";
by (Simp_tac 1);
qed "subtype_Int_conv";

Goalw [lesub_def,subtype_def] "(Integer [=_S T) = (T = Integer)";
by (Blast_tac 1);
qed "Int_subtype_conv";

Goalw [lesub_def,subtype_def,is_Class_def]
 "(T [=_S Void) = (T = Void)";
by (Simp_tac 1);
qed "subtype_Void_conv";

Goalw [lesub_def,subtype_def] "(Void [=_S T) = (T = Void)";
by (Blast_tac 1);
qed "Void_subtype_conv";

AddIffs [subtype_Int_conv,Int_subtype_conv,
         subtype_Void_conv,Void_subtype_conv];

Goalw [lesub_def,subtype_def,is_Class_def]
 "T [=_S NullT = (T=NullT)";
by (Simp_tac 1);
qed "subtype_NullT_conv";

Goalw [lesub_def,subtype_def,is_Class_def]
 "NullT [=_S T = (T=NullT | (? C. T = Class C))";
by (simp_tac (simpset() addsplits [ty.split]) 1);
qed "NullT_subtype_conv";

AddIffs [NullT_subtype_conv,subtype_NullT_conv];

Goalw [lesub_def,subtype_def,is_Class_def]
 "T [=_S Class C = (T=NullT | (? D. T = Class D & (D,C) : S^*))";
by (Simp_tac 1);
by (Blast_tac 1);
qed "subtype_Class_conv";

Goalw [lesub_def,subtype_def,refl_def]
 "Class D [=_S T = (? C. T = Class C & (D,C):S^*)";
by (Blast_tac 1);
qed "Class_subtype_conv";

AddIffs [Class_subtype_conv,subtype_Class_conv];

Goalw [lesub_def,subtype_def,is_Class_def]
 "[| A [=_S B; B [=_S C |] ==> A [=_S C";
by (asm_full_simp_tac (simpset() addsplits [ty.split,ty.split_asm]) 1);
by (blast_tac (claset() addDs [transD] addIs [rtrancl_trans]) 1);
qed "subtype_transD";

Goalw [order_def,subtype_def,lesub_def,is_Class_def]
 "acyclic S ==> order (subtype S)";
by (dtac acyclic_impl_antisym_rtrancl 1);
by (auto_tac (claset() addIs [rtrancl_trans],simpset() addsimps [antisymD]) );
qed "acyclic_impl_order_subtype";

Goalw [acc_def,lesssub_def]
 "wf(S^-1) ==> acc(subtype S)";
by (dres_inst_tac [("p","S^-1 - Id")] wf_subset 1);
 by (Blast_tac 1);
by (dtac wf_trancl 1);
by (asm_full_simp_tac (simpset() addsimps [wf_eq_minimal]) 1);
by (Clarify_tac 1);
by (rename_tac "M T" 1);
by (case_tac "EX C. Class C : M" 1);
 by (case_tac "T" 2);
    by (Blast_tac 2);
   by (Blast_tac 2);
  by (res_inst_tac [("x","T")] bexI 2);
   by (Blast_tac 2);
  by (assume_tac 2);
 by (Blast_tac 2);
by (eres_inst_tac [("x","{C. Class C : M}")] allE 1);
by (Auto_tac);
by (rename_tac "D" 1);
by (res_inst_tac [("x","Class D")] bexI 1);
 by (atac 2);
by (Clarify_tac 1);
by (cut_inst_tac [("r","S")] (standard(rtrancl_r_diff_Id RS sym)) 1);
by (Asm_full_simp_tac 1);
by (etac rtranclE 1);
 by (Blast_tac 1);
by (dtac rtrancl_converseI 1);
by (subgoal_tac "(S-Id)^-1 = (S^-1 - Id)" 1);
 by (Blast_tac 2);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addIs [rtrancl_into_trancl2]) 1);
qed "wf_converse_subcls1_impl_acc_subtype";

Addsimps [is_type_def];

Goalw [closed_def,plussub_def,lift2_def,err_def,JType.sup_def]
 "[| single_valued S; acyclic S |] ==> \
\ closed (err(types S)) (lift2 (JType.sup S))";
by (simp_tac (simpset() addsplits [err.split,ty.split]) 1);
by (blast_tac (claset() addSDs [is_lub_some_lub,is_lubD,is_ubD]
                       addSIs [is_ubI]) 1);
qed "closed_err_types";

AddIffs [OK_le_conv];

Goalw [semilat_def, split_conv RS eq_reflection,JType.esl_def,Err.sl_def]
 "[| single_valued S; acyclic S |] ==> err_semilat (JType.esl S)";
by (asm_full_simp_tac (simpset() addsimps [acyclic_impl_order_subtype,closed_err_types]) 1);

by (rtac conjI 1);
 by (Clarify_tac 1);
 by (case_tac "x" 1);
  by (Clarify_tac 1);
  by (Simp_tac 1);
 by (case_tac "y" 1);
  by (Clarify_tac 1);
  by (Simp_tac 1);
 by (fast_tac (claset() addDs [is_lub_some_lub,is_lubD,is_ubD] addss
             (simpset() addsimps [plussub_def,lift2_def,JType.sup_def]
                        addsplits [ty.split])) 1);

by (rtac conjI 1);
 by (Clarify_tac 1);
 by (case_tac "x" 1);
  by (Clarify_tac 1);
  by (Simp_tac 1);
 by (case_tac "y" 1);
  by (Clarify_tac 1);
  by (Simp_tac 1);
 by (fast_tac (claset() addDs [is_lub_some_lub,is_lubD,is_ubD] addss
             (simpset() addsimps [plussub_def,lift2_def,JType.sup_def]
                        addsplits [ty.split])) 1);

by (Clarify_tac 1);
by (case_tac "x" 1);
 by (Clarify_tac 1);
by (case_tac "y" 1);
 by (Clarify_tac 1);
by (asm_simp_tac(simpset() addsimps [plussub_def,lift2_def,JType.sup_def]
                          addsplits [ty.split]) 1);
by (rtac conjI 1);
 by (Blast_tac 1);
by (rtac conjI 1);
 by (Blast_tac 1);
by (rtac conjI 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (rtac conjI 1);
 by (Clarify_tac 1);
by (rtac conjI 1);
 by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addSDs [is_lub_some_lub,is_lubD,is_ubD]
                       addSIs [is_ubI]) 1);
qed "err_semilat_JType_esl";

DelIffs [OK_le_conv];
