(*  Title:      HOL/BCV/Opt.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

Goalw [lesub_def,le_def]
 "o1 <=_(le r) o2 = \
\ (case o2 of None => o1=None | \
\             Some y => (case o1 of None => True | Some x => x <=_r y))";
br refl 1;
qed "unfold_le_opt";

Goal "order r ==> o1 <=_(le r) o1";
by (asm_simp_tac (simpset() addsimps [unfold_le_opt] addsplits [option.split]) 1);
qed "le_opt_refl";

Goal "order r ==> \
\     o1 <=_(le r) o2 --> o2 <=_(le r) o3 --> o1 <=_(le r) o3";
by (simp_tac (simpset() addsimps [unfold_le_opt] addsplits [option.split]) 1);
by (blast_tac (claset() addIs [order_trans]) 1);
qed_spec_mp "le_opt_trans";

Goal "order r ==> o1 <=_(le r) o2 --> o2 <=_(le r) o1 --> o1=o2";
by (simp_tac (simpset() addsimps [unfold_le_opt] addsplits [option.split]) 1);
by (blast_tac (claset() addIs [order_antisym]) 1);
qed_spec_mp "le_opt_antisym";

Goal "order r ==> order(le r)";
by(stac order_def 1);
by(blast_tac (claset() addIs [le_opt_refl,le_opt_trans,le_opt_antisym]) 1);
qed "order_le_opt";
AddSIs [order_le_opt];
Addsimps [order_le_opt];

Goalw [lesub_def,le_def] "None <=_(le r) ox";
by(simp_tac (simpset() addsplits [option.split]) 1);
qed "None_bot";
AddIffs [None_bot];

Goalw [lesub_def,le_def]
 "(Some x <=_(le r) ox) = (? y. ox = Some y & x <=_r y)";
by(simp_tac (simpset() addsplits [option.split]) 1);
qed "Some_le";
AddIffs [Some_le];

Goalw [lesub_def,le_def] "(ox <=_(le r) None) = (ox = None)";
by(simp_tac (simpset() addsplits [option.split]) 1);
qed "le_None";
AddIffs [le_None];


Goalw [Opt.sl_def,semilat_def,closed_def,split RS eq_reflection]
 "!!L. semilat L ==> semilat (Opt.sl L)";
by(split_all_tac 1);
by (asm_full_simp_tac (simpset() addsplits [option.split]
 addsimps [lesub_def,Opt.le_def,plussub_def,Opt.sup_def,opt_def,Bex_def]) 1);
by (asm_full_simp_tac (simpset() addsimps [order_def,lesub_def]) 1);
qed "semilat_opt";


Goalw [top_def] "top (le r) (Some T) = top r T";
br iffI 1;
 by(Blast_tac 1);
br allI 1;
by(case_tac "x" 1);
by(ALLGOALS Asm_simp_tac);
qed "top_le_opt_Some";
AddIffs [top_le_opt_Some];

Goalw [top_def] "[| order r; top r T |] ==> (T <=_r x) = (x = T)";
by(blast_tac (claset() addIs [order_antisym]) 1);
qed "Top_le_conv";


Goalw [opt_def] "None : opt A";
by (Simp_tac 1);
qed "None_in_opt";
AddIffs [None_in_opt];

Goalw [opt_def] "(Some x : opt A) = (x:A)";
by (Auto_tac);
qed "Some_in_opt";
AddIffs [Some_in_opt];

Goalw [acc_def,lesub_def,le_def,lesssub_def] "acc r ==> acc(le r)";
by (asm_full_simp_tac (simpset() addsimps [wf_eq_minimal] addsplits [option.split]) 1);
by (Clarify_tac 1);
by (case_tac "? a. Some a : Q" 1);
 by (eres_inst_tac [("x","{a . Some a : Q}")] allE 1);
 by (Blast_tac 1);
by (case_tac "x" 1);
 by (Blast_tac 1);
by (Blast_tac 1);
qed "acc_le_optI";
AddSIs [acc_le_optI];


Goalw [option_map_def]
 "[| ox : opt S; !x:S. ox = Some x --> f x : S |] \
\ ==> option_map f ox : opt S";
by (asm_simp_tac (simpset() addsplits [option.split]) 1);
by(Blast_tac 1);
qed "option_map_in_optionI";

