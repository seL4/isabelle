(*  Title:      HOL/Lex/AutoChopper.ML
    ID:         $Id$
    Author:     Richard Mayr & Tobias Nipkow
    Copyright   1995 TUM

Main result: auto_chopper satisfies the is_auto_chopper specification.
*)

Delsimps (ex_simps @ all_simps);
Delsimps [split_paired_All];

Addsimps [Let_def];

Goalw [acc_prefix_def] "~acc_prefix A [] s";
by (Simp_tac 1);
qed"acc_prefix_Nil";
Addsimps [acc_prefix_Nil];

Goalw [acc_prefix_def]
 "acc_prefix A (x#xs) s = (fin A (next A x s) | acc_prefix A xs (next A x s))";
by (simp_tac (simpset() addsimps [thm "prefix_Cons"]) 1);
by Safe_tac;
  by (Asm_full_simp_tac 1);
  by (case_tac "zs=[]" 1);
   by (hyp_subst_tac 1);
   by (Asm_full_simp_tac 1);
  by (Fast_tac 1);
 by (res_inst_tac [("x","[x]")] exI 1);
 by (asm_simp_tac (simpset() addsimps [eq_sym_conv]) 1);
by (res_inst_tac [("x","x#us")] exI 1);
by (Asm_simp_tac 1);
qed"acc_prefix_Cons";
Addsimps [acc_prefix_Cons];

Goal "!st us p y ys. acc A st p (ys@[y]) xs us ~= ([],zs)";
by (induct_tac "xs" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed_spec_mp "accept_not_Nil";
Addsimps [accept_not_Nil];

Goal
"!st us. acc A st ([],ys) [] xs us = ([], zs) --> \
\        zs = ys & (!ys. ys ~= [] & ys<=xs --> ~fin A (delta A ys st))";
by (induct_tac "xs" 1);
by (simp_tac (simpset() addcongs [conj_cong]) 1);
by (Simp_tac 1);
by (strip_tac 1);
by (rtac conjI 1);
by (Fast_tac 1);
by (simp_tac (simpset() addsimps [thm "prefix_Cons"] addcongs [conj_cong]) 1);
by (strip_tac 1);
by (REPEAT(eresolve_tac [conjE,exE] 1));
by (hyp_subst_tac 1);
by (Simp_tac 1);
by (case_tac "zsa = []" 1);
by (Asm_simp_tac 1);
by (Fast_tac 1);
qed_spec_mp "no_acc";


val [prem] = goal HOL.thy "? x. P(f(x)) ==> ? y. P(y)";
by (cut_facts_tac [prem] 1);
by (Fast_tac 1);
val ex_special = result();


Goal
"! r erk l rst st ys yss zs::'a list. \
\    acc A st (l,rst) erk xs r = (ys#yss, zs) --> \
\    ys@concat(yss)@zs = (if acc_prefix A xs st then r@xs else erk@concat(l)@rst)";
by (induct_tac "xs" 1);
 by (simp_tac (simpset() addcongs [conj_cong]) 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("p","acc A (start A) ([],list) [] list []")] PairE 1);
by (rename_tac "vss lrst" 1);  
by (Asm_simp_tac 1);
by (case_tac "vss" 1);
 by (hyp_subst_tac 1);
 by (Simp_tac 1);
 by (fast_tac (claset() addSDs [no_acc]) 1);
by (hyp_subst_tac 1);
by (Asm_simp_tac 1);
qed_spec_mp "step2_a";


Goal
 "! st erk r l rest ys yss zs.\
\   acc A st (l,rest) erk xs r = (ys#yss, zs) --> \
\     (if acc_prefix A xs st \
\      then ys ~= [] \
\      else ys ~= [] | (erk=[] & (l,rest) = (ys#yss,zs)))";
by (Simp_tac 1);
by (induct_tac "xs" 1);
 by (simp_tac (simpset() addcongs [conj_cong]) 1);
 by (Fast_tac 1);
by (asm_simp_tac (simpset() addcongs [conj_cong]) 1);
by (res_inst_tac [("p","acc A (start A) ([],list) [] list []")] PairE 1);
by (rename_tac "vss lrst" 1);  
by (Asm_simp_tac 1);
by (strip_tac 1);
by (case_tac "acc_prefix A list (next A a st)" 1);
 by (Asm_simp_tac 1);
by (subgoal_tac "r @ [a] ~= []" 1);
 by (Fast_tac 1);
by (Simp_tac 1);
qed_spec_mp "step2_b";


Goal  
 "! st erk r l rest ys yss zs. \
\   acc A st (l,rest) erk xs r = (ys#yss, zs) --> \
\     (if acc_prefix A xs st                   \
\      then ? g. ys=r@g & fin A (delta A g st)  \
\      else (erk~=[] & erk=ys) | (erk=[] & (l,rest) = (ys#yss,zs)))";
by (Simp_tac 1);
by (induct_tac "xs" 1);
 by (simp_tac (simpset() addcongs [conj_cong]) 1);
 by (Fast_tac 1);
by (asm_simp_tac (simpset() addcongs [conj_cong]) 1);
by (strip_tac 1);
by (rtac conjI 1);
 by (res_inst_tac [("p","acc A (start A) ([],list) [] list []")] PairE 1);
 by (rename_tac "vss lrst" 1);  
 by (Asm_simp_tac 1);
 by (case_tac "acc_prefix A list (next A a st)" 1);
  by (strip_tac 1);
  by (res_inst_tac [("f","%k. a#k")] ex_special 1);
  by (Simp_tac 1);
  by (res_inst_tac [("t","%k. ys=r@a#k"),("s","%k. ys=(r@[a])@k")] subst 1);
   by (Simp_tac 1);
  by (Fast_tac 1);
 by (strip_tac 1);
 by (res_inst_tac [("x","[a]")] exI 1);
 by (Asm_simp_tac 1);
 by (subgoal_tac "r @ [a] ~= []" 1);
  by (rtac sym 1);
  by (Fast_tac 1);
 by (Simp_tac 1);
by (strip_tac 1);
by (res_inst_tac [("f","%k. a#k")] ex_special 1);
by (Simp_tac 1);
by (res_inst_tac [("t","%k. ys=r@a#k"),("s","%k. ys=(r@[a])@k")] subst 1);
 by (Simp_tac 1);
by (Fast_tac 1);
qed_spec_mp "step2_c";


Goal
 "! st erk r l rest ys yss zs. \
\   acc A st (l,rest) erk xs r = (ys#yss, zs) --> \
\     (if acc_prefix A xs st       \
\      then acc A (start A) ([],concat(yss)@zs) [] (concat(yss)@zs) [] = (yss,zs) \
\      else (erk~=[] & (l,rest)=(yss,zs)) | (erk=[] & (l, rest)=(ys#yss,zs)))";
by (Simp_tac 1);
by (induct_tac "xs" 1);
 by (simp_tac (simpset() addcongs [conj_cong]) 1);
 by (Fast_tac 1);
by (asm_simp_tac (simpset() addcongs [conj_cong]) 1);
by (res_inst_tac [("p","acc A (start A) ([],list) [] list []")] PairE 1);
by (rename_tac "vss lrst" 1);  
by (Asm_simp_tac 1);
by (strip_tac 1);
by (case_tac "acc_prefix A list (next A a st)" 1);
 by (Asm_simp_tac 1);
by (subgoal_tac "acc A (start A) ([],list) [] list [] = (yss,zs)" 1);
 by (Asm_simp_tac 2);
 by (subgoal_tac "r@[a] ~= []" 2);
  by (Fast_tac 2);
 by (Simp_tac 2);
by (subgoal_tac "concat(yss) @ zs = list" 1);
 by (hyp_subst_tac 1);
 by (atac 1);
by (case_tac "yss = []" 1);
 by (Asm_simp_tac 1);
 by (hyp_subst_tac 1);
 by (fast_tac (claset() addSDs [no_acc]) 1);
by (etac ((neq_Nil_conv RS iffD1) RS exE) 1);
by (etac exE 1);
by (hyp_subst_tac 1);
by (Simp_tac 1);
by (rtac trans 1);
 by (etac step2_a 1);
by (Simp_tac 1);
qed_spec_mp "step2_d";

Goal 
"! st erk r p ys yss zs. \
\  acc A st p erk xs r = (ys#yss, zs) --> \
\  (if acc_prefix A xs st  \
\   then ? g. ys=r@g & (!as. as<=xs & g<=as & g~=as --> ~fin A (delta A as st))\
\   else (erk~=[] & ys=erk) | (erk=[] & (ys#yss,zs)=p))";
by (Simp_tac 1);
by (induct_tac "xs" 1);
 by (simp_tac (simpset() addcongs [conj_cong]) 1);
 by (Fast_tac 1);
by (asm_simp_tac (simpset() addcongs [conj_cong]) 1);
by (strip_tac 1);
by (case_tac "acc_prefix A list (next A a st)" 1);
 by (rtac conjI 1);
  by (strip_tac 1);
  by (res_inst_tac [("f","%k. a#k")] ex_special 1);
  by (res_inst_tac [("t","%k. ys=r@a#k"),("s","%k. ys=(r@[a])@k")] subst 1);
   by (Simp_tac 1);
  by (res_inst_tac [("P","%k. ys = (r@[a])@k & (!as. as<=list & k<=as & k ~= as --> ~ fin A (delta A as (next A a st)))")] exE 1);
   by (asm_simp_tac HOL_ss 1);
  by (res_inst_tac [("x","x")] exI 1);
  by (Asm_simp_tac 1);
  by(rtac allI 1);
  by(case_tac "as" 1);
   by (Asm_simp_tac 1);
  by (asm_simp_tac (simpset() addcongs[conj_cong]) 1);
 by (strip_tac 1);
 by (res_inst_tac [("f","%k. a#k")] ex_special 1);
 by (res_inst_tac [("t","%k. ys=r@a#k"),("s","%k. ys=(r@[a])@k")] subst 1);
  by (Simp_tac 1);
 by (res_inst_tac [("P","%k. ys=(r@[a])@k & (!as. as<=list & k<=as & k~=as --> ~ fin A (delta A as (next A a st)))")] exE 1);
  by (asm_simp_tac HOL_ss 1);
 by (res_inst_tac [("x","x")] exI 1);
 by (Asm_simp_tac 1);
 by(rtac allI 1);
 by(case_tac "as" 1);
  by (Asm_simp_tac 1);
 by (asm_simp_tac (simpset() addcongs[conj_cong]) 1);
by (Asm_simp_tac 1);
by (strip_tac 1);
by (res_inst_tac [("x","[a]")] exI 1);
by (rtac conjI 1);
 by (subgoal_tac "r @ [a] ~= []" 1);
  by (Fast_tac 1);
 by (Simp_tac 1);
by(rtac allI 1);
by(case_tac "as" 1);
 by (Asm_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [acc_prefix_def] addcongs[conj_cong]) 1);
by (etac thin_rl 1); (* speed up *)
by (Fast_tac 1);
qed_spec_mp "step2_e";

Addsimps[split_paired_All];

Goalw [accepts_def, is_auto_chopper_def, auto_chopper_def,
           Chopper.is_longest_prefix_chopper_def]
 "is_auto_chopper(auto_chopper)";
by (REPEAT(ares_tac [no_acc,allI,impI,conjI] 1));
 by (rtac mp 1);
  by (etac step2_b 2);
 by (Simp_tac 1);
by (rtac conjI 1);
 by (rtac mp 1);
  by (etac step2_c 2);
 by (Simp_tac 1);
by (rtac conjI 1);
 by (asm_simp_tac (simpset() addsimps [step2_a]) 1);
by (rtac conjI 1);
 by (rtac mp 1);
  by (etac step2_d 2);
 by (Simp_tac 1);
by (rtac mp 1);
 by (etac step2_e 2);
 by (Simp_tac 1);
qed"auto_chopper_is_auto_chopper";
