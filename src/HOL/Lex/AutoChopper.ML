(*  Title:      HOL/Lex/AutoChopper.ML
    ID:         $Id$
    Author:     Richard Mayr & Tobias Nipkow
    Copyright   1995 TUM

Main result: auto_chopper satisfies the is_auto_chopper specification.
*)

Delsimps (ex_simps @ all_simps);

open AutoChopper;

infix repeat_RS;
fun th1 repeat_RS th2 = ((th1 RS th2) repeat_RS th2) handle _ => th1;

Addsimps [Let_def];

goal AutoChopper.thy "!st us p y ys. acc xs st (ys@[y]) us p A ~= ([],zs)";
by (list.induct_tac "xs" 1);
by (Simp_tac 1);
by (asm_simp_tac (!simpset setloop (split_tac [expand_if])) 1);
val accept_not_Nil = result() repeat_RS spec;
Addsimps [accept_not_Nil];

goal AutoChopper.thy
"!st us. acc xs st [] us ([],ys) A = ([], zs) --> \
\        zs = ys & (!ys. ys ~= [] & ys<=xs --> ~fin A (nexts A st ys))";
by (list.induct_tac "xs" 1);
by (simp_tac (!simpset addcongs [conj_cong]) 1);
by (simp_tac (!simpset setloop (split_tac[expand_if])) 1);
by (strip_tac 1);
by (rtac conjI 1);
by (Fast_tac 1);
by (simp_tac (!simpset addsimps [prefix_Cons] addcongs [conj_cong]) 1);
by (strip_tac 1);
by (REPEAT(eresolve_tac [conjE,exE] 1));
by (hyp_subst_tac 1);
by (Simp_tac 1);
by (case_tac "zsa = []" 1);
by (Asm_simp_tac 1);
by (Fast_tac 1);
bind_thm("no_acc", result() RS spec RS spec RS mp);


val [prem] = goal HOL.thy "? x.P(f(x)) ==> ? y.P(y)";
by (cut_facts_tac [prem] 1);
by (Fast_tac 1);
val ex_special = result();


goal AutoChopper.thy
"! r erk l rst st ys yss zs::'a list. \
\    acc xs st erk r (l,rst) A = (ys#yss, zs) --> \
\    ys@concat(yss)@zs = (if acc_prefix A st xs then r@xs else erk@concat(l)@rst)";
by (list.induct_tac "xs" 1);
 by (simp_tac (!simpset addcongs [conj_cong] setloop (split_tac [expand_if])) 1);
by (asm_simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (res_inst_tac [("p","acc list (start A) [] [] ([],list) A")] PairE 1);
by (rename_tac "vss lrst" 1);  
by (asm_simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (res_inst_tac[("xs","vss")] list_eq_cases 1);
 by (hyp_subst_tac 1);
 by (Simp_tac 1);
 by (fast_tac (!claset addSDs [no_acc]) 1);
by (hyp_subst_tac 1);
by (asm_simp_tac (!simpset setloop (split_tac [expand_if])) 1);
val step2_a = (result() repeat_RS spec) RS mp;


goal AutoChopper.thy
 "! st erk r l rest ys yss zs.\
\   acc xs st erk r (l,rest) A = (ys#yss, zs) --> \
\     (if acc_prefix A st xs \
\      then ys ~= [] \
\      else ys ~= [] | (erk=[] & (l,rest) = (ys#yss,zs)))";
by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (list.induct_tac "xs" 1);
 by (simp_tac (!simpset addcongs [conj_cong] setloop (split_tac [expand_if])) 1);
 by (Fast_tac 1);
by (asm_simp_tac (!simpset addcongs [conj_cong] setloop (split_tac [expand_if])) 1);
by (res_inst_tac [("p","acc list (start A) [] [] ([],list) A")] PairE 1);
by (rename_tac "vss lrst" 1);  
by (Asm_simp_tac 1);
by (strip_tac 1);
by (case_tac "acc_prefix A (next A st a) list" 1);
 by (Asm_simp_tac 1);
by (subgoal_tac "r @ [a] ~= []" 1);
 by (Fast_tac 1);
by (Simp_tac 1);
val step2_b = (result() repeat_RS spec) RS mp;


goal AutoChopper.thy  
 "! st erk r l rest ys yss zs. \
\   acc xs st erk r (l,rest) A = (ys#yss, zs) --> \
\     (if acc_prefix A st xs                   \
\      then ? g. ys=r@g & fin A (nexts A st g)  \
\      else (erk~=[] & erk=ys) | (erk=[] & (l,rest) = (ys#yss,zs)))";
by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (list.induct_tac "xs" 1);
 by (simp_tac (!simpset addcongs [conj_cong] setloop (split_tac [expand_if])) 1);
 by (Fast_tac 1);
by (asm_simp_tac (!simpset addcongs [conj_cong] setloop (split_tac [expand_if])) 1);
by (strip_tac 1);
by (rtac conjI 1);
 by (res_inst_tac [("p","acc list (start A) [] [] ([],list) A")] PairE 1);
 by (rename_tac "vss lrst" 1);  
 by (Asm_simp_tac 1);
 by (case_tac "acc_prefix A (next A st a) list" 1);
  by (strip_tac 1);
  by (res_inst_tac [("f","%k.a#k")] ex_special 1);
  by (Simp_tac 1);
  by (res_inst_tac [("t","%k.ys=r@a#k"),("s","%k.ys=(r@[a])@k")] subst 1);
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
by (res_inst_tac [("f","%k.a#k")] ex_special 1);
by (Simp_tac 1);
by (res_inst_tac [("t","%k.ys=r@a#k"),("s","%k.ys=(r@[a])@k")] subst 1);
 by (Simp_tac 1);
by (Fast_tac 1);
val step2_c = (result() repeat_RS spec) RS mp;


goal AutoChopper.thy
 "! st erk r l rest ys yss zs. \
\   acc xs st erk r (l,rest) A = (ys#yss, zs) --> \
\     (if acc_prefix A st xs       \
\      then acc(concat(yss)@zs)(start A) [] [] ([],concat(yss)@zs) A = (yss,zs) \
\      else (erk~=[] & (l,rest)=(yss,zs)) | (erk=[] & (l, rest)=(ys#yss,zs)))";
by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (list.induct_tac "xs" 1);
 by (simp_tac (!simpset addcongs [conj_cong] setloop (split_tac [expand_if])) 1);
 by (Fast_tac 1);
by (asm_simp_tac (!simpset addcongs [conj_cong] setloop (split_tac [expand_if])) 1);
by (res_inst_tac [("p","acc list (start A) [] [] ([],list) A")] PairE 1);
by (rename_tac "vss lrst" 1);  
by (Asm_simp_tac 1);
by (strip_tac 1);
by (case_tac "acc_prefix A (next A st a) list" 1);
 by (Asm_simp_tac 1);
by (subgoal_tac "acc list (start A) [] [] ([],list) A = (yss,zs)" 1);
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
 by (fast_tac (!claset addSDs [no_acc]) 1);
by (etac ((neq_Nil_conv RS iffD1) RS exE) 1);
by (etac exE 1);
by (hyp_subst_tac 1);
by (Simp_tac 1);
by (rtac trans 1);
 by (etac step2_a 1);
by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
val step2_d = (result() repeat_RS spec) RS mp;

Delsimps [split_paired_All];
goal AutoChopper.thy 
"! st erk r p ys yss zs. \
\  acc xs st erk r p A = (ys#yss, zs) --> \
\  (if acc_prefix A st xs  \
\   then ? g.ys=r@g & (!as. as<=xs & g<=as & g~=as --> ~fin A (nexts A st as))\
\   else (erk~=[] & ys=erk) | (erk=[] & (ys#yss,zs)=p))";
by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (list.induct_tac "xs" 1);
 by (simp_tac (!simpset addcongs [conj_cong] setloop (split_tac [expand_if])) 1);
 by (Fast_tac 1);
by (asm_simp_tac (!simpset addcongs [conj_cong] setloop (split_tac [expand_if])) 1);
by (strip_tac 1);
by (case_tac "acc_prefix A (next A st a) list" 1);
 by (rtac conjI 1);
  by (strip_tac 1);
  by (res_inst_tac [("f","%k.a#k")] ex_special 1);
  by (res_inst_tac [("t","%k.ys=r@a#k"),("s","%k.ys=(r@[a])@k")] subst 1);
   by (Simp_tac 1);
  by (res_inst_tac [("P","%k.ys = (r@[a])@k & (!as. as<=list & k<=as & k ~= as --> ~ fin A (nexts A (next A st a) as))")] exE 1);
   by (asm_simp_tac HOL_ss 1);
  by (res_inst_tac [("x","x")] exI 1);
  by (Asm_simp_tac 1);
  by (rtac list_cases 1);
   by (Simp_tac 1);
  by (asm_simp_tac (!simpset addcongs[conj_cong]) 1);
 by (strip_tac 1);
 by (res_inst_tac [("f","%k.a#k")] ex_special 1);
 by (res_inst_tac [("t","%k.ys=r@a#k"),("s","%k.ys=(r@[a])@k")] subst 1);
  by (Simp_tac 1);
 by (res_inst_tac [("P","%k.ys=(r@[a])@k & (!as. as<=list & k<=as & k~=as --> ~ fin A (nexts A (next A st a) as))")] exE 1);
  by (asm_simp_tac HOL_ss 1);
 by (res_inst_tac [("x","x")] exI 1);
 by (Asm_simp_tac 1);
 by (rtac list_cases 1);
  by (Simp_tac 1);
 by (asm_simp_tac (!simpset addcongs[conj_cong]) 1);
by (Asm_simp_tac 1);
by (strip_tac 1);
by (res_inst_tac [("x","[a]")] exI 1);
by (rtac conjI 1);
 by (subgoal_tac "r @ [a] ~= []" 1);
  by (Fast_tac 1);
 by (Simp_tac 1);
by (rtac list_cases 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (!simpset addsimps [acc_prefix_def] addcongs[conj_cong]) 1);
by (etac thin_rl 1); (* speed up *)
by (Fast_tac 1);
val step2_e = (result() repeat_RS spec) RS mp;
Addsimps[split_paired_All];

goalw AutoChopper.thy [accepts_def, is_auto_chopper_def, auto_chopper_def,
                       Chopper.is_longest_prefix_chopper_def]
 "is_auto_chopper(auto_chopper)";
by (REPEAT(ares_tac [no_acc,allI,impI,conjI] 1));
 by (rtac mp 1);
  by (etac step2_b 2);
 by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (rtac conjI 1);
 by (rtac mp 1);
  by (etac step2_c 2);
 by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (rtac conjI 1);
 by (asm_simp_tac (!simpset addsimps [step2_a] setloop (split_tac [expand_if])) 1);
by (rtac conjI 1);
 by (rtac mp 1);
  by (etac step2_d 2);
 by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (rtac mp 1);
 by (etac step2_e 2);
 by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
qed"auto_chopper_is_auto_chopper";
