(*  Title:      HOL/IOA/NTP/Multiset.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

Axiomatic multisets.
Should be done as a subtype and moved to a global place.
*)

goalw Multiset.thy [Multiset.count_def, Multiset.countm_empty_def]
   "count {|} x = 0";
 by (rtac refl 1);
qed "count_empty";

goal Multiset.thy 
     "count (addm M x) y = (if y=x then Suc(count M y) else count M y)";
  by (asm_simp_tac (simpset() addsimps 
                    [Multiset.count_def,Multiset.countm_nonempty_def]
                    setloop (split_tac [expand_if])) 1);
qed "count_addm_simp";

goal Multiset.thy "count M y <= count (addm M x) y";
  by (simp_tac (simpset() addsimps [count_addm_simp]
                         setloop (split_tac [expand_if])) 1);
qed "count_leq_addm";

goalw Multiset.thy [Multiset.count_def] 
     "count (delm M x) y = (if y=x then pred(count M y) else count M y)";
  by (res_inst_tac [("M","M")] Multiset.induction 1);
  by (asm_simp_tac (simpset() 
                   addsimps [Multiset.delm_empty_def,Multiset.countm_empty_def]
                   setloop (split_tac [expand_if])) 1);
  by (asm_full_simp_tac (simpset() 
                         addsimps [Multiset.delm_nonempty_def,
                                   Multiset.countm_nonempty_def]
                         setloop (split_tac [expand_if])) 1);
  by (safe_tac (claset()));
  by (Asm_full_simp_tac 1);
qed "count_delm_simp";

goal Multiset.thy "!!M. (!x. P(x) --> Q(x)) ==> (countm M P <= countm M Q)";
  by (res_inst_tac [("M","M")] Multiset.induction 1);
  by (simp_tac (simpset() addsimps [Multiset.countm_empty_def]) 1);
  by (simp_tac (simpset() addsimps[Multiset.countm_nonempty_def]) 1);
  by (etac (less_eq_add_cong RS mp RS mp) 1);
  by (asm_full_simp_tac (simpset() addsimps [le_eq_less_or_eq]
                                  setloop (split_tac [expand_if])) 1);
qed "countm_props";

goal Multiset.thy "!!P. ~P(obj) ==> countm M P = countm (delm M obj) P";
  by (res_inst_tac [("M","M")] Multiset.induction 1);
  by (simp_tac (simpset() addsimps [Multiset.delm_empty_def,
                                   Multiset.countm_empty_def]) 1);
  by (asm_simp_tac (simpset() addsimps[Multiset.countm_nonempty_def,
                                      Multiset.delm_nonempty_def]
                             setloop (split_tac [expand_if])) 1);
qed "countm_spurious_delm";


goal Multiset.thy "!!P. P(x) ==> 0<count M x --> 0<countm M P";
  by (res_inst_tac [("M","M")] Multiset.induction 1);
  by (simp_tac (simpset() addsimps 
                          [Multiset.delm_empty_def,Multiset.count_def,
                           Multiset.countm_empty_def]) 1);
  by (asm_simp_tac (simpset() addsimps 
                       [Multiset.count_def,Multiset.delm_nonempty_def,
                        Multiset.countm_nonempty_def]
                    setloop (split_tac [expand_if])) 1);
val pos_count_imp_pos_countm = store_thm("pos_count_imp_pos_countm", standard(result() RS mp));

goal Multiset.thy
   "!!P. P(x) ==> 0<count M x --> countm (delm M x) P = pred (countm M P)";
  by (res_inst_tac [("M","M")] Multiset.induction 1);
  by (simp_tac (simpset() addsimps 
                          [Multiset.delm_empty_def,
                           Multiset.countm_empty_def]) 1);
  by (asm_simp_tac (simpset() addsimps 
                      [eq_sym_conv,count_addm_simp,Multiset.delm_nonempty_def,
                       Multiset.countm_nonempty_def,pos_count_imp_pos_countm,
                       suc_pred_id]
                    setloop (split_tac [expand_if])) 1);
qed "countm_done_delm";


Addsimps [count_addm_simp, count_delm_simp,
          Multiset.countm_empty_def, Multiset.delm_empty_def,
          count_empty];
