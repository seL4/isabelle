(*  Title:      HOL/IOA/NTP/Multiset.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Axiomatic multisets.
Should be done as a subtype and moved to a global place.
*)

Goalw [Multiset.count_def, Multiset.countm_empty_def]
   "count {|} x = 0";
 by (rtac refl 1);
qed "count_empty";

Goal 
     "count (addm M x) y = (if y=x then Suc(count M y) else count M y)";
  by (asm_simp_tac (simpset() addsimps 
                    [Multiset.count_def,Multiset.countm_nonempty_def]) 1);
qed "count_addm_simp";

Goal "count M y <= count (addm M x) y";
  by (simp_tac (simpset() addsimps [count_addm_simp]) 1);
qed "count_leq_addm";

Goalw [Multiset.count_def] 
     "count (delm M x) y = (if y=x then count M y - 1 else count M y)";
by (res_inst_tac [("M","M")] Multiset.induction 1);
by (asm_simp_tac (simpset() 
             addsimps [Multiset.delm_empty_def,Multiset.countm_empty_def]) 1);
by (asm_full_simp_tac (simpset() 
                         addsimps [Multiset.delm_nonempty_def,
                                   Multiset.countm_nonempty_def]) 1);
by Safe_tac;
by (Asm_full_simp_tac 1);
qed "count_delm_simp";

Goal "!!M. (!x. P(x) --> Q(x)) ==> (countm M P <= countm M Q)";
by (res_inst_tac [("M","M")] Multiset.induction 1);
 by (simp_tac (simpset() addsimps [Multiset.countm_empty_def]) 1);
by (simp_tac (simpset() addsimps[Multiset.countm_nonempty_def]) 1);
by Auto_tac;
qed "countm_props";

Goal "!!P. ~P(obj) ==> countm M P = countm (delm M obj) P";
  by (res_inst_tac [("M","M")] Multiset.induction 1);
  by (simp_tac (simpset() addsimps [Multiset.delm_empty_def,
                                   Multiset.countm_empty_def]) 1);
  by (asm_simp_tac (simpset() addsimps[Multiset.countm_nonempty_def,
                                      Multiset.delm_nonempty_def]) 1);
qed "countm_spurious_delm";


Goal "!!P. P(x) ==> 0<count M x --> 0<countm M P";
  by (res_inst_tac [("M","M")] Multiset.induction 1);
  by (simp_tac (simpset() addsimps 
                          [Multiset.delm_empty_def,Multiset.count_def,
                           Multiset.countm_empty_def]) 1);
  by (asm_simp_tac (simpset() addsimps 
                       [Multiset.count_def,Multiset.delm_nonempty_def,
                        Multiset.countm_nonempty_def]) 1);
qed_spec_mp "pos_count_imp_pos_countm";

Goal
   "!!P. P(x) ==> 0<count M x --> countm (delm M x) P = countm M P - 1";
  by (res_inst_tac [("M","M")] Multiset.induction 1);
  by (simp_tac (simpset() addsimps 
                          [Multiset.delm_empty_def,
                           Multiset.countm_empty_def]) 1);
  by (asm_simp_tac (simpset() addsimps 
                      [eq_sym_conv,count_addm_simp,Multiset.delm_nonempty_def,
                       Multiset.countm_nonempty_def,pos_count_imp_pos_countm]) 1);
qed "countm_done_delm";


Addsimps [count_addm_simp, count_delm_simp,
          Multiset.countm_empty_def, Multiset.delm_empty_def,
          count_empty];
