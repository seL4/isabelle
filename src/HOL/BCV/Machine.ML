(*  Title:      HOL/BCV/Machine.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM
*)

Addsimps [Let_def];

Addsimps [stype_def];


(*** Machine specific ***)

Goal "!p. p<size(bs) --> maxreg(bs!p) < maxregs(bs)";
by (induct_tac "bs" 1);
by (auto_tac (claset(), simpset() addsimps [nth_Cons,less_max_iff_disj]
                                 addsplits [nat.split]));
qed_spec_mp "maxreg_less_maxregs";

Goalw [le_typ] "(t <= Ctyp) = (t = Ctyp)";
by (Simp_tac 1);
qed "le_Ctyp_conv";

Goalw [le_typ] "(t ~= Top) = (t = Atyp | t = Btyp | t = Ctyp)";
by (induct_tac "t" 1);
by (ALLGOALS Simp_tac);
qed "le_Top_conv";

Goalw [step_pres_type_def,listsn_def,exec_def,stype_def]
 "step_pres_type (%p. exec (bs!p)) (length bs) (stype bs)";
by (force_tac (claset(), simpset() addsplits [instr.split_asm,split_if_asm]) 1);
qed "exec_pres_type";

Goalw [wti_is_fix_step_def,stable_def,wt_instr_def,exec_def,succs_def]
 "wti_is_fix_step (%p. exec (bs!p)) (%u. wt_instr (bs ! u) u) \
\     (%p. succs (bs ! p) p) (length bs) (stype bs)";
by (force_tac (claset() addDs [maxreg_less_maxregs,
                              le_Top_conv RS iffD1,le_Ctyp_conv RS iffD1],
              simpset() addsplits [option.split,instr.split]) 1);
qed "wt_instr_is_fix_exec";


Goalw [step_mono_None_def,exec_def,succs_def,le_list]
 "step_mono_None (%p. exec (bs!p)) (length bs) (stype bs)";
by (Clarify_tac 1);
by (ftac maxreg_less_maxregs 1);
by (split_asm_tac [instr.split_asm] 1);

by (ALLGOALS (asm_full_simp_tac (simpset() addsplits [split_if_asm])));

by (rotate_tac 1 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addIs [order_trans]) 1);

by (rotate_tac 1 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addIs [order_trans]) 1);

by (rotate_tac 1 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addIs [order_trans]) 1);

by (rotate_tac 1 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "s!nat1 <= t!nat1" 1);
by (Blast_tac 2);
by (subgoal_tac "s!nat2 <= t!nat2" 1);
by (Blast_tac 2);
by (etac thin_rl 1);
by (asm_full_simp_tac (simpset() addsimps [le_typ])1);
by (exhaust_tac "t!nat1" 1);
by (ALLGOALS Asm_full_simp_tac);
by (exhaust_tac "t!nat2" 1);
by (ALLGOALS Asm_full_simp_tac);
by (exhaust_tac "t!nat2" 1);
by (ALLGOALS Asm_full_simp_tac);
by (exhaust_tac "s!nat1" 1);
by (ALLGOALS Asm_full_simp_tac);
by (exhaust_tac "t!nat2" 1);
by (ALLGOALS Asm_full_simp_tac);

qed "exec_mono_None";

Goalw [step_mono_def,exec_def,succs_def]
 "step_mono (%p. exec (bs!p)) (length bs) (stype bs)";
by (Clarify_tac 1);
by (ftac maxreg_less_maxregs 1);
by (split_asm_tac [instr.split_asm] 1);
by (ALLGOALS
   (fast_tac (claset() addIs [list_update_le_cong,le_listD]
               addss (simpset() addsplits [split_if_asm]))));

qed_spec_mp "exec_mono_Some";

Goalw [stype_def] "semilat(stype bs)";
by (Blast_tac 1);
qed "lat_stype";

Goalw [stype_def] "acc(stype bs)";
by (Simp_tac 1);
qed "acc_stype";

Delsimps [stype_def];

Goal
 "[| is_next next; \
\    succs_bounded (%p. succs (bs!p) p) (size bs); \
\    sos : listsn (size bs) (option(stype bs)) |] ==> \
\ fix(next (%p. exec (bs!p)) (%p. succs (bs!p) p), sos) = \
\ (? tos : listsn (size bs) (option(stype bs)). \
\      sos <= tos & welltyping (%p. wt_instr (bs!p) p) tos)";
by (simp_tac (simpset() delsimps [not_None_eq]) 1);
by (REPEAT(ares_tac [fix_next_iff_welltyping,exec_pres_type,
                    exec_mono_None,exec_mono_Some,
                    wt_instr_is_fix_exec,lat_stype,acc_stype] 1));

qed "fix_iff_welltyped";
