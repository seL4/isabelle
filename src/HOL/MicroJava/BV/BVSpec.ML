(*  Title:      HOL/MicroJava/BV/BVSpec.ML
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen
*)

Goalw [wt_jvm_prog_def] "wt_jvm_prog G phi \\<Longrightarrow> (\\<exists>wt. wf_prog wt G)";
by(Blast_tac 1);
qed "wt_jvm_progD";


Goalw [wt_jvm_prog_def]
"\\<lbrakk> wt_jvm_prog G phi; \
\   cmethd (G,C) sig = Some (C,rT,maxl,ins); \
\   pc < length ins \\<rbrakk> \
\\\<Longrightarrow> wt_instr (ins!pc) G rT (phi C sig) (length ins) pc";
by(forward_tac [rotate_prems 2 cmethd_wf_mdecl] 1);
 by (Asm_full_simp_tac 1);
by(asm_full_simp_tac (simpset() addsimps [wf_mdecl_def,wt_method_def]) 1);
qed "wt_jvm_prog_impl_wt_instr";

Goalw [wt_jvm_prog_def]
"\\<lbrakk> wt_jvm_prog G phi; \
\   cmethd (G,C) sig = Some (C,rT,maxl,ins) \\<rbrakk> \\<Longrightarrow> \
\ 0 < (length ins) \\<and> wt_start G C (snd sig) maxl (phi C sig)";
by(forward_tac [rotate_prems 2 cmethd_wf_mdecl] 1);
 by (Asm_full_simp_tac 1);
by(asm_full_simp_tac (simpset() addsimps [wf_mdecl_def,wt_method_def]) 1);
qed "wt_jvm_prog_impl_wt_start";
