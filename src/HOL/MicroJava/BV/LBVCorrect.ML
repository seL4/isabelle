(*  Title:      HOL/MicroJava/BV/BVLcorrect.ML
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)


Goal "\\<exists> l. n < length l";
by (induct_tac "n" 1);
by Auto_tac;
by (res_inst_tac [("x","x#l")] exI 1);
by (Simp_tac 1);
qed "exists_list";


Goal "\\<forall> s0 pc. wtl_inst_list is G rT s0 s2 cert (pc+length is) pc \
\     \\<longrightarrow> (\\<exists> phi. pc + length is < length phi \\<and> fits_partial phi pc is G rT s0 s2 cert)";
by (induct_tac "is" 1);
 by (asm_full_simp_tac (simpset() addsimps [fits_partial_def, exists_list]) 1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (eres_inst_tac [("x","ab")] allE 1);
by (eres_inst_tac [("x","ba")] allE 1);
by (eres_inst_tac [("x","Suc pc")] allE 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (case_tac "cert ! pc" 1);
 by (res_inst_tac [("x","phi[pc:=(aa, b)]")] exI 1);
 by (asm_full_simp_tac (simpset() addsimps [fits_partial_def]) 1);
 by (Clarify_tac 1);
 by (case_tac "ac" 1);
  by (Asm_full_simp_tac 1);
 by (Asm_full_simp_tac 1);
 by (Clarify_tac 1);
 by (eres_inst_tac [("x","lista")] allE 1);
 by (eres_inst_tac [("x","bb")] allE 1);
 by (eres_inst_tac [("x","i")] allE 1);
 by (Asm_full_simp_tac 1);
 by (datac wtl_inst_option_unique 1 1);
 by (Asm_full_simp_tac 1);
 by (smp_tac 2 1);
 be impE 1;
  by (Force_tac 1);
 ba 1;
by (res_inst_tac [("x","phi[pc:=ac]")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [fits_partial_def]) 1);
by (Clarify_tac 1);
by (case_tac "ad" 1);
 by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (eres_inst_tac [("x","lista")] allE 1);
by (eres_inst_tac [("x","bc")] allE 1);
by (eres_inst_tac [("x","i")] allE 1);
by (Asm_full_simp_tac 1);
by (datac wtl_inst_option_unique 1 1);
by (Asm_full_simp_tac 1);
by (smp_tac 2 1);
be impE 1;
 by (Force_tac 1);
ba 1;
bind_thm ("exists_phi_partial", result() RS spec RS spec);


Goal "wtl_inst_list is G rT s0 s2 cert (length is) 0 \\<Longrightarrow> \\<exists> phi. fits phi is G rT s0 s2 cert \\<and> length is < length phi";
by (cut_inst_tac [("is","is"),("G","G"),("rT","rT"),("s2.0","s2"),("x","0"),("xa","s0"),("cert","cert")] exists_phi_partial 1);
by (asm_full_simp_tac (simpset() addsimps [fits_def]) 1);
by (Force_tac 1);
qed "exists_phi";


Goal "\\<lbrakk>wtl_inst_list is G rT s0 s3 cert (length is) 0; \
\      fits phi is G rT s0 s3 cert\\<rbrakk> \\<Longrightarrow> \ 
\     \\<forall> pc t. pc < length is \\<longrightarrow> (cert ! pc) = Some t \\<longrightarrow> (phi ! pc) = t";
by (Clarify_tac 1);
by (forward_tac [wtl_partial] 1);
ba 1;
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [fits_def, fits_partial_def ,neq_Nil_conv]) 1);
by (Clarify_tac 1);
by (eres_inst_tac [("x","aa")] allE 1);
by (eres_inst_tac [("x","ys")] allE 1);
by (eres_inst_tac [("x","y")] allE 1);
by (Asm_full_simp_tac 1);
qed "fits_lemma1";


Goal "\\<lbrakk>wtl_inst_list a G rT s0 s1 cert (length (a@i#b)) 0; \
\     wtl_inst_option i G rT s1 s2 cert (length (a@i#b)) (length a); \
\     wtl_inst_list b G rT s2 s3 cert (length (a@i#b)) (Suc (length a)); \
\     fits phi (a@i#b) G rT s0 s3 cert \\<rbrakk> \\<Longrightarrow> \
\ b \\<noteq> [] \\<longrightarrow> G \\<turnstile> s2 <=s (phi ! (Suc (length a)))";
by (forward_tac [wtl_append] 1);
  ba 1;
 ba 1;
by (case_tac "b=[]" 1);
 by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [neq_Nil_conv]) 1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (case_tac "cert!(Suc (length a))" 1);
 by (asm_full_simp_tac (simpset() addsimps [fits_def, fits_partial_def]) 1);
 by (eres_inst_tac [("x","a@[i]")] allE 1);
 by (eres_inst_tac [("x","ys")] allE 1);
 by (eres_inst_tac [("x","y")] allE 1);
 by (Asm_full_simp_tac 1);
 by (pair_tac "s2" 1);
 by (smp_tac 2 1);
 be impE 1;
  by (Force_tac 1);
 by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [fits_def, fits_partial_def]) 1);
by (eres_inst_tac [("x","a@[i]")] allE 1);
by (eres_inst_tac [("x","ys")] allE 1);
by (eres_inst_tac [("x","y")] allE 1);
by (Asm_full_simp_tac 1);
by (pair_tac "s2" 1);
by (smp_tac 2 1);
by (Clarify_tac 1);
be impE 1;
 by (Force_tac 1);
by (asm_full_simp_tac (simpset() addsimps [wtl_inst_option_def]) 1);
qed "wtl_suc_pc";


Goal "\\<lbrakk>wtl_inst_list a G rT s0 s1 cert (length (a@i#b)) 0; \
\      wtl_inst_option i G rT s1 s2 cert (length (a@i#b)) (length a); \
\      fits phi (a@i#b) G rT s0 s3 cert; cert!(length a) = None; \
\      wtl_inst_list b G rT s2 s3 cert (length (a@i#b)) (Suc (length a))\\<rbrakk> \
\    \\<Longrightarrow>  phi!(length a) = s1";
by (asm_full_simp_tac (simpset() addsimps [fits_def, fits_partial_def]) 1);
by (eres_inst_tac [("x","a")] allE 1);
by (eres_inst_tac [("x","b")] allE 1);
by (eres_inst_tac [("x","i")] allE 1);
by (Asm_full_simp_tac 1);
by (pair_tac "s1" 1);
by (eres_inst_tac [("x","x")] allE 1);
by (eres_inst_tac [("x","y")] allE 1);
by (Asm_full_simp_tac 1);
be impE 1;
 by (pair_tac "s2" 1);
 by (Force_tac 1);
ba 1;
qed "fits_lemma2";

fun ls g1 g2 = if g1 > g2 then ls g2 g1
               else if g1 = g2 then [g1]
               else g2::(ls g1 (g2-1))
fun GOALS t g1 g2 = EVERY (map t (ls g1 g2));

Goal "is=(i1@i#i2) \\<longrightarrow> wtl_inst_list (i1@i#i2) G rT s0 s3 cert (length is) 0 \\<longrightarrow> \
\     wtl_inst_list i1 G rT s0 s1 cert (length is) 0 \\<longrightarrow> \
\     wtl_inst_option i G rT s1 s2 cert (length is) (length i1) \\<longrightarrow> \
\     wtl_inst_list i2 G rT s2 s3 cert (length is) (Suc (length i1)) \\<longrightarrow> \
\     fits phi (i1@i#i2) G rT s0 s3 cert \\<longrightarrow> \
\       wt_instr i G rT phi (length is) (length i1)";
by (Clarify_tac 1);
by (forward_tac [wtl_suc_pc] 1);
by (TRYALL atac);
by (forward_tac [fits_lemma1] 1);
 ba 1;
by (case_tac "cert!(length i1)" 1);
 by (forward_tac [fits_lemma2] 1);
     by (TRYALL atac);
 by (case_tac "i" 1);
        by (case_tac "check_object" 4);
        by (case_tac "manipulate_object" 3);
         by (case_tac "create_object" 2);
         by (case_tac "load_and_store" 1);
            by (GOALS (force_tac (claset(), 
                simpset() addsimps [wt_instr_def,wtl_inst_option_def])) 1 8);
    by (case_tac "meth_inv" 1);
    by (thin_tac "\\<forall>pc t.\
\                 pc < length (i1 @ i # i2) \\<longrightarrow> \
\                 cert ! pc = Some t \\<longrightarrow> phi ! pc = t" 1);
    by (pair_tac "s1" 1);
    by (asm_full_simp_tac (simpset() addsimps [wt_instr_def,wtl_inst_option_def]) 1);    
    by (Force_tac 1);
   by (case_tac "meth_ret" 1);
   by (asm_full_simp_tac (simpset() addsimps [wt_instr_def,wtl_inst_option_def]) 1);
  by (case_tac "branch" 2);
   by (case_tac "op_stack" 1);
       by (GOALS (asm_full_simp_tac (simpset() addsimps [wt_instr_def,wtl_inst_option_def]) 
                  THEN_MAYBE' Force_tac) 1 7);
by (forw_inst_tac [("x","length i1")] spec 1);
by (eres_inst_tac [("x","a")] allE 1);
by (case_tac "i" 1);
       by (case_tac "check_object" 4);
       by (case_tac "manipulate_object" 3);
        by (case_tac "create_object" 2);
        by (case_tac "load_and_store" 1);
           by (GOALS (asm_full_simp_tac (simpset() addsimps [wt_instr_def,wtl_inst_option_def]) 
                      THEN' Force_tac) 1 8);
   by (case_tac "meth_inv" 1);
   by (thin_tac "\\<forall>pc t.\
\                pc < length (i1 @ i # i2) \\<longrightarrow> \
\                cert ! pc = Some t \\<longrightarrow> phi ! pc = t" 1);
   by (force_tac (claset(), simpset() addsimps [wt_instr_def,wtl_inst_option_def]) 1);
  by (case_tac "branch" 3);
   by (case_tac "op_stack" 2);
       by (case_tac "meth_ret" 1);
       by (GOALS (asm_full_simp_tac (simpset() addsimps [wt_instr_def,wtl_inst_option_def]) 
                  THEN_MAYBE' Force_tac) 1 8);
qed "wtl_lemma";

Goal "\\<lbrakk>wtl_inst_list is G rT s0 s2 cert (length is) 0; \
\     fits phi is G rT s0 s2 cert\\<rbrakk> \
\ \\<Longrightarrow> \\<forall>pc. pc < length is \\<longrightarrow> wt_instr (is ! pc) G rT phi (length is) pc";
by (Clarify_tac 1);
by (forward_tac [wtl_partial] 1);
ba 1;
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [neq_Nil_conv]) 1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (cut_inst_tac [("is","a@y#ys"),("i1.0","a"),("i2.0","ys"),("i","y"),("G","G"),("rT","rT"),("s0.0","s0"),("cert","cert"),("phi","phi"),("s1.0","(aa,ba)"),("s2.0","(ab,b)"),("s3.0","s2")] wtl_lemma 1);
by (asm_full_simp_tac (simpset() addsimps [nth_append]) 1);
qed "wtl_fits_wt";


Goal "wtl_inst_list is G rT s0 s2 cert (length is) 0 \\<Longrightarrow> \
\     \\<exists> phi. \\<forall>pc. pc < length is \\<longrightarrow> wt_instr (is ! pc) G rT phi (length is) pc";
by (forward_tac [exists_phi] 1);
by (Clarify_tac 1);
by (forward_tac [wtl_fits_wt] 1);
ba 1;
by (Force_tac 1);
qed "wtl_inst_list_correct";

Goal "\\<lbrakk>is \\<noteq> []; wtl_inst_list is G rT s0 s2 cert (length is) 0; \
\     fits phi is G rT s0 s2 cert\\<rbrakk> \\<Longrightarrow> G \\<turnstile> s0 <=s phi ! 0";
by (forw_inst_tac [("pc'","0")] wtl_partial 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [fits_def, fits_partial_def, neq_Nil_conv]) 1);
by (Clarsimp_tac 1);
by (eres_inst_tac [("x","[]")] allE 1);
by (eres_inst_tac [("x","ys")] allE 1);
by (eres_inst_tac [("x","y")] allE 1);
by (Asm_full_simp_tac 1);
be impE 1;
by (Force_tac 1);
by (case_tac "cert ! 0" 1);
by (auto_tac (claset(), simpset() addsimps [wtl_inst_option_def]));
qed "fits_first";


Goal "wtl_method G C pTs rT mxl ins cert \\<Longrightarrow> \\<exists> phi. wt_method G C pTs rT mxl ins phi";
by (asm_full_simp_tac (simpset() addsimps [wtl_method_def, wt_method_def, wt_start_def]) 1);
by (Clarify_tac 1);
by (forward_tac [exists_phi] 1);
by (Clarify_tac 1);
by (forward_tac [wtl_fits_wt] 1);
ba 1;
by (res_inst_tac [("x","phi")] exI 1);
by (auto_tac (claset(), simpset() addsimps [fits_first]));
qed "wtl_method_correct";

Goal "(a,b,c,d)\\<in>set l \\<longrightarrow> unique l \\<longrightarrow> (a',b',c',d') \\<in> set l \\<longrightarrow> a = a' \\<longrightarrow> b=b' \\<and> c=c' \\<and> d=d'";
by (induct_tac "l" 1);
by Auto_tac;
qed_spec_mp "unique_set";

Goal "(a,b,c,d)\\<in>set l \\<longrightarrow> unique l \\<longrightarrow> (\\<epsilon> (a',b',c',d'). (a',b',c',d') \\<in> set l \\<and> a'=a) = (a,b,c,d)";
by (auto_tac (claset(), simpset() addsimps [unique_set]));
qed_spec_mp "unique_epsilon";

Goalw[wtl_jvm_prog_def,wt_jvm_prog_def] "wtl_jvm_prog G cert ==> \\<exists> Phi. wt_jvm_prog G Phi";
by (asm_full_simp_tac (simpset() addsimps [wf_prog_def, wf_cdecl_def, wf_mdecl_def]) 1);
by (res_inst_tac [("x",
  "\\<lambda> C sig.\
\    let (C,x,y,mdecls) = \\<epsilon> (Cl,x,y,mdecls). (Cl,x,y,mdecls) \\<in> set G \\<and> Cl = C in\
\      let (sig,rT,maxl,b) = \\<epsilon> (sg,rT,maxl,b). (sg,rT,maxl,b) \\<in> set mdecls \\<and> sg = sig in\
\        \\<epsilon> phi. wt_method G C (snd sig) rT maxl b phi")] exI 1);
by Safe_tac;
by (GOALS Force_tac 1 3);
by (GOALS Force_tac 2 3);
by (eres_inst_tac [("x","(a, aa, ab, b)")] BallE 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (eres_inst_tac [("x","((ac, ba), ad, ae, bb)")] BallE 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
bd wtl_method_correct 1;
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [unique_epsilon]) 1);
br selectI 1;
ba 1;
qed "wtl_correct";

