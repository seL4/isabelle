(*  Title:      HOL/MicroJava/BV/BVLightSpec.ML
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

Goal "\\<lbrakk>length a = n; length x = n; rev a @ b # c = rev x @ y # z\\<rbrakk> \\<Longrightarrow> a = x \\<and> b = y \\<and> c = z";
by Auto_tac;
qed "rev_eq";


Goal "\\<lbrakk>wtl_inst i G rT s0 s1 cert max_pc pc; \
\      wtl_inst i G rT s0 s1' cert max_pc pc\\<rbrakk> \\<Longrightarrow> s1 = s1'";
by (exhaust_tac "i" 1);
by (exhaust_tac "branch" 8);
by (exhaust_tac "op_stack" 7);
by (exhaust_tac "meth_ret" 6);
by (exhaust_tac "meth_inv" 5);
by (exhaust_tac "check_object" 4);
by (exhaust_tac "manipulate_object" 3);
by (exhaust_tac "create_object" 2);
by (exhaust_tac "load_and_store" 1);
by Auto_tac;
by (ALLGOALS (dtac rev_eq));
by (TRYALL atac);
by (ALLGOALS Asm_full_simp_tac);
qed "wtl_inst_unique";


Goal "\\<lbrakk>wtl_inst_option i G rT s0 s1 cert max_pc pc; \
\      wtl_inst_option i G rT s0 s1' cert max_pc pc\\<rbrakk> \\<Longrightarrow> s1 = s1'";
by (exhaust_tac "cert!pc" 1);
by (auto_tac (claset(), simpset() addsimps [wtl_inst_unique, wtl_inst_option_def]));
qed "wtl_inst_option_unique";

Goal "\\<forall> s0 pc. wtl_inst_list is G rT s0 s1 cert max_pc pc \\<longrightarrow> \
\              wtl_inst_list is G rT s0 s1' cert max_pc pc \\<longrightarrow> s1=s1'";
by (induct_tac "is" 1);
 by Auto_tac;
by (datac wtl_inst_option_unique 1 1);
by (Asm_full_simp_tac 1);
qed "wtl_inst_list_unique";

Goal "\\<forall> pc' pc s. \
\       wtl_inst_list is G rT s s' cert mpc pc \\<longrightarrow> \
\       pc' < length is \\<longrightarrow> \
\       (\\<exists> a b s1. a @ b = is \\<and> length a = pc' \\<and> \
\                  wtl_inst_list a G rT s  s1 cert mpc pc \\<and> \
\                  wtl_inst_list b G rT s1 s' cert mpc (pc+length a))";
by(induct_tac "is" 1);
 by Auto_tac;
by (exhaust_tac "pc'" 1);
 by (dres_inst_tac [("x","pc'")] spec 1);
 by (smp_tac 3 1);
 by (res_inst_tac [("x","[]")] exI 1);
 by (Asm_full_simp_tac 1);
 by (exhaust_tac "cert!pc" 1);
  by (Force_tac 1);
 by (force_tac (claset(), simpset() addsimps [wtl_inst_option_def]) 1);
by (dres_inst_tac [("x","nat")] spec 1);
by (smp_tac 3 1);
by Safe_tac;
 by (res_inst_tac [("x","a#list")] exI 1);
 by (Asm_full_simp_tac 1);
by (res_inst_tac [("x","a#ac")] exI 1);
by (Force_tac 1);
qed_spec_mp "wtl_partial";


Goal "\\<forall> s0 pc. wtl_inst_list a G rT s0 s1 cert (pc+length (a@i#b)) pc \\<longrightarrow> \
\       wtl_inst_option i G rT s1 s2 cert (pc+length (a@i#b)) (pc + length a) \\<longrightarrow> \
\       wtl_inst_list b G rT s2 s3 cert (pc+length (a@i#b)) (Suc (pc + length a)) \\<longrightarrow> \
\         wtl_inst_list (a@[i]) G rT s0 s2 cert (pc+length (a@i#b)) pc";
by (induct_tac "a" 1);
 by (Clarify_tac 1);
 by (Asm_full_simp_tac 1);
 by (pair_tac "s2" 1);
 by (Force_tac 1);
(* ---- 
 by (exhaust_tac "cert!Suc pc" 1);
  by (exhaust_tac "cert!pc" 1);
   by (Force_tac 1);
 by (res_inst_tac [("x","fst aa")] exI 1);
 by (res_inst_tac [("x","snd aa")] exI 1);
  by (force_tac (claset(), simpset() addsimps [wtl_inst_option_def]) 1);
 by (exhaust_tac "cert!pc" 1);
  by (force_tac (claset(), simpset() addsimps [wtl_inst_option_def]) 1);
 by (Asm_full_simp_tac 1);
  by (force_tac (claset(), simpset() addsimps [wtl_inst_option_def]) 1);
 

  by (exhaust_tac "cert!pc" 1);
   by (force_tac (claset(), simpset() addsimps [wtl_inst_option_def]) 1);
   by (force_tac (claset(), simpset() addsimps [wtl_inst_option_def]) 1);
   by (force_tac (claset(), simpset() addsimps [wtl_inst_option_def]) 1);


 by (res_inst_tac [("x","x")] exI 1);
 by (res_inst_tac [("x","y")] exI 1);
 by (exhaust_tac "cert!pc" 1);
  by (exhaust_tac "cert!Suc pc" 1);
   by (Force_tac 1);
  by (force_tac (claset(), simpset() addsimps [wtl_inst_option_def]) 1);
 ------- *)
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (eres_inst_tac [("x","ab")] allE 1);
by (eres_inst_tac [("x","baa")] allE 1);
by (eres_inst_tac [("x","Suc pc")] allE 1);
by (Force_tac 1);
bind_thm ("wtl_append_lemma", result() RS spec RS spec);

Goal "\\<lbrakk>wtl_inst_list a G rT s0 s1 cert (length (a@i#b)) 0;  \
\      wtl_inst_option i G rT s1 s2 cert (length (a@i#b)) (length a); \
\      wtl_inst_list b G rT s2 s3 cert (length (a@i#b)) (Suc (length a))\\<rbrakk> \\<Longrightarrow> \
\      wtl_inst_list (a@[i]) G rT s0 s2 cert (length (a@i#b)) 0";
by (cut_inst_tac [("a","a"),("G","G"),("rT","rT"),("xa","s0"),("s1.0","s1"),("cert","cert"),("x","0"),("i","i"),("b","b"),("s2.0","s2"),("s3.0","s3")] wtl_append_lemma 1);
by (Asm_full_simp_tac 1);
qed "wtl_append";


