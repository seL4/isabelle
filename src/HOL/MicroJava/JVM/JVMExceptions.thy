(*  Title:      HOL/MicroJava/JVM/JVMExceptions.thy
    ID:         $Id$
    Author:     Gerwin Klein, Martin Strecker
    Copyright   2001 Technische Universitaet Muenchen
*)

header {* Exception handling in the JVM *}

theory JVMExceptions = JVMInstructions:

constdefs
  match_exception_entry :: "jvm_prog \<Rightarrow> cname \<Rightarrow> p_count \<Rightarrow> exception_entry \<Rightarrow> bool"
  "match_exception_entry G cn pc ee == 
                 let (start_pc, end_pc, handler_pc, catch_type) = ee in
                 start_pc <= pc \<and> pc < end_pc \<and> G\<turnstile> cn \<preceq>C catch_type"


consts
  match_exception_table :: "jvm_prog \<Rightarrow> cname \<Rightarrow> p_count \<Rightarrow> exception_table
                          \<Rightarrow> p_count option"
primrec
  "match_exception_table G cn pc []     = None"
  "match_exception_table G cn pc (e#es) = (if match_exception_entry G cn pc e
                                           then Some (fst (snd (snd e))) 
                                           else match_exception_table G cn pc es)"


consts
  cname_of :: "aheap \<Rightarrow> val \<Rightarrow> cname"
  ex_table_of :: "jvm_method \<Rightarrow> exception_table"

translations
  "cname_of hp v" == "fst (the (hp (the_Addr v)))"
  "ex_table_of m" == "snd (snd (snd m))"


consts
  find_handler :: "jvm_prog \<Rightarrow> val option \<Rightarrow> aheap \<Rightarrow> frame list \<Rightarrow> jvm_state"
primrec
  "find_handler G xcpt hp [] = (xcpt, hp, [])"
  "find_handler G xcpt hp (fr#frs) = 
      (case xcpt of
         None \<Rightarrow> (None, hp, fr#frs)
       | Some xc \<Rightarrow> 
       let (stk,loc,C,sig,pc) = fr in
       (case match_exception_table G (cname_of hp xc) pc 
              (ex_table_of (snd(snd(the(method (G,C) sig))))) of
          None \<Rightarrow> find_handler G (Some xc) hp frs
        | Some handler_pc \<Rightarrow> (None, hp, ([xc], loc, C, sig, handler_pc)#frs)))"



lemma cname_of_xcp:
  "raise_system_xcpt b x = Some xcp \<Longrightarrow> cname_of (hp::aheap) xcp = Xcpt x"
proof -
  assume "raise_system_xcpt b x = Some xcp"
  hence "xcp = Addr (XcptRef x)"
    by (simp add: raise_system_xcpt_def split: split_if_asm)
  moreover
  have "hp (XcptRef x) = Some (Xcpt x, empty)"
    by (rule system_xcpt_allocated)
  ultimately
  show ?thesis by simp
qed

end
