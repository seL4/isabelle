(*  Title:      HOL/MicroJava/JVM/JVMExceptions.thy
    ID:         $Id$
    Author:     Gerwin Klein, Martin Strecker
    Copyright   2001 Technische Universitaet Muenchen
*)

header {* \isaheader{Exception handling in the JVM} *}

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
  ex_table_of :: "jvm_method \<Rightarrow> exception_table"
translations
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


text {*
  System exceptions are allocated in all heaps:
*}


text {*
  Only program counters that are mentioned in the exception table
  can be returned by @{term match_exception_table}:
*}
lemma match_exception_table_in_et:
  "match_exception_table G C pc et = Some pc' \<Longrightarrow> \<exists>e \<in> set et. pc' = fst (snd (snd e))"
  by (induct et) (auto split: split_if_asm)


end
