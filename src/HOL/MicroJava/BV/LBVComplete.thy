(*  Title:      HOL/MicroJava/BV/LBVComplete.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen

Proof of completeness for the lightweight bytecode verifier
*)

LBVComplete= LBVSpec +

constdefs
  is_approx :: "['a option list, 'a list] \\<Rightarrow> bool"
  "is_approx a b \\<equiv> length a = length b \\<and> (\\<forall> n. n < length a \\<longrightarrow>
                   (a!n = None \\<or> a!n = Some (b!n)))"
  
  fits :: "[instr list, certificate, method_type] \\<Rightarrow> bool"
  "fits ins cert phi \\<equiv> is_approx cert phi \\<and> length ins < length phi \\<and>
                            (\\<forall> pc. pc < length ins \\<longrightarrow>
                                   contains_dead ins cert phi pc \\<and> 
                                   contains_targets ins cert phi pc)"

  contains_dead :: "[instr list, certificate, method_type, p_count] \\<Rightarrow> bool"
  "contains_dead ins cert phi pc \\<equiv>
    (((\\<exists> branch. ins!pc = BR (Goto branch)) \\<or> ins!pc = MR Return) \\<or>
     (\\<exists>mi. ins!pc = MI mi)) \\<longrightarrow> Suc pc < length phi \\<longrightarrow>
      cert ! (Suc pc) = Some (phi ! Suc pc)"

  contains_targets :: "[instr list, certificate, method_type, p_count] \\<Rightarrow> bool"
  "contains_targets ins cert phi pc \\<equiv> 
    \\<forall> branch. (ins!pc = BR (Goto branch) \\<or> ins!pc = BR (Ifcmpeq branch)) \\<longrightarrow>
        (let pc' = nat (int pc+branch) in pc' < length phi \\<longrightarrow> cert!pc' = Some (phi!pc'))" 

  is_target :: "[instr list, p_count] \\<Rightarrow> bool" 
  "is_target ins pc \\<equiv> 
     \\<exists> pc' branch. pc' < length ins \\<and> 
                   (ins ! pc' = (BR (Ifcmpeq branch)) \\<or> ins ! pc' = (BR (Goto branch))) \\<and> 
                   pc = (nat(int pc'+branch))"
  
  maybe_dead :: "[instr list, p_count] \\<Rightarrow> bool"
  "maybe_dead ins pc \\<equiv>
     \\<exists> pc'. pc = pc'+1 \\<and> ((\\<exists> branch. ins!pc' = BR (Goto branch)) \\<or>
                          ins!pc' = MR Return \\<or>
                          (\\<exists>mi. ins!pc' = MI mi))"


  mdot :: "[instr list, p_count] \\<Rightarrow> bool"
  "mdot ins pc \\<equiv> maybe_dead ins pc \\<or> is_target ins pc"


consts
  option_filter_n :: "['a list, nat \\<Rightarrow> bool, nat] \\<Rightarrow> 'a option list" 
primrec 
  "option_filter_n []    P n = []"  
  "option_filter_n (h#t) P n = (if (P n) then Some h # option_filter_n t P (n+1) 
                                         else None   # option_filter_n t P (n+1))"  
  
constdefs 
  option_filter :: "['a list, nat \\<Rightarrow> bool] \\<Rightarrow> 'a option list" 
  "option_filter l P \\<equiv> option_filter_n l P 0" 
  
  make_cert :: "[instr list, method_type] \\<Rightarrow> certificate"
  "make_cert ins phi \\<equiv> option_filter phi (mdot ins)"
  
  make_Cert :: "[jvm_prog, prog_type] \\<Rightarrow> prog_certificate"
  "make_Cert G Phi \\<equiv>  \\<lambda> C sig.
    let (C,x,y,mdecls) = \\<epsilon> (Cl,x,y,mdecls). (Cl,x,y,mdecls) \\<in> set G \\<and> Cl = C in
      let (sig,rT,maxl,b) = \\<epsilon> (sg,rT,maxl,b). (sg,rT,maxl,b) \\<in> set mdecls \\<and> sg = sig in
        make_cert b (Phi C sig)"
  
constdefs
  wfprg :: "jvm_prog \\<Rightarrow> bool"
  "wfprg G \\<equiv> \\<exists>wf_mb. wf_prog wf_mb G"

end
