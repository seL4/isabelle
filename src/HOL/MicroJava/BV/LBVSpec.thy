(*  Title:      HOL/MicroJava/BV/LBVSpec.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* The Lightweight Bytecode Verifier *}


theory LBVSpec = Step :

types
  certificate       = "state_type option list" 
  class_certificate = "sig \<Rightarrow> certificate"
  prog_certificate  = "cname \<Rightarrow> class_certificate"


constdefs
  check_cert :: "[instr, jvm_prog, state_type option, certificate, p_count, p_count]
                 \<Rightarrow> bool"
  "check_cert i G s cert pc max_pc \<equiv> \<forall>pc' \<in> set (succs i pc). pc' < max_pc \<and>  
                                     (pc' \<noteq> pc+1 \<longrightarrow> G \<turnstile> step i G s <=' cert!pc')"

  wtl_inst :: "[instr,jvm_prog,ty,state_type option,certificate,p_count,p_count] 
               \<Rightarrow> state_type option err" 
  "wtl_inst i G rT s cert max_pc pc \<equiv> 
     if app i G rT s \<and> check_cert i G s cert pc max_pc then 
       if pc+1 mem (succs i pc) then Ok (step i G s) else Ok (cert!(pc+1))
     else Err";

lemma wtl_inst_Ok:
"(wtl_inst i G rT s cert max_pc pc = Ok s') =
 (app i G rT s \<and> (\<forall>pc' \<in> set (succs i pc). 
                   pc' < max_pc \<and> (pc' \<noteq> pc+1 \<longrightarrow> G \<turnstile> step i G s <=' cert!pc')) \<and> 
 (if pc+1 \<in> set (succs i pc) then s' = step i G s else s' = cert!(pc+1)))"
  by (auto simp add: wtl_inst_def check_cert_def set_mem_eq);


constdefs
  wtl_cert :: "[instr,jvm_prog,ty,state_type option,certificate,p_count,p_count] 
               \<Rightarrow> state_type option err"  
  "wtl_cert i G rT s cert max_pc pc \<equiv>
     case cert!pc of
        None    \<Rightarrow> wtl_inst i G rT s cert max_pc pc
      | Some s' \<Rightarrow> if G \<turnstile> s <=' (Some s') then 
                    wtl_inst i G rT (Some s') cert max_pc pc 
                  else Err"

consts 
  wtl_inst_list :: "[instr list,jvm_prog,ty,certificate,p_count,p_count, 
                     state_type option] \<Rightarrow> state_type option err"
primrec
  "wtl_inst_list []     G rT cert max_pc pc s = Ok s"
  "wtl_inst_list (i#is) G rT cert max_pc pc s = 
    (let s' = wtl_cert i G rT s cert max_pc pc in
     strict (wtl_inst_list is G rT cert max_pc (pc+1)) s')";
              

constdefs
 wtl_method :: "[jvm_prog,cname,ty list,ty,nat,instr list,certificate] \<Rightarrow> bool"  
 "wtl_method G C pTs rT mxl ins cert \<equiv>  
	let max_pc = length ins  
  in 
  0 < max_pc \<and>   
  wtl_inst_list ins G rT cert max_pc 0 
                (Some ([],(Ok (Class C))#((map Ok pTs))@(replicate mxl Err))) \<noteq> Err"

 wtl_jvm_prog :: "[jvm_prog,prog_certificate] \<Rightarrow> bool" 
 "wtl_jvm_prog G cert \<equiv>  
  wf_prog (\<lambda>G C (sig,rT,maxl,b). wtl_method G C (snd sig) rT maxl b (cert C sig)) G"

text {* \medskip *} 

lemma strict_Some [simp]: 
"(strict f x = Ok y) = (\<exists> z. x = Ok z \<and> f z = Ok y)"
  by (cases x, auto)

lemma wtl_Cons:
  "wtl_inst_list (i#is) G rT cert max_pc pc s \<noteq> Err = 
  (\<exists>s'. wtl_cert i G rT s cert max_pc pc = Ok s' \<and> 
        wtl_inst_list is G rT cert max_pc (pc+1) s' \<noteq> Err)"
by (auto simp del: split_paired_Ex)

lemma wtl_append:
"\<forall> s pc. (wtl_inst_list (a@b) G rT cert mpc pc s = Ok s') =
   (\<exists>s''. wtl_inst_list a G rT cert mpc pc s = Ok s'' \<and> 
          wtl_inst_list b G rT cert mpc (pc+length a) s'' = Ok s')" 
  (is "\<forall> s pc. ?C s pc a" is "?P a")
proof (induct ?P a)

  show "?P []" by simp
  
  fix x xs
  assume IH: "?P xs"

  show "?P (x#xs)"
  proof (intro allI)
    fix s pc 

    show "?C s pc (x#xs)"
    proof (cases "wtl_cert x G rT s cert mpc pc")
      case Err thus ?thesis by simp
    next
      fix s0
      assume Ok: "wtl_cert x G rT s cert mpc pc = Ok s0"

      with IH
      have "?C s0 (Suc pc) xs" by blast
      
      with Ok
      show ?thesis by simp
    qed
  qed
qed

lemma wtl_take:
  "wtl_inst_list is G rT cert mpc pc s = Ok s'' ==>
   \<exists>s'. wtl_inst_list (take pc' is) G rT cert mpc pc s = Ok s'"
proof -
  assume "wtl_inst_list is G rT cert mpc pc s = Ok s''"

  hence "wtl_inst_list (take pc' is @ drop pc' is) G rT cert mpc pc s = Ok s''"
    by simp

  thus ?thesis 
    by (auto simp add: wtl_append simp del: append_take_drop_id)
qed

lemma take_Suc:
  "\<forall>n. n < length l \<longrightarrow> take (Suc n) l = (take n l)@[l!n]" (is "?P l")
proof (induct l)
  show "?P []" by simp

  fix x xs
  assume IH: "?P xs"
  
  show "?P (x#xs)"
  proof (intro strip)
    fix n
    assume "n < length (x#xs)"
    with IH
    show "take (Suc n) (x # xs) = take n (x # xs) @ [(x # xs) ! n]"
      by - (cases n, auto)
  qed
qed

lemma wtl_Suc:
 "[| wtl_inst_list (take pc is) G rT cert (length is) 0 s = Ok s'; 
     wtl_cert (is!pc) G rT s' cert (length is) pc = Ok s'';
     Suc pc < length is |] ==>
  wtl_inst_list (take (Suc pc) is)  G rT cert (length is) 0 s = Ok s''" 
proof -
  assume wtt: "wtl_inst_list (take pc is) G rT cert (length is) 0 s = Ok s'"
  assume wtc: "wtl_cert (is!pc) G rT s' cert (length is) pc = Ok s''"
  assume pc: "Suc pc < length is"

  hence "take (Suc pc) is = (take pc is)@[is!pc]" 
    by (simp add: take_Suc)

  with wtt wtc pc
  show ?thesis
    by (simp add: wtl_append min_def)
qed

lemma wtl_all:
  "[| wtl_inst_list is G rT cert (length is) 0 s \<noteq> Err;
      pc < length is |] ==> 
   \<exists>s' s''. wtl_inst_list (take pc is) G rT cert (length is) 0 s = Ok s' \<and> 
            wtl_cert (is!pc) G rT s' cert (length is) pc = Ok s''"
proof -
  assume all: "wtl_inst_list is G rT cert (length is) 0 s \<noteq> Err"

  assume pc: "pc < length is"
  hence  "0 < length (drop pc is)" by simp
  then 
  obtain i r where 
    Cons: "drop pc is = i#r" 
    by (auto simp add: neq_Nil_conv simp del: length_drop)
  hence "i#r = drop pc is" ..
  with all
  have take: "wtl_inst_list (take pc is@i#r) G rT cert (length is) 0 s \<noteq> Err"
    by simp
 
  from pc
  have "is!pc = drop pc is ! 0" by simp
  with Cons
  have "is!pc = i" by simp

  with take pc
  show ?thesis
    by (auto simp add: wtl_append min_def)
qed

end
