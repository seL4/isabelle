(*  Title:      HOL/MicroJava/BV/LBVSpec.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{The Lightweight Bytecode Verifier} *}

theory LBVSpec = Effect + Kildall:

text {* 
  The Lightweight Bytecode Verifier with exceptions has not 
  made it completely into the Isabelle 2001 release. Currently 
  there is only the specification itself available. The proofs of
  soundness and completeness are broken (they still need to be
  ported to the exception version). Both theories are included
  for documentation (but they don't work for this specification), 
  please see the Isabelle 99-2 release for a working copy, or
  \url{http://isabelle.in.tum.de/verificard} for the most recent
  development of \mJava.
*}

types
  certificate       = "state_type option list" 
  class_certificate = "sig \<Rightarrow> certificate"
  prog_certificate  = "cname \<Rightarrow> class_certificate"

consts
  merge :: "[jvm_prog, p_count, nat, nat, p_count, certificate, (nat \<times> (state_type option)) list, state] \<Rightarrow> state"
primrec
  "merge G pc mxs mxr max_pc cert []     x = x"
  "merge G pc mxs mxr max_pc cert (s#ss) x = (let (pc',s') = s in 
                                       if pc' < max_pc \<and> pc' = pc+1 then 
                                         merge G pc mxs mxr max_pc cert ss (OK s' +_(sup G mxs mxr) x) 
                                       else if pc' < max_pc \<and> G \<turnstile> s' <=' cert!pc' then 
                                         merge G pc mxs mxr max_pc cert ss x
                                       else Err)"

constdefs 
  wtl_inst :: "[instr,jvm_prog,ty,state_type option,certificate,nat,nat,p_count,exception_table,p_count] 
               \<Rightarrow> state_type option err" 
  "wtl_inst i G rT s cert maxs maxr max_pc et pc == 
     if app i G maxs rT pc et s then 
       merge G pc maxs maxr max_pc cert (eff i G pc et s) (OK (cert!(pc+1)))
     else Err"

  wtl_cert :: "[instr,jvm_prog,ty,state_type option,certificate,nat,nat,p_count,exception_table,p_count] 
               \<Rightarrow> state_type option err"  
  "wtl_cert i G rT s cert maxs maxr max_pc et pc ==
     case cert!pc of
        None    \<Rightarrow> wtl_inst i G rT s cert maxs maxr max_pc et pc
      | Some s' \<Rightarrow> if G \<turnstile> s <=' (Some s') then 
                    wtl_inst i G rT (Some s') cert maxs maxr max_pc et pc 
                  else Err"

consts 
  wtl_inst_list :: "[instr list,jvm_prog,ty,certificate,nat,nat,p_count,exception_table,p_count,
                     state_type option] \<Rightarrow> state_type option err"
primrec
  "wtl_inst_list []     G rT cert maxs maxr max_pc et pc s = OK s"
  "wtl_inst_list (i#is) G rT cert maxs maxr max_pc et pc s = 
    (let s' = wtl_cert i G rT s cert maxs maxr max_pc et pc in
     strict (wtl_inst_list is G rT cert maxs maxr max_pc et (pc+1)) s')"
              

constdefs
 wtl_method :: "[jvm_prog,cname,ty list,ty,nat,nat,exception_table,instr list,certificate] \<Rightarrow> bool"  
 "wtl_method G C pTs rT mxs mxl et ins cert ==  
	let max_pc = length ins  
  in 
  0 < max_pc \<and>   
  wtl_inst_list ins G rT cert mxs mxl max_pc et 0 
                (Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err))) \<noteq> Err"

 wtl_jvm_prog :: "[jvm_prog,prog_certificate] \<Rightarrow> bool" 
 "wtl_jvm_prog G cert ==  
  wf_prog (\<lambda>G C (sig,rT,maxs,maxl,b,et). wtl_method G C (snd sig) rT maxs maxl et b (cert C sig)) G"


lemmas [iff] = not_Err_eq

lemma if_eq_cases:
  "(P \<Longrightarrow> x = z) \<Longrightarrow> (\<not>P \<Longrightarrow> y = z) \<Longrightarrow> (if P then x else y) = z"
  by simp

lemma merge_def:
  "\<And>x. merge G pc mxs mxr max_pc cert ss x = 
  (if \<forall>(pc',s') \<in> set ss. pc' < max_pc \<and> (pc' \<noteq> pc+1 \<longrightarrow> G \<turnstile> s' <=' cert!pc') then
    map (OK \<circ> snd) [(p',t') \<in> ss. p'=pc+1] ++_(sup G mxs mxr) x
  else Err)" (is "\<And>x. ?merge ss x = ?if ss x" is "\<And>x. ?P ss x")
proof (induct ss)
  show "\<And>x. ?P [] x" by simp
next
  have OK_snd: "(\<lambda>u. OK (snd u)) = OK \<circ> snd" by (rule ext) auto
  fix x ss and s::"nat \<times> (state_type option)"
  assume IH: "\<And>x. ?P ss x"
  obtain pc' s' where s: "s = (pc',s')" by (cases s)  
  hence "?merge (s#ss) x = ?merge ((pc',s')#ss) x" by hypsubst (rule refl)
  also
  have "\<dots> = (if pc' < max_pc \<and> pc' = pc+1 then 
               ?merge ss (OK s' +_(sup G mxs mxr) x)
             else if pc' < max_pc \<and> G \<turnstile> s' <=' cert!pc' then 
               ?merge ss x
             else Err)" 
    (is "_ = (if ?pc' then ?merge ss (_ +_?f _) else if ?G then _ else _)")
    by simp 
  also 
  let "if ?all ss then _ else _" = "?if ss x"    
  have "\<dots> = ?if ((pc',s')#ss) x"
  proof (cases "?pc'")    
    case True
    hence "?all (((pc',s')#ss)) = (pc+1 < max_pc \<and> ?all ss)" by simp
    with True
    have "?if ss (OK s' +_?f x) = ?if ((pc',s')#ss) x" by (auto simp add: OK_snd)
    hence "?merge ss (OK s' +_?f x) = ?if ((pc',s')#ss) x" by (simp only: IH)
    with True show ?thesis by (fast intro: if_eq_cases)
  next
    case False
    have "(if ?G then ?merge ss x else Err) = ?if ((pc',s')#ss) x" 
    proof (cases ?G)
      assume G: ?G with False
      have "?if ss x = ?if ((pc',s')#ss) x" by (auto simp add: OK_snd)
      hence "?merge ss x = ?if ((pc',s')#ss) x" by (simp only: IH)
      with G show ?thesis by (fast intro: if_eq_cases)
    next
      assume G: "\<not>?G"
      with False have "Err = ?if ((pc',s')#ss) x" by auto
      with G show ?thesis by (fast intro: if_eq_cases)
    qed
    with False show ?thesis by (fast intro: if_eq_cases)
  qed
  also from s have "\<dots> = ?if (s#ss) x" by hypsubst (rule refl)
  finally show "?P (s#ss) x" .
qed
  

lemma wtl_inst_OK:
"(wtl_inst i G rT s cert mxs mxr max_pc et pc = OK s') = (
 app i G mxs rT pc et s \<and> 
  (\<forall>(pc',r) \<in> set (eff i G pc et s). 
  pc' < max_pc \<and> (pc' \<noteq> pc+1 \<longrightarrow> G \<turnstile> r <=' cert!pc')) \<and> 
  map (OK \<circ> snd) [(p',t') \<in> (eff i G pc et s). p'=pc+1] 
  ++_(sup G mxs mxr) (OK (cert!(pc+1))) = OK s')"
  by (auto simp add: wtl_inst_def merge_def split: split_if_asm)

lemma wtl_Cons:
  "wtl_inst_list (i#is) G rT cert maxs maxr max_pc et pc s \<noteq> Err = 
  (\<exists>s'. wtl_cert i G rT s cert maxs maxr max_pc et pc = OK s' \<and> 
        wtl_inst_list is G rT cert maxs maxr max_pc et (pc+1) s' \<noteq> Err)"
  by (auto simp del: split_paired_Ex)

lemma wtl_append:
"\<forall> s pc. (wtl_inst_list (a@b) G rT cert mxs mxr mpc et pc s = OK s') =
   (\<exists>s''. wtl_inst_list a G rT cert mxs mxr mpc et pc s = OK s'' \<and> 
          wtl_inst_list b G rT cert mxs mxr mpc et (pc+length a) s'' = OK s')" 
  (is "\<forall> s pc. ?C s pc a" is "?P a")
proof (induct ?P a)
  show "?P []" by simp
next
  fix x xs  assume IH: "?P xs"
  show "?P (x#xs)"
  proof (intro allI)
    fix s pc 
    show "?C s pc (x#xs)"
    proof (cases "wtl_cert x G rT s cert mxs mxr mpc et pc")
      case Err thus ?thesis by simp
    next
      fix s0 assume "wtl_cert x G rT s cert mxs mxr mpc et pc = OK s0"      
      with IH have "?C s0 (Suc pc) xs" by blast
      thus ?thesis by (simp!)
    qed
  qed
qed

lemma wtl_take:
  "wtl_inst_list is G rT cert mxs mxr mpc et pc s = OK s'' \<Longrightarrow>
   \<exists>s'. wtl_inst_list (take pc' is) G rT cert mxs mxr mpc et pc s = OK s'"
proof -
  assume "wtl_inst_list is G rT cert mxs mxr mpc et pc s = OK s''"
  hence "wtl_inst_list (take pc' is @ drop pc' is) G rT cert mxs mxr mpc et pc s = OK s''"
    by simp
  thus ?thesis by (auto simp add: wtl_append simp del: append_take_drop_id)
qed

lemma take_Suc:
  "\<forall>n. n < length l \<longrightarrow> take (Suc n) l = (take n l)@[l!n]" (is "?P l")
proof (induct l)
  show "?P []" by simp
next
  fix x xs assume IH: "?P xs"  
  show "?P (x#xs)"
  proof (intro strip)
    fix n assume "n < length (x#xs)"
    with IH show "take (Suc n) (x # xs) = take n (x # xs) @ [(x # xs) ! n]" 
      by (cases n, auto)
  qed
qed

lemma wtl_Suc:
 "\<lbrakk> wtl_inst_list (take pc is) G rT cert maxs maxr (length is) et 0 s = OK s'; 
     wtl_cert (is!pc) G rT s' cert maxs maxr (length is) et pc = OK s'';
     Suc pc < length is \<rbrakk> \<Longrightarrow>
  wtl_inst_list (take (Suc pc) is) G rT cert maxs maxr (length is) et 0 s = OK s''" 
proof -
  assume "wtl_inst_list (take pc is) G rT cert maxs maxr (length is) et 0 s = OK s'"
         "wtl_cert (is!pc) G rT s' cert maxs maxr (length is) et pc = OK s''"
         "Suc pc < length is"
  hence "take (Suc pc) is = (take pc is)@[is!pc]" by (simp add: take_Suc)
  thus ?thesis by (simp! add: wtl_append min_def)
qed

lemma wtl_all:
  "\<lbrakk> wtl_inst_list is G rT cert maxs maxr (length is) et 0 s \<noteq> Err;
      pc < length is \<rbrakk> \<Longrightarrow> 
   \<exists>s' s''. wtl_inst_list (take pc is) G rT cert maxs maxr (length is) et 0 s = OK s' \<and> 
            wtl_cert (is!pc) G rT s' cert maxs maxr (length is) et pc = OK s''"
proof -
  assume all: "wtl_inst_list is G rT cert maxs maxr (length is) et 0 s \<noteq> Err"

  assume pc: "pc < length is"
  hence  "0 < length (drop pc is)" by simp
  then  obtain i r where Cons: "drop pc is = i#r" 
    by (auto simp add: neq_Nil_conv simp del: length_drop)
  hence "i#r = drop pc is" ..
  with all have take: 
    "wtl_inst_list (take pc is@i#r) G rT cert maxs maxr (length is) et 0 s \<noteq> Err"
    by simp
 
  from pc have "is!pc = drop pc is ! 0" by simp
  with Cons have "is!pc = i" by simp
  with take pc show ?thesis by (auto simp add: wtl_append min_def)
qed


end
