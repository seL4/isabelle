(*  Title:      HOL/MicroJava/BV/JVM.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM
*)

header {* \isaheader{LBV for the JVM}\label{sec:JVM} *}

theory LBVJVM = LBVCorrect + LBVComplete + Typing_Framework_JVM:

types prog_cert = "cname \<Rightarrow> sig \<Rightarrow> state list"

constdefs
  check_cert :: "jvm_prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state list \<Rightarrow> bool"
  "check_cert G mxs mxr n cert \<equiv> check_types G mxs mxr cert \<and> length cert = n+1 \<and>
                                 (\<forall>i<n. cert!i \<noteq> Err) \<and> cert!n = OK None"

  lbvjvm :: "jvm_prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> exception_table \<Rightarrow> 
             state list \<Rightarrow> instr list \<Rightarrow> state \<Rightarrow> state"
  "lbvjvm G maxs maxr rT et cert bs \<equiv>
  wtl_inst_list bs cert  (JVMType.sup G maxs maxr) (JVMType.le G maxs maxr) Err (OK None) (exec G maxs rT et bs) 0"

  wt_lbv :: "jvm_prog \<Rightarrow> cname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
             exception_table \<Rightarrow> state list \<Rightarrow> instr list \<Rightarrow> bool"
  "wt_lbv G C pTs rT mxs mxl et cert ins \<equiv>
   check_bounded ins et \<and> 
   check_cert G mxs (1+size pTs+mxl) (length ins) cert \<and>
   0 < size ins \<and> 
   (let start  = Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err));
        result = lbvjvm G mxs (1+size pTs+mxl) rT et cert ins (OK start)
    in result \<noteq> Err)"

  wt_jvm_prog_lbv :: "jvm_prog \<Rightarrow> prog_cert \<Rightarrow> bool"
  "wt_jvm_prog_lbv G cert \<equiv>
  wf_prog (\<lambda>G C (sig,rT,(maxs,maxl,b,et)). wt_lbv G C (snd sig) rT maxs maxl et (cert C sig) b) G"

  mk_cert :: "jvm_prog \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> exception_table \<Rightarrow> instr list 
              \<Rightarrow> method_type \<Rightarrow> state list"
  "mk_cert G maxs rT et bs phi \<equiv> make_cert (exec G maxs rT et bs) (map OK phi) (OK None)"

  prg_cert :: "jvm_prog \<Rightarrow> prog_type \<Rightarrow> prog_cert"
  "prg_cert G phi C sig \<equiv> let (C,rT,(maxs,maxl,ins,et)) = the (method (G,C) sig) in 
                           mk_cert G maxs rT et ins (phi C sig)"
 
  
lemma wt_method_def2:
  fixes pTs and mxl and G and mxs and rT and et and bs and phi 
  defines [simp]: "mxr   \<equiv> 1 + length pTs + mxl"
  defines [simp]: "r     \<equiv> sup_state_opt G"
  defines [simp]: "app0  \<equiv> \<lambda>pc. app (bs!pc) G mxs rT pc et"
  defines [simp]: "step0 \<equiv> \<lambda>pc. eff (bs!pc) G pc et"

  shows
  "wt_method G C pTs rT mxs mxl bs et phi = 
  (bs \<noteq> [] \<and> 
   length phi = length bs \<and>
   check_bounded bs et \<and> 
   check_types G mxs mxr (map OK phi) \<and>   
   wt_start G C pTs mxl phi \<and> 
   wt_app_eff r app0 step0 phi)"
  by (auto simp add: wt_method_def wt_app_eff_def wt_instr_def lesub_def
           dest: check_bounded_is_bounded boundedD)


lemma check_certD:
  "check_cert G mxs mxr n cert \<Longrightarrow> cert_ok cert n Err (OK None) (states G mxs mxr)"
  apply (unfold cert_ok_def check_cert_def check_types_def)
  apply (auto simp add: list_all_ball)
  done


lemma wt_lbv_wt_step:
  assumes wf:  "wf_prog wf_mb G"
  assumes lbv: "wt_lbv G C pTs rT mxs mxl et cert ins"
  assumes C:   "is_class G C" 
  assumes pTs: "set pTs \<subseteq> types G"
  
  defines [simp]: "mxr \<equiv> 1+length pTs+mxl"

  shows "\<exists>ts \<in> list (size ins) (states G mxs mxr). 
            wt_step (JVMType.le G mxs mxr) Err (exec G mxs rT et ins) ts
          \<and> OK (Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err))) <=_(JVMType.le G mxs mxr) ts!0"
proof -
  let ?step = "exec G mxs rT et ins"
  let ?r    = "JVMType.le G mxs mxr"
  let ?f    = "JVMType.sup G mxs mxr"
  let ?A    = "states G mxs mxr"

  have "semilat (JVMType.sl G mxs mxr)" by (rule semilat_JVM_slI)
  hence "semilat (?A, ?r, ?f)" by (unfold sl_triple_conv)
  moreover
  have "top ?r Err"  by (simp add: JVM_le_unfold)
  moreover
  have "Err \<in> ?A" by (simp add: JVM_states_unfold)
  moreover
  have "bottom ?r (OK None)" 
    by (simp add: JVM_le_unfold bottom_def)
  moreover
  have "OK None \<in> ?A" by (simp add: JVM_states_unfold)
  moreover
  from lbv
  have "bounded ?step (length ins)" 
    by (clarsimp simp add: wt_lbv_def exec_def) 
       (intro bounded_lift check_bounded_is_bounded) 
  moreover
  from lbv
  have "cert_ok cert (length ins) Err (OK None) ?A" 
    by (unfold wt_lbv_def) (auto dest: check_certD)
  moreover
  have "pres_type ?step (length ins) ?A" by (rule exec_pres_type)
  moreover
  let ?start = "OK (Some ([],(OK (Class C))#(map OK pTs)@(replicate mxl Err)))"
  from lbv
  have "wtl_inst_list ins cert ?f ?r Err (OK None) ?step 0 ?start \<noteq> Err"
    by (simp add: wt_lbv_def lbvjvm_def)    
  moreover
  from C pTs have "?start \<in> ?A"
    by (unfold JVM_states_unfold) (auto intro: list_appendI, force)
  moreover
  from lbv have "0 < length ins" by (simp add: wt_lbv_def)
  ultimately
  show ?thesis by (rule lbvs.wtl_sound_strong)
qed
  
lemma wt_lbv_wt_method:
  assumes wf:  "wf_prog wf_mb G"
  assumes lbv: "wt_lbv G C pTs rT mxs mxl et cert ins"
  assumes C:   "is_class G C" 
  assumes pTs: "set pTs \<subseteq> types G"
  
  shows "\<exists>phi. wt_method G C pTs rT mxs mxl ins et phi"
proof -
  let ?mxr   = "1 + length pTs + mxl"
  let ?step  = "exec G mxs rT et ins"
  let ?r     = "JVMType.le G mxs ?mxr"
  let ?f     = "JVMType.sup G mxs ?mxr"
  let ?A     = "states G mxs ?mxr"
  let ?start = "OK (Some ([],(OK (Class C))#(map OK pTs)@(replicate mxl Err)))"
  
  from lbv have l: "ins \<noteq> []" by (simp add: wt_lbv_def)
  moreover
  from wf lbv C pTs
  obtain phi where 
    list:  "phi \<in> list (length ins) ?A" and
    step:  "wt_step ?r Err ?step phi" and    
    start: "?start <=_?r phi!0" 
    by (blast dest: wt_lbv_wt_step)
  from list have [simp]: "length phi = length ins" by simp
  have "length (map ok_val phi) = length ins" by simp  
  moreover
  from l have 0: "0 < length phi" by simp
  with step obtain phi0 where "phi!0 = OK phi0"
    by (unfold wt_step_def) blast
  with start 0
  have "wt_start G C pTs mxl (map ok_val phi)"
    by (simp add: wt_start_def JVM_le_Err_conv lesub_def)
  moreover
  from lbv  have chk_bounded: "check_bounded ins et"
    by (simp add: wt_lbv_def)
  moreover {
    from list
    have "check_types G mxs ?mxr phi"
      by (simp add: check_types_def)
    also from step
    have [symmetric]: "map OK (map ok_val phi) = phi" 
      by (auto intro!: map_id simp add: wt_step_def)
    finally have "check_types G mxs ?mxr (map OK (map ok_val phi))" .
  }
  moreover {  
    let ?app = "\<lambda>pc. app (ins!pc) G mxs rT pc et"
    let ?eff = "\<lambda>pc. eff (ins!pc) G pc et"

    from chk_bounded
    have "bounded (err_step (length ins) ?app ?eff) (length ins)"
      by (blast dest: check_bounded_is_bounded boundedD intro: bounded_err_stepI)
    moreover
    from step
    have "wt_err_step (sup_state_opt G) ?step phi"
      by (simp add: wt_err_step_def JVM_le_Err_conv)
    ultimately
    have "wt_app_eff (sup_state_opt G) ?app ?eff (map ok_val phi)"
      by (auto intro: wt_err_imp_wt_app_eff simp add: exec_def)
  }    
  ultimately
  have "wt_method G C pTs rT mxs mxl ins et (map ok_val phi)"
    by - (rule wt_method_def2 [THEN iffD2], simp)
  thus ?thesis ..
qed


lemma wt_method_wt_lbv:
  assumes wf:  "wf_prog wf_mb G"
  assumes wt:  "wt_method G C pTs rT mxs mxl ins et phi"
  assumes C:   "is_class G C" 
  assumes pTs: "set pTs \<subseteq> types G"
  
  defines [simp]: "cert \<equiv> mk_cert G mxs rT et ins phi"

  shows "wt_lbv G C pTs rT mxs mxl et cert ins"
proof -
  let ?mxr  = "1 + length pTs + mxl"
  let ?step = "exec G mxs rT et ins"
  let ?app  = "\<lambda>pc. app (ins!pc) G mxs rT pc et"
  let ?eff  = "\<lambda>pc. eff (ins!pc) G pc et"
  let ?r    = "JVMType.le G mxs ?mxr"
  let ?f    = "JVMType.sup G mxs ?mxr"
  let ?A    = "states G mxs ?mxr"
  let ?phi  = "map OK phi"
  let ?cert = "make_cert ?step ?phi (OK None)"

  from wt obtain 
    0:          "0 < length ins" and
    length:     "length ins = length ?phi" and
    ck_bounded: "check_bounded ins et" and
    ck_types:   "check_types G mxs ?mxr ?phi" and
    wt_start:   "wt_start G C pTs mxl phi" and
    app_eff:    "wt_app_eff (sup_state_opt G) ?app ?eff phi"
    by (simp (asm_lr) add: wt_method_def2)
  
  have "semilat (JVMType.sl G mxs ?mxr)" by (rule semilat_JVM_slI)
  hence "semilat (?A, ?r, ?f)" by (unfold sl_triple_conv)
  moreover
  have "top ?r Err"  by (simp add: JVM_le_unfold)
  moreover
  have "Err \<in> ?A" by (simp add: JVM_states_unfold)
  moreover
  have "bottom ?r (OK None)" 
    by (simp add: JVM_le_unfold bottom_def)
  moreover
  have "OK None \<in> ?A" by (simp add: JVM_states_unfold)
  moreover
  from ck_bounded
  have bounded: "bounded ?step (length ins)" 
    by (clarsimp simp add: exec_def) 
       (intro bounded_lift check_bounded_is_bounded)
  with wf
  have "mono ?r ?step (length ins) ?A" by (rule exec_mono)
  hence "mono ?r ?step (length ?phi) ?A" by (simp add: length)
  moreover
  have "pres_type ?step (length ins) ?A" by (rule exec_pres_type)
  hence "pres_type ?step (length ?phi) ?A" by (simp add: length)
  moreover
  from ck_types
  have "set ?phi \<subseteq> ?A" by (simp add: check_types_def) 
  hence "\<forall>pc. pc < length ?phi \<longrightarrow> ?phi!pc \<in> ?A \<and> ?phi!pc \<noteq> Err" by auto
  moreover 
  from bounded 
  have "bounded (exec G mxs rT et ins) (length ?phi)" by (simp add: length)
  moreover
  have "OK None \<noteq> Err" by simp
  moreover
  from bounded length app_eff
  have "wt_err_step (sup_state_opt G) ?step ?phi"
    by (auto intro: wt_app_eff_imp_wt_err simp add: exec_def)
  hence "wt_step ?r Err ?step ?phi"
    by (simp add: wt_err_step_def JVM_le_Err_conv)
  moreover 
  let ?start = "OK (Some ([],(OK (Class C))#(map OK pTs)@(replicate mxl Err)))"  
  from 0 length have "0 < length phi" by auto
  hence "?phi!0 = OK (phi!0)" by simp
  with wt_start have "?start <=_?r ?phi!0"
    by (clarsimp simp add: wt_start_def lesub_def JVM_le_Err_conv)
  moreover
  from C pTs have "?start \<in> ?A"
    by (unfold JVM_states_unfold) (auto intro: list_appendI, force)
  moreover
  have "?start \<noteq> Err" by simp
  moreover
  note length 
  ultimately
  have "wtl_inst_list ins ?cert ?f ?r Err (OK None) ?step 0 ?start \<noteq> Err"
    by (rule lbvc.wtl_complete)
  moreover
  from 0 length have "phi \<noteq> []" by auto
  moreover
  from ck_types
  have "check_types G mxs ?mxr ?cert"
    by (auto simp add: make_cert_def check_types_def JVM_states_unfold)
  moreover
  note ck_bounded 0 length
  ultimately 
  show ?thesis 
    by (simp add: wt_lbv_def lbvjvm_def mk_cert_def 
      check_cert_def make_cert_def nth_append)
qed  



theorem jvm_lbv_correct:
  "wt_jvm_prog_lbv G Cert \<Longrightarrow> \<exists>Phi. wt_jvm_prog G Phi"
proof -  
  let ?Phi = "\<lambda>C sig. let (C,rT,(maxs,maxl,ins,et)) = the (method (G,C) sig) in 
              SOME phi. wt_method G C (snd sig) rT maxs maxl ins et phi"
    
  assume "wt_jvm_prog_lbv G Cert"
  hence "wt_jvm_prog G ?Phi"
    apply (unfold wt_jvm_prog_def wt_jvm_prog_lbv_def)
    apply (erule jvm_prog_lift)
    apply (auto dest: wt_lbv_wt_method intro: someI)
    done
  thus ?thesis by blast
qed

theorem jvm_lbv_complete:
  "wt_jvm_prog G Phi \<Longrightarrow> wt_jvm_prog_lbv G (prg_cert G Phi)"
  apply (unfold wt_jvm_prog_def wt_jvm_prog_lbv_def)
  apply (erule jvm_prog_lift)
  apply (auto simp add: prg_cert_def intro wt_method_wt_lbv)
  done  

end
