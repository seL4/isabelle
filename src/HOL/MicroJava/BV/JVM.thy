(*  Title:      HOL/MicroJava/BV/JVM.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM
*)

header {* \isaheader{Kildall for the JVM}\label{sec:JVM} *}

theory JVM = Kildall + Typing_Framework_JVM:


constdefs
  kiljvm :: "jvm_prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> exception_table \<Rightarrow> 
             instr list \<Rightarrow> state list \<Rightarrow> state list"
  "kiljvm G maxs maxr rT et bs ==
  kildall (JVMType.le G maxs maxr) (JVMType.sup G maxs maxr) (exec G maxs rT et bs)"

  wt_kil :: "jvm_prog \<Rightarrow> cname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
             exception_table \<Rightarrow> instr list \<Rightarrow> bool"
  "wt_kil G C pTs rT mxs mxl et ins ==
   check_bounded ins et \<and> 0 < size ins \<and> 
   (let first  = Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err));
        start  = OK first#(replicate (size ins - 1) (OK None));
        result = kiljvm G mxs (1+size pTs+mxl) rT et ins start
    in \<forall>n < size ins. result!n \<noteq> Err)"

  wt_jvm_prog_kildall :: "jvm_prog \<Rightarrow> bool"
  "wt_jvm_prog_kildall G ==
  wf_prog (\<lambda>G C (sig,rT,(maxs,maxl,b,et)). wt_kil G C (snd sig) rT maxs maxl et b) G"



theorem is_bcv_kiljvm:
  "\<lbrakk> wf_prog wf_mb G; bounded (exec G maxs rT et bs) (size bs) \<rbrakk> \<Longrightarrow>
      is_bcv (JVMType.le G maxs maxr) Err (exec G maxs rT et bs)
             (size bs) (states G maxs maxr) (kiljvm G maxs maxr rT et bs)"
  apply (unfold kiljvm_def sl_triple_conv)
  apply (rule is_bcv_kildall)
       apply (simp (no_asm) add: sl_triple_conv [symmetric]) 
       apply (force intro!: semilat_JVM_slI dest: wf_acyclic simp add: symmetric sl_triple_conv)
      apply (simp (no_asm) add: JVM_le_unfold)
      apply (blast intro!: order_widen wf_converse_subcls1_impl_acc_subtype
                   dest: wf_subcls1 wf_acyclic) 
     apply (simp add: JVM_le_unfold)
    apply (erule exec_pres_type)
   apply assumption
  apply (erule exec_mono, assumption)  
  done

lemma subset_replicate: "set (replicate n x) \<subseteq> {x}"
  by (induct n) auto

lemma in_set_replicate:
  "x \<in> set (replicate n y) \<Longrightarrow> x = y"
proof -
  assume "x \<in> set (replicate n y)"
  also have "set (replicate n y) \<subseteq> {y}" by (rule subset_replicate)
  finally have "x \<in> {y}" .
  thus ?thesis by simp
qed

theorem wt_kil_correct:
  assumes wf:  "wf_prog wf_mb G"
  assumes C:   "is_class G C"
  assumes pTs: "set pTs \<subseteq> types G"
  
  assumes wtk: "wt_kil G C pTs rT maxs mxl et bs"
  
  shows "\<exists>phi. wt_method G C pTs rT maxs mxl bs et phi"
proof -
  let ?start = "OK (Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err)))
                #(replicate (size bs - 1) (OK None))"

  from wtk obtain maxr r where    
    bounded: "check_bounded bs et" and
    result:  "r = kiljvm G maxs maxr rT et bs ?start" and
    success: "\<forall>n < size bs. r!n \<noteq> Err" and
    instrs:  "0 < size bs" and
    maxr:    "maxr = Suc (length pTs + mxl)" 
    by (unfold wt_kil_def) simp

  from bounded have "bounded (exec G maxs rT et bs) (size bs)"
    by (unfold exec_def) (intro bounded_lift check_bounded_is_bounded)
  with wf have bcv:
    "is_bcv (JVMType.le G maxs maxr) Err (exec G maxs rT et bs) 
    (size bs) (states G maxs maxr) (kiljvm G maxs maxr rT et bs)"
    by (rule is_bcv_kiljvm)
    
  from C pTs instrs maxr
  have "?start \<in> list (length bs) (states G maxs maxr)"
    apply (unfold JVM_states_unfold)
    apply (rule listI)
    apply (auto intro: list_appendI dest!: in_set_replicate)
    apply force
    done    

  with bcv success result have 
    "\<exists>ts\<in>list (length bs) (states G maxs maxr).
         ?start <=[JVMType.le G maxs maxr] ts \<and>
         wt_step (JVMType.le G maxs maxr) Err (exec G maxs rT et bs) ts"
    by (unfold is_bcv_def) auto
  then obtain phi' where
    phi': "phi' \<in> list (length bs) (states G maxs maxr)" and
    s: "?start <=[JVMType.le G maxs maxr] phi'" and
    w: "wt_step (JVMType.le G maxs maxr) Err (exec G maxs rT et bs) phi'"
    by blast
  hence wt_err_step:
    "wt_err_step (sup_state_opt G) (exec G maxs rT et bs) phi'"
    by (simp add: wt_err_step_def exec_def JVM_le_Err_conv)

  from s have le: "JVMType.le G maxs maxr (?start ! 0) (phi'!0)"
    by (drule_tac p=0 in le_listD) (simp add: lesub_def)+

  from phi' have l: "size phi' = size bs" by simp  
  with instrs w have "phi' ! 0 \<noteq> Err" by (unfold wt_step_def) simp
  with instrs l have phi0: "OK (map ok_val phi' ! 0) = phi' ! 0"
    by (clarsimp simp add: not_Err_eq)  

  from phi' have "check_types G maxs maxr phi'" by(simp add: check_types_def)
  also from w have "phi' = map OK (map ok_val phi')" 
    apply (clarsimp simp add: wt_step_def not_Err_eq) 
    apply (rule map_id [symmetric])
    apply (erule allE, erule impE, assumption)
    apply clarsimp
    done    
  finally 
  have check_types:
    "check_types G maxs maxr (map OK (map ok_val phi'))" .

  from l bounded 
  have "bounded (\<lambda>pc. eff (bs!pc) G pc et) (length phi')"
    by (simp add: exec_def check_bounded_is_bounded)  
  hence bounded': "bounded (exec G maxs rT et bs) (length bs)"
    by (auto intro: bounded_lift simp add: exec_def l)
  with wt_err_step
  have "wt_app_eff (sup_state_opt G) (\<lambda>pc. app (bs!pc) G maxs rT pc et) 
                   (\<lambda>pc. eff (bs!pc) G pc et) (map ok_val phi')"
    by (auto intro: wt_err_imp_wt_app_eff simp add: l exec_def)
  with instrs l le bounded bounded' check_types maxr
  have "wt_method G C pTs rT maxs mxl bs et (map ok_val phi')"
    apply (unfold wt_method_def wt_app_eff_def)
    apply simp
    apply (rule conjI)
     apply (unfold wt_start_def)
     apply (rule JVM_le_convert [THEN iffD1])
     apply (simp (no_asm) add: phi0)
    apply clarify
    apply (erule allE, erule impE, assumption)
    apply (elim conjE)
    apply (clarsimp simp add: lesub_def wt_instr_def)
    apply (simp add: exec_def)
    apply (drule bounded_err_stepD, assumption+)
    apply blast
    done

  thus ?thesis by blast
qed


theorem wt_kil_complete:
  assumes wf:  "wf_prog wf_mb G"  
  assumes C:   "is_class G C"
  assumes pTs: "set pTs \<subseteq> types G"

  assumes wtm: "wt_method G C pTs rT maxs mxl bs et phi"

  shows "wt_kil G C pTs rT maxs mxl et bs"
proof -
  let ?mxr = "1+size pTs+mxl"
  
  from wtm obtain
    instrs:   "0 < length bs" and
    len:      "length phi = length bs" and
    bounded:  "check_bounded bs et" and
    ck_types: "check_types G maxs ?mxr (map OK phi)" and
    wt_start: "wt_start G C pTs mxl phi" and
    wt_ins:   "\<forall>pc. pc < length bs \<longrightarrow> 
                    wt_instr (bs ! pc) G rT phi maxs (length bs) et pc"
    by (unfold wt_method_def) simp

  from ck_types len
  have istype_phi: 
    "map OK phi \<in> list (length bs) (states G maxs (1+size pTs+mxl))"
    by (auto simp add: check_types_def intro!: listI)

  let ?eff  = "\<lambda>pc. eff (bs!pc) G pc et"
  let ?app   = "\<lambda>pc. app (bs!pc) G maxs rT pc et"

  from bounded
  have bounded_exec: "bounded (exec G maxs rT et bs) (size bs)"
    by (unfold exec_def) (intro bounded_lift check_bounded_is_bounded)
 
  from wt_ins
  have "wt_app_eff (sup_state_opt G) ?app ?eff phi"
    apply (unfold wt_app_eff_def wt_instr_def lesub_def)
    apply (simp (no_asm) only: len)
    apply blast
    done
  with bounded_exec
  have "wt_err_step (sup_state_opt G) (err_step (size phi) ?app ?eff) (map OK phi)"
    by - (erule wt_app_eff_imp_wt_err,simp add: exec_def len)
  hence wt_err:
    "wt_err_step (sup_state_opt G) (exec G maxs rT et bs) (map OK phi)"
    by (unfold exec_def) (simp add: len)
 
  from wf bounded_exec
  have is_bcv: 
    "is_bcv (JVMType.le G maxs ?mxr) Err (exec G maxs rT et bs) 
            (size bs) (states G maxs ?mxr) (kiljvm G maxs ?mxr rT et bs)"
    by (rule is_bcv_kiljvm)

  let ?start = "OK (Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err)))
                #(replicate (size bs - 1) (OK None))"

  from C pTs instrs
  have start: "?start \<in> list (length bs) (states G maxs ?mxr)"
    apply (unfold JVM_states_unfold)
    apply (rule listI)
    apply (auto intro!: list_appendI dest!: in_set_replicate)
    apply force
    done    

  let ?phi = "map OK phi"  
  have less_phi: "?start <=[JVMType.le G maxs ?mxr] ?phi"
  proof -
    from len instrs
    have "length ?start = length (map OK phi)" by simp
    moreover
    { fix n
      from wt_start
      have "G \<turnstile> ok_val (?start!0) <=' phi!0"
        by (simp add: wt_start_def)
      moreover
      from instrs len
      have "0 < length phi" by simp
      ultimately
      have "JVMType.le G maxs ?mxr (?start!0) (?phi!0)"
        by (simp add: JVM_le_Err_conv Err.le_def lesub_def)
      moreover
      { fix n'
        have "JVMType.le G maxs ?mxr (OK None) (?phi!n)"
          by (auto simp add: JVM_le_Err_conv Err.le_def lesub_def 
            split: err.splits)        
        hence "\<lbrakk> n = Suc n'; n < length ?start \<rbrakk> 
          \<Longrightarrow> JVMType.le G maxs ?mxr (?start!n) (?phi!n)"
          by simp
      }
      ultimately
      have "n < length ?start \<Longrightarrow> (?start!n) <=_(JVMType.le G maxs ?mxr) (?phi!n)"
        by (unfold lesub_def) (cases n, blast+)
    } 
    ultimately show ?thesis by (rule le_listI)
  qed         

  from wt_err
  have "wt_step (JVMType.le G maxs ?mxr) Err (exec G maxs rT et bs) ?phi"
    by (simp add: wt_err_step_def JVM_le_Err_conv)  
  with start istype_phi less_phi is_bcv
  have "\<forall>p. p < length bs \<longrightarrow> kiljvm G maxs ?mxr rT et bs ?start ! p \<noteq> Err"
    by (unfold is_bcv_def) auto
  with bounded instrs
  show "wt_kil G C pTs rT maxs mxl et bs" by (unfold wt_kil_def) simp
qed


theorem jvm_kildall_sound_complete:
  "wt_jvm_prog_kildall G = (\<exists>Phi. wt_jvm_prog G Phi)"
proof 
  let ?Phi = "\<lambda>C sig. let (C,rT,(maxs,maxl,ins,et)) = the (method (G,C) sig) in 
              SOME phi. wt_method G C (snd sig) rT maxs maxl ins et phi"
  
  assume "wt_jvm_prog_kildall G"
  hence "wt_jvm_prog G ?Phi"
    apply (unfold wt_jvm_prog_def wt_jvm_prog_kildall_def)
    apply (erule jvm_prog_lift)
    apply (auto dest!: wt_kil_correct intro: someI)
    done
  thus "\<exists>Phi. wt_jvm_prog G Phi" by fast
next
  assume "\<exists>Phi. wt_jvm_prog G Phi"
  thus "wt_jvm_prog_kildall G"
    apply (clarify)
    apply (unfold wt_jvm_prog_def wt_jvm_prog_kildall_def)
    apply (erule jvm_prog_lift)
    apply (auto intro: wt_kil_complete)
    done
qed

end
