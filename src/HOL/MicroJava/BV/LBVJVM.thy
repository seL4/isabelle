(*  Title:      HOL/MicroJava/BV/JVM.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM
*)

header {* \isaheader{LBV for the JVM}\label{sec:JVM} *}

theory LBVJVM = LBVCorrect + LBVComplete + EffectMono + BVSpec + Kildall_Lift:

types prog_cert = "cname \<Rightarrow> sig \<Rightarrow> state list"

constdefs
  check_cert :: "jvm_prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state list \<Rightarrow> bool"
  "check_cert G mxs mxr n cert \<equiv> check_types G mxs mxr cert \<and> length cert = n+1 \<and>
                                 (\<forall>i<n. cert!i \<noteq> Err) \<and> cert!n = OK None"

  exec :: "jvm_prog \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> exception_table \<Rightarrow> instr list \<Rightarrow> state step_type"
  "exec G maxs rT et bs \<equiv>
  err_step (size bs) (\<lambda>pc. app (bs!pc) G maxs rT pc et) (\<lambda>pc. eff (bs!pc) G pc et)"

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
 

text {*
  Executability of @{term check_bounded}:
*}
consts
  list_all'_rec :: "('a \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool"
primrec
  "list_all'_rec P n []     = True"
  "list_all'_rec P n (x#xs) = (P x n \<and> list_all'_rec P (Suc n) xs)"

constdefs
  list_all' :: "('a \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  "list_all' P xs \<equiv> list_all'_rec P 0 xs"

lemma list_all'_rec:
  "\<And>n. list_all'_rec P n xs = (\<forall>p < size xs. P (xs!p) (p+n))"
  apply (induct xs)
  apply auto
  apply (case_tac p)
  apply auto
  done

lemma list_all' [iff]:
  "list_all' P xs = (\<forall>n < size xs. P (xs!n) n)"
  by (unfold list_all'_def) (simp add: list_all'_rec)

lemma list_all_ball:
  "list_all P xs = (\<forall>x \<in> set xs. P x)"
  by (induct xs) auto

lemma [code]:
  "check_bounded ins et = 
  (list_all' (\<lambda>i pc. list_all (\<lambda>pc'. pc' < length ins) (succs i pc)) ins \<and> 
   list_all (\<lambda>e. fst (snd (snd e)) < length ins) et)"
  by (simp add: list_all_ball check_bounded_def)
  
text {*
  Lemmas for LBV instantiation
*}

lemma check_bounded_is_bounded:
  "check_bounded ins et \<Longrightarrow> bounded (\<lambda>pc. eff (ins!pc) G pc et) (length ins)"
  by (unfold bounded_def) (auto dest: check_boundedD)

lemma check_certD:
  "check_cert G mxs mxr n cert \<Longrightarrow> cert_ok cert n Err (OK None) (states G mxs mxr)"
  apply (unfold cert_ok_def check_cert_def check_types_def)
  apply (auto simp add: list_all_ball)
  done

lemma special_ex_swap_lemma [iff]: 
  "(? X. (? n. X = A n & P n) & Q X) = (? n. Q(A n) & P n)"
  by blast

lemmas [iff del] = not_None_eq

theorem exec_pres_type [intro]:
  "wf_prog wf_mb S \<Longrightarrow> 
  pres_type (exec S maxs rT et bs) (size bs) (states S maxs maxr)"
  apply (unfold exec_def JVM_states_unfold)
  apply (rule pres_type_lift)
  apply clarify
  apply (case_tac s)
   apply simp
   apply (drule effNone)
   apply simp  
  apply (simp add: eff_def xcpt_eff_def norm_eff_def)
  apply (case_tac "bs!p")

  apply (clarsimp simp add: not_Err_eq)
  apply (drule listE_nth_in, assumption)
  apply fastsimp

  apply (fastsimp simp add: not_None_eq)

  apply (fastsimp simp add: not_None_eq typeof_empty_is_type)

  apply clarsimp
  apply (erule disjE)
   apply fastsimp
  apply clarsimp
  apply (rule_tac x="1" in exI)
  apply fastsimp

  apply clarsimp
  apply (erule disjE)
   apply (fastsimp dest: field_fields fields_is_type)
  apply (simp add: match_some_entry split: split_if_asm)
  apply (rule_tac x=1 in exI)
  apply fastsimp

  apply clarsimp
  apply (erule disjE)
   apply fastsimp
  apply (simp add: match_some_entry split: split_if_asm)
  apply (rule_tac x=1 in exI)
  apply fastsimp

  apply clarsimp
  apply (erule disjE)
   apply fastsimp
  apply clarsimp
  apply (rule_tac x=1 in exI)
  apply fastsimp

  defer 

  apply fastsimp
  apply fastsimp

  apply clarsimp
  apply (rule_tac x="n'+2" in exI)  
  apply simp
  apply (drule listE_length)+
  apply fastsimp

  apply clarsimp
  apply (rule_tac x="Suc (Suc (Suc (length ST)))" in exI)  
  apply simp
  apply (drule listE_length)+
  apply fastsimp

  apply clarsimp
  apply (rule_tac x="Suc (Suc (Suc (Suc (length ST))))" in exI)  
  apply simp
  apply (drule listE_length)+
  apply fastsimp

  apply fastsimp
  apply fastsimp
  apply fastsimp
  apply fastsimp

  apply clarsimp
  apply (erule disjE)
   apply fastsimp
  apply clarsimp
  apply (rule_tac x=1 in exI)
  apply fastsimp
  
  apply (erule disjE)
   apply (clarsimp simp add: Un_subset_iff)  
   apply (drule method_wf_mdecl, assumption+)
   apply (clarsimp simp add: wf_mdecl_def wf_mhead_def)
   apply fastsimp
  apply clarsimp
  apply (rule_tac x=1 in exI)
  apply fastsimp
  done

lemmas [iff] = not_None_eq


lemma sup_state_opt_unfold:
  "sup_state_opt G \<equiv> Opt.le (Product.le (Listn.le (subtype G)) (Listn.le (Err.le (subtype G))))"
  by (simp add: sup_state_opt_def sup_state_def sup_loc_def sup_ty_opt_def)

constdefs
  opt_states :: "'c prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (ty list \<times> ty err list) option set"
  "opt_states G maxs maxr \<equiv> opt (\<Union>{list n (types G) |n. n \<le> maxs} \<times> list maxr (err (types G)))"

lemma app_mono:
  "app_mono (sup_state_opt G) (\<lambda>pc. app (bs!pc) G maxs rT pc et) (length bs) (opt_states G maxs maxr)"
  by (unfold app_mono_def lesub_def) (blast intro: EffectMono.app_mono)
  

lemma lesubstep_type_simple:
  "a <=[Product.le (op =) r] b \<Longrightarrow> a <=|r| b"
  apply (unfold lesubstep_type_def)
  apply clarify
  apply (simp add: set_conv_nth)
  apply clarify
  apply (drule le_listD, assumption)
  apply (clarsimp simp add: lesub_def Product.le_def)
  apply (rule exI)
  apply (rule conjI)
   apply (rule exI)
   apply (rule conjI)
    apply (rule sym)
    apply assumption
   apply assumption
  apply assumption
  done
  

lemma eff_mono:
  "\<lbrakk>p < length bs; s <=_(sup_state_opt G) t; app (bs!p) G maxs rT pc et t\<rbrakk>
  \<Longrightarrow> eff (bs!p) G p et s <=|sup_state_opt G| eff (bs!p) G p et t"
  apply (unfold eff_def)
  apply (rule lesubstep_type_simple)
  apply (rule le_list_appendI)
   apply (simp add: norm_eff_def)
   apply (rule le_listI)
    apply simp
   apply simp
   apply (simp add: lesub_def)
   apply (case_tac s)
    apply simp
   apply (simp del: split_paired_All split_paired_Ex)
   apply (elim exE conjE)
   apply simp
   apply (drule eff'_mono, assumption)
   apply assumption
  apply (simp add: xcpt_eff_def)
  apply (rule le_listI)
    apply simp
  apply simp
  apply (simp add: lesub_def)
  apply (case_tac s)
   apply simp
  apply simp
  apply (case_tac t)
   apply simp
  apply (clarsimp simp add: sup_state_conv)
  done

lemma order_sup_state_opt:
  "wf_prog wf_mb G \<Longrightarrow> order (sup_state_opt G)"
  by (unfold sup_state_opt_unfold) (blast dest: acyclic_subcls1 order_widen)

theorem exec_mono:
  "wf_prog wf_mb G \<Longrightarrow> bounded (exec G maxs rT et bs) (size bs) \<Longrightarrow>
  mono (JVMType.le G maxs maxr) (exec G maxs rT et bs) (size bs) (states G maxs maxr)"  
  apply (unfold exec_def JVM_le_unfold JVM_states_unfold)  
  apply (rule mono_lift)
     apply (fold sup_state_opt_unfold opt_states_def)
     apply (erule order_sup_state_opt)
    apply (rule app_mono)
   apply assumption
  apply clarify
  apply (rule eff_mono)
  apply assumption+
  done

theorem semilat_JVM_slI [intro]:
  "wf_prog wf_mb G \<Longrightarrow> semilat (JVMType.sl G maxs maxr)"
  apply (unfold JVMType.sl_def stk_esl_def reg_sl_def)
  apply (rule semilat_opt)
  apply (rule err_semilat_Product_esl)
  apply (rule err_semilat_upto_esl)
  apply (rule err_semilat_JType_esl, assumption+)
  apply (rule err_semilat_eslI)
  apply (rule Listn_sl)
  apply (rule err_semilat_JType_esl, assumption+)
  done

lemma sl_triple_conv:
  "JVMType.sl G maxs maxr == 
  (states G maxs maxr, JVMType.le G maxs maxr, JVMType.sup G maxs maxr)"
  by (simp (no_asm) add: states_def JVMType.le_def JVMType.sup_def)


lemma list_appendI:
  "\<lbrakk>a \<in> list x A; b \<in> list y A\<rbrakk> \<Longrightarrow> a @ b \<in> list (x+y) A"
  apply (unfold list_def)
  apply (simp (no_asm))
  apply blast
  done

lemma list_map [simp]:
  "(map f xs \<in> list (length xs) A) = (f ` set xs \<subseteq> A)"
  apply (unfold list_def)
  apply simp
  done

lemma [iff]:
  "(OK ` A \<subseteq> err B) = (A \<subseteq> B)"
  apply (unfold err_def)
  apply blast
  done

lemma [intro]:
  "x \<in> A \<Longrightarrow> replicate n x \<in> list n A"
  by (induct n, auto)


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

  have "semilat (JVMType.sl G mxs mxr)" ..
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
  have "pres_type ?step (length ins) ?A" ..
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
  

lemma map_ident [rule_format]:
  "(\<forall>n < length xs. f (g (xs!n)) = xs!n) \<longrightarrow> map f (map g xs) = xs"
  by (induct xs, auto)
    

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
      by (auto intro!: map_ident simp add: wt_step_def)
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


lemma is_type_pTs:
  "\<lbrakk> wf_prog wf_mb G; (C,S,fs,mdecls) \<in> set G; ((mn,pTs),rT,code) \<in> set mdecls \<rbrakk>
  \<Longrightarrow> set pTs \<subseteq> types G"
proof 
  assume "wf_prog wf_mb G" 
         "(C,S,fs,mdecls) \<in> set G"
         "((mn,pTs),rT,code) \<in> set mdecls"
  hence "wf_mdecl wf_mb G C ((mn,pTs),rT,code)"
    by (unfold wf_prog_def wf_cdecl_def) auto  
  hence "\<forall>t \<in> set pTs. is_type G t" 
    by (unfold wf_mdecl_def wf_mhead_def) auto
  moreover
  fix t assume "t \<in> set pTs"
  ultimately
  have "is_type G t" by blast
  thus "t \<in> types G" ..
qed


theorem jvm_lbv_correct:
  "wt_jvm_prog_lbv G Cert \<Longrightarrow> \<exists>Phi. wt_jvm_prog G Phi"
proof -  
  assume wtk: "wt_jvm_prog_lbv G Cert"
  then obtain wf_mb where wf: "wf_prog wf_mb G"
    by (auto simp add: wt_jvm_prog_lbv_def)

  let ?Phi = "\<lambda>C sig. let (C,rT,(maxs,maxl,ins,et)) = the (method (G,C) sig) in 
              SOME phi. wt_method G C (snd sig) rT maxs maxl ins et phi"
    
  from wtk have "wt_jvm_prog G ?Phi"
    apply (unfold wt_jvm_prog_def wt_jvm_prog_lbv_def wf_prog_def wf_cdecl_def)
    apply clarsimp
    apply (drule bspec, assumption)
    apply (unfold wf_mdecl_def)
    apply clarsimp
    apply (drule bspec, assumption)
    apply clarsimp
    apply (frule methd [OF wf], assumption+)
    apply (frule is_type_pTs [OF wf], assumption+)
    apply (drule wt_lbv_wt_method [OF wf])
    apply (auto intro: someI)
    done
  thus ?thesis by blast
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
    by (simp add: wt_method_def2)
  

  have "semilat (JVMType.sl G mxs ?mxr)" ..
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
  have "pres_type ?step (length ins) ?A" ..
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


theorem jvm_lbv_complete:
  "wt_jvm_prog G Phi \<Longrightarrow> wt_jvm_prog_lbv G (prg_cert G Phi)"
proof -
  assume wt: "wt_jvm_prog G Phi"

  then obtain wf_mb where
    wf: "wf_prog wf_mb G"
    by (auto simp add: wt_jvm_prog_def)

  from wt show ?thesis
    apply (unfold wt_jvm_prog_def wt_jvm_prog_lbv_def wf_prog_def wf_cdecl_def)
    apply clarsimp
    apply (drule bspec, assumption)
    apply (unfold wf_mdecl_def)
    apply clarsimp
    apply (drule bspec, assumption)
    apply clarsimp
    apply (frule methd [OF wf], assumption+)
    apply clarify
    apply (frule is_type_pTs [OF wf], assumption+)
    apply (drule wt_method_wt_lbv [OF wf])
    apply (auto simp add: prg_cert_def)
    done  
qed

end
