(*  Title:      HOL/MicroJava/BV/JVM.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM
*)

header {* \isaheader{Kildall for the JVM}\label{sec:JVM} *}

theory JVM = Kildall_Lift + JVMType + EffectMono + BVSpec:


constdefs
  check_bounded :: "instr list \<Rightarrow> exception_table \<Rightarrow> bool"
  "check_bounded ins et \<equiv> (\<forall>pc < length ins. \<forall>pc' \<in> set (succs (ins!pc) pc). pc' < length ins) \<and>
                          (\<forall>e \<in> set et. fst (snd (snd e)) < length ins)"

  exec :: "jvm_prog \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> exception_table \<Rightarrow> instr list \<Rightarrow> state step_type"
  "exec G maxs rT et bs == 
  err_step (size bs) (\<lambda>pc. app (bs!pc) G maxs rT pc et) (\<lambda>pc. eff (bs!pc) G pc et)"

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
  Lemmas for Kildall instantiation
*}

lemma check_bounded_is_bounded:
  "check_bounded ins et \<Longrightarrow> bounded (\<lambda>pc. eff (ins!pc) G pc et) (length ins)"
  apply (unfold bounded_def eff_def)
  apply clarify
  apply simp
  apply (unfold check_bounded_def)
  apply clarify
  apply (erule disjE)
   apply blast
  apply (erule allE, erule impE, assumption)
  apply (unfold xcpt_eff_def)
  apply clarsimp    
  apply (drule xcpt_names_in_et)
  apply clarify
  apply (drule bspec, assumption)
  apply simp
  done
   

lemma special_ex_swap_lemma [iff]: 
  "(? X. (? n. X = A n & P n) & Q X) = (? n. Q(A n) & P n)"
  by blast

lemmas [iff del] = not_None_eq

theorem exec_pres_type:
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

theorem semilat_JVM_slI:
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


theorem wt_kil_correct:
  "\<lbrakk> wt_kil G C pTs rT maxs mxl et bs; wf_prog wf_mb G; 
      is_class G C; \<forall>x \<in> set pTs. is_type G x \<rbrakk>
  \<Longrightarrow> \<exists>phi. wt_method G C pTs rT maxs mxl bs et phi"
proof -
  let ?start = "OK (Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err)))
                #(replicate (size bs - 1) (OK None))"

  assume wf:      "wf_prog wf_mb G"
  assume isclass: "is_class G C"
  assume istype:  "\<forall>x \<in> set pTs. is_type G x"

  assume "wt_kil G C pTs rT maxs mxl et bs"
  then obtain maxr r where    
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
    
  { fix l x have "set (replicate l x) \<subseteq> {x}" by (cases "0 < l") simp+
  } note subset_replicate = this
  from istype have "set pTs \<subseteq> types G" by auto
  hence "OK ` set pTs \<subseteq> err (types G)" by auto
  with instrs maxr isclass 
  have "?start \<in> list (length bs) (states G maxs maxr)"
    apply (unfold list_def JVM_states_unfold)
    apply simp
    apply (rule conjI)
     apply (simp add: Un_subset_iff)
     apply (rule_tac B = "{Err}" in subset_trans)
      apply (simp add: subset_replicate)
     apply simp
    apply (rule_tac B = "{OK None}" in subset_trans)
     apply (simp add: subset_replicate)
    apply simp
    done
  with bcv success result have 
    "\<exists>ts\<in>list (length bs) (states G maxs maxr).
         ?start <=[JVMType.le G maxs maxr] ts \<and>
         wt_step (JVMType.le G maxs maxr) Err (exec G maxs rT et bs) ts"
    by (unfold is_bcv_def) auto
  then obtain phi' where
    l: "phi' \<in> list (length bs) (states G maxs maxr)" and
    s: "?start <=[JVMType.le G maxs maxr] phi'" and
    w: "wt_step (JVMType.le G maxs maxr) Err (exec G maxs rT et bs) phi'"
    by blast
  hence wt_err_step:
    "wt_err_step (sup_state_opt G) (exec G maxs rT et bs) phi'"
    by (simp add: wt_err_step_def exec_def JVM_le_Err_conv)

  from s have le: "JVMType.le G maxs maxr (?start ! 0) (phi'!0)"
    by (drule_tac p=0 in le_listD) (simp add: lesub_def)+

  from l have l: "size phi' = size bs" by simp  
  with instrs w have "phi' ! 0 \<noteq> Err" by (unfold wt_step_def) simp
  with instrs l have phi0: "OK (map ok_val phi' ! 0) = phi' ! 0"
    by (clarsimp simp add: not_Err_eq)

  from l bounded 
  have "bounded (\<lambda>pc. eff (bs!pc) G pc et) (length phi')"
    by (simp add: exec_def check_bounded_is_bounded)  
  hence bounded': "bounded (exec G maxs rT et bs) (length bs)"
    by (auto intro: bounded_lift simp add: exec_def l)
  with wt_err_step
  have "wt_app_eff (sup_state_opt G) (\<lambda>pc. app (bs!pc) G maxs rT pc et) 
                   (\<lambda>pc. eff (bs!pc) G pc et) (map ok_val phi')"
    by (auto intro: wt_err_imp_wt_app_eff simp add: l exec_def)
  with instrs l le bounded'
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
  "\<lbrakk> wt_method G C pTs rT maxs mxl bs et phi; wf_prog wf_mb G; 
     check_bounded bs et; length phi = length bs; is_class G C; 
      \<forall>x \<in> set pTs. is_type G x;
      map OK phi \<in> list (length bs) (states G maxs (1+size pTs+mxl)) \<rbrakk>
  \<Longrightarrow> wt_kil G C pTs rT maxs mxl et bs"
proof -
  assume wf: "wf_prog wf_mb G"  
  assume isclass: "is_class G C"
  assume istype: "\<forall>x \<in> set pTs. is_type G x"
  assume length: "length phi = length bs"
  assume istype_phi: "map OK phi \<in> list (length bs) (states G maxs (1+size pTs+mxl))"
  assume bounded: "check_bounded bs et"

  assume "wt_method G C pTs rT maxs mxl bs et phi"
  then obtain
    instrs:   "0 < length bs" and
    wt_start: "wt_start G C pTs mxl phi" and
    wt_ins:   "\<forall>pc. pc < length bs \<longrightarrow> 
                    wt_instr (bs ! pc) G rT phi maxs (length bs) et pc"
    by (unfold wt_method_def) simp

  let ?eff  = "\<lambda>pc. eff (bs!pc) G pc et"
  let ?app   = "\<lambda>pc. app (bs!pc) G maxs rT pc et"

  from bounded
  have bounded_exec: "bounded (exec G maxs rT et bs) (size bs)"
    by (unfold exec_def) (intro bounded_lift check_bounded_is_bounded)
 
  from wt_ins
  have "wt_app_eff (sup_state_opt G) ?app ?eff phi"
    apply (unfold wt_app_eff_def wt_instr_def lesub_def)
    apply (simp (no_asm) only: length)
    apply blast
    done
  with bounded_exec
  have "wt_err_step (sup_state_opt G) (err_step (size phi) ?app ?eff) (map OK phi)"
    by - (erule wt_app_eff_imp_wt_err,simp add: exec_def length)
  hence wt_err:
    "wt_err_step (sup_state_opt G) (exec G maxs rT et bs) (map OK phi)"
    by (unfold exec_def) (simp add: length)
 
  let ?maxr = "1+size pTs+mxl"
  from wf bounded_exec
  have is_bcv: 
    "is_bcv (JVMType.le G maxs ?maxr) Err (exec G maxs rT et bs) 
            (size bs) (states G maxs ?maxr) (kiljvm G maxs ?maxr rT et bs)"
    by (rule is_bcv_kiljvm)

  let ?start = "OK (Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err)))
                #(replicate (size bs - 1) (OK None))"

  { fix l x have "set (replicate l x) \<subseteq> {x}" by (cases "0 < l") simp+
  } note subset_replicate = this

  from istype have "set pTs \<subseteq> types G" by auto
  hence "OK ` set pTs \<subseteq> err (types G)" by auto
  with instrs isclass have start:
    "?start \<in> list (length bs) (states G maxs ?maxr)"
    apply (unfold list_def JVM_states_unfold)
    apply simp
    apply (rule conjI)
     apply (simp add: Un_subset_iff)
     apply (rule_tac B = "{Err}" in subset_trans)
      apply (simp add: subset_replicate)
     apply simp
    apply (rule_tac B = "{OK None}" in subset_trans)
     apply (simp add: subset_replicate)
    apply simp
    done

  let ?phi = "map OK phi"  
  have less_phi: "?start <=[JVMType.le G maxs ?maxr] ?phi"
  proof -
    from length instrs
    have "length ?start = length (map OK phi)" by simp
    moreover
    { fix n
      from wt_start
      have "G \<turnstile> ok_val (?start!0) <=' phi!0"
        by (simp add: wt_start_def)
      moreover
      from instrs length
      have "0 < length phi" by simp
      ultimately
      have "JVMType.le G maxs ?maxr (?start!0) (?phi!0)"
        by (simp add: JVM_le_Err_conv Err.le_def lesub_def)
      moreover
      { fix n'
        have "JVMType.le G maxs ?maxr (OK None) (?phi!n)"
          by (auto simp add: JVM_le_Err_conv Err.le_def lesub_def 
            split: err.splits)        
        hence "\<lbrakk> n = Suc n'; n < length ?start \<rbrakk> 
          \<Longrightarrow> JVMType.le G maxs ?maxr (?start!n) (?phi!n)"
          by simp
      }
      ultimately
      have "n < length ?start \<Longrightarrow> (?start!n) <=_(JVMType.le G maxs ?maxr) (?phi!n)"
        by (unfold lesub_def) (cases n, blast+)
    } 
    ultimately show ?thesis by (rule le_listI)
  qed         

  from wt_err
  have "wt_step (JVMType.le G maxs ?maxr) Err (exec G maxs rT et bs) ?phi"
    by (simp add: wt_err_step_def JVM_le_Err_conv)  
  with start istype_phi less_phi is_bcv
  have "\<forall>p. p < length bs \<longrightarrow> kiljvm G maxs ?maxr rT et bs ?start ! p \<noteq> Err"
    by (unfold is_bcv_def) auto
  with bounded instrs
  show "wt_kil G C pTs rT maxs mxl et bs" by (unfold wt_kil_def) simp
qed
text {*
  The above theorem @{text wt_kil_complete} is all nice'n shiny except
  for one assumption: @{term "map OK phi \<in> list (length bs) (states G maxs (1+size pTs+mxl))"}  
  It does not hold for all @{text phi} that satisfy @{text wt_method}.

  The assumption states mainly that all entries in @{text phi} are legal
  types in the program context, that the stack size is bounded by @{text maxs},
  and that the register sizes are exactly @{term "1+size pTs+mxl"}. 
  The BV specification, i.e.~@{text wt_method}, only gives us this
  property for \emph{reachable} code. For unreachable code, 
  e.g.~unused registers may contain arbitrary garbage. Even the stack
  and register sizes can be different from the rest of the program (as 
  long as they are consistent inside each chunk of unreachable code).
  
  All is not lost, though: for each @{text phi} that satisfies 
  @{text wt_method} there is a @{text phi'} that also satisfies 
  @{text wt_method} and that additionally satisfies our assumption.
  The construction is quite easy: the entries for reachable code
  are the same in @{text phi} and @{text phi'}, the entries for
  unreachable code are all @{text None} in @{text phi'} (as it would
  be produced by Kildall's algorithm). 

  Although this is proved easily by comment, it requires some more
  overhead (i.e.~talking about reachable instructions) if you try
  it the hard way. Thus it is missing here for the time being.

  The other direction (@{text wt_kil_correct}) can be lifted to
  programs without problems:
*}
lemma is_type_pTs:
  "\<lbrakk> wf_prog wf_mb G; (C,S,fs,mdecls) \<in> set G; (sig,rT,code) \<in> set mdecls; 
      t \<in> set (snd sig) \<rbrakk>
  \<Longrightarrow> is_type G t"
proof -
  assume "wf_prog wf_mb G" 
         "(C,S,fs,mdecls) \<in> set G"
         "(sig,rT,code) \<in> set mdecls"
  hence "wf_mdecl wf_mb G C (sig,rT,code)"
    by (unfold wf_prog_def wf_cdecl_def) auto
  hence "\<forall>t \<in> set (snd sig). is_type G t" 
    by (unfold wf_mdecl_def wf_mhead_def) auto
  moreover
  assume "t \<in> set (snd sig)"
  ultimately
  show ?thesis by blast
qed


theorem jvm_kildall_correct:
  "wt_jvm_prog_kildall G \<Longrightarrow> \<exists>Phi. wt_jvm_prog G Phi"
proof -  
  assume wtk: "wt_jvm_prog_kildall G"

  then obtain wf_mb where
    wf: "wf_prog wf_mb G"
    by (auto simp add: wt_jvm_prog_kildall_def)

  let ?Phi = "\<lambda>C sig. let (C,rT,(maxs,maxl,ins,et)) = the (method (G,C) sig) in 
              SOME phi. wt_method G C (snd sig) rT maxs maxl ins et phi"
   
  { fix C S fs mdecls sig rT code
    assume "(C,S,fs,mdecls) \<in> set G" "(sig,rT,code) \<in> set mdecls"
    with wf
    have "method (G,C) sig = Some (C,rT,code) \<and> is_class G C \<and> (\<forall>t \<in> set (snd sig). is_type G t)"
      by (simp add: methd is_type_pTs)
  } note this [simp]
 
  from wtk
  have "wt_jvm_prog G ?Phi"
    apply (unfold wt_jvm_prog_def wt_jvm_prog_kildall_def wf_prog_def wf_cdecl_def)
    apply clarsimp
    apply (drule bspec, assumption)
    apply (unfold wf_mdecl_def)
    apply clarsimp
    apply (drule bspec, assumption)
    apply clarsimp
    apply (drule wt_kil_correct [OF _ wf])
    apply (auto intro: someI)
    done

  thus ?thesis by blast
qed


end
