(*  Title:      HOL/BCV/JVM.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

*)

header "Kildall for the JVM"

theory JVM = Kildall + JType + Opt + Product + DFA_err + StepMono + BVSpec:

types state = "state_type option err"

constdefs
 stk_esl :: "'c prog => nat => ty list esl"
"stk_esl S maxs == upto_esl maxs (JType.esl S)"

 reg_sl :: "'c prog => nat => ty err list sl"
"reg_sl S maxr == Listn.sl maxr (Err.sl (JType.esl S))"

 sl :: "'c prog => nat => nat => state sl"
"sl S maxs maxr ==
 Err.sl(Opt.esl(Product.esl (stk_esl S maxs) (Err.esl(reg_sl S maxr))))"

 states :: "'c prog => nat => nat => state set"
"states S maxs maxr == fst(sl S maxs maxr)"

 le :: "'c prog => nat => nat => state ord"
"le S maxs maxr == fst(snd(sl S maxs maxr))"

 sup :: "'c prog => nat => nat => state binop"
"sup S maxs maxr == snd(snd(sl S maxs maxr))"


constdefs
  exec :: "jvm_prog \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  "exec G maxs rT bs == err_step (\<lambda>pc. app (bs!pc) G maxs rT) (\<lambda>pc. step (bs!pc) G)"

  kiljvm :: "jvm_prog => nat => nat => ty => instr list => state list => state list"
  "kiljvm G maxs maxr rT bs ==
  kildall (sl G maxs maxr) (exec G maxs rT bs) (\<lambda>pc. succs (bs!pc) pc)"

  wt_kil :: "jvm_prog \<Rightarrow> cname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> instr list \<Rightarrow> bool"
  "wt_kil G C pTs rT mxs mxl ins ==
   bounded (\<lambda>n. succs (ins!n) n) (size ins) \<and> 0 < size ins \<and> 
   (let first  = Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err));
        start  = OK first#(replicate (size ins-1) (OK None));
        result = kiljvm G mxs (1+size pTs+mxl) rT ins start
    in \<forall>n < size ins. result!n \<noteq> Err)"

  wt_jvm_prog_kildall :: "jvm_prog => bool"
  "wt_jvm_prog_kildall G ==
  wf_prog (\<lambda>G C (sig,rT,(maxs,maxl,b)). wt_kil G C (snd sig) rT maxs maxl b) G"

lemma JVM_states_unfold: 
  "states S maxs maxr == err(opt((Union {list n (types S) |n. n <= maxs}) <*>
                                  list maxr (err(types S))))"
  apply (unfold states_def JVM.sl_def Opt.esl_def Err.sl_def
         stk_esl_def reg_sl_def Product.esl_def
         Listn.sl_def upto_esl_def JType.esl_def Err.esl_def)
  by simp


lemma JVM_le_unfold:
 "le S m n == 
  Err.le(Opt.le(Product.le(Listn.le(subtype S))(Listn.le(Err.le(subtype S)))))" 
  apply (unfold JVM.le_def JVM.sl_def Opt.esl_def Err.sl_def
         stk_esl_def reg_sl_def Product.esl_def  
         Listn.sl_def upto_esl_def JType.esl_def Err.esl_def) 
  by simp


lemma Err_convert:
  "Err.le (subtype G) a b = G \<turnstile> a <=o b"
  by (auto simp add: Err.le_def sup_ty_opt_def lift_top_def lesub_def subtype_def
           split: err.split)

lemma loc_convert:
  "Listn.le (Err.le (subtype G)) a b = G \<turnstile> a <=l b"
  by (unfold Listn.le_def lesub_def sup_loc_def list_all2_def)
     (simp add: Err_convert)

lemma zip_map [rule_format]:
  "\<forall>a. length a = length b --> zip (map f a) (map g b) = map (\<lambda>(x,y). (f x, g y)) (zip a b)"
  apply (induct b) 
   apply simp
  apply clarsimp
  apply (case_tac aa)
  apply simp+
  done

lemma stk_convert:
  "Listn.le (subtype G) a b = G \<turnstile> map OK a <=l map OK b"
proof 
  assume "Listn.le (subtype G) a b"

  hence le: "list_all2 (subtype G) a b"
    by (unfold Listn.le_def lesub_def)
  
  { fix x' y'
    assume "length a = length b"
           "(x',y') \<in> set (zip (map OK a) (map OK b))"
    then
    obtain x y where OK:
      "x' = OK x" "y' = OK y" "(x,y) \<in> set (zip a b)"
      by (auto simp add: zip_map)
    with le
    have "subtype G x y"
      by (simp add: list_all2_def Ball_def)
    with OK
    have "G \<turnstile> x' <=o y'"
      by (simp add: subtype_def)
  }
  
  with le
  show "G \<turnstile> map OK a <=l map OK b"
    by (auto simp add: sup_loc_def list_all2_def)
next
  assume "G \<turnstile> map OK a <=l map OK b"

  thus "Listn.le (subtype G) a b"
    apply (unfold sup_loc_def list_all2_def Listn.le_def lesub_def)
    apply (clarsimp simp add: zip_map subtype_def)
    apply (drule bspec, assumption)
    apply auto
    done
qed


lemma state_conv:
  "Product.le (Listn.le (subtype G)) (Listn.le (Err.le (subtype G))) a b = G \<turnstile> a <=s b"
  by (unfold Product.le_def lesub_def sup_state_def)
     (simp add: split_beta stk_convert loc_convert)

lemma state_opt_conv:
  "Opt.le (Product.le (Listn.le (subtype G)) (Listn.le (Err.le (subtype G)))) a b = G \<turnstile> a <=' b"
  by (unfold Opt.le_def lesub_def sup_state_opt_def lift_bottom_def)
     (auto simp add: state_conv split: option.split)

lemma JVM_le_convert:
  "le G m n (OK t1) (OK t2) = G \<turnstile> t1 <=' t2"
  by (simp add: JVM_le_unfold Err.le_def lesub_def state_opt_conv)

lemma JVM_le_Err_conv:
  "le G m n = Err.le (sup_state_opt G)"
  apply (simp add: expand_fun_eq)
  apply (unfold Err.le_def JVM_le_unfold lesub_def)
  apply (clarsimp split: err.splits)
  apply (simp add: state_opt_conv)
  done

lemma special_ex_swap_lemma [iff]: 
  "(? X. (? n. X = A n & P n) & Q X) = (? n. Q(A n) & P n)"
  by blast

lemmas [iff del] = not_None_eq

theorem exec_pres_type:
  "[| wf_prog wf_mb S |] ==> 
      pres_type (exec S maxs rT bs) (size bs) (states S maxs maxr)"
 apply (unfold pres_type_def list_def step_def JVM_states_unfold)
 apply (clarify elim!: option_map_in_optionI lift_in_errI)
 apply (simp add: exec_def err_step_def lift_def split: err.split)
 apply (simp add: step_def option_map_def split: option.splits)  
 apply clarify
 apply (case_tac "bs!p")

 apply fastsimp
 apply fastsimp
 apply fastsimp
 apply fastsimp
 apply fastsimp
 apply clarsimp
 defer
 apply fastsimp
 apply fastsimp
 apply clarsimp
 defer
 apply fastsimp
 apply fastsimp
 apply fastsimp
 apply fastsimp
 apply fastsimp
 apply fastsimp
 apply fastsimp
 apply fastsimp
 apply fastsimp
 defer

 (* Invoke *)
 apply (simp add: Un_subset_iff)
 apply (drule method_wf_mdecl, assumption+)
 apply (simp add: wf_mdecl_def wf_mhead_def)

 (* Getfield *)
 apply (rule_tac fn = "(vname,cname)" in fields_is_type)
 defer
 apply assumption+
 apply (simp add: field_def)
 apply (drule map_of_SomeD)
 apply (rule map_of_SomeI)
 apply (auto simp add: unique_fields)
 done


lemmas [iff] = not_None_eq


theorem exec_mono:
  "wf_prog wf_mb G ==>
  mono (JVM.le G maxs maxr) (exec G maxs rT bs) (size bs) (states G maxs maxr)"
  apply (unfold mono_def)
  apply clarify
  apply (unfold lesub_def)
  apply (case_tac t)
   apply (simp add: JVM_le_unfold Err.le_def exec_def err_step_def lift_def)
  apply (case_tac s)
   apply (simp add: JVM_le_unfold Err.le_def exec_def err_step_def lift_def)
  apply (simp add: JVM_le_convert exec_def err_step_def lift_def)
  apply (simp add: JVM_le_unfold Err.le_def exec_def err_step_def lift_def)
  apply (rule conjI)
   apply clarify
   apply (rule step_mono, assumption+)
  apply (rule impI)
  apply (erule contrapos_nn)
  apply (rule app_mono, assumption+)
  done

theorem semilat_JVM_slI:
  "[| wf_prog wf_mb G |] ==> semilat(sl G maxs maxr)"
  apply (unfold JVM.sl_def stk_esl_def reg_sl_def)
  apply (rule semilat_opt)
  apply (rule err_semilat_Product_esl)
  apply (rule err_semilat_upto_esl)
  apply (rule err_semilat_JType_esl, assumption+)
  apply (rule err_semilat_eslI)
  apply (rule semilat_Listn_sl)
  apply (rule err_semilat_JType_esl, assumption+)  
  done

lemma sl_triple_conv:
  "sl G maxs maxr == 
  (states G maxs maxr, le G maxs maxr, sup G maxs maxr)"
  by (simp (no_asm) add: states_def JVM.le_def JVM.sup_def)


ML_setup {* bind_thm ("wf_subcls1", wf_subcls1); *}

theorem is_bcv_kiljvm:
  "[| wf_prog wf_mb G; bounded (\<lambda>pc. succs (bs!pc) pc) (size bs) |] ==> 
      is_bcv (JVM.le G maxs maxr) Err (exec G maxs rT bs) (\<lambda>pc. succs (bs!pc) pc)
             (size bs) (states G maxs maxr) (kiljvm G maxs maxr rT bs)"
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
  apply (erule exec_mono)
  done


theorem wt_kil_correct:
  "[| wt_kil G C pTs rT maxs mxl bs; wf_prog wf_mb G; 
      is_class G C; \<forall>x \<in> set pTs. is_type G x |]
  ==> \<exists>phi. wt_method G C pTs rT maxs mxl bs phi"
proof -
  let ?start = "OK (Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err)))
                #(replicate (size bs-1) (OK None))"

  assume wf:      "wf_prog wf_mb G"
  assume isclass: "is_class G C"
  assume istype:  "\<forall>x \<in> set pTs. is_type G x"

  assume "wt_kil G C pTs rT maxs mxl bs"
  then obtain maxr r where    
    bounded: "bounded (\<lambda>pc. succs (bs!pc) pc) (size bs)" and
    result:  "r = kiljvm G maxs maxr rT bs ?start" and
    success: "\<forall>n < size bs. r!n \<noteq> Err" and
    instrs:  "0 < size bs" and
    maxr:    "maxr = Suc (length pTs + mxl)" 
    by (unfold wt_kil_def) simp

  { fix pc
    have "succs (bs!pc) pc \<noteq> []"
      by (cases "bs!pc") auto
  }

  hence non_empty: "non_empty (\<lambda>pc. succs (bs!pc) pc)"
    by (unfold non_empty_def) blast

  from wf bounded
  have bcv:
    "is_bcv (le G maxs maxr) Err (exec G maxs rT bs) (\<lambda>pc. succs (bs!pc) pc)
            (size bs) (states G maxs maxr) (kiljvm G maxs maxr rT bs)"
    by (rule is_bcv_kiljvm)

  { fix l x
    have "set (replicate l x) \<subseteq> {x}"
      by (cases "0 < l") simp+
  } note subset_replicate = this

  from istype
  have "set pTs \<subseteq> types G"
    by auto

  hence "OK `` set pTs \<subseteq> err (types G)"
    by auto

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

  with bcv success result 
  have 
    "\<exists>ts\<in>list (length bs) (states G maxs maxr).
         ?start <=[le G maxs maxr] ts \<and>
         welltyping (JVM.le G maxs maxr) Err (JVM.exec G maxs rT bs) (\<lambda>pc. succs (bs ! pc) pc) ts"
    by (unfold is_bcv_def) auto

  then obtain phi' where
    l: "phi' \<in> list (length bs) (states G maxs maxr)" and
    s: "?start <=[le G maxs maxr] phi'" and
    w: "welltyping (le G maxs maxr) Err (exec G maxs rT bs) (\<lambda>pc. succs (bs ! pc) pc) phi'"
    by blast
   
  hence dynamic:
    "dynamic_wt (sup_state_opt G) (exec G maxs rT bs) (\<lambda>pc. succs (bs ! pc) pc) phi'"
    by (simp add: dynamic_wt_def exec_def JVM_le_Err_conv)

  from s
  have le: "le G maxs maxr (?start ! 0) (phi'!0)"    
    by (drule_tac p=0 in le_listD) (simp add: lesub_def)+

  from l
  have l: "size phi' = size bs"
    by simp
  
  with instrs w
  have "phi' ! 0 \<noteq> Err"
    by (unfold welltyping_def) simp

  with instrs l
  have phi0: "OK (map ok_val phi' ! 0) = phi' ! 0"
    by clarsimp

  from l bounded
  have "bounded (\<lambda>pc. succs (bs ! pc) pc) (length phi')"
    by simp

  with dynamic non_empty
  have "static_wt (sup_state_opt G) (\<lambda>pc. app (bs!pc) G maxs rT) (\<lambda>pc. step (bs!pc) G) 
                                    (\<lambda>pc. succs (bs!pc) pc) (map ok_val phi')"
    by (auto intro: dynamic_imp_static simp add: exec_def)

  with instrs l le bounded
  have "wt_method G C pTs rT maxs mxl bs (map ok_val phi')"
    apply (unfold wt_method_def static_wt_def)
    apply simp
    apply (rule conjI)
     apply (unfold wt_start_def)
     apply (rule JVM_le_convert [THEN iffD1])
     apply (simp (no_asm) add: phi0)
    apply clarify
    apply (erule allE, erule impE, assumption)
    apply (elim conjE)
    apply (clarsimp simp add: lesub_def wt_instr_def)
    apply (unfold bounded_def)
    apply blast    
    done

  thus ?thesis by blast
qed


(* there's still two nontrivial (but provable) "sorry"s in here  *)
theorem wt_kil_complete:
  "[| wt_method G C pTs rT maxs mxl bs phi; wf_prog wf_mb G; 
      length phi = length bs; is_class G C; \<forall>x \<in> set pTs. is_type G x |]
  ==> wt_kil G C pTs rT maxs mxl bs"
proof -
  assume wf:      "wf_prog wf_mb G"  
  assume isclass: "is_class G C"
  assume istype:  "\<forall>x \<in> set pTs. is_type G x"
  assume length:  "length phi = length bs"

  assume "wt_method G C pTs rT maxs mxl bs phi"
  then obtain
    instrs:   "0 < length bs" and
    wt_start: "wt_start G C pTs mxl phi" and
    wt_ins:   "\<forall>pc. pc < length bs \<longrightarrow> 
                    wt_instr (bs ! pc) G rT phi maxs (length bs) pc"
    by (unfold wt_method_def) simp

  let ?succs = "\<lambda>pc. succs (bs!pc) pc"
  let ?step  = "\<lambda>pc. step (bs!pc) G"
  let ?app   = "\<lambda>pc. app (bs!pc) G maxs rT"

  from wt_ins
  have bounded: "bounded ?succs (size bs)"
    by (unfold wt_instr_def bounded_def) blast

  from wt_ins
  have "static_wt (sup_state_opt G) ?app ?step ?succs phi"
    apply (unfold static_wt_def wt_instr_def lesub_def)
    apply (simp (no_asm) only: length)
    apply blast
    done

  with bounded
  have "dynamic_wt (sup_state_opt G) (err_step ?app ?step) ?succs (map OK phi)"
    by - (erule static_imp_dynamic, simp add: length)

  hence dynamic:
    "dynamic_wt (sup_state_opt G) (exec G maxs rT bs) ?succs (map OK phi)"
    by (unfold exec_def)
 
  let ?maxr = "1+size pTs+mxl"

  from wf bounded
  have is_bcv: 
    "is_bcv (JVM.le G maxs ?maxr) Err (exec G maxs rT bs) ?succs 
            (size bs) (states G maxs ?maxr) (kiljvm G maxs ?maxr rT bs)"
    by (rule is_bcv_kiljvm)

  let ?start = "OK (Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err)))
                #(replicate (size bs-1) (OK None))"

  { fix l x
    have "set (replicate l x) \<subseteq> {x}"
      by (cases "0 < l") simp+
  } note subset_replicate = this

  from istype
  have "set pTs \<subseteq> types G"
    by auto

  hence "OK `` set pTs \<subseteq> err (types G)"
    by auto

  with instrs isclass 
  have start:
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

  have 1: "?phi \<in> list (length bs) (states G maxs ?maxr)" sorry

  from wt_start
  have 2: "?start <=[le G maxs ?maxr] ?phi" sorry

  from dynamic
  have "welltyping (le G maxs ?maxr) Err (exec G maxs rT bs) ?succs ?phi"
    by (simp add: dynamic_wt_def JVM_le_Err_conv)
  
  with start 1 2 is_bcv
  have "\<forall>p. p < length bs \<longrightarrow> kiljvm G maxs ?maxr rT bs ?start ! p \<noteq> Err"
    by (unfold is_bcv_def) blast

  with bounded instrs
  show "wt_kil G C pTs rT maxs mxl bs"
    by (unfold wt_kil_def) simp
qed

lemma is_type_pTs:
  "[| wf_prog wf_mb G; (C,S,fs,mdecls) \<in> set G; (sig,rT,code) \<in> set mdecls; 
      t \<in> set (snd sig) |]
  ==> is_type G t"
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
  "wt_jvm_prog_kildall G ==> \<exists>Phi. wt_jvm_prog G Phi"
proof -  
  assume wtk: "wt_jvm_prog_kildall G"

  then obtain wf_mb where
    wf: "wf_prog wf_mb G"
    by (auto simp add: wt_jvm_prog_kildall_def)

  let ?Phi = "\<lambda>C sig. let (C,rT,(maxs,maxl,ins)) = the (method (G,C) sig) in 
              SOME phi. wt_method G C (snd sig) rT maxs maxl ins phi"
   
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
