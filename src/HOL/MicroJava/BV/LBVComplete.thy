(*  Title:      HOL/MicroJava/BV/LBVComplete.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

header {* Completeness of the LBV *}

theory LBVComplete = BVSpec + LBVSpec + StepMono:

constdefs
  contains_targets :: "[instr list, certificate, method_type, p_count] \<Rightarrow> bool"
  "contains_targets ins cert phi pc \<equiv> 
     \<forall>pc' \<in> set (succs (ins!pc) pc). 
      pc' \<noteq> pc+1 \<and> pc' < length ins \<longrightarrow> cert!pc' = phi!pc'"

  fits :: "[instr list, certificate, method_type] \<Rightarrow> bool"
  "fits ins cert phi \<equiv> \<forall>pc. pc < length ins \<longrightarrow> 
                       contains_targets ins cert phi pc \<and>
                       (cert!pc = None \<or> cert!pc = phi!pc)"

  is_target :: "[instr list, p_count] \<Rightarrow> bool" 
  "is_target ins pc \<equiv> 
     \<exists>pc'. pc \<noteq> pc'+1 \<and> pc' < length ins \<and> pc \<in> set (succs (ins!pc') pc')"


constdefs 
  make_cert :: "[instr list, method_type] \<Rightarrow> certificate"
  "make_cert ins phi \<equiv> 
     map (\<lambda>pc. if is_target ins pc then phi!pc else None) [0..length ins(]"

  make_Cert :: "[jvm_prog, prog_type] \<Rightarrow> prog_certificate"
  "make_Cert G Phi \<equiv>  \<lambda> C sig.
     let (C,x,y,mdecls)  = \<epsilon> (Cl,x,y,mdecls). (Cl,x,y,mdecls) \<in> set G \<and> Cl = C;
         (sig,rT,maxl,b) = \<epsilon> (sg,rT,maxl,b). (sg,rT,maxl,b) \<in> set mdecls \<and> sg = sig
     in make_cert b (Phi C sig)"
  

lemmas [simp del] = split_paired_Ex

lemma make_cert_target:
  "[| pc < length ins; is_target ins pc |] ==> make_cert ins phi ! pc = phi!pc"
  by (simp add: make_cert_def)

lemma make_cert_approx:
  "[| pc < length ins; make_cert ins phi ! pc \<noteq> phi ! pc |] ==> 
   make_cert ins phi ! pc = None"
  by (auto simp add: make_cert_def)

lemma make_cert_contains_targets:
  "pc < length ins ==> contains_targets ins (make_cert ins phi) phi pc"
proof (unfold contains_targets_def, intro strip, elim conjE)
 
  fix pc'
  assume "pc < length ins" 
         "pc' \<in> set (succs (ins ! pc) pc)" 
         "pc' \<noteq> pc+1" and
    pc': "pc' < length ins"

  hence "is_target ins pc'" 
    by (auto simp add: is_target_def)

  with pc'
  show "make_cert ins phi ! pc' = phi ! pc'" 
    by (auto intro: make_cert_target)
qed

theorem fits_make_cert:
  "fits ins (make_cert ins phi) phi"
  by (auto dest: make_cert_approx simp add: fits_def make_cert_contains_targets)


lemma fitsD: 
  "[| fits ins cert phi; pc' \<in> set (succs (ins!pc) pc); 
      pc' \<noteq> Suc pc; pc < length ins; pc' < length ins |]
  ==> cert!pc' = phi!pc'"
  by (clarsimp simp add: fits_def contains_targets_def)

lemma fitsD2:
   "[| fits ins cert phi; pc < length ins; cert!pc = Some s |]
  ==> cert!pc = phi!pc"
  by (auto simp add: fits_def)
                           

lemma wtl_inst_mono:
  "[| wtl_inst i G rT s1 cert mpc pc = Ok s1'; fits ins cert phi; 
      pc < length ins;  G \<turnstile> s2 <=' s1; i = ins!pc |] ==>
  \<exists> s2'. wtl_inst (ins!pc) G rT s2 cert mpc pc = Ok s2' \<and> (G \<turnstile> s2' <=' s1')"
proof -
  assume pc:   "pc < length ins" "i = ins!pc"
  assume wtl:  "wtl_inst i G rT s1 cert mpc pc = Ok s1'"
  assume fits: "fits ins cert phi"
  assume G:    "G \<turnstile> s2 <=' s1"
  
  let "?step s" = "step i G s"

  from wtl G
  have app: "app i G rT s2" by (auto simp add: wtl_inst_Ok app_mono)
  
  from wtl G
  have step: "succs i pc \<noteq> [] ==> G \<turnstile> ?step s2 <=' ?step s1" 
    by - (drule step_mono, auto simp add: wtl_inst_Ok)

  {
    fix pc'
    assume 0: "pc' \<in> set (succs i pc)" "pc' \<noteq> pc+1"
    hence "succs i pc \<noteq> []" by auto
    hence "G \<turnstile> ?step s2 <=' ?step s1" by (rule step)
    also 
    from wtl 0
    have "G \<turnstile> ?step s1 <=' cert!pc'"
      by (auto simp add: wtl_inst_Ok) 
    finally
    have "G\<turnstile> ?step s2 <=' cert!pc'" .
  } note cert = this
    
  have "\<exists>s2'. wtl_inst i G rT s2 cert mpc pc = Ok s2' \<and> G \<turnstile> s2' <=' s1'"
  proof (cases "pc+1 \<in> set (succs i pc)")
    case True
    with wtl
    have s1': "s1' = ?step s1" by (simp add: wtl_inst_Ok)

    have "wtl_inst i G rT s2 cert mpc pc = Ok (?step s2) \<and> G \<turnstile> ?step s2 <=' s1'" 
      (is "?wtl \<and> ?G")
    proof
      from True s1'
      show ?G by (auto intro: step)

      from True app wtl
      show ?wtl
        by (clarsimp intro!: cert simp add: wtl_inst_Ok)
    qed
    thus ?thesis by blast
  next
    case False
    with wtl
    have "s1' = cert ! Suc pc" by (simp add: wtl_inst_Ok)

    with False app wtl
    have "wtl_inst i G rT s2 cert mpc pc = Ok s1' \<and> G \<turnstile> s1' <=' s1'"
      by (clarsimp intro!: cert simp add: wtl_inst_Ok)

    thus ?thesis by blast
  qed
  
  with pc show ?thesis by simp
qed


lemma wtl_cert_mono:
  "[| wtl_cert i G rT s1 cert mpc pc = Ok s1'; fits ins cert phi; 
      pc < length ins; G \<turnstile> s2 <=' s1; i = ins!pc |] ==>
  \<exists> s2'. wtl_cert (ins!pc) G rT s2 cert mpc pc = Ok s2' \<and> (G \<turnstile> s2' <=' s1')"
proof -
  assume wtl:  "wtl_cert i G rT s1 cert mpc pc = Ok s1'" and
         fits: "fits ins cert phi" "pc < length ins"
               "G \<turnstile> s2 <=' s1" "i = ins!pc"

  show ?thesis
  proof (cases (open) "cert!pc")
    case None
    with wtl fits
    show ?thesis 
      by - (rule wtl_inst_mono [elimify], (simp add: wtl_cert_def)+)
  next
    case Some
    with wtl fits

    have G: "G \<turnstile> s2 <=' (Some a)"
      by - (rule sup_state_opt_trans, auto simp add: wtl_cert_def split: if_splits)

    from Some wtl
    have "wtl_inst i G rT (Some a) cert mpc pc = Ok s1'" 
      by (simp add: wtl_cert_def split: if_splits)

    with G fits
    have "\<exists> s2'. wtl_inst (ins!pc) G rT (Some a) cert mpc pc = Ok s2' \<and> 
                 (G \<turnstile> s2' <=' s1')"
      by - (rule wtl_inst_mono, (simp add: wtl_cert_def)+)
    
    with Some G
    show ?thesis by (simp add: wtl_cert_def)
  qed
qed

 
lemma wt_instr_imp_wtl_inst:
  "[| wt_instr (ins!pc) G rT phi max_pc pc; fits ins cert phi;
      pc < length ins; length ins = max_pc |] ==> 
  wtl_inst (ins!pc) G rT (phi!pc) cert max_pc pc \<noteq> Err"
 proof -
  assume wt:   "wt_instr (ins!pc) G rT phi max_pc pc" 
  assume fits: "fits ins cert phi"
  assume pc:   "pc < length ins" "length ins = max_pc"

  from wt 
  have app: "app (ins!pc) G rT (phi!pc)" by (simp add: wt_instr_def)

  from wt pc
  have pc': "\<And>pc'. pc' \<in> set (succs (ins!pc) pc) ==> pc' < length ins"
    by (simp add: wt_instr_def)

  let ?s' = "step (ins!pc) G (phi!pc)"

  from wt fits pc
  have cert: "!!pc'. \<lbrakk>pc' \<in> set (succs (ins!pc) pc); pc' < max_pc; pc' \<noteq> pc+1\<rbrakk> 
    \<Longrightarrow> G \<turnstile> ?s' <=' cert!pc'"
    by (auto dest: fitsD simp add: wt_instr_def)     

  from app pc cert pc'
  show ?thesis
    by (auto simp add: wtl_inst_Ok)
qed

lemma wt_less_wtl:
  "[| wt_instr (ins!pc) G rT phi max_pc pc; 
      wtl_inst (ins!pc) G rT (phi!pc) cert max_pc pc = Ok s;
      fits ins cert phi; Suc pc < length ins; length ins = max_pc |] ==> 
  G \<turnstile> s <=' phi ! Suc pc"
proof -
  assume wt:   "wt_instr (ins!pc) G rT phi max_pc pc" 
  assume wtl:  "wtl_inst (ins!pc) G rT (phi!pc) cert max_pc pc = Ok s"
  assume fits: "fits ins cert phi"
  assume pc:   "Suc pc < length ins" "length ins = max_pc"

  { assume suc: "Suc pc \<in> set (succs (ins ! pc) pc)"
    with wtl         have "s = step (ins!pc) G (phi!pc)"
      by (simp add: wtl_inst_Ok)
    also from suc wt have "G \<turnstile> ... <=' phi!Suc pc"
      by (simp add: wt_instr_def)
    finally have ?thesis .
  }

  moreover
  { assume "Suc pc \<notin> set (succs (ins ! pc) pc)"
    
    with wtl
    have "s = cert!Suc pc" 
      by (simp add: wtl_inst_Ok)
    with fits pc
    have ?thesis
      by - (cases "cert!Suc pc", simp, drule fitsD2, assumption+, simp)
  }

  ultimately
  show ?thesis by blast
qed
  

lemma wt_instr_imp_wtl_cert:
  "[| wt_instr (ins!pc) G rT phi max_pc pc; fits ins cert phi;
      pc < length ins; length ins = max_pc |] ==> 
  wtl_cert (ins!pc) G rT (phi!pc) cert max_pc pc \<noteq> Err"
proof -
  assume "wt_instr (ins!pc) G rT phi max_pc pc" and 
   fits: "fits ins cert phi" and
     pc: "pc < length ins" and
         "length ins = max_pc"
  
  hence wtl: "wtl_inst (ins!pc) G rT (phi!pc) cert max_pc pc \<noteq> Err"
    by (rule wt_instr_imp_wtl_inst)

  hence "cert!pc = None ==> ?thesis"
    by (simp add: wtl_cert_def)

  moreover
  { fix s
    assume c: "cert!pc = Some s"
    with fits pc
    have "cert!pc = phi!pc"
      by (rule fitsD2)
    from this c wtl
    have ?thesis
      by (clarsimp simp add: wtl_cert_def)
  }

  ultimately
  show ?thesis by blast
qed
  

lemma wt_less_wtl_cert:
  "[| wt_instr (ins!pc) G rT phi max_pc pc; 
      wtl_cert (ins!pc) G rT (phi!pc) cert max_pc pc = Ok s;
      fits ins cert phi; Suc pc < length ins; length ins = max_pc |] ==> 
  G \<turnstile> s <=' phi ! Suc pc"
proof -
  assume wtl: "wtl_cert (ins!pc) G rT (phi!pc) cert max_pc pc = Ok s"

  assume wti: "wt_instr (ins!pc) G rT phi max_pc pc"
              "fits ins cert phi" 
              "Suc pc < length ins" "length ins = max_pc"
  
  { assume "cert!pc = None"
    with wtl
    have "wtl_inst (ins!pc) G rT (phi!pc) cert max_pc pc = Ok s"
      by (simp add: wtl_cert_def)
    with wti
    have ?thesis
      by - (rule wt_less_wtl)
  }
  moreover
  { fix t
    assume c: "cert!pc = Some t"
    with wti
    have "cert!pc = phi!pc"
      by - (rule fitsD2, simp+)
    with c wtl
    have "wtl_inst (ins!pc) G rT (phi!pc) cert max_pc pc = Ok s"
      by (simp add: wtl_cert_def)
    with wti
    have ?thesis
      by - (rule wt_less_wtl)
  }   
    
  ultimately
  show ?thesis by blast
qed


text {*
  \medskip
  Main induction over the instruction list.
*}

theorem wt_imp_wtl_inst_list:
"\<forall> pc. (\<forall>pc'. pc' < length all_ins \<longrightarrow> 
        wt_instr (all_ins ! pc') G rT phi (length all_ins) pc') \<longrightarrow>
       fits all_ins cert phi \<longrightarrow> 
       (\<exists>l. pc = length l \<and> all_ins = l@ins) \<longrightarrow>  
       pc < length all_ins \<longrightarrow>      
       (\<forall> s. (G \<turnstile> s <=' (phi!pc)) \<longrightarrow> 
             wtl_inst_list ins G rT cert (length all_ins) pc s \<noteq> Err)" 
(is "\<forall>pc. ?wt \<longrightarrow> ?fits \<longrightarrow> ?l pc ins \<longrightarrow> ?len pc \<longrightarrow> ?wtl pc ins"  
 is "\<forall>pc. ?C pc ins" is "?P ins") 
proof (induct "?P" "ins")
  case Nil
  show "?P []" by simp
next
  fix i ins'
  assume Cons: "?P ins'"

  show "?P (i#ins')" 
  proof (intro allI impI, elim exE conjE)
    fix pc s l
    assume wt  : "\<forall>pc'. pc' < length all_ins \<longrightarrow> 
                        wt_instr (all_ins ! pc') G rT phi (length all_ins) pc'"
    assume fits: "fits all_ins cert phi"
    assume l   : "pc < length all_ins"
    assume G   : "G \<turnstile> s <=' phi ! pc"
    assume pc  : "all_ins = l@i#ins'" "pc = length l"
    hence  i   : "all_ins ! pc = i"
      by (simp add: nth_append)

    from l wt
    have wti: "wt_instr (all_ins!pc) G rT phi (length all_ins) pc" by blast

    with fits l 
    have c: "wtl_cert (all_ins!pc) G rT (phi!pc) cert (length all_ins) pc \<noteq> Err"
      by - (drule wt_instr_imp_wtl_cert, auto)
    
    from Cons
    have "?C (Suc pc) ins'" by blast
    with wt fits pc
    have IH: "?len (Suc pc) \<longrightarrow> ?wtl (Suc pc) ins'" by auto

    show "wtl_inst_list (i#ins') G rT cert (length all_ins) pc s \<noteq> Err" 
    proof (cases "?len (Suc pc)")
      case False
      with pc
      have "ins' = []" by simp
      with G i c fits l
      show ?thesis by (auto dest: wtl_cert_mono)
    next
      case True
      with IH
      have wtl: "?wtl (Suc pc) ins'" by blast

      from c wti fits l True
      obtain s'' where
        "wtl_cert (all_ins!pc) G rT (phi!pc) cert (length all_ins) pc = Ok s''"
        "G \<turnstile> s'' <=' phi ! Suc pc"
        by clarsimp (drule wt_less_wtl_cert, auto)
      moreover
      from calculation fits G l
      obtain s' where
        c': "wtl_cert (all_ins!pc) G rT s cert (length all_ins) pc = Ok s'" and
        "G \<turnstile> s' <=' s''"
        by - (drule wtl_cert_mono, auto)
      ultimately
      have G': "G \<turnstile> s' <=' phi ! Suc pc" 
        by - (rule sup_state_opt_trans)

      with wtl
      have "wtl_inst_list ins' G rT cert (length all_ins) (Suc pc) s' \<noteq> Err"
        by auto

      with i c'
      show ?thesis by auto
    qed
  qed
qed
  

lemma fits_imp_wtl_method_complete:
  "[| wt_method G C pTs rT mxl ins phi; fits ins cert phi |] ==> 
  wtl_method G C pTs rT mxl ins cert"
by (simp add: wt_method_def wtl_method_def)
   (rule wt_imp_wtl_inst_list [rulify, elimify], auto simp add: wt_start_def) 


lemma wtl_method_complete:
  "wt_method G C pTs rT mxl ins phi ==> 
  wtl_method G C pTs rT mxl ins (make_cert ins phi)"
proof -
  assume "wt_method G C pTs rT mxl ins phi" 
  moreover
  have "fits ins (make_cert ins phi) phi"
    by (rule fits_make_cert)
  ultimately
  show ?thesis 
    by (rule fits_imp_wtl_method_complete)
qed

lemma unique_set:
"(a,b,c,d)\<in>set l \<longrightarrow> unique l \<longrightarrow> (a',b',c',d') \<in> set l \<longrightarrow> 
  a = a' \<longrightarrow> b=b' \<and> c=c' \<and> d=d'"
  by (induct "l") auto

lemma unique_epsilon:
  "(a,b,c,d)\<in>set l \<longrightarrow> unique l \<longrightarrow> 
  (\<epsilon> (a',b',c',d'). (a',b',c',d') \<in> set l \<and> a'=a) = (a,b,c,d)"
  by (auto simp add: unique_set)


theorem wtl_complete: 
  "wt_jvm_prog G Phi ==> wtl_jvm_prog G (make_Cert G Phi)"
proof (simp only: wt_jvm_prog_def)

  assume wfprog: 
    "wf_prog (\<lambda>G C (sig,rT,maxl,b). wt_method G C (snd sig) rT maxl b (Phi C sig)) G"

  thus ?thesis 
  proof (simp add: wtl_jvm_prog_def wf_prog_def wf_cdecl_def wf_mdecl_def, auto)
    fix a aa ab b ac ba ad ae bb 
    assume 1 : "\<forall>(C,sc,fs,ms)\<in>set G.
             Ball (set fs) (wf_fdecl G) \<and>
             unique fs \<and>
             (\<forall>(sig,rT,mb)\<in>set ms. wf_mhead G sig rT \<and> 
               (\<lambda>(maxl,b). wt_method G C (snd sig) rT maxl b (Phi C sig)) mb) \<and>
             unique ms \<and>
             (case sc of None \<Rightarrow> C = Object
              | Some D \<Rightarrow>
                  is_class G D \<and>
                  (D, C) \<notin> (subcls1 G)^* \<and>
                  (\<forall>(sig,rT,b)\<in>set ms. 
                   \<forall>D' rT' b'. method (G, D) sig = Some (D', rT', b') \<longrightarrow> G\<turnstile>rT\<preceq>rT'))"
             "(a, aa, ab, b) \<in> set G"
  
    assume uG : "unique G" 
    assume b  : "((ac, ba), ad, ae, bb) \<in> set b"

    from 1
    show "wtl_method G a ba ad ae bb (make_Cert G Phi a (ac, ba))"
    proof (rule bspec [elimify], clarsimp)
      assume ub : "unique b"
      assume m: "\<forall>(sig,rT,mb)\<in>set b. wf_mhead G sig rT \<and> 
                  (\<lambda>(maxl,b). wt_method G a (snd sig) rT maxl b (Phi a sig)) mb" 
      from m b
      show ?thesis
      proof (rule bspec [elimify], clarsimp)
        assume "wt_method G a ba ad ae bb (Phi a (ac, ba))"         
        with wfprog uG ub b 1
        show ?thesis
          by - (rule wtl_method_complete [elimify], assumption+, 
                simp add: make_Cert_def unique_epsilon)
      qed 
    qed
  qed
qed

lemmas [simp] = split_paired_Ex

end
