(*  Title:      HOL/MicroJava/BV/LBVComplete.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

header {* Completeness of the LBV *}

theory LBVComplete = BVSpec + LBVSpec + StepMono:


constdefs
  is_approx :: "['a option list, 'a list] \<Rightarrow> bool"
  "is_approx a b \<equiv> length a = length b \<and> (\<forall> n. n < length a \<longrightarrow>
                   (a!n = None \<or> a!n = Some (b!n)))"
  
  contains_dead :: "[instr list, certificate, method_type, p_count] \<Rightarrow> bool"
  "contains_dead ins cert phi pc \<equiv>
     Suc pc \<notin> succs (ins!pc) pc \<and> Suc pc < length phi \<longrightarrow>
     cert ! (Suc pc) = Some (phi ! Suc pc)"

  contains_targets :: "[instr list, certificate, method_type, p_count] \<Rightarrow> bool"
  "contains_targets ins cert phi pc \<equiv> (
     \<forall> pc' \<in> succs (ins!pc) pc. pc' \<noteq> Suc pc \<and> pc' < length phi \<longrightarrow> 
     cert!pc' = Some (phi!pc'))" 


  fits :: "[instr list, certificate, method_type] \<Rightarrow> bool"
  "fits ins cert phi \<equiv> is_approx cert phi \<and> length ins < length phi \<and>
                            (\<forall> pc. pc < length ins \<longrightarrow>
                                   contains_dead ins cert phi pc \<and> 
                                   contains_targets ins cert phi pc)"

  is_target :: "[instr list, p_count] \<Rightarrow> bool" 
  "is_target ins pc \<equiv> \<exists> pc'. pc' < length ins \<and> pc \<in> succs (ins!pc') pc'"

  maybe_dead :: "[instr list, p_count] \<Rightarrow> bool"
  "maybe_dead ins pc \<equiv> \<exists> pc'. pc = pc'+1 \<and> pc \<notin> succs (ins!pc') pc'"

  mdot :: "[instr list, p_count] \<Rightarrow> bool"
  "mdot ins pc \<equiv> maybe_dead ins pc \<or> is_target ins pc"


consts
  option_filter_n :: "['a list, nat \<Rightarrow> bool, nat] \<Rightarrow> 'a option list"
primrec 
  "option_filter_n []    P n = []"  
  "option_filter_n (h#t) P n = (if (P n) then Some h # option_filter_n t P (n+1) 
                                         else None   # option_filter_n t P (n+1))"  
  
constdefs 
  option_filter :: "['a list, nat \<Rightarrow> bool] \<Rightarrow> 'a option list" 
  "option_filter l P \<equiv> option_filter_n l P 0" 
  
  make_cert :: "[instr list, method_type] \<Rightarrow> certificate"
  "make_cert ins phi \<equiv> option_filter phi (mdot ins)"
  
  make_Cert :: "[jvm_prog, prog_type] \<Rightarrow> prog_certificate"
  "make_Cert G Phi \<equiv>  \<lambda> C sig.
    let (C,x,y,mdecls) = \<epsilon> (Cl,x,y,mdecls). (Cl,x,y,mdecls) \<in> set G \<and> Cl = C in
      let (sig,rT,maxl,b) = \<epsilon> (sg,rT,maxl,b). (sg,rT,maxl,b) \<in> set mdecls \<and> sg = sig in
        make_cert b (Phi C sig)"
  

lemmas [simp del] = split_paired_Ex

lemma length_ofn [rulify]: "\<forall>n. length (option_filter_n l P n) = length l"
  by (induct l) auto


lemma is_approx_option_filter: "is_approx (option_filter l P) l" 
proof -
  {
    fix a n
    have "\<forall>n. is_approx (option_filter_n a P n) a" (is "?P a")
    proof (induct a)
      show "?P []" by (auto simp add: is_approx_def)
    
      fix l ls
      assume Cons: "?P ls"
    
      show "?P (l#ls)"
      proof (unfold is_approx_def, intro allI conjI impI)
        fix n
        show "length (option_filter_n (l # ls) P n) = length (l # ls)" 
          by (simp only: length_ofn)
      
        fix m
        assume "m < length (option_filter_n (l # ls) P n)"
        hence m: "m < Suc (length ls)" by (simp only: length_ofn) simp
      
        show "option_filter_n (l # ls) P n ! m = None \<or>
              option_filter_n (l # ls) P n ! m = Some ((l # ls) ! m)" 
        proof (cases "m")
          assume "m = 0"
          with m show ?thesis by simp
        next
          fix m' assume Suc: "m = Suc m'"
          from Cons
          show ?thesis
          proof (unfold is_approx_def, elim allE impE conjE)
            from m Suc
            show "m' < length (option_filter_n ls P (Suc n))" by (simp add: length_ofn)
          
            assume "option_filter_n ls P (Suc n) ! m' = None \<or> 
                    option_filter_n ls P (Suc n) ! m' = Some (ls ! m')"
            with m Suc
            show ?thesis by auto
          qed
        qed
      qed
    qed
  }
  
  thus ?thesis    
    by (auto simp add: option_filter_def)
qed

lemma option_filter_Some:
"\<lbrakk>n < length l; P n\<rbrakk> \<Longrightarrow> option_filter l P ! n = Some (l!n)"
proof -
  
  assume 1: "n < length l" "P n"

  have "\<forall>n n'. n < length l \<longrightarrow> P (n+n') \<longrightarrow>  option_filter_n l P n' ! n = Some (l!n)"
    (is "?P l")
  proof (induct l)
    show "?P []" by simp

    fix l ls assume Cons: "?P ls"
    show "?P (l#ls)"
    proof (intro)
      fix n n'
      assume l: "n < length (l # ls)"
      assume P: "P (n + n')"
      show "option_filter_n (l # ls) P n' ! n = Some ((l # ls) ! n)"
      proof (cases "n")
        assume "n=0"
        with P show ?thesis by simp
      next
        fix m assume "n = Suc m"
        with l P Cons
        show ?thesis by simp
      qed
    qed
  qed

  with 1
  show ?thesis by (auto simp add: option_filter_def)
qed

lemma option_filter_contains_dead:
"contains_dead ins (option_filter phi (mdot ins)) phi pc" 
  by (auto intro: option_filter_Some simp add: contains_dead_def mdot_def maybe_dead_def)

lemma option_filter_contains_targets:
"pc < length ins \<Longrightarrow> contains_targets ins (option_filter phi (mdot ins)) phi pc"
proof (unfold contains_targets_def, clarsimp)
 
  fix pc'
  assume "pc < length ins" 
         "pc' \<in> succs (ins ! pc) pc" 
         "pc' \<noteq> Suc pc" and
    pc': "pc' < length phi"

  hence "is_target ins pc'" by (auto simp add: is_target_def)

  with pc'
  show "option_filter phi (mdot ins) ! pc' = Some (phi ! pc')"
    by (auto intro: option_filter_Some simp add: mdot_def)
qed
  

lemma fits_make_cert:
  "length ins < length phi \<Longrightarrow> fits ins (make_cert ins phi) phi"
proof -
  assume l: "length ins < length phi"

  thus "fits ins (make_cert ins phi) phi"
  proof (unfold fits_def make_cert_def, intro conjI allI impI)
    show "is_approx (option_filter phi (mdot ins)) phi" 
      by (rule is_approx_option_filter)

    show "length ins < length phi" .

    fix pc
    show "contains_dead ins (option_filter phi (mdot ins)) phi pc" 
      by (rule option_filter_contains_dead)
    
    assume "pc < length ins" 
    thus "contains_targets ins (option_filter phi (mdot ins)) phi pc" 
      by (rule option_filter_contains_targets)
  qed
qed

lemma fitsD: 
"\<lbrakk>fits ins cert phi; pc' \<in> succs (ins!pc) pc; pc' \<noteq> Suc pc; pc < length ins; pc' < length ins\<rbrakk> 
  \<Longrightarrow> cert!pc' = Some (phi!pc')"
by (clarsimp simp add: fits_def contains_dead_def contains_targets_def)

lemma fitsD2:
"\<lbrakk>fits ins cert phi; Suc pc \<notin> succs (ins!pc) pc;  pc < length ins\<rbrakk> 
  \<Longrightarrow> cert ! Suc pc = Some (phi ! Suc pc)"
by (clarsimp simp add: fits_def contains_dead_def contains_targets_def)


lemma wtl_inst_mono:
"\<lbrakk>wtl_inst i G rT s1 s1' cert mpc pc; fits ins cert phi; pc < length ins; 
  G \<turnstile> s2 <=s s1; i = ins!pc\<rbrakk> \<Longrightarrow> 
 \<exists> s2'. wtl_inst (ins!pc) G rT s2 s2' cert mpc pc \<and> (G \<turnstile> s2' <=s s1')"
proof -
  assume pc:   "pc < length ins" "i = ins!pc"
  assume wtl:  "wtl_inst i G rT s1 s1' cert mpc pc"
  assume fits: "fits ins cert phi"
  assume G:    "G \<turnstile> s2 <=s s1"
  
  let "?step s" = "step (i, G, s)"

  from wtl G
  have app: "app (i, G, rT, s2)" by (auto simp add: wtl_inst_def app_mono)
  
  from wtl G
  have step: "succs i pc \<noteq> {} \<Longrightarrow> G \<turnstile> the (?step s2) <=s the (?step s1)" 
    by - (drule step_mono, auto simp add: wtl_inst_def)
  
  with app
  have some: "succs i pc \<noteq> {} \<Longrightarrow> ?step s2 \<noteq> None" by (simp add: app_step_some)

  {
    fix pc'
    assume 0: "pc' \<in> succs i pc" "pc' \<noteq> pc+1"
    hence "succs i pc \<noteq> {}" by auto
    hence "G \<turnstile> the (?step s2) <=s the (?step s1)" by (rule step)
    also 
    from wtl 0
    have "G \<turnstile> the (?step s1) <=s the (cert!pc')"
      by (auto simp add: wtl_inst_def) 
    finally
    have "G\<turnstile> the (?step s2) <=s the (cert!pc')" .
  } note cert = this
    
  have "\<exists>s2'. wtl_inst i G rT s2 s2' cert mpc pc \<and> G \<turnstile> s2' <=s s1'"
  proof (cases "pc+1 \<in> succs i pc")
    case True
    with wtl
    have s1': "s1' = the (?step s1)" by (simp add: wtl_inst_def)

    have "wtl_inst i G rT s2 (the (?step s2)) cert mpc pc \<and> G \<turnstile> (the (?step s2)) <=s s1'" 
      (is "?wtl \<and> ?G")
    proof
      from True s1'
      show ?G by (auto intro: step)

      from True app wtl
      show ?wtl
        by (clarsimp intro!: cert simp add: wtl_inst_def)
    qed
    thus ?thesis by blast
  next
    case False
    with wtl
    have "s1' = the (cert ! Suc pc)" by (simp add: wtl_inst_def)

    with False app wtl
    have "wtl_inst i G rT s2 s1' cert mpc pc \<and> G \<turnstile> s1' <=s s1'"
      by (clarsimp intro!: cert simp add: wtl_inst_def)

    thus ?thesis by blast
  qed
  
  with pc show ?thesis by simp
qed
    

lemma wtl_option_mono:
"\<lbrakk>wtl_inst_option i G rT s1 s1' cert mpc pc; fits ins cert phi; 
  pc < length ins; G \<turnstile> s2 <=s s1; i = ins!pc\<rbrakk> \<Longrightarrow> 
 \<exists> s2'. wtl_inst_option (ins!pc) G rT s2 s2' cert mpc pc \<and> (G \<turnstile> s2' <=s s1')"
proof -
  assume wtl:  "wtl_inst_option i G rT s1 s1' cert mpc pc" and
         fits: "fits ins cert phi" "pc < length ins"
               "G \<turnstile> s2 <=s s1" "i = ins!pc"

  show ?thesis
  proof (cases (open) "cert!pc")
    case None
    with wtl fits
    show ?thesis 
      by - (rule wtl_inst_mono [elimify], (simp add: wtl_inst_option_def)+)
  next
    case Some
    with wtl fits

    have G: "G \<turnstile> s2 <=s a"
     by - (rule sup_state_trans, (simp add: wtl_inst_option_def)+)

    from Some wtl
    have "wtl_inst i G rT a s1' cert mpc pc" by (simp add: wtl_inst_option_def)

    with G fits
    have "\<exists> s2'. wtl_inst (ins!pc) G rT a s2' cert mpc pc \<and> (G \<turnstile> s2' <=s s1')"
      by - (rule wtl_inst_mono, (simp add: wtl_inst_option_def)+)
    
    with Some G
    show ?thesis by (simp add: wtl_inst_option_def)
  qed
qed


    
lemma wt_instr_imp_wtl_inst:
"\<lbrakk>wt_instr (ins!pc) G rT phi max_pc pc; fits ins cert phi;
  pc < length ins; length ins = max_pc\<rbrakk> \<Longrightarrow> 
  \<exists> s. wtl_inst (ins!pc) G rT (phi!pc) s cert max_pc pc \<and> G \<turnstile> s <=s phi ! Suc pc"
proof -
  assume wt:   "wt_instr (ins!pc) G rT phi max_pc pc" 
  assume fits: "fits ins cert phi"
  assume pc:   "pc < length ins" "length ins = max_pc"

  from wt 
  have app: "app (ins!pc, G, rT, phi!pc)" by (simp add: wt_instr_def)

  from wt pc
  have pc': "!!pc'. pc' \<in> succs (ins!pc) pc \<Longrightarrow> pc' < length ins"
    by (simp add: wt_instr_def)

  let ?s' = "the (step (ins!pc,G, phi!pc))"

  from wt
  have G: "!!pc'. pc' \<in> succs (ins!pc) pc \<Longrightarrow> G \<turnstile> ?s' <=s phi ! pc'"
    by (simp add: wt_instr_def)

  from wt fits pc
  have cert: "!!pc'. \<lbrakk>pc' \<in> succs (ins!pc) pc; pc' < max_pc; pc' \<noteq> pc+1\<rbrakk> 
    \<Longrightarrow> cert!pc' \<noteq> None \<and> G \<turnstile> ?s' <=s the (cert!pc')"
    by (auto dest: fitsD simp add: wt_instr_def)

  show ?thesis
  proof (cases "pc+1 \<in> succs (ins!pc) pc")
    case True

    have "wtl_inst (ins!pc) G rT (phi!pc) ?s' cert max_pc pc \<and> G \<turnstile> ?s' <=s phi ! Suc pc" (is "?wtl \<and> ?G")
    proof 
      from True
      show "G \<turnstile> ?s' <=s phi ! Suc pc"  by (simp add: G)

      from True fits app pc cert pc'
      show "?wtl"
        by (auto simp add: wtl_inst_def)
    qed

    thus ?thesis by blast
    
  next    
    let ?s'' = "the (cert ! Suc pc)"

    case False
    with fits app pc cert pc'
    have "wtl_inst (ins ! pc) G rT (phi ! pc) ?s'' cert max_pc pc \<and> G \<turnstile> ?s'' <=s phi ! Suc pc" 
      by (auto dest: fitsD2 simp add: wtl_inst_def)

    thus ?thesis by blast
  qed
qed

  
lemma wt_instr_imp_wtl_option:
"\<lbrakk>fits ins cert phi; pc < length ins; wt_instr (ins!pc) G rT phi max_pc pc;  max_pc = length ins\<rbrakk> \<Longrightarrow> 
 \<exists> s. wtl_inst_option (ins!pc) G rT (phi!pc) s cert max_pc pc \<and> G \<turnstile> s <=s phi ! Suc pc"
proof -
  assume fits : "fits ins cert phi" "pc < length ins" 
         and "wt_instr (ins!pc) G rT phi max_pc pc" 
             "max_pc = length ins"

  hence * : "\<exists> s. wtl_inst (ins!pc) G rT (phi!pc) s cert max_pc pc \<and> G \<turnstile> s <=s phi ! Suc pc"
    by - (rule wt_instr_imp_wtl_inst, simp+)
  
  show ?thesis
  proof (cases "cert ! pc")
    case None
    with *
    show ?thesis by (simp add: wtl_inst_option_def)

  next
    case Some

    from fits 
    have "pc < length phi" by (clarsimp simp add: fits_def)
    with fits Some
    have "cert ! pc = Some (phi!pc)" by (auto simp add: fits_def is_approx_def)
     
    with * 
    show ?thesis by (simp add: wtl_inst_option_def)
  qed
qed


text {*
  \medskip
  Main induction over the instruction list.
*}

theorem wt_imp_wtl_inst_list:
"\<forall> pc. (\<forall>pc'. pc' < length all_ins \<longrightarrow> wt_instr (all_ins ! pc') G rT phi (length all_ins) pc') \<longrightarrow>   
       fits all_ins cert phi \<longrightarrow> 
       (\<exists>l. pc = length l \<and> all_ins = l@ins) \<longrightarrow>  
       pc < length all_ins \<longrightarrow>      
       (\<forall> s. (G \<turnstile> s <=s (phi!pc)) \<longrightarrow> 
             (\<exists>s'. wtl_inst_list ins G rT s s' cert (length all_ins) pc))" 
(is "\<forall>pc. ?wt \<longrightarrow> ?fits \<longrightarrow> ?l pc ins \<longrightarrow> ?len pc \<longrightarrow> ?wtl pc ins" is "\<forall>pc. ?C pc ins" is "?P ins") 
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
    assume G   : "G \<turnstile> s <=s phi ! pc"
    assume l   : "pc < length all_ins"

    assume pc  : "all_ins = l@i#ins'" "pc = length l"
    hence  i   : "all_ins ! pc = i"
      by (simp add: nth_append)

    from l wt
    have "wt_instr (all_ins!pc) G rT phi (length all_ins) pc" by blast

    with fits l 
    obtain s1 where
          "wtl_inst_option (all_ins!pc) G rT (phi!pc) s1 cert (length all_ins) pc" and
      s1: "G \<turnstile> s1 <=s phi ! (Suc pc)"
      by - (drule wt_instr_imp_wtl_option, assumption+, simp, elim exE conjE, simp) 
    
    with fits l
    obtain s2 where
      o:  "wtl_inst_option (all_ins!pc) G rT s s2 cert (length all_ins) pc" 
      and "G \<turnstile> s2 <=s s1"
      by - (drule wtl_option_mono, assumption+, simp, elim exE conjE, rule that) 

    with s1
    have G': "G \<turnstile> s2 <=s phi ! (Suc pc)"
      by - (rule sup_state_trans, auto)

    from Cons
    have "?C (Suc pc) ins'" by blast
    with wt fits pc
    have IH: "?len (Suc pc) \<longrightarrow> ?wtl (Suc pc) ins'" by auto

    show "\<exists>s'. wtl_inst_list (i#ins') G rT s s' cert (length all_ins) pc"
    proof (cases "?len (Suc pc)")
      case False
      with pc
      have "ins' = []" by simp
      with i o 
      show ?thesis by auto
    next
      case True
      with IH
      have "?wtl (Suc pc) ins'" by blast
      with G'
      obtain s' where
        "wtl_inst_list ins' G rT s2 s' cert (length all_ins) (Suc pc)"
        by - (elim allE impE, auto)        
      with i o
      show ?thesis by auto
    qed
  qed
qed
  

lemma fits_imp_wtl_method_complete:
"\<lbrakk>wt_method G C pTs rT mxl ins phi; fits ins cert phi; wf_prog wf_mb G\<rbrakk> 
  \<Longrightarrow> wtl_method G C pTs rT mxl ins cert"
by (simp add: wt_method_def wtl_method_def)
   (rule wt_imp_wtl_inst_list [rulify, elimify], auto simp add: wt_start_def) 


lemma wtl_method_complete:
"\<lbrakk>wt_method G C pTs rT mxl ins phi; wf_prog wf_mb G\<rbrakk> 
  \<Longrightarrow> wtl_method G C pTs rT mxl ins (make_cert ins phi)"
proof -
  assume * : "wt_method G C pTs rT mxl ins phi" "wf_prog wf_mb G"
  
  hence "fits ins (make_cert ins phi) phi"
    by - (rule fits_make_cert, simp add: wt_method_def)

  with *
  show ?thesis by - (rule fits_imp_wtl_method_complete)
qed

lemma unique_set:
"(a,b,c,d)\<in>set l \<longrightarrow> unique l \<longrightarrow> (a',b',c',d') \<in> set l \<longrightarrow> a = a' \<longrightarrow> b=b' \<and> c=c' \<and> d=d'"
  by (induct "l") auto

lemma unique_epsilon:
"(a,b,c,d)\<in>set l \<longrightarrow> unique l \<longrightarrow> (\<epsilon> (a',b',c',d'). (a',b',c',d') \<in> set l \<and> a'=a) = (a,b,c,d)"
  by (auto simp add: unique_set)


theorem wtl_complete: "\<lbrakk>wt_jvm_prog G Phi\<rbrakk> \<Longrightarrow> wtl_jvm_prog G (make_Cert G Phi)"
proof (simp only: wt_jvm_prog_def)

  assume wfprog: "wf_prog (\<lambda>G C (sig,rT,maxl,b). wt_method G C (snd sig) rT maxl b (Phi C sig)) G"

  thus ?thesis 
  proof (simp add: wtl_jvm_prog_def wf_prog_def wf_cdecl_def wf_mdecl_def, auto)
    fix a aa ab b ac ba ad ae bb 
    assume 1 : "\<forall>(C,sc,fs,ms)\<in>set G.
             Ball (set fs) (wf_fdecl G) \<and>
             unique fs \<and>
             (\<forall>(sig,rT,mb)\<in>set ms. wf_mhead G sig rT \<and> (\<lambda>(maxl,b). wt_method G C (snd sig) rT maxl b (Phi C sig)) mb) \<and>
             unique ms \<and>
             (case sc of None \<Rightarrow> C = Object
              | Some D \<Rightarrow>
                  is_class G D \<and>
                  (D, C) \<notin> (subcls1 G)^* \<and>
                  (\<forall>(sig,rT,b)\<in>set ms. \<forall>D' rT' b'. method (G, D) sig = Some (D', rT', b') \<longrightarrow> G\<turnstile>rT\<preceq>rT'))"
             "(a, aa, ab, b) \<in> set G"
  
    assume uG : "unique G" 
    assume b  : "((ac, ba), ad, ae, bb) \<in> set b"

    from 1
    show "wtl_method G a ba ad ae bb (make_Cert G Phi a (ac, ba))"
    proof (rule bspec [elimify], clarsimp)
      assume ub : "unique b"
      assume m: "\<forall>(sig,rT,mb)\<in>set b. wf_mhead G sig rT \<and> (\<lambda>(maxl,b). wt_method G a (snd sig) rT maxl b (Phi a sig)) mb" 
      from m b
      show ?thesis
      proof (rule bspec [elimify], clarsimp)
        assume "wt_method G a ba ad ae bb (Phi a (ac, ba))"         
        with wfprog uG ub b 1
        show ?thesis
          by - (rule wtl_method_complete [elimify], assumption+, simp add: make_Cert_def unique_epsilon)
      qed 
    qed
  qed
qed

lemmas [simp] = split_paired_Ex

end
