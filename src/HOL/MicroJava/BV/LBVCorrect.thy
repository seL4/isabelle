(*  Title:      HOL/MicroJava/BV/BVLCorrect.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* Correctness of the LBV *}

(* This theory is currently broken. The port to exceptions
  didn't make it into the Isabelle 2001 release. It is included for 
  documentation only. See Isabelle 99-2 for a working copy of this
  theory. *)


theory LBVCorrect = BVSpec + LBVSpec:

lemmas [simp del] = split_paired_Ex split_paired_All

constdefs
fits :: "[method_type,instr list,jvm_prog,ty,state_type option,nat,nat,exception_table,certificate] => bool"
"fits phi is G rT s0 maxs maxr et cert == 
  (\<forall>pc s1. pc < length is -->
    (wtl_inst_list (take pc is) G rT cert maxs maxr (length is) et 0 s0 = OK s1 -->
    (case cert!pc of None   => phi!pc = s1
                   | Some t => phi!pc = Some t)))"

constdefs
make_phi :: "[instr list,jvm_prog,ty,state_type option,nat,nat,exception_table,certificate] => method_type"
"make_phi is G rT s0 maxs maxr et cert == 
   map (\<lambda>pc. case cert!pc of 
               None   => ok_val (wtl_inst_list (take pc is) G rT cert maxs maxr (length is) et 0 s0) 
             | Some t => Some t) [0..length is(]"


lemma fitsD_None:
  "[|fits phi is G rT s0 mxs mxr et cert; pc < length is;
    wtl_inst_list (take pc is) G rT cert mxs mxr (length is) et 0 s0 = OK s1; 
    cert ! pc = None|] ==> phi!pc = s1"
  by (auto simp add: fits_def)

lemma fitsD_Some:
  "[|fits phi is G rT s0 mxs mxr et cert; pc < length is;
    wtl_inst_list (take pc is) G rT cert mxs mxr (length is) et 0 s0 = OK s1; 
    cert ! pc = Some t|] ==> phi!pc = Some t"
  by (auto simp add: fits_def)

lemma make_phi_Some:
  "[| pc < length is; cert!pc = Some t |] ==> 
  make_phi is G rT s0 mxs mxr et cert ! pc = Some t"
  by (simp add: make_phi_def)

lemma make_phi_None:
  "[| pc < length is; cert!pc = None |] ==> 
  make_phi is G rT s0 mxs mxr et cert ! pc = 
  ok_val (wtl_inst_list (take pc is) G rT cert mxs mxr (length is) et 0 s0)"
  by (simp add: make_phi_def)

lemma exists_phi:
  "\<exists>phi. fits phi is G rT s0 mxs mxr et cert"  
proof - 
  have "fits (make_phi is G rT s0 mxs mxr et cert) is G rT s0 mxs mxr et cert"
    by (auto simp add: fits_def make_phi_Some make_phi_None 
             split: option.splits) 
  thus ?thesis by fast
qed
  
lemma fits_lemma1:
  "[| wtl_inst_list is G rT cert mxs mxr (length is) et 0 s = OK s'; fits phi is G rT s mxs mxr et cert |]
  ==> \<forall>pc t. pc < length is --> cert!pc = Some t --> phi!pc = Some t"
proof (intro strip)
  fix pc t 
  assume "wtl_inst_list is G rT cert mxs mxr (length is) et 0 s = OK s'"
  then obtain s'' where
    "wtl_inst_list (take pc is) G rT cert mxs mxr (length is) et 0 s = OK s''"
    by (blast dest: wtl_take)
  moreover
  assume "fits phi is G rT s mxs mxr et cert" 
         "pc < length is" 
         "cert ! pc = Some t"
  ultimately
  show "phi!pc = Some t" by (auto dest: fitsD_Some)
qed


lemma wtl_suc_pc:
 "[| wtl_inst_list is G rT cert mxs mxr (length is) et 0 s \<noteq> Err;
     wtl_inst_list (take pc is) G rT cert mxs mxr (length is) et 0 s = OK s';
     wtl_cert (is!pc) G rT s' cert mxs mxr (length is) et pc = OK s'';
     fits phi is G rT s mxs mxr et cert; Suc pc < length is |] ==>
  G \<turnstile> s'' <=' phi ! Suc pc"
proof -
  
  assume all:  "wtl_inst_list is G rT cert mxs mxr (length is) et 0 s \<noteq> Err"
  assume fits: "fits phi is G rT s mxs mxr et cert"

  assume wtl:  "wtl_inst_list (take pc is) G rT cert mxs mxr (length is) et 0 s = OK s'" and
         wtc:  "wtl_cert (is!pc) G rT s' cert mxs mxr (length is) et pc = OK s''" and
         pc:   "Suc pc < length is"

  hence wts: 
    "wtl_inst_list (take (Suc pc) is) G rT cert mxs mxr (length is) et 0 s = OK s''"
    by (rule wtl_Suc)

  from all
  have app: 
  "wtl_inst_list (take (Suc pc) is@drop (Suc pc) is) G rT cert mxs mxr (length is) et 0 s \<noteq> Err"
    by simp

  from pc 
  have "0 < length (drop (Suc pc) is)" 
    by simp
  then obtain l ls where
    "drop (Suc pc) is = l#ls"
    by (auto simp add: neq_Nil_conv simp del: length_drop)
  with app wts pc
  obtain x where 
    "wtl_cert l G rT s'' cert mxs mxr (length is) et (Suc pc) = OK x"
    by (auto simp add: wtl_append min_def simp del: append_take_drop_id)

  hence c1: "!!t. cert!Suc pc = Some t ==> G \<turnstile> s'' <=' cert!Suc pc"
    by (simp add: wtl_cert_def split: split_if_asm)
  moreover
  from fits pc wts
  have c2: "!!t. cert!Suc pc = Some t ==> phi!Suc pc = cert!Suc pc"
    by - (drule fitsD_Some, auto)
  moreover
  from fits pc wts
  have c3: "cert!Suc pc = None ==> phi!Suc pc = s''"
    by (rule fitsD_None)
  ultimately
  show ?thesis by (cases "cert!Suc pc", auto)
qed


lemma wtl_fits_wt:
  "[| wtl_inst_list is G rT cert mxs mxr (length is) et 0 s \<noteq> Err; 
      fits phi is G rT s mxs mxr et cert; pc < length is |] ==>
   wt_instr (is!pc) G rT phi mxs (length is) et pc"
proof -
  assume fits: "fits phi is G rT s mxs mxr et cert"
  assume pc:  "pc < length is" and
         wtl: "wtl_inst_list is G rT cert mxs mxr (length is) et 0 s \<noteq> Err"        
  then obtain s' s'' where
    w: "wtl_inst_list (take pc is) G rT cert mxs mxr (length is) et 0 s = OK s'" and
    c: "wtl_cert (is!pc) G rT s' cert mxs mxr (length is) et pc = OK s''"
    by - (drule wtl_all, auto)

  from fits wtl pc have cert_Some: 
    "!!t pc. [| pc < length is; cert!pc = Some t |] ==> phi!pc = Some t"
    by (auto dest: fits_lemma1)
  
  from fits wtl pc have cert_None: "cert!pc = None ==> phi!pc = s'"
    by - (drule fitsD_None)
  
  from pc c cert_None cert_Some
  have wti: "wtl_inst (is ! pc) G rT (phi!pc) cert mxs mxr (length is) et pc = OK s''"
    by (auto simp add: wtl_cert_def split: split_if_asm option.splits)

  -- "we now must show that @{text wt_instr} holds; the definition 
      of @{text wt_instr} is: @{thm [display] wt_instr_def[no_vars]}"

  { fix pc' r
    assume pc': "(pc',r) \<in> set (eff (is!pc) G pc et (phi!pc))"

    with wti have less: "pc' < length is" by (simp add: wtl_inst_OK) blast

    have "G \<turnstile> r <=' phi ! pc'" 
    proof (cases "pc' = Suc pc")
      case False          
      with wti pc'
      have G: "G \<turnstile> r <=' cert ! pc'" by (simp add: wtl_inst_OK) blast
      hence "cert!pc' = None ==> r = None" by simp
      hence "cert!pc' = None ==> ?thesis" by simp
      moreover {
        fix t assume "cert!pc' = Some t"
        with less have "phi!pc' = cert!pc'" by (simp add: cert_Some)
        with G have ?thesis by simp
      }
      ultimately show ?thesis by blast      
    next
      case True
      with pc' wti
      have "G \<turnstile> r <=' s''"  sorry
      also
      from wtl w fits c pc 
      have "Suc pc < length is ==> G \<turnstile> s'' <=' phi ! Suc pc" 
        by - (rule wtl_suc_pc)
      with True less
      have "G \<turnstile> s'' <=' phi ! Suc pc" by blast
      finally show ?thesis by (simp add: True)
    qed
  }  
  with wti show ?thesis
    by (auto simp add: wtl_inst_OK wt_instr_def)
qed


    
lemma fits_first:
  "[| 0 < length is; wtl_inst_list is G rT cert mxs mxr (length is) et 0 s \<noteq> Err; 
      fits phi is G rT s mxs mxr et cert |] ==> 
  G \<turnstile> s <=' phi ! 0"
proof -
  assume wtl:  "wtl_inst_list is G rT cert mxs mxr (length is) et 0 s \<noteq> Err"
  assume fits: "fits phi is G rT s mxs mxr et cert"
  assume pc:   "0 < length is"

  from wtl
  have wt0: "wtl_inst_list (take 0 is) G rT cert mxs mxr (length is) et 0 s = OK s"
    by simp
  
  with fits pc
  have "cert!0 = None ==> phi!0 = s"
    by (rule fitsD_None)
  moreover    
  from fits pc wt0
  have "!!t. cert!0 = Some t ==> phi!0 = cert!0"
    by - (drule fitsD_Some, auto)
  moreover
  from pc
  obtain x xs where "is = x#xs" 
    by (auto simp add: neq_Nil_conv)
  with wtl
  obtain s' where
    "wtl_cert x G rT s cert mxs mxr (length is) et 0 = OK s'"
    by auto
  hence 
    "!!t. cert!0 = Some t ==> G \<turnstile> s <=' cert!0"
    by (simp add: wtl_cert_def split: split_if_asm)

  ultimately
  show ?thesis
    by (cases "cert!0") auto
qed

  
lemma wtl_method_correct:
"wtl_method G C pTs rT mxs mxl et ins cert ==> \<exists> phi. wt_method G C pTs rT mxs mxl ins et phi"
proof (unfold wtl_method_def, simp only: Let_def, elim conjE)
  let "?s0" = "Some ([], OK (Class C) # map OK pTs @ replicate mxl Err)"
  assume pc:  "0 < length ins"
  assume wtl: "wtl_inst_list ins G rT cert mxs mxl (length ins) et 0 ?s0 \<noteq> Err"

  obtain phi where fits: "fits phi ins G rT ?s0 mxs mxl et cert"    
    by (rule exists_phi [elim_format]) blast

  with wtl
  have allpc:
    "\<forall>pc. pc < length ins --> wt_instr (ins ! pc) G rT phi mxs (length ins) et pc"
    by (blast intro: wtl_fits_wt)

  from pc wtl fits
  have "wt_start G C pTs mxl phi"
    by (unfold wt_start_def) (rule fits_first)

  with pc allpc 
  show ?thesis by (auto simp add: wt_method_def)
qed


theorem wtl_correct:
  "wtl_jvm_prog G cert ==> \<exists> Phi. wt_jvm_prog G Phi"
proof -  
  assume wtl: "wtl_jvm_prog G cert"

  let ?Phi = "\<lambda>C sig. let (C,rT,(maxs,maxl,ins,et)) = the (method (G,C) sig) in 
              SOME phi. wt_method G C (snd sig) rT maxs maxl ins et phi"
   
  { fix C S fs mdecls sig rT code
    assume "(C,S,fs,mdecls) \<in> set G" "(sig,rT,code) \<in> set mdecls"
    moreover
    from wtl obtain wf_mb where "wf_prog wf_mb G" 
      by (auto simp add: wtl_jvm_prog_def)
    ultimately
    have "method (G,C) sig = Some (C,rT,code)"
      by (simp add: methd)
  } note this [simp]
 
  from wtl
  have "wt_jvm_prog G ?Phi"
    apply (clarsimp simp add: wt_jvm_prog_def wtl_jvm_prog_def wf_prog_def wf_cdecl_def)
    apply (drule bspec, assumption)
    apply (clarsimp simp add: wf_mdecl_def)
    apply (drule bspec, assumption)
    apply (clarsimp dest!: wtl_method_correct)
    apply (rule someI, assumption)
    done

  thus ?thesis
    by blast
qed   
      
end
