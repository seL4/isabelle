(*  Title:      HOL/MicroJava/BV/BVLCorrect.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Correctness of the LBV} *}

theory LBVCorrect = LBVSpec + Typing_Framework:

constdefs
fits :: "'s option list \<Rightarrow> 's certificate \<Rightarrow> 's ebinop \<Rightarrow> 's ord \<Rightarrow> 
         's steptype \<Rightarrow> 's option \<Rightarrow> 'a list \<Rightarrow> bool"
"fits phi cert f r step s0 is \<equiv>
  length phi = length is \<and>
  (\<forall>pc s. pc < length is -->
    (wtl_inst_list (take pc is) cert f r step 0 s0 = OK s \<longrightarrow>
    (case cert!pc of None   => phi!pc = s
                   | Some t => phi!pc = Some t)))"

make_phi :: "'s certificate \<Rightarrow> 's ebinop \<Rightarrow> 's ord \<Rightarrow> 
             's steptype \<Rightarrow> 's option \<Rightarrow> 'a list \<Rightarrow> 's option list"
"make_phi cert f r step s0 is \<equiv> 
   map (\<lambda>pc. case cert!pc of 
               None   => ok_val (wtl_inst_list (take pc is) cert f r step 0 s0)
             | Some t => Some t) [0..length is(]"

lemma fitsD_None [intro?]:
  "\<lbrakk> fits phi cert f r step s0 is; pc < length is;
     wtl_inst_list (take pc is) cert f r step 0 s0 = OK s; 
     cert!pc = None \<rbrakk> \<Longrightarrow> phi!pc = s"
  by (auto simp add: fits_def)

lemma fitsD_Some [intro?]:
  "\<lbrakk> fits phi cert f r step s0 is; pc < length is;
     wtl_inst_list (take pc is) cert f r step 0 s0 = OK s; 
     cert!pc = Some t \<rbrakk> \<Longrightarrow> phi!pc = Some t"
  by (auto simp add: fits_def)

lemma make_phi_Some:
  "pc < length is \<Longrightarrow> cert!pc = Some t \<Longrightarrow>
  make_phi cert f r step s0 is ! pc = Some t"
  by (simp add: make_phi_def)

lemma make_phi_None:
  "pc < length is \<Longrightarrow> cert!pc = None \<Longrightarrow>
  make_phi cert f r step s0 is ! pc = 
  ok_val (wtl_inst_list (take pc is) cert f r step 0 s0)"
  by (simp add: make_phi_def)

lemma make_phi_len:
  "length (make_phi cert f r step s0 is) = length is"
  by (simp add: make_phi_def)

lemma exists_phi:
  "\<exists>phi. fits phi cert f r step s0 is"
proof - 
  have "fits (make_phi cert f r step s0 is) cert f r step s0 is"
    by (auto simp add: fits_def make_phi_Some make_phi_None make_phi_len
             split: option.splits) 
  thus ?thesis by fast
qed
  
lemma fits_lemma1 [intro?]:
  "\<lbrakk>wtl_inst_list is cert f r step 0 s \<noteq> Err; fits phi cert f r step s is\<rbrakk>
  \<Longrightarrow> \<forall>pc t. pc < length is \<longrightarrow> cert!pc = Some t \<longrightarrow> phi!pc = Some t"
proof (intro strip)
  fix pc t 
  assume "wtl_inst_list is cert f r step 0 s \<noteq> Err"
  then obtain s'' where
    "wtl_inst_list (take pc is) cert f r step 0 s = OK s''" 
    by (blast dest: wtl_take)
  moreover
  assume "fits phi cert f r step s is"
         "pc < length is" "cert ! pc = Some t"
  ultimately
  show "phi!pc = Some t" by (auto dest: fitsD_Some)
qed


lemma wtl_suc_pc:
  assumes
    semi: "err_semilat (A,r,f)" and
    all:  "wtl_inst_list is cert f r step 0 s0 \<noteq> Err" and
    wtl:  "wtl_inst_list (take pc is) cert f r step 0 s0 = OK s'" and
    cert: "wtl_cert cert f r step pc s' = OK s''" and
    fits: "fits phi cert f r step s0 is" and
    pc:   "pc+1 < length is"
  shows "OK s'' \<le>|r OK (phi!(pc+1))"
proof -
  from wtl cert pc
  have wts: "wtl_inst_list (take (pc+1) is) cert f r step 0 s0 = OK s''"
    by (rule wtl_Suc)
  moreover
  from all pc
  have "\<exists>s' s''. wtl_inst_list (take (pc+1) is) cert f r step 0 s0 = OK s' \<and> 
                 wtl_cert cert f r step (pc+1) s' = OK s''"
    by (rule wtl_all)
  ultimately
  obtain x where "wtl_cert cert f r step (pc+1) s'' = OK x" by auto
  hence "\<And>t. cert!(pc+1) = Some t \<Longrightarrow> OK s'' \<le>|r OK (cert!(pc+1))"
    by (simp add: wtl_cert_def split: split_if_asm)
  also from fits pc wts
  have "\<And>t. cert!(pc+1) = Some t \<Longrightarrow> cert!(pc+1) = phi!(pc+1)"
    by (auto dest!: fitsD_Some)
  finally have "\<And>t. cert!(pc+1) = Some t \<Longrightarrow> OK s'' \<le>|r OK (phi!(pc+1))" .
  moreover
  from fits pc wts have "cert!(pc+1) = None \<Longrightarrow> s'' = phi!(pc+1)"
    by (rule fitsD_None [symmetric])
  with semi have "cert!(pc+1) = None \<Longrightarrow> OK s'' \<le>|r OK (phi!(pc+1))" by simp
  ultimately
  show "OK s'' \<le>|r OK (phi!(pc+1))" by (cases "cert!(pc+1)", blast+)
qed    

lemma wtl_stable:
  assumes
    semi:    "err_semilat (A,r,f)" and
    pres:    "pres_type step (length is) (err (opt A))" and
    s0_in_A: "s0 \<in> opt A" and
    cert_ok: "cert_ok cert (length is) A" and
    fits:    "fits phi cert f r step s0 is"  and
    wtl:     "wtl_inst_list is cert f r step 0 s0 \<noteq> Err" and
    pc:      "pc < length is" and
    bounded: "bounded step (length is)"
  shows "stable (Err.le (Opt.le r)) step (map OK phi) pc"
proof (unfold stable_def, clarify)
  fix pc' s' assume step: "(pc',s') \<in> set (step pc ((map OK phi) ! pc))" 
                      (is "(pc',s') \<in> set (?step pc)")
  
  from step pc bounded have pc': "pc' < length is"
    by (unfold bounded_def) blast
  
  from wtl pc obtain s1 s2 where
    tkpc: "wtl_inst_list (take pc is) cert f r step 0 s0 = OK s1" and
    cert: "wtl_cert cert f r step pc s1 = OK s2" 
    by - (drule wtl_all, auto)

  have c_Some: "\<forall>pc t. pc < length is \<longrightarrow> cert!pc = Some t \<longrightarrow> phi!pc = Some t" ..
  have c_None: "cert!pc = None \<Longrightarrow> phi!pc = s1" ..

  from cert pc c_None c_Some 
  have inst: "wtl_inst cert f r step pc (phi!pc) = OK s2"
    by (simp add: wtl_cert_def split: option.splits split_if_asm)
  
  from semi have "order (Err.le (Opt.le r))" by simp note order_trans [OF this, trans]
  
  from pc fits have [simp]: "map OK phi!pc = OK (phi!pc)" by (simp add: fits_def)
  from pc' fits have [simp]: "map OK phi!pc' = OK (phi!pc')" by (simp add: fits_def)

  have "s1 \<in> opt A" by (rule wtl_inst_list_pres)
  with pc c_Some cert_ok c_None
  have "phi!pc \<in> opt A" by (cases "cert!pc") (auto dest: cert_okD)
  with pc pres
  have step_in_A: "\<forall>(pc',s') \<in> set (?step pc). s' \<in> err (opt A)" 
    by (auto dest: pres_typeD)

  show "s' \<le>|r (map OK phi) ! pc'"
  proof (cases "pc' = pc+1")
    case True
    with pc' cert_ok
    have cert_in_A: "OK (cert!(pc+1)) \<in> err (opt A)" by (auto dest: cert_okD)
    from inst 
    have ok: "OK s2 = merge cert f r pc (?step pc) (OK (cert!(pc+1)))" 
      by (simp add: wtl_inst_def)
    also    
    have "\<dots> = (map snd [(p',t')\<in>?step pc. p'=pc+1] ++|f (OK (cert!(pc+1))))"
      using cert_in_A step_in_A semi ok
      by - (drule merge_def, auto split: split_if_asm)
    finally
    have "s' \<le>|r OK s2" 
      using semi step_in_A cert_in_A True step by (auto intro: ub1')
    also 
    from True pc' have "pc+1 < length is" by simp
    with semi wtl tkpc cert fits
    have "OK s2 \<le>|r (OK (phi ! (pc+1)))" by (rule wtl_suc_pc)
    also note True [symmetric]
    finally show ?thesis by simp
  next
    case False
    from inst 
    have "\<forall>(pc', s')\<in>set (?step pc). pc'\<noteq>pc+1 \<longrightarrow> s' \<le>|r OK (cert!pc')"
      by (unfold wtl_inst_def) (rule merge_ok, simp)
    with step False 
    have ok: "s' \<le>|r (OK (cert!pc'))" by blast
    moreover
    from ok
    have "cert!pc' = None \<longrightarrow> s' = OK None" by auto
    moreover
    from c_Some pc'
    have "cert!pc' \<noteq> None \<longrightarrow> phi!pc' = cert!pc'" by auto
    ultimately
    show ?thesis by auto
  qed
qed


lemma wtl_fits:
  "wtl_inst_list is cert f r step 0 s0 \<noteq> Err \<Longrightarrow>
  fits phi cert f r step s0 is \<Longrightarrow>
  err_semilat (A,r,f) \<Longrightarrow>
  bounded step (length is) \<Longrightarrow>
  pres_type step (length is) (err (opt A)) \<Longrightarrow>
  s0 \<in> opt A \<Longrightarrow>
  cert_ok cert (length is) A \<Longrightarrow>
  wt_step (Err.le (Opt.le r)) Err step (map OK phi)"
  apply (unfold wt_step_def)
  apply (intro strip)
  apply (rule conjI, simp)
  apply (rule wtl_stable)
  apply assumption+
  apply (simp add: fits_def)
  apply assumption
  done

  
theorem wtl_sound:
  assumes "wtl_inst_list is cert f r step 0 s0 \<noteq> Err" 
  assumes "err_semilat (A,r,f)" and "bounded step (length is)"
  assumes "s0 \<in> opt A" and "cert_ok cert (length is) A"
  assumes "pres_type step (length is) (err (opt A))"
  shows "\<exists>ts. wt_step (Err.le (Opt.le r)) Err step ts"
proof -
  obtain phi where "fits phi cert f r step s0 is" by (insert exists_phi) fast
  have "wt_step (Err.le (Opt.le r)) Err step (map OK phi)" by (rule wtl_fits)
  thus ?thesis ..
qed


end
