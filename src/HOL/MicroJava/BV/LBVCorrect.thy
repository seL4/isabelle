(*  Title:      HOL/MicroJava/BV/BVLcorrect.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* Correctness of the LBV *}

theory LBVCorrect = BVSpec + LBVSpec:

constdefs
fits_partial :: "[method_type,nat,instr list,jvm_prog,ty,state_type,state_type,certificate] \<Rightarrow> bool" 
"fits_partial phi pc is G rT s0 s2 cert \<equiv> (\<forall> a b i s1. (a@(i#b) = is) \<longrightarrow> 
                   wtl_inst_list a G rT s0 s1 cert (pc+length is) pc \<longrightarrow> 
                   wtl_inst_list (i#b) G rT s1 s2 cert (pc+length is) (pc+length a) \<longrightarrow> 
                      ((cert!(pc+length a)      = None   \<longrightarrow> phi!(pc+length a) = s1) \<and> 
                       (\<forall> t. cert!(pc+length a) = Some t \<longrightarrow> phi!(pc+length a) = t)))"
  
fits :: "[method_type,instr list,jvm_prog,ty,state_type,state_type,certificate] \<Rightarrow> bool"
"fits phi is G rT s0 s2 cert \<equiv> fits_partial phi 0 is G rT s0 s2 cert"

lemma fitsD: 
"fits phi is G rT s0 s2 cert \<Longrightarrow>
 (a@(i#b) = is) \<Longrightarrow>
 wtl_inst_list a G rT s0 s1 cert (0+length is) 0 \<Longrightarrow>
 wtl_inst_list (i#b) G rT s1 s2 cert (0+length is) (0+length a) \<Longrightarrow>
 ((cert!(0+length a)     = None   \<longrightarrow> phi!(0+length a) = s1) \<and> 
 (\<forall> t. cert!(0+length a) = Some t \<longrightarrow> phi!(0+length a) = t))"
by (unfold fits_def fits_partial_def) blast

lemma exists_list: "\<exists>l. n < length l" (is "?Q n")
proof (induct "n")
  fix n  assume "?Q n"
  thus "?Q (Suc n)"
  proof elim
    fix l assume "n < length (l::'a list)"
    hence "Suc n < length (a#l)" by simp
    thus ?thesis ..
  qed
qed auto

lemma exists_phi:
"wtl_inst_list is G rT s0 s2 cert (length is) 0 \<Longrightarrow> 
 \<exists> phi. fits phi is G rT s0 s2 cert \<and> length is < length phi"
proof -
  assume all: "wtl_inst_list is G rT s0 s2 cert (length is) 0"
  have "\<forall> s0 pc. wtl_inst_list is G rT s0 s2 cert (pc+length is) pc 
     \<longrightarrow> (\<exists> phi. pc + length is < length phi \<and> fits_partial phi pc is G rT s0 s2 cert)"
    (is "?P is")
  proof (induct "?P" "is")
    case Nil
    show "?P []" by (simp add: fits_partial_def exists_list)
    case Cons
    show "?P (a#list)" 
    proof (intro allI impI)
      fix s0 pc
      assume wtl: "wtl_inst_list (a # list) G rT s0 s2 cert (pc + length (a # list)) pc"

      from this
      obtain s1 where 
        opt:    "wtl_inst_option a G rT s0 s1 cert (Suc pc + length list) pc" and
        wtlSuc: "wtl_inst_list list G rT s1 s2 cert (Suc pc + length list) (Suc pc)"
        by auto 

      with Cons
      obtain phi where 
        fits:   "fits_partial phi (Suc pc) list G rT s1 s2 cert" and
        length: "(Suc pc) + length list < length phi" 
        by blast

      let "?A phi pc x s1'" = 
        "(cert ! (pc + length (x::instr list)) = None \<longrightarrow> phi ! (pc + length x) = s1') \<and>
         (\<forall>t. cert ! (pc + length x) = Some t \<longrightarrow> phi ! (pc + length x) = t)"

      show "\<exists>phi. pc + length (a # list) < length phi \<and> 
                  fits_partial phi pc (a # list) G rT s0 s2 cert" 
      proof (cases "cert!pc")
        case None            
        have "fits_partial (phi[pc:= s0]) pc (a # list) G rT s0 s2 cert" 
        proof (unfold fits_partial_def, intro allI impI)
          fix x i y s1' 
          assume * : 
            "x @ i # y = a # list"
            "wtl_inst_list x G rT s0 s1' cert (pc + length (a # list)) pc"
            "wtl_inst_list (i # y) G rT s1' s2 cert (pc + length (a # list)) (pc + length x)"
          show "?A (phi[pc:= s0]) pc x s1'" 
          proof (cases "x")
            assume "x = []"
            with * length None
            show ?thesis by simp
          next
            fix b l assume Cons: "x = b#l"
            with fits *
            have "?A (phi[pc:= s0]) (Suc pc) l s1'" 
            proof (unfold fits_partial_def, elim allE impE)
              from * Cons
              show "l @ i # y = list" by simp 
              from Cons opt * 
              show "wtl_inst_list l G rT s1 s1' cert (Suc pc + length list) (Suc pc)" 
                by (simp, elim) (drule wtl_inst_option_unique, assumption, simp)
            qed simp+
            with Cons length
            show ?thesis by auto
          qed
        qed
        with length
        show ?thesis by intro auto
      next
        fix c assume Some: "cert!pc = Some c"
        have "fits_partial (phi[pc:= c]) pc (a # list) G rT s0 s2 cert"
        proof (unfold fits_partial_def, intro allI impI)
          fix x i y s1' 
          assume * : 
            "x @ i # y = a # list"
            "wtl_inst_list x G rT s0 s1' cert (pc + length (a # list)) pc"
            "wtl_inst_list (i # y) G rT s1' s2 cert (pc + length (a # list)) (pc + length x)"
          show "?A (phi[pc:= c]) pc x s1'"
          proof (cases "x")
            assume "x = []"
            with length Some
            show ?thesis by simp
          next
            fix b l assume Cons: "x = b#l"
            with fits *
            have "?A (phi[pc:= c]) (Suc pc) l s1'" 
            proof (unfold fits_partial_def, elim allE impE)
              from * Cons
              show "l @ i # y = list" by simp 
              from Cons opt * 
              show "wtl_inst_list l G rT s1 s1' cert (Suc pc + length list) (Suc pc)" 
                by (simp, elim) (drule wtl_inst_option_unique, assumption, simp)
            qed simp+
            with Cons length
            show ?thesis by auto
          qed
        qed
        with length
        show ?thesis by intro auto
      qed 
    qed 
  qed  
  with all 
  show ?thesis  
  proof (elim exE allE impE conjE) 
    show "wtl_inst_list is G rT s0 s2 cert (0+length is) 0" by simp 
  qed (auto simp add: fits_def)  
qed 


lemma fits_lemma1:
"\<lbrakk>wtl_inst_list is G rT s0 s3 cert (length is) 0; fits phi is G rT s0 s3 cert\<rbrakk> \<Longrightarrow> 
  \<forall> pc t. pc < length is \<longrightarrow> (cert ! pc) = Some t \<longrightarrow> (phi ! pc) = t"
proof intro
  fix pc t
  assume wtl:  "wtl_inst_list is G rT s0 s3 cert (length is) 0"
  assume fits: "fits phi is G rT s0 s3 cert"
  assume pc:   "pc < length is"
  assume cert: "cert ! pc = Some t"
  from pc
  have "is \<noteq> []" by auto
  hence cons: "\<exists>i y. is = i#y" by (simp add: neq_Nil_conv)
  from wtl pc
  have "\<exists>a b s1. a@b = is \<and> length a = pc \<and> 
                 wtl_inst_list a G rT s0 s1 cert (length is) 0 \<and> 
                 wtl_inst_list b G rT s1 s3 cert (length is) (0+length a)"
    (is "\<exists>a b s1. ?A a b \<and> ?L a \<and> ?W1 a s1 \<and> ?W2 a b s1")
  by (rule wtl_partial [rulify])
  with cons
  show "phi ! pc = t"
  proof (elim exE conjE)
    fix a b s1 i y
    assume * :"?A a b" "?L a" "?W1 a s1" "?W2 a b s1" "is = i#y"
    with pc
    have "b \<noteq> []" by auto
    hence "\<exists>b' bs. b = b'#bs" by (simp add: neq_Nil_conv)
    thus ?thesis
    proof (elim exE)
      fix b' bs assume Cons: "b=b'#bs"
      with * fits cert     
      show ?thesis 
      proof (unfold fits_def fits_partial_def, elim allE impE) 
        from * Cons show "a@b'#bs=is" by simp
      qed simp+
    qed
  qed
qed

lemma fits_lemma2:
"\<lbrakk>wtl_inst_list a G rT s0 s1 cert (length (a@i#b)) 0; 
  wtl_inst_option i G rT s1 s2 cert (length (a@i#b)) (length a); 
  fits phi (a@i#b) G rT s0 s3 cert; cert!(length a) = None; 
  wtl_inst_list b G rT s2 s3 cert (length (a@i#b)) (Suc (length a))\<rbrakk> 
 \<Longrightarrow>  phi!(length a) = s1"
proof (unfold fits_def fits_partial_def, elim allE impE)
qed (auto simp del: split_paired_Ex)



lemma wtl_suc_pc:
"\<lbrakk>wtl_inst_list a G rT s0 s1 cert (length (a@i#b)) 0; 
  wtl_inst_option i G rT s1 s2 cert (length (a@i#b)) (length a); 
  wtl_inst_list b G rT s2 s3 cert (length (a@i#b)) (Suc (length a)); 
  fits phi (a@i#b) G rT s0 s3 cert \<rbrakk> \<Longrightarrow> 
  b \<noteq> [] \<longrightarrow> G \<turnstile> s2 <=s (phi ! (Suc (length a)))"
proof
  assume f: "fits phi (a@i#b) G rT s0 s3 cert"
  assume "wtl_inst_list a G rT s0 s1 cert (length (a@i#b)) 0"
         "wtl_inst_option i G rT s1 s2 cert (length (a@i#b)) (length a)"
  and w: "wtl_inst_list b G rT s2 s3 cert (length (a@i#b)) (Suc (length a))"
  hence a: "wtl_inst_list (a@[i]) G rT s0 s2 cert (length (a@i#b)) 0" by (rule wtl_append)
  assume "b \<noteq> []"

  from this
  obtain b' bs where Cons: "b = b' # bs" by (simp add: neq_Nil_conv) (elim exE, rule that)
  hence "(a@[i]) @ b' # bs = a @ i # b" by simp
  with f
  show "G \<turnstile> s2 <=s phi ! Suc (length a)"
  proof (rule fitsD [elimify]) 
    from Cons w       
    show "wtl_inst_list (b' # bs) G rT s2 s3 cert (0 + length (a @ i # b)) (0 + length (a @ [i]))"
      by simp
    from a 
    show "wtl_inst_list (a @ [i]) G rT s0 s2 cert (0 + length (a @ i # b)) 0" by simp
    
    assume cert:
      "(cert ! (0 + length (a @ [i])) = None \<longrightarrow> phi ! (0 + length (a @ [i])) = s2) \<and>
      (\<forall>t. cert ! (0 + length (a @ [i])) = Some t \<longrightarrow> phi ! (0 + length (a @ [i])) = t)"
    show ?thesis
    proof (cases "cert ! Suc (length a)")
      assume "cert ! Suc (length a) = None"
      with cert
      have "s2 = phi ! Suc (length a)" by simp 
      thus ?thesis by simp
    next
      fix t assume "cert ! Suc (length a) = Some t"
      with cert
      have "phi ! Suc (length a) = t" by (simp del: split_paired_All)
      with cert Cons w
      show ?thesis  by (auto simp add: wtl_inst_option_def)
    qed
  qed
qed

lemma wtl_lemma: 
"\<lbrakk>wtl_inst_list i1 G rT s0 s1 cert (length (i1@i#i2)) 0;
  wtl_inst_option i G rT s1 s2 cert (length (i1@i#i2)) (length i1);
  wtl_inst_list i2 G rT s2 s3 cert (length (i1@i#i2)) (Suc (length i1));
  fits phi (i1@i#i2) G rT s0 s3 cert\<rbrakk> \<Longrightarrow>
  wt_instr i G rT phi (length (i1@i#i2)) (length i1)" (concl is "?P i")
proof -
  assume w1: "wtl_inst_list i1 G rT s0 s1 cert (length (i1@i#i2)) 0" (is ?w1)
  assume wo: "wtl_inst_option i G rT s1 s2 cert (length (i1@i#i2)) (length i1)"
  assume w2: "wtl_inst_list i2 G rT s2 s3 cert (length (i1@i#i2)) (Suc (length i1))"
  assume f:  "fits phi (i1@i#i2) G rT s0 s3 cert"

  from w1 wo w2
  have wtl: "wtl_inst_list (i1@i#i2) G rT s0 s3 cert (length (i1@i#i2)) 0" 
    by (rule wtl_cons_appendl)

  with f  
  have c1: "\<forall>t. cert ! (length i1) = Some t \<longrightarrow> phi ! (length i1) = t"
    by intro (rule fits_lemma1 [rulify], auto)

  from w1 wo w2 f
  have c2: "cert ! (length i1) = None \<Longrightarrow> phi ! (length i1) = s1"
    by - (rule fits_lemma2)

  from wtl f
  have c3: "\<forall>pc t. pc < length(i1@i#i2) \<longrightarrow> cert ! pc = Some t \<longrightarrow> phi ! pc = t"
    by (rule fits_lemma1)

  from w1 wo w2 f
  have suc: "i2 \<noteq> [] \<Longrightarrow> G \<turnstile> s2 <=s phi ! Suc (length i1)" 
    by (rule wtl_suc_pc [rulify]) 

  with wo
  show ?thesis
    by (auto simp add: c1 c2 c3 wt_instr_def wtl_inst_def wtl_inst_option_def split: option.split_asm)
qed


lemma wtl_fits_wt:
"\<lbrakk>wtl_inst_list is G rT s0 s3 cert (length is) 0; fits phi is G rT s0 s3 cert\<rbrakk> 
 \<Longrightarrow> \<forall>pc. pc < length is \<longrightarrow> wt_instr (is ! pc) G rT phi (length is) pc"
proof intro
  assume fits: "fits phi is G rT s0 s3 cert"

  fix pc
  assume wtl: "wtl_inst_list is G rT s0 s3 cert (length is) 0"
     and pc:  "pc < length is"
  
  from this
  obtain i1 i2' s1 where 
    l:  "i1 @ i2' = is" "length i1 = pc" and
    w1: "wtl_inst_list i1 G rT s0 s1 cert (length is) 0" and 
    w2: "wtl_inst_list i2' G rT s1 s3 cert (length is) (0 + length i1)" 
    by (rule wtl_partial [rulify, elimify]) (elim, rule that)

  from l pc
  have "i2' \<noteq> []" by auto

  from this
  obtain i i2 where c: "i2' = i#i2" 
    by (simp add: neq_Nil_conv) (elim, rule that)

  with w2 l
  obtain s2 
    where w3: 
    "wtl_inst_option i G rT s1 s2 cert (length (i1@i#i2)) (length i1)"
    "wtl_inst_list i2 G rT s2 s3 cert (length (i1@i#i2)) (Suc (length i1))" 
    by auto
      
  from w1 l c
  have w4: "wtl_inst_list i1 G rT s0 s1 cert (length (i1 @ i # i2)) 0" by simp
  
  from l c fits
  have "fits phi (i1@i#i2) G rT s0 s3 cert" by simp
  with w4 w3
  have "wt_instr i G rT phi (length (i1@i#i2)) (length i1)" by (rule wtl_lemma)

  with l c
  show "wt_instr (is ! pc) G rT phi (length is) pc"
    by (auto simp add: nth_append)
qed
    
lemma wtl_inst_list_correct:
"wtl_inst_list is G rT s0 s2 cert (length is) 0 \<Longrightarrow> 
 \<exists> phi. \<forall>pc. pc < length is \<longrightarrow> wt_instr (is ! pc) G rT phi (length is) pc"
proof -
  assume wtl: "wtl_inst_list is G rT s0 s2 cert (length is) 0"

  from this
  obtain phi where "fits phi is G rT s0 s2 cert"
    by (rule exists_phi [elimify]) blast

  with wtl
  show ?thesis
    by (rule wtl_fits_wt [elimify]) blast
qed
    
lemma fits_first:
"\<lbrakk>is \<noteq> [];wtl_inst_list is G rT s0 s2 cert (length is) 0; 
 fits phi is G rT s0 s2 cert\<rbrakk> \<Longrightarrow> G \<turnstile> s0 <=s phi ! 0"
proof -
  assume wtl: "wtl_inst_list is G rT s0 s2 cert (length is) 0"
  assume fits: "fits phi is G rT s0 s2 cert"
  assume "is \<noteq> []"
  
  from this 
  obtain y ys where cons: "is = y#ys" 
    by (simp add: neq_Nil_conv) (elim, rule that)

  from fits
  show ?thesis
  proof (rule fitsD [elimify])
    from cons show "[]@y#ys = is" by simp
    
    from cons wtl
    show "wtl_inst_list (y#ys) G rT s0 s2 cert (0 + length is) (0 + length [])"
      by simp

    assume cert:
      "(cert ! (0 + length []) = None \<longrightarrow> phi ! (0 + length []) = s0) \<and>
       (\<forall>t. cert ! (0 + length []) = Some t \<longrightarrow> phi ! (0 + length []) = t)"

    show ?thesis
    proof (cases "cert!0")
      assume "cert!0 = None"
      with cert
      show ?thesis by simp
    next
      fix t assume "cert!0 = Some t"
      with cert
      have "phi!0 = t" by (simp del: split_paired_All)
      with cert cons wtl
      show ?thesis by (auto simp add: wtl_inst_option_def)
    qed
  qed simp
qed
  
lemma wtl_method_correct:
"wtl_method G C pTs rT mxl ins cert \<Longrightarrow> \<exists> phi. wt_method G C pTs rT mxl ins phi"
proof (unfold wtl_method_def, simp del: split_paired_Ex, elim exE conjE)
  let "?s0" = "([], Some (Class C) # map Some pTs @ replicate mxl None)"
  fix s2
  assume neqNil: "ins \<noteq> []"
  assume wtl: "wtl_inst_list ins G rT ?s0 s2 cert (length ins) 0"

  from this
  obtain phi where fits: "fits phi ins G rT ?s0 s2 cert \<and> length ins < length phi"
    by (rule exists_phi [elimify]) blast

  with wtl
  have allpc:
    "\<forall>pc. pc < length ins \<longrightarrow> wt_instr (ins ! pc) G rT phi (length ins) pc"
    by elim (rule wtl_fits_wt [elimify])

  from neqNil wtl fits
  have "wt_start G C pTs mxl phi"
    by (elim conjE, unfold wt_start_def) (rule fits_first)

  with neqNil allpc fits
  show ?thesis by (auto simp add: wt_method_def)
qed

lemma unique_set:
"(a,b,c,d)\<in>set l \<longrightarrow> unique l \<longrightarrow> (a',b',c',d') \<in> set l \<longrightarrow> a = a' \<longrightarrow> b=b' \<and> c=c' \<and> d=d'"
  by (induct "l") auto

lemma unique_epsilon:
"(a,b,c,d)\<in>set l \<longrightarrow> unique l \<longrightarrow> (\<epsilon> (a',b',c',d'). (a',b',c',d') \<in> set l \<and> a'=a) = (a,b,c,d)"
  by (auto simp add: unique_set)

theorem wtl_correct:
"wtl_jvm_prog G cert ==> \<exists> Phi. wt_jvm_prog G Phi"
proof (clarsimp simp add: wt_jvm_prog_def wf_prog_def, intro conjI)

  assume wtl_prog: "wtl_jvm_prog G cert"
  thus "ObjectC \<in> set G" by (simp add: wtl_jvm_prog_def wf_prog_def)

  from wtl_prog 
  show uniqueG: "unique G" by (simp add: wtl_jvm_prog_def wf_prog_def)

  show "\<exists>Phi. Ball (set G) (wf_cdecl (\<lambda>G C (sig,rT,maxl,b). wt_method G C (snd sig) rT maxl b (Phi C sig)) G)"
    (is "\<exists>Phi. ?Q Phi")
  proof (intro exI)
    let "?Phi" = 
        "\<lambda> C sig. let (C,x,y,mdecls) = \<epsilon> (Cl,x,y,mdecls). (Cl,x,y,mdecls) \<in> set G \<and> Cl = C in
                   let (sig,rT,maxl,b) = \<epsilon> (sg,rT,maxl,b). (sg,rT,maxl,b) \<in> set mdecls \<and> sg = sig in\
                     \<epsilon> phi. wt_method G C (snd sig) rT maxl b phi"
    from wtl_prog
    show "?Q ?Phi"
    proof (unfold wf_cdecl_def, intro)
      fix x a b aa ba ab bb m
      assume 1: "x \<in> set G" "x = (a, b)" "b = (aa, ba)" "ba = (ab, bb)" "m \<in> set bb"
      with wtl_prog
      show "wf_mdecl (\<lambda>G C (sig,rT,maxl,b). wt_method G C (snd sig) rT maxl b (?Phi C sig)) G a m"
      proof (simp add: wf_mdecl_def wtl_jvm_prog_def wf_prog_def wf_cdecl_def, elim conjE)
        apply_end (drule bspec, assumption, simp, elim conjE)
        assume "\<forall>(sig,rT,mb)\<in>set bb. wf_mhead G sig rT \<and> 
                 (\<lambda>(maxl,b). wtl_method G a (snd sig) rT maxl b (cert a sig)) mb"
               "unique bb"
        with 1 uniqueG
        show "(\<lambda>(sig,rT,mb).
          wf_mhead G sig rT \<and>
          (\<lambda>(maxl,b).
              wt_method G a (snd sig) rT maxl b 
               ((\<lambda>(C,x,y,mdecls).
                    (\<lambda>(sig,rT,maxl,b). Eps (wt_method G C (snd sig) rT maxl b))
                     (\<epsilon>(sg,rT,maxl,b). (sg, rT, maxl, b) \<in> set mdecls \<and> sg = sig))
                 (\<epsilon>(Cl,x,y,mdecls). (Cl, x, y, mdecls) \<in> set G \<and> Cl = a))) mb) m"
          by - (drule bspec, assumption, 
                clarsimp dest!: wtl_method_correct,
                clarsimp intro!: selectI simp add: unique_epsilon)
      qed
    qed (auto simp add: wtl_jvm_prog_def wf_prog_def wf_cdecl_def)
  qed
qed
    

end
