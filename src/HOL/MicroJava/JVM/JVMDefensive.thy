(*  Title:      HOL/MicroJava/JVM/JVMDefensive.thy
    ID:         $Id$
    Author:     Gerwin Klein
*)

header {* \isaheader{A Defensive JVM} *}

theory JVMDefensive = JVMExec:

text {*
  Extend the state space by one element indicating a type error (or
  other abnormal termination) *}
datatype 'a type_error = TypeError | Normal 'a


syntax "fifth" :: "'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<Rightarrow> 'e"
translations
  "fifth x" == "fst(snd(snd(snd(snd x))))"


consts isAddr :: "val \<Rightarrow> bool"
recdef isAddr "{}"
  "isAddr (Addr loc) = True"
  "isAddr v          = False"

consts isIntg :: "val \<Rightarrow> bool"
recdef isIntg "{}"
  "isIntg (Intg i) = True"
  "isIntg v        = False"

constdefs
  isRef :: "val \<Rightarrow> bool"
  "isRef v \<equiv> v = Null \<or> isAddr v"


consts
  check_instr :: "[instr, jvm_prog, aheap, opstack, locvars, 
                  cname, sig, p_count, nat, frame list] \<Rightarrow> bool"
primrec 
  "check_instr (Load idx) G hp stk vars C sig pc mxs frs = 
  (idx < length vars \<and> size stk < mxs)"

  "check_instr (Store idx) G hp stk vars Cl sig pc mxs frs = 
  (0 < length stk \<and> idx < length vars)"

  "check_instr (LitPush v) G hp stk vars Cl sig pc mxs frs = 
  (\<not>isAddr v \<and> size stk < mxs)"

  "check_instr (New C) G hp stk vars Cl sig pc mxs frs = 
  (is_class G C \<and> size stk < mxs)"

  "check_instr (Getfield F C) G hp stk vars Cl sig pc mxs frs = 
  (0 < length stk \<and> is_class G C \<and> field (G,C) F \<noteq> None \<and> 
  (let (C', T) = the (field (G,C) F); ref = hd stk in 
    C' = C \<and> isRef ref \<and> (ref \<noteq> Null \<longrightarrow> 
      hp (the_Addr ref) \<noteq> None \<and> 
      (let (D,vs) = the (hp (the_Addr ref)) in 
        G \<turnstile> D \<preceq>C C \<and> vs (F,C) \<noteq> None \<and> G,hp \<turnstile> the (vs (F,C)) ::\<preceq> T))))" 

  "check_instr (Putfield F C) G hp stk vars Cl sig pc mxs frs = 
  (1 < length stk \<and> is_class G C \<and> field (G,C) F \<noteq> None \<and> 
  (let (C', T) = the (field (G,C) F); v = hd stk; ref = hd (tl stk) in 
    C' = C \<and> isRef ref \<and> (ref \<noteq> Null \<longrightarrow> 
      hp (the_Addr ref) \<noteq> None \<and> 
      (let (D,vs) = the (hp (the_Addr ref)) in 
        G \<turnstile> D \<preceq>C C \<and> G,hp \<turnstile> v ::\<preceq> T))))" 

  "check_instr (Checkcast C) G hp stk vars Cl sig pc mxs frs =
  (0 < length stk \<and> is_class G C \<and> isRef (hd stk))"

  "check_instr (Invoke C mn ps) G hp stk vars Cl sig pc mxs frs =
  (length ps < length stk \<and> 
  (let n = length ps; v = stk!n in
  isRef v \<and> (v \<noteq> Null \<longrightarrow> 
    hp (the_Addr v) \<noteq> None \<and>
    method (G,cname_of hp v) (mn,ps) \<noteq> None \<and>
    list_all2 (\<lambda>v T. G,hp \<turnstile> v ::\<preceq> T) (rev (take n stk)) ps)))"
  
  "check_instr Return G hp stk0 vars Cl sig0 pc mxs frs =
  (0 < length stk0 \<and> (0 < length frs \<longrightarrow> 
    method (G,Cl) sig0 \<noteq> None \<and>    
    (let v = hd stk0;  (C, rT, body) = the (method (G,Cl) sig0) in
    Cl = C \<and> G,hp \<turnstile> v ::\<preceq> rT)))"
 
  "check_instr Pop G hp stk vars Cl sig pc mxs frs = 
  (0 < length stk)"

  "check_instr Dup G hp stk vars Cl sig pc mxs frs = 
  (0 < length stk \<and> size stk < mxs)"

  "check_instr Dup_x1 G hp stk vars Cl sig pc mxs frs = 
  (1 < length stk \<and> size stk < mxs)"

  "check_instr Dup_x2 G hp stk vars Cl sig pc mxs frs = 
  (2 < length stk \<and> size stk < mxs)"

  "check_instr Swap G hp stk vars Cl sig pc mxs frs =
  (1 < length stk)"

  "check_instr IAdd G hp stk vars Cl sig pc mxs frs =
  (1 < length stk \<and> isIntg (hd stk) \<and> isIntg (hd (tl stk)))"

  "check_instr (Ifcmpeq b) G hp stk vars Cl sig pc mxs frs =
  (1 < length stk \<and> 0 \<le> int pc+b)"

  "check_instr (Goto b) G hp stk vars Cl sig pc mxs frs =
  (0 \<le> int pc+b)"

  "check_instr Throw G hp stk vars Cl sig pc mxs frs =
  (0 < length stk \<and> isRef (hd stk))"

constdefs
  check :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> bool"
  "check G s \<equiv> let (xcpt, hp, frs) = s in
               (case frs of [] \<Rightarrow> True | (stk,loc,C,sig,pc)#frs' \<Rightarrow> 
                (let  (C',rt,mxs,mxl,ins,et) = the (method (G,C) sig); i = ins!pc in
                 pc < size ins \<and> 
                 check_instr i G hp stk loc C sig pc mxs frs'))"


  exec_d :: "jvm_prog \<Rightarrow> jvm_state type_error \<Rightarrow> jvm_state option type_error"
  "exec_d G s \<equiv> case s of 
      TypeError \<Rightarrow> TypeError 
    | Normal s' \<Rightarrow> if check G s' then Normal (exec (G, s')) else TypeError"


consts
  "exec_all_d" :: "jvm_prog \<Rightarrow> jvm_state type_error \<Rightarrow> jvm_state type_error \<Rightarrow> bool" 
                   ("_ |- _ -jvmd-> _" [61,61,61]60)

syntax (xsymbols)
  "exec_all_d" :: "jvm_prog \<Rightarrow> jvm_state type_error \<Rightarrow> jvm_state type_error \<Rightarrow> bool" 
                   ("_ \<turnstile> _ -jvmd\<rightarrow> _" [61,61,61]60)  
 
defs
  exec_all_d_def:
  "G \<turnstile> s -jvmd\<rightarrow> t \<equiv>
         (s,t) \<in> ({(s,t). exec_d G s = TypeError \<and> t = TypeError} \<union> 
                  {(s,t). \<exists>t'. exec_d G s = Normal (Some t') \<and> t = Normal t'})\<^sup>*"


declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

lemma [dest!]:
  "(if P then A else B) \<noteq> B \<Longrightarrow> P"
  by (cases P, auto)

lemma exec_d_no_errorI [intro]:
  "check G s \<Longrightarrow> exec_d G (Normal s) \<noteq> TypeError"
  by (unfold exec_d_def) simp

theorem no_type_error_commutes:
  "exec_d G (Normal s) \<noteq> TypeError \<Longrightarrow> 
  exec_d G (Normal s) = Normal (exec (G, s))"
  by (unfold exec_d_def, auto)


lemma defensive_imp_aggressive:
  "G \<turnstile> (Normal s) -jvmd\<rightarrow> (Normal t) \<Longrightarrow> G \<turnstile> s -jvm\<rightarrow> t"
proof -
  have "\<And>x y. G \<turnstile> x -jvmd\<rightarrow> y \<Longrightarrow> \<forall>s t. x = Normal s \<longrightarrow> y = Normal t \<longrightarrow>  G \<turnstile> s -jvm\<rightarrow> t"
    apply (unfold exec_all_d_def)
    apply (erule rtrancl_induct)
     apply (simp add: exec_all_def)
    apply (fold exec_all_d_def)
    apply simp
    apply (intro allI impI)
    apply (erule disjE, simp)
    apply (elim exE conjE)
    apply (erule allE, erule impE, assumption)
    apply (simp add: exec_all_def exec_d_def split: type_error.splits split_if_asm)
    apply (rule rtrancl_trans, assumption)
    apply blast
    done
  moreover
  assume "G \<turnstile> (Normal s) -jvmd\<rightarrow> (Normal t)" 
  ultimately
  show "G \<turnstile> s -jvm\<rightarrow> t" by blast
qed

end