(*  Title:      HOL/MicroJava/BV/BVLightSpec.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* Specification of the LBV *}


theory LBVSpec = Step :

types
  certificate       = "state_type option list" 
  class_certificate = "sig \\<Rightarrow> certificate"
  prog_certificate  = "cname \\<Rightarrow> class_certificate"

constdefs
wtl_inst :: "[instr,jvm_prog,ty,state_type,state_type,certificate,p_count,p_count] \\<Rightarrow> bool"

"wtl_inst i G rT s s' cert max_pc pc \\<equiv> app (i,G,rT,s) \\<and> 
                                       (let s'' = the (step (i,G,s)) in
                                          (\\<forall> pc' \\<in> (succs i pc). pc' < max_pc \\<and>  
                                             ((pc' \\<noteq> pc+1) \\<longrightarrow> cert!pc' \\<noteq> None \\<and> G \\<turnstile> s'' <=s the (cert!pc'))) \\<and>  
                                          (if (pc+1) \\<in> (succs i pc) then  
                                             s' = s'' 
                                           else 
                                             cert ! (pc+1) = Some s'))" 

lemma [simp]: 
"succs i pc = {pc+1} \\<Longrightarrow> 
  wtl_inst i G rT s s' cert max_pc pc = (app (i,G,rT,s) \\<and> pc+1 < max_pc \\<and> (s' = the (step (i,G,s))))"
by (unfold wtl_inst_def, auto)

lemma [simp]:
"succs i pc = {} \\<Longrightarrow> wtl_inst i G rT s s' cert max_pc pc = (app (i,G,rT,s) \\<and> cert!(pc+1) = Some s')"
by (unfold wtl_inst_def, auto)


constdefs
wtl_inst_option :: "[instr,jvm_prog,ty,state_type,state_type,certificate,p_count,p_count] \\<Rightarrow> bool"
"wtl_inst_option i G rT s0 s1 cert max_pc pc \\<equiv>
     (case cert!pc of 
          None     \\<Rightarrow> wtl_inst i G rT s0 s1 cert max_pc pc
        | Some s0' \\<Rightarrow> (G \\<turnstile> s0 <=s s0') \\<and>
                      wtl_inst i G rT s0' s1 cert max_pc pc)"
  
consts
 wtl_inst_list :: "[instr list,jvm_prog,ty,state_type,state_type,certificate,p_count,p_count] \\<Rightarrow> bool"
primrec
  "wtl_inst_list [] G rT s0 s2 cert max_pc pc = (s0 = s2)"

  "wtl_inst_list (instr#is) G rT s0 s2 cert max_pc pc =
     (\\<exists>s1. wtl_inst_option instr G rT s0 s1 cert max_pc pc \\<and> 
           wtl_inst_list is G rT s1 s2 cert max_pc (pc+1))"

constdefs
 wtl_method :: "[jvm_prog,cname,ty list,ty,nat,instr list,certificate] \\<Rightarrow> bool" 
 "wtl_method G C pTs rT mxl ins cert \\<equiv> 
	let max_pc = length ins 
        in 
	0 < max_pc \\<and>  
        (\\<exists>s2. wtl_inst_list ins G rT 
                            ([],(Some(Class C))#((map Some pTs))@(replicate mxl None))
                            s2 cert max_pc 0)"

 wtl_jvm_prog :: "[jvm_prog,prog_certificate] \\<Rightarrow> bool"
 "wtl_jvm_prog G cert \\<equiv> 
    wf_prog (\\<lambda>G C (sig,rT,maxl,b). 
               wtl_method G C (snd sig) rT maxl b (cert C sig)) G" 

text {* \medskip *}

lemma rev_eq: "\\<lbrakk>length a = n; length x = n; rev a @ b # c = rev x @ y # z\\<rbrakk> \\<Longrightarrow> a = x \\<and> b = y \\<and> c = z"
by auto

lemma wtl_inst_unique: 
"wtl_inst i G rT s0 s1 cert max_pc pc \\<longrightarrow>
 wtl_inst i G rT s0 s1' cert max_pc pc \\<longrightarrow> s1 = s1'" (is "?P i")
by (unfold wtl_inst_def, auto)

lemma wtl_inst_option_unique:
"\\<lbrakk>wtl_inst_option i G rT s0 s1 cert max_pc pc; 
  wtl_inst_option i G rT s0 s1' cert max_pc pc\\<rbrakk> \\<Longrightarrow> s1 = s1'"
by (cases "cert!pc") (auto simp add: wtl_inst_unique wtl_inst_option_def)

lemma wtl_inst_list_unique: 
"\\<forall> s0 pc. wtl_inst_list is G rT s0 s1 cert max_pc pc \\<longrightarrow> 
 wtl_inst_list is G rT s0 s1' cert max_pc pc \\<longrightarrow> s1=s1'" (is "?P is")
proof (induct "?P" "is") 
  case Nil
  show "?P []" by simp

  case Cons
  show "?P (a # list)" 
  proof intro
    fix s0 fix pc 
    let "?o s0 s1" = "wtl_inst_option a G rT s0 s1 cert max_pc pc"
    let "?l l s1 s2 pc" = "wtl_inst_list l G rT s1 s2 cert max_pc pc" 
    assume a: "?l (a#list) s0 s1 pc"
    assume b: "?l (a#list) s0 s1' pc"
    with a
    obtain s s' where   "?o s0 s" "?o s0 s'"
                and l:  "?l list s s1 (Suc pc)"
                and l': "?l list s' s1' (Suc pc)" by auto

    have "s=s'" by(rule wtl_inst_option_unique)
    with l l' Cons
    show "s1 = s1'" by blast
  qed
qed
        
lemma wtl_partial:
"\\<forall> pc' pc s. 
   wtl_inst_list is G rT s s' cert mpc pc \\<longrightarrow> \
   pc' < length is \\<longrightarrow> \
   (\\<exists> a b s1. a @ b = is \\<and> length a = pc' \\<and> \
              wtl_inst_list a G rT s  s1 cert mpc pc \\<and> \
              wtl_inst_list b G rT s1 s' cert mpc (pc+length a))" (is "?P is")
proof (induct "?P" "is")
  case Nil
  show "?P []" by auto
  
  case Cons
  show "?P (a#list)"
  proof (intro allI impI)
    fix pc' pc s
    assume length: "pc' < length (a # list)"
    assume wtl:    "wtl_inst_list (a # list) G rT s s' cert mpc pc"
    show "\\<exists> a' b s1. 
            a' @ b = a#list \\<and> length a' = pc' \\<and> \
            wtl_inst_list a' G rT s  s1 cert mpc pc \\<and> \
            wtl_inst_list b G rT s1 s' cert mpc (pc+length a')"
        (is "\\<exists> a b s1. ?E a b s1")
    proof (cases "pc'")
      case 0
      with wtl
      have "?E [] (a#list) s" by simp
      thus ?thesis by blast
    next
      case Suc
      with wtl      
      obtain s0 where wtlSuc: "wtl_inst_list list G rT s0 s' cert mpc (Suc pc)"
                and   wtlOpt: "wtl_inst_option a G rT s s0 cert mpc pc" by auto
      from Cons
      obtain a' b s1' 
        where "a' @ b = list" "length a' = nat"
        and w:"wtl_inst_list a' G rT s0 s1' cert mpc (Suc pc)"
        and   "wtl_inst_list b G rT s1' s' cert mpc (Suc pc + length a')" 
      proof (elim allE impE)
        from length Suc show "nat < length list" by simp 
        from wtlSuc     show "wtl_inst_list list G rT s0 s' cert mpc (Suc pc)" . 
      qed (elim exE conjE, auto)
      with Suc wtlOpt          
      have "?E (a#a') b s1'" by (auto simp del: split_paired_Ex)   
      thus ?thesis by blast
    qed
  qed
qed

lemma "wtl_append1":
"\\<lbrakk>wtl_inst_list x G rT s0 s1 cert (length (x@y)) 0; 
  wtl_inst_list y G rT s1 s2 cert (length (x@y)) (length x)\\<rbrakk> \\<Longrightarrow>
  wtl_inst_list (x@y) G rT s0 s2 cert (length (x@y)) 0"
proof -
  assume w:
    "wtl_inst_list x G rT s0 s1 cert (length (x@y)) 0"
    "wtl_inst_list y G rT s1 s2 cert (length (x@y)) (length x)"

  have
    "\\<forall> pc s0. 
    wtl_inst_list x G rT s0 s1 cert (pc+length (x@y)) pc \\<longrightarrow> 
    wtl_inst_list y G rT s1 s2 cert (pc+length (x@y)) (pc+length x) \\<longrightarrow>
    wtl_inst_list (x@y) G rT s0 s2 cert (pc+length (x@y)) pc" (is "?P x")
  proof (induct "?P" "x")
    case Nil
    show "?P []" by simp
  next
    case Cons
    show "?P (a#list)" 
    proof intro
      fix pc s0
      assume y: 
        "wtl_inst_list y G rT s1 s2 cert (pc + length ((a # list) @ y)) (pc + length (a # list))"
      assume al: 
        "wtl_inst_list (a # list) G rT s0 s1 cert (pc + length ((a # list) @ y)) pc"
      from this
      obtain s' where 
        a: "wtl_inst_option a G rT s0 s' cert (Suc pc + length (list@y)) pc" and
        l: "wtl_inst_list list G rT s' s1 cert (Suc pc + length (list@y)) (Suc pc)" by auto      
      with y Cons
      have "wtl_inst_list (list @ y) G rT s' s2 cert (Suc pc + length (list @ y)) (Suc pc)"
        by (elim allE impE) (assumption, simp+)
      with a
      show "wtl_inst_list ((a # list) @ y) G rT s0 s2 cert (pc + length ((a # list) @ y)) pc"
        by (auto simp del: split_paired_Ex)
    qed
  qed
  
  with w
  show ?thesis 
  proof (elim allE impE)
    from w show "wtl_inst_list x G rT s0 s1 cert (0+length (x @ y)) 0" by simp
  qed simp+
qed

lemma wtl_cons_appendl:
"\\<lbrakk>wtl_inst_list a G rT s0 s1 cert (length (a@i#b)) 0; 
  wtl_inst_option i G rT s1 s2 cert (length (a@i#b)) (length a); 
  wtl_inst_list b G rT s2 s3 cert (length (a@i#b)) (Suc (length a))\\<rbrakk> \\<Longrightarrow> 
  wtl_inst_list (a@i#b) G rT s0 s3 cert (length (a@i#b)) 0"
proof -
  assume a: "wtl_inst_list a G rT s0 s1 cert (length (a@i#b)) 0"

  assume "wtl_inst_option i G rT s1 s2 cert (length (a@i#b)) (length a)"
         "wtl_inst_list b G rT s2 s3 cert (length (a@i#b)) (Suc (length a))"

  hence "wtl_inst_list (i#b) G rT s1 s3 cert (length (a@i#b)) (length a)"
    by (auto simp del: split_paired_Ex)

  with a
  show ?thesis by (rule wtl_append1)
qed

lemma "wtl_append":
"\\<lbrakk>wtl_inst_list a G rT s0 s1 cert (length (a@i#b)) 0; 
  wtl_inst_option i G rT s1 s2 cert (length (a@i#b)) (length a); 
  wtl_inst_list b G rT s2 s3 cert (length (a@i#b)) (Suc (length a))\\<rbrakk> \\<Longrightarrow> 
  wtl_inst_list (a@[i]) G rT s0 s2 cert (length (a@i#b)) 0"
proof -
  assume a: "wtl_inst_list a G rT s0 s1 cert (length (a@i#b)) 0"
  assume i: "wtl_inst_option i G rT s1 s2 cert (length (a@i#b)) (length a)"
  assume b: "wtl_inst_list b G rT s2 s3 cert (length (a@i#b)) (Suc (length a))"

  have "\\<forall> s0 pc. wtl_inst_list a G rT s0 s1 cert (pc+length (a@i#b)) pc \\<longrightarrow> 
        wtl_inst_option i G rT s1 s2 cert (pc+length (a@i#b)) (pc + length a) \\<longrightarrow> 
        wtl_inst_list b G rT s2 s3 cert (pc+length (a@i#b)) (Suc pc + length a) \\<longrightarrow> 
          wtl_inst_list (a@[i]) G rT s0 s2 cert (pc+length (a@i#b)) pc" (is "?P a")
  proof (induct "?P" "a")
    case Nil
    show "?P []" by (simp del: split_paired_Ex)
    case Cons
    show "?P (a#list)" (is "\\<forall>s0 pc. ?x s0 pc \\<longrightarrow> ?y s0 pc \\<longrightarrow> ?z s0 pc \\<longrightarrow> ?p s0 pc") 
    proof intro
      fix s0 pc
      assume y: "?y s0 pc"
      assume z: "?z s0 pc"
      assume "?x s0 pc"
      from this
      obtain s0' where opt: "wtl_inst_option a G rT s0 s0' cert (pc + length ((a # list) @ i # b)) pc"
                  and list: "wtl_inst_list list G rT s0' s1 cert (Suc pc + length (list @ i # b)) (Suc pc)"
        by (auto simp del: split_paired_Ex)
      with y z Cons
      have "wtl_inst_list (list @ [i]) G rT s0' s2 cert (Suc pc + length (list @ i # b)) (Suc pc)" 
      proof (elim allE impE) 
        from list show "wtl_inst_list list G rT s0' s1 cert (Suc pc + length (list @ i # b)) (Suc pc)" .
      qed auto
      with opt
      show "?p s0 pc"
        by (auto simp del: split_paired_Ex)
    qed
  qed
  with a i b
  show ?thesis 
  proof (elim allE impE)
    from a show "wtl_inst_list a G rT s0 s1 cert (0+length (a@i#b)) 0" by simp
  qed auto
qed

end
