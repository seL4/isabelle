(*  Title:      HOL/MicroJava/BV/BVLightSpec.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* Specification of the LBV *}


theory LBVSpec = BVSpec:

types
  certificate       = "state_type option list" 
  class_certificate = "sig \\<Rightarrow> certificate"
  prog_certificate  = "cname \\<Rightarrow> class_certificate"

consts
 wtl_LS :: "[load_and_store,state_type,state_type,p_count,p_count] \\<Rightarrow> bool"
primrec
"wtl_LS (Load idx) s s' max_pc pc =
 (let (ST,LT) = s
  in
  pc+1 < max_pc \\<and>
  idx < length LT \\<and> 
  (\\<exists>ts. (LT ! idx) = Some ts \\<and>  
   (ts # ST , LT) = s'))"
  
"wtl_LS (Store idx) s s' max_pc pc =
 (let (ST,LT) = s
  in
  pc+1 < max_pc \\<and>
  idx < length LT \\<and>
  (\\<exists>ts ST'. ST = ts # ST' \\<and>
   (ST' , LT[idx:=Some ts]) = s'))"

"wtl_LS (Bipush i) s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 ((PrimT Integer) # ST , LT) = s')"

"wtl_LS (Aconst_null) s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 (NT # ST , LT) = s')"

consts
 wtl_MO	:: "[manipulate_object,jvm_prog,state_type,state_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wtl_MO (Getfield F C) G s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and>
	 (\\<exists>T oT ST'. field (G,C) F = Some(C,T) \\<and>
                          ST = oT # ST'  \\<and> 
		                  G \\<turnstile> oT \\<preceq> (Class C) \\<and>
		          (T # ST' , LT) = s'))"

"wtl_MO (Putfield F C) G s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and> 
	 (\\<exists>T vT oT ST'.
             field (G,C) F = Some(C,T) \\<and>
             ST = vT # oT # ST' \\<and> 
             G \\<turnstile> oT \\<preceq> (Class C) \\<and>
             G \\<turnstile> vT \\<preceq> T  \\<and>
             (ST' , LT) = s'))"


consts 
 wtl_CO	:: "[create_object,jvm_prog,state_type,state_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wtl_CO (New C) G s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and>
	 ((Class C) # ST , LT) = s')"

consts
 wtl_CH	:: "[check_object,jvm_prog,state_type,state_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wtl_CH (Checkcast C) G s s' max_pc pc = 
	(let (ST,LT) = s 
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and> 
	 (\\<exists>rt ST'. ST = RefT rt # ST' \\<and>
                   (Class C # ST' , LT) = s'))"

consts 
 wtl_OS	:: "[op_stack,state_type,state_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wtl_OS Pop s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 \\<exists>ts ST'. pc+1 < max_pc \\<and>
		ST = ts # ST' \\<and> 	 
		(ST' , LT) = s')"

"wtl_OS Dup s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts ST'. ST = ts # ST' \\<and> 	 
		   (ts # ts # ST' , LT) = s'))"

"wtl_OS Dup_x1 s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts1 ts2 ST'. ST = ts1 # ts2 # ST' \\<and> 	 
		        (ts1 # ts2 # ts1 # ST' , LT) = s'))"

"wtl_OS Dup_x2 s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts1 ts2 ts3 ST'. ST = ts1 # ts2 # ts3 # ST' \\<and> 	 
		            (ts1 # ts2 # ts3 # ts1 # ST' , LT) = s'))"

"wtl_OS Swap s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts ts' ST'. ST = ts' # ts # ST' \\<and> 	 
		       (ts # ts' # ST' , LT) = s'))"

"wtl_OS ADD s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ST'. ST = (PrimT Integer) # (PrimT Integer) # ST' \\<and> 	 
		       ((PrimT Integer) # ST' , LT) = s'))"
consts 
 wtl_BR	:: "[branch,jvm_prog,state_type,state_type,certificate,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wtl_BR (Ifcmpeq branch) G s s' cert max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and> (nat(int pc+branch)) < max_pc \\<and> 
	 (\\<exists>ts ts' ST'. ST = ts # ts' # ST' \\<and>
          ((\\<exists>p. ts = PrimT p \\<and> ts' = PrimT p) \\<or>
           (\\<exists>r r'. ts = RefT r \\<and> ts' = RefT r')) \\<and>
		       ((ST' , LT) = s') \\<and>
            cert ! (nat(int pc+branch)) \\<noteq> None \\<and>
		       G \\<turnstile> (ST' , LT) <=s the (cert ! (nat(int pc+branch)))))"
  
"wtl_BR (Goto branch) G s s' cert max_pc pc =
	((let (ST,LT) = s
	 in
	 (nat(int pc+branch)) < max_pc \\<and> cert ! (nat(int pc+branch)) \\<noteq> None \\<and>
	 G \\<turnstile> (ST , LT) <=s the (cert ! (nat(int pc+branch)))) \\<and>
   (cert ! (pc+1) = Some s'))"
  
consts
 wtl_MI :: "[meth_inv,jvm_prog,state_type,state_type,certificate,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wtl_MI (Invoke mn fpTs) G s s' cert max_pc pc =
	(let (ST,LT) = s
	 in
         pc+1 < max_pc \\<and>
         (\\<exists>apTs X ST'. ST = (rev apTs) @ (X # ST') \\<and>
         length apTs = length fpTs \\<and>
         (\\<exists>s''. cert ! (pc+1) = Some s'' \\<and> 
         ((s'' = s' \\<and> X = NT) \\<or>
          ((G \\<turnstile> s' <=s s'') \\<and> (\\<exists>C. X = Class C \\<and>  
          (\\<forall>(aT,fT)\\<in>set(zip apTs fpTs). G \\<turnstile> aT \\<preceq> fT) \\<and> 
          (\\<exists>D rT b. method (G,C) (mn,fpTs) = Some(D,rT,b) \\<and>
          (rT # ST' , LT) = s')))))))"

consts
 wtl_MR	:: "[meth_ret,jvm_prog,ty,state_type,state_type,certificate,p_count,p_count] \\<Rightarrow> bool"
primrec
  "wtl_MR Return G rT s s' cert max_pc pc = 
	((let (ST,LT) = s
	 in
	 (\\<exists>T ST'. ST = T # ST' \\<and> G \\<turnstile> T \\<preceq> rT)) \\<and>
   (cert ! (pc+1) = Some s'))"


consts 
 wtl_inst :: "[instr,jvm_prog,ty,state_type,state_type,certificate,p_count,p_count] \\<Rightarrow> bool"
 primrec
 "wtl_inst (LS ins) G rT s s' cert max_pc pc = wtl_LS ins s s' max_pc pc"
 "wtl_inst (CO ins) G rT s s' cert max_pc pc = wtl_CO ins G s s' max_pc pc"
 "wtl_inst (MO ins) G rT s s' cert max_pc pc = wtl_MO ins G s s' max_pc pc"
 "wtl_inst (CH ins) G rT s s' cert max_pc pc = wtl_CH ins G s s' max_pc pc"
 "wtl_inst (MI ins) G rT s s' cert max_pc pc = wtl_MI ins G s s' cert max_pc pc"
 "wtl_inst (MR ins) G rT s s' cert max_pc pc = wtl_MR ins G rT s s' cert max_pc pc"
 "wtl_inst (OS ins) G rT s s' cert max_pc pc = wtl_OS ins s s' max_pc pc"
 "wtl_inst (BR ins) G rT s s' cert max_pc pc = wtl_BR ins G s s' cert max_pc pc"


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
proof (induct i)
case LS
 show "?P (LS load_and_store)" by (induct load_and_store) auto
case CO
 show "?P (CO create_object)" by (induct create_object) auto
case MO
 show "?P (MO manipulate_object)" by (induct manipulate_object) auto
case CH
 show "?P (CH check_object)" by (induct check_object) auto
case MI
 show "?P (MI meth_inv)" proof (induct meth_inv)
 case Invoke
  have "\\<exists>x y. s0 = (x,y)" by (simp)
  thus "wtl_inst (MI (Invoke mname list)) G rT s0 s1 cert max_pc pc \\<longrightarrow>
        wtl_inst (MI (Invoke mname list)) G rT s0 s1' cert max_pc pc \\<longrightarrow>
        s1 = s1'"
  proof elim
    apply_end(clarsimp_tac, drule rev_eq, assumption+)
  qed auto
 qed
case MR
 show "?P (MR meth_ret)" by (induct meth_ret) auto
case OS 
 show "?P (OS op_stack)" by (induct op_stack) auto
case BR  
 show "?P (BR branch)" by (induct branch) auto
qed

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
    show "s1 = s1'"
      obtain s s' where   "?o s0 s" "?o s0 s'"
                  and l:  "?l list s s1 (Suc pc)"
                  and l': "?l list s' s1' (Suc pc)" by auto
      have "s=s'" by(rule wtl_inst_option_unique)
      with l l' Cons
      show ?thesis by blast
    qed
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
      show ?thesis 
        obtain s0 where wtlSuc: "wtl_inst_list list G rT s0 s' cert mpc (Suc pc)"
                  and   wtlOpt: "wtl_inst_option a G rT s s0 cert mpc pc" by auto
        from Cons
        show ?thesis 
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
    thus "wtl_inst_list ((a # list) @ y) G rT s0 s2 cert (pc + length ((a # list) @ y)) pc"
      obtain s' where 
       a: "wtl_inst_option a G rT s0 s' cert (Suc pc + length (list@y)) pc" and
       l: "wtl_inst_list list G rT s' s1 cert (Suc pc + length (list@y)) (Suc pc)" by auto      
      with y Cons
      have "wtl_inst_list (list @ y) G rT s' s2 cert (Suc pc + length (list @ y)) (Suc pc)"
        by (elim allE impE) (assumption, simp+)
      with a
      show ?thesis by (auto simp del: split_paired_Ex)
    qed
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
      thus "?p s0 pc"
        obtain s0' where opt: "wtl_inst_option a G rT s0 s0' cert (pc + length ((a # list) @ i # b)) pc"
                    and list: "wtl_inst_list list G rT s0' s1 cert (Suc pc + length (list @ i # b)) (Suc pc)"
          by (auto simp del: split_paired_Ex)
        with y z Cons
        have "wtl_inst_list (list @ [i]) G rT s0' s2 cert (Suc pc + length (list @ i # b)) (Suc pc)" 
        proof (elim allE impE) 
          from list show "wtl_inst_list list G rT s0' s1 cert (Suc pc + length (list @ i # b)) (Suc pc)" .
        qed auto
        with opt
        show ?thesis by (auto simp del: split_paired_Ex)
      qed
    qed
  qed
  with a i b
  show ?thesis 
  proof (elim allE impE)
    from a show "wtl_inst_list a G rT s0 s1 cert (0+length (a@i#b)) 0" by simp
  qed auto
qed

end
