(*  Title:      HOL/MicroJava/BV/Effect.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

header {* \isaheader{Effect of Instructions on the State Type} *}

theory Effect = JVMType + JVMExceptions:

types
  succ_type = "(p_count \<times> state_type option) list"

text {* Program counter of successor instructions: *}
consts
  succs :: "instr \<Rightarrow> p_count \<Rightarrow> p_count list"
primrec 
  "succs (Load idx) pc         = [pc+1]"
  "succs (Store idx) pc        = [pc+1]"
  "succs (LitPush v) pc        = [pc+1]"
  "succs (Getfield F C) pc     = [pc+1]"
  "succs (Putfield F C) pc     = [pc+1]"
  "succs (New C) pc            = [pc+1]"
  "succs (Checkcast C) pc      = [pc+1]"
  "succs Pop pc                = [pc+1]"
  "succs Dup pc                = [pc+1]"
  "succs Dup_x1 pc             = [pc+1]"
  "succs Dup_x2 pc             = [pc+1]"
  "succs Swap pc               = [pc+1]"
  "succs IAdd pc               = [pc+1]"
  "succs (Ifcmpeq b) pc        = [pc+1, nat (int pc + b)]"
  "succs (Goto b) pc           = [nat (int pc + b)]"
  "succs Return pc             = [pc]"  
  "succs (Invoke C mn fpTs) pc = [pc+1]"
  "succs Throw pc              = [pc]"

text "Effect of instruction on the state type:"
consts 
eff' :: "instr \<times> jvm_prog \<times> state_type \<Rightarrow> state_type"

recdef eff' "{}"
"eff' (Load idx,  G, (ST, LT))          = (ok_val (LT ! idx) # ST, LT)"
"eff' (Store idx, G, (ts#ST, LT))       = (ST, LT[idx:= OK ts])"
"eff' (LitPush v, G, (ST, LT))           = (the (typeof (\<lambda>v. None) v) # ST, LT)"
"eff' (Getfield F C, G, (oT#ST, LT))    = (snd (the (field (G,C) F)) # ST, LT)"
"eff' (Putfield F C, G, (vT#oT#ST, LT)) = (ST,LT)"
"eff' (New C, G, (ST,LT))               = (Class C # ST, LT)"
"eff' (Checkcast C, G, (RefT rt#ST,LT)) = (Class C # ST,LT)"
"eff' (Pop, G, (ts#ST,LT))              = (ST,LT)"
"eff' (Dup, G, (ts#ST,LT))              = (ts#ts#ST,LT)"
"eff' (Dup_x1, G, (ts1#ts2#ST,LT))      = (ts1#ts2#ts1#ST,LT)"
"eff' (Dup_x2, G, (ts1#ts2#ts3#ST,LT))  = (ts1#ts2#ts3#ts1#ST,LT)"
"eff' (Swap, G, (ts1#ts2#ST,LT))        = (ts2#ts1#ST,LT)"
"eff' (IAdd, G, (PrimT Integer#PrimT Integer#ST,LT)) 
                                         = (PrimT Integer#ST,LT)"
"eff' (Ifcmpeq b, G, (ts1#ts2#ST,LT))   = (ST,LT)"
"eff' (Goto b, G, s)                    = s"
  -- "Return has no successor instruction in the same method"
"eff' (Return, G, s)                    = s" 
  -- "Throw always terminates abruptly"
"eff' (Throw, G, s)                     = s"
"eff' (Invoke C mn fpTs, G, (ST,LT))    = (let ST' = drop (length fpTs) ST 
  in  (fst (snd (the (method (G,C) (mn,fpTs))))#(tl ST'),LT))" 


consts
  match_any :: "jvm_prog \<Rightarrow> p_count \<Rightarrow> exception_table \<Rightarrow> cname list"
primrec
  "match_any G pc [] = []"
  "match_any G pc (e#es) = (let (start_pc, end_pc, handler_pc, catch_type) = e;
                                es' = match_any G pc es 
                            in 
                            if start_pc <= pc \<and> pc < end_pc then catch_type#es' else es')"

consts
  match :: "jvm_prog \<Rightarrow> xcpt \<Rightarrow> p_count \<Rightarrow> exception_table \<Rightarrow> cname list"
primrec
  "match G X pc [] = []"
  "match G X pc (e#es) = 
  (if match_exception_entry G (Xcpt X) pc e then [Xcpt X] else match G X pc es)"

lemma match_some_entry:
  "match G X pc et = (if \<exists>e \<in> set et. match_exception_entry G (Xcpt X) pc e then [Xcpt X] else [])"
  by (induct et) auto

consts
  xcpt_names :: "instr \<times> jvm_prog \<times> p_count \<times> exception_table \<Rightarrow> cname list" 
recdef xcpt_names "{}"
  "xcpt_names (Getfield F C, G, pc, et) = match G NullPointer pc et" 
  "xcpt_names (Putfield F C, G, pc, et) = match G NullPointer pc et" 
  "xcpt_names (New C, G, pc, et)        = match G OutOfMemory pc et"
  "xcpt_names (Checkcast C, G, pc, et)  = match G ClassCast pc et"
  "xcpt_names (Throw, G, pc, et)        = match_any G pc et"
  "xcpt_names (Invoke C m p, G, pc, et) = match_any G pc et" 
  "xcpt_names (i, G, pc, et)            = []" 


constdefs
  xcpt_eff :: "instr \<Rightarrow> jvm_prog \<Rightarrow> p_count \<Rightarrow> state_type option \<Rightarrow> exception_table \<Rightarrow> succ_type"
  "xcpt_eff i G pc s et == 
   map (\<lambda>C. (the (match_exception_table G C pc et), case s of None \<Rightarrow> None | Some s' \<Rightarrow> Some ([Class C], snd s'))) 
       (xcpt_names (i,G,pc,et))"

  norm_eff :: "instr \<Rightarrow> jvm_prog \<Rightarrow> state_type option \<Rightarrow> state_type option"
  "norm_eff i G == option_map (\<lambda>s. eff' (i,G,s))"

  eff :: "instr \<Rightarrow> jvm_prog \<Rightarrow> p_count \<Rightarrow> exception_table \<Rightarrow> state_type option \<Rightarrow> succ_type"
  "eff i G pc et s == (map (\<lambda>pc'. (pc',norm_eff i G s)) (succs i pc)) @ (xcpt_eff i G pc s et)"

constdefs
  isPrimT :: "ty \<Rightarrow> bool"
  "isPrimT T == case T of PrimT T' \<Rightarrow> True | RefT T' \<Rightarrow> False"

  isRefT :: "ty \<Rightarrow> bool"
  "isRefT T == case T of PrimT T' \<Rightarrow> False | RefT T' \<Rightarrow> True"

lemma isPrimT [simp]:
  "isPrimT T = (\<exists>T'. T = PrimT T')" by (simp add: isPrimT_def split: ty.splits)

lemma isRefT [simp]:
  "isRefT T = (\<exists>T'. T = RefT T')" by (simp add: isRefT_def split: ty.splits)


lemma "list_all2 P a b \<Longrightarrow> \<forall>(x,y) \<in> set (zip a b). P x y"
  by (simp add: list_all2_def) 


text "Conditions under which eff is applicable:"
consts
app' :: "instr \<times> jvm_prog \<times> p_count \<times> nat \<times> ty \<times> state_type \<Rightarrow> bool"

recdef app' "{}"
"app' (Load idx, G, pc, maxs, rT, s) = 
  (idx < length (snd s) \<and> (snd s) ! idx \<noteq> Err \<and> length (fst s) < maxs)"
"app' (Store idx, G, pc, maxs, rT, (ts#ST, LT)) = 
  (idx < length LT)"
"app' (LitPush v, G, pc, maxs, rT, s) = 
  (length (fst s) < maxs \<and> typeof (\<lambda>t. None) v \<noteq> None)"
"app' (Getfield F C, G, pc, maxs, rT, (oT#ST, LT)) = 
  (is_class G C \<and> field (G,C) F \<noteq> None \<and> fst (the (field (G,C) F)) = C \<and> 
  G \<turnstile> oT \<preceq> (Class C))"
"app' (Putfield F C, G, pc, maxs, rT, (vT#oT#ST, LT)) = 
  (is_class G C \<and> field (G,C) F \<noteq> None \<and> fst (the (field (G,C) F)) = C \<and>
  G \<turnstile> oT \<preceq> (Class C) \<and> G \<turnstile> vT \<preceq> (snd (the (field (G,C) F))))" 
"app' (New C, G, pc, maxs, rT, s) = 
  (is_class G C \<and> length (fst s) < maxs)"
"app' (Checkcast C, G, pc, maxs, rT, (RefT rt#ST,LT)) = 
  (is_class G C)"
"app' (Pop, G, pc, maxs, rT, (ts#ST,LT)) = 
  True"
"app' (Dup, G, pc, maxs, rT, (ts#ST,LT)) = 
  (1+length ST < maxs)"
"app' (Dup_x1, G, pc, maxs, rT, (ts1#ts2#ST,LT)) = 
  (2+length ST < maxs)"
"app' (Dup_x2, G, pc, maxs, rT, (ts1#ts2#ts3#ST,LT)) = 
  (3+length ST < maxs)"
"app' (Swap, G, pc, maxs, rT, (ts1#ts2#ST,LT)) = 
  True"
"app' (IAdd, G, pc, maxs, rT, (PrimT Integer#PrimT Integer#ST,LT)) =
  True"
"app' (Ifcmpeq b, G, pc, maxs, rT, (ts#ts'#ST,LT)) = 
  (0 \<le> int pc + b \<and> (isPrimT ts \<and> ts' = ts \<or> isRefT ts \<and> isRefT ts'))"
"app' (Goto b, G, pc, maxs, rT, s) = 
  (0 \<le> int pc + b)"
"app' (Return, G, pc, maxs, rT, (T#ST,LT)) = 
  (G \<turnstile> T \<preceq> rT)"
"app' (Throw, G, pc, maxs, rT, (T#ST,LT)) = 
  isRefT T"
"app' (Invoke C mn fpTs, G, pc, maxs, rT, s) = 
  (length fpTs < length (fst s) \<and> 
  (let apTs = rev (take (length fpTs) (fst s));
       X    = hd (drop (length fpTs) (fst s)) 
   in  
       G \<turnstile> X \<preceq> Class C \<and> is_class G C \<and> method (G,C) (mn,fpTs) \<noteq> None \<and>
       list_all2 (\<lambda>x y. G \<turnstile> x \<preceq> y) apTs fpTs))"
  
"app' (i,G, pc,maxs,rT,s) = False"

constdefs
  xcpt_app :: "instr \<Rightarrow> jvm_prog \<Rightarrow> nat \<Rightarrow> exception_table \<Rightarrow> bool"
  "xcpt_app i G pc et \<equiv> \<forall>C\<in>set(xcpt_names (i,G,pc,et)). is_class G C"

  app :: "instr \<Rightarrow> jvm_prog \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> exception_table \<Rightarrow> state_type option \<Rightarrow> bool"
  "app i G maxs rT pc et s == case s of None \<Rightarrow> True | Some t \<Rightarrow> app' (i,G,pc,maxs,rT,t) \<and> xcpt_app i G pc et"


lemma match_any_match_table:
  "C \<in> set (match_any G pc et) \<Longrightarrow> match_exception_table G C pc et \<noteq> None"
  apply (induct et)
   apply simp
  apply simp
  apply clarify
  apply (simp split: split_if_asm)
  apply (auto simp add: match_exception_entry_def)
  done

lemma match_X_match_table:
  "C \<in> set (match G X pc et) \<Longrightarrow> match_exception_table G C pc et \<noteq> None"
  apply (induct et)
   apply simp
  apply (simp split: split_if_asm)
  done

lemma xcpt_names_in_et:
  "C \<in> set (xcpt_names (i,G,pc,et)) \<Longrightarrow> 
  \<exists>e \<in> set et. the (match_exception_table G C pc et) = fst (snd (snd e))"
  apply (cases i)
  apply (auto dest!: match_any_match_table match_X_match_table 
              dest: match_exception_table_in_et)
  done


lemma 1: "2 < length a \<Longrightarrow> (\<exists>l l' l'' ls. a = l#l'#l''#ls)"
proof (cases a)
  fix x xs assume "a = x#xs" "2 < length a"
  thus ?thesis by - (cases xs, simp, cases "tl xs", auto)
qed auto

lemma 2: "\<not>(2 < length a) \<Longrightarrow> a = [] \<or> (\<exists> l. a = [l]) \<or> (\<exists> l l'. a = [l,l'])"
proof -;
  assume "\<not>(2 < length a)"
  hence "length a < (Suc (Suc (Suc 0)))" by simp
  hence * : "length a = 0 \<or> length a = Suc 0 \<or> length a = Suc (Suc 0)" 
    by (auto simp add: less_Suc_eq)

  { 
    fix x 
    assume "length x = Suc 0"
    hence "\<exists> l. x = [l]"  by - (cases x, auto)
  } note 0 = this

  have "length a = Suc (Suc 0) \<Longrightarrow> \<exists>l l'. a = [l,l']" by (cases a, auto dest: 0)
  with * show ?thesis by (auto dest: 0)
qed

lemmas [simp] = app_def xcpt_app_def

text {* 
\medskip
simp rules for @{term app}
*}
lemma appNone[simp]: "app i G maxs rT pc et None = True" by simp


lemma appLoad[simp]:
"(app (Load idx) G maxs rT pc et (Some s)) = (\<exists>ST LT. s = (ST,LT) \<and> idx < length LT \<and> LT!idx \<noteq> Err \<and> length ST < maxs)"
  by (cases s, simp)

lemma appStore[simp]:
"(app (Store idx) G maxs rT pc et (Some s)) = (\<exists>ts ST LT. s = (ts#ST,LT) \<and> idx < length LT)"
  by (cases s, cases "2 < length (fst s)", auto dest: 1 2)

lemma appLitPush[simp]:
"(app (LitPush v) G maxs rT pc et (Some s)) = (\<exists>ST LT. s = (ST,LT) \<and> length ST < maxs \<and> typeof (\<lambda>v. None) v \<noteq> None)"
  by (cases s, simp)

lemma appGetField[simp]:
"(app (Getfield F C) G maxs rT pc et (Some s)) = 
 (\<exists> oT vT ST LT. s = (oT#ST, LT) \<and> is_class G C \<and>  
  field (G,C) F = Some (C,vT) \<and> G \<turnstile> oT \<preceq> (Class C) \<and> (\<forall>x \<in> set (match G NullPointer pc et). is_class G x))"
  by (cases s, cases "2 <length (fst s)", auto dest!: 1 2)

lemma appPutField[simp]:
"(app (Putfield F C) G maxs rT pc et (Some s)) = 
 (\<exists> vT vT' oT ST LT. s = (vT#oT#ST, LT) \<and> is_class G C \<and> 
  field (G,C) F = Some (C, vT') \<and> G \<turnstile> oT \<preceq> (Class C) \<and> G \<turnstile> vT \<preceq> vT' \<and>
  (\<forall>x \<in> set (match G NullPointer pc et). is_class G x))"
  by (cases s, cases "2 <length (fst s)", auto dest!: 1 2)

lemma appNew[simp]:
  "(app (New C) G maxs rT pc et (Some s)) = 
  (\<exists>ST LT. s=(ST,LT) \<and> is_class G C \<and> length ST < maxs \<and>
  (\<forall>x \<in> set (match G OutOfMemory pc et). is_class G x))"
  by (cases s, simp)

lemma appCheckcast[simp]: 
  "(app (Checkcast C) G maxs rT pc et (Some s)) =  
  (\<exists>rT ST LT. s = (RefT rT#ST,LT) \<and> is_class G C \<and>
  (\<forall>x \<in> set (match G ClassCast pc et). is_class G x))"
  by (cases s, cases "fst s", simp add: app_def) (cases "hd (fst s)", auto)

lemma appPop[simp]: 
"(app Pop G maxs rT pc et (Some s)) = (\<exists>ts ST LT. s = (ts#ST,LT))"
  by (cases s, cases "2 <length (fst s)", auto dest: 1 2)


lemma appDup[simp]:
"(app Dup G maxs rT pc et (Some s)) = (\<exists>ts ST LT. s = (ts#ST,LT) \<and> 1+length ST < maxs)" 
  by (cases s, cases "2 <length (fst s)", auto dest: 1 2)


lemma appDup_x1[simp]:
"(app Dup_x1 G maxs rT pc et (Some s)) = (\<exists>ts1 ts2 ST LT. s = (ts1#ts2#ST,LT) \<and> 2+length ST < maxs)" 
  by (cases s, cases "2 <length (fst s)", auto dest: 1 2)


lemma appDup_x2[simp]:
"(app Dup_x2 G maxs rT pc et (Some s)) = (\<exists>ts1 ts2 ts3 ST LT. s = (ts1#ts2#ts3#ST,LT) \<and> 3+length ST < maxs)"
  by (cases s, cases "2 <length (fst s)", auto dest: 1 2)


lemma appSwap[simp]:
"app Swap G maxs rT pc et (Some s) = (\<exists>ts1 ts2 ST LT. s = (ts1#ts2#ST,LT))" 
  by (cases s, cases "2 <length (fst s)", auto dest: 1 2)


lemma appIAdd[simp]:
"app IAdd G maxs rT pc et (Some s) = (\<exists> ST LT. s = (PrimT Integer#PrimT Integer#ST,LT))"
  (is "?app s = ?P s")
proof (cases (open) s)
  case Pair
  have "?app (a,b) = ?P (a,b)"
  proof (cases "a")
    fix t ts assume a: "a = t#ts"
    show ?thesis
    proof (cases t)
      fix p assume p: "t = PrimT p"
      show ?thesis
      proof (cases p)
        assume ip: "p = Integer"
        show ?thesis
        proof (cases ts)
          fix t' ts' assume t': "ts = t' # ts'"
          show ?thesis
          proof (cases t')
            fix p' assume "t' = PrimT p'"
            with t' ip p a
            show ?thesis by - (cases p', auto)
          qed (auto simp add: a p ip t')
        qed (auto simp add: a p ip)
      qed (auto simp add: a p)
    qed (auto simp add: a)
  qed auto
  with Pair show ?thesis by simp
qed


lemma appIfcmpeq[simp]:
"app (Ifcmpeq b) G maxs rT pc et (Some s) = 
  (\<exists>ts1 ts2 ST LT. s = (ts1#ts2#ST,LT) \<and> 0 \<le> int pc + b \<and>
  ((\<exists> p. ts1 = PrimT p \<and> ts2 = PrimT p) \<or> (\<exists>r r'. ts1 = RefT r \<and> ts2 = RefT r')))" 
  by (cases s, cases "2 <length (fst s)", auto dest!: 1 2)

lemma appReturn[simp]:
"app Return G maxs rT pc et (Some s) = (\<exists>T ST LT. s = (T#ST,LT) \<and> (G \<turnstile> T \<preceq> rT))" 
  by (cases s, cases "2 <length (fst s)", auto dest: 1 2)

lemma appGoto[simp]:
"app (Goto b) G maxs rT pc et (Some s) = (0 \<le> int pc + b)"
  by simp

lemma appThrow[simp]:
  "app Throw G maxs rT pc et (Some s) = 
  (\<exists>T ST LT r. s=(T#ST,LT) \<and> T = RefT r \<and> (\<forall>C \<in> set (match_any G pc et). is_class G C))"
  by (cases s, cases "2 < length (fst s)", auto dest: 1 2)

lemma appInvoke[simp]:
"app (Invoke C mn fpTs) G maxs rT pc et (Some s) = (\<exists>apTs X ST LT mD' rT' b'.
  s = ((rev apTs) @ (X # ST), LT) \<and> length apTs = length fpTs \<and> is_class G C \<and>
  G \<turnstile> X \<preceq> Class C \<and> (\<forall>(aT,fT)\<in>set(zip apTs fpTs). G \<turnstile> aT \<preceq> fT) \<and> 
  method (G,C) (mn,fpTs) = Some (mD', rT', b') \<and> 
  (\<forall>C \<in> set (match_any G pc et). is_class G C))" (is "?app s = ?P s")
proof (cases (open) s)
  note list_all2_def [simp]
  case Pair
  have "?app (a,b) \<Longrightarrow> ?P (a,b)"
  proof -
    assume app: "?app (a,b)"
    hence "a = (rev (rev (take (length fpTs) a))) @ (drop (length fpTs) a) \<and> 
           length fpTs < length a" (is "?a \<and> ?l") 
      by (auto simp add: app_def)
    hence "?a \<and> 0 < length (drop (length fpTs) a)" (is "?a \<and> ?l") 
      by auto
    hence "?a \<and> ?l \<and> length (rev (take (length fpTs) a)) = length fpTs" 
      by (auto simp add: min_def)
    hence "\<exists>apTs ST. a = rev apTs @ ST \<and> length apTs = length fpTs \<and> 0 < length ST" 
      by blast
    hence "\<exists>apTs ST. a = rev apTs @ ST \<and> length apTs = length fpTs \<and> ST \<noteq> []" 
      by blast
    hence "\<exists>apTs ST. a = rev apTs @ ST \<and> length apTs = length fpTs \<and> 
           (\<exists>X ST'. ST = X#ST')" 
      by (simp add: neq_Nil_conv)
    hence "\<exists>apTs X ST. a = rev apTs @ X # ST \<and> length apTs = length fpTs" 
      by blast
    with app
    show ?thesis by (unfold app_def, clarsimp) blast
  qed
  with Pair 
  have "?app s \<Longrightarrow> ?P s" by (simp only:)
  moreover
  have "?P s \<Longrightarrow> ?app s" by (unfold app_def) (clarsimp simp add: min_def)
  ultimately
  show ?thesis by (rule iffI) 
qed 

lemma effNone: 
  "(pc', s') \<in> set (eff i G pc et None) \<Longrightarrow> s' = None"
  by (auto simp add: eff_def xcpt_eff_def norm_eff_def)


text {* some helpers to make the specification directly executable: *}
declare list_all2_Nil [code]
declare list_all2_Cons [code]

lemma xcpt_app_lemma [code]:
  "xcpt_app i G pc et = list_all (is_class G) (xcpt_names (i, G, pc, et))"
  by (simp add: list_all_conv)

lemmas [simp del] = app_def xcpt_app_def

end
