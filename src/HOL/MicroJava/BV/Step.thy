(*  Title:      HOL/MicroJava/BV/Step.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

header {* Effect of instructions on the state type *}


theory Step = JVMType + JVMExec:


text "Effect of instruction on the state type:"
consts 
step' :: "instr \<times> jvm_prog \<times> state_type => state_type"

recdef step' "{}"
"step' (Load idx,  G, (ST, LT))          = (ok_val (LT ! idx) # ST, LT)"
"step' (Store idx, G, (ts#ST, LT))       = (ST, LT[idx:= OK ts])"
"step' (LitPush v, G, (ST, LT))           = (the (typeof (\<lambda>v. None) v) # ST, LT)"
"step' (Getfield F C, G, (oT#ST, LT))    = (snd (the (field (G,C) F)) # ST, LT)"
"step' (Putfield F C, G, (vT#oT#ST, LT)) = (ST,LT)"
"step' (New C, G, (ST,LT))               = (Class C # ST, LT)"
"step' (Checkcast C, G, (RefT rt#ST,LT)) = (Class C # ST,LT)"
"step' (Pop, G, (ts#ST,LT))              = (ST,LT)"
"step' (Dup, G, (ts#ST,LT))              = (ts#ts#ST,LT)"
"step' (Dup_x1, G, (ts1#ts2#ST,LT))      = (ts1#ts2#ts1#ST,LT)"
"step' (Dup_x2, G, (ts1#ts2#ts3#ST,LT))  = (ts1#ts2#ts3#ts1#ST,LT)"
"step' (Swap, G, (ts1#ts2#ST,LT))        = (ts2#ts1#ST,LT)"
"step' (IAdd, G, (PrimT Integer#PrimT Integer#ST,LT)) 
                                         = (PrimT Integer#ST,LT)"
"step' (Ifcmpeq b, G, (ts1#ts2#ST,LT))   = (ST,LT)"
"step' (Goto b, G, s)                    = s"
  (* Return has no successor instruction in the same method *)
"step' (Return, G, s)                    = s" 
"step' (Invoke C mn fpTs, G, (ST,LT))    = (let ST' = drop (length fpTs) ST 
  in  (fst (snd (the (method (G,C) (mn,fpTs))))#(tl ST'),LT))" 


constdefs
  step :: "instr => jvm_prog => state_type option => state_type option"
  "step i G == option_map (\<lambda>s. step' (i,G,s))"


text "Conditions under which step is applicable:"
consts
app' :: "instr \<times> jvm_prog \<times> nat \<times> ty \<times> state_type => bool"

recdef app' "{}"
"app' (Load idx, G, maxs, rT, s)                  = (idx < length (snd s) \<and> 
                                                    (snd s) ! idx \<noteq> Err \<and> 
                                                    maxs < length (fst s))"
"app' (Store idx, G, maxs, rT, (ts#ST, LT))       = (idx < length LT)"
"app' (LitPush v, G, maxs, rT, s)                  = (maxs < length (fst s) \<and> typeof (\<lambda>t. None) v \<noteq> None)"
"app' (Getfield F C, G, maxs, rT, (oT#ST, LT))    = (is_class G C \<and>
                                              field (G,C) F \<noteq> None \<and>
                                              fst (the (field (G,C) F)) = C \<and>
                                              G \<turnstile> oT \<preceq> (Class C))"
"app' (Putfield F C, G, maxs, rT, (vT#oT#ST, LT)) = (is_class G C \<and> 
                                              field (G,C) F \<noteq> None \<and>
                                              fst (the (field (G,C) F)) = C \<and>
                                              G \<turnstile> oT \<preceq> (Class C) \<and>
                                              G \<turnstile> vT \<preceq> (snd (the (field (G,C) F))))" 
"app' (New C, G, maxs, rT, s)                     = (is_class G C \<and> maxs < length (fst s))"
"app' (Checkcast C, G, maxs, rT, (RefT rt#ST,LT)) = (is_class G C)"
"app' (Pop, G, maxs, rT, (ts#ST,LT))              = True"
"app' (Dup, G, maxs, rT, (ts#ST,LT))              = (maxs < Suc (length ST))"
"app' (Dup_x1, G, maxs, rT, (ts1#ts2#ST,LT))      = (maxs < Suc (Suc (length ST)))"
"app' (Dup_x2, G, maxs, rT, (ts1#ts2#ts3#ST,LT))  = (maxs < Suc (Suc (Suc (length ST))))"
"app' (Swap, G, maxs, rT, (ts1#ts2#ST,LT))        = True"
"app' (IAdd, G, maxs, rT, (PrimT Integer#PrimT Integer#ST,LT)) 
                                                 = True"
"app' (Ifcmpeq b, G, maxs, rT, (ts#ts'#ST,LT))    = ((\<exists>p. ts = PrimT p \<and> ts' = PrimT p) \<or> 
                                              (\<exists>r r'. ts = RefT r \<and> ts' = RefT r'))"
"app' (Goto b, G, maxs, rT, s)                    = True"
"app' (Return, G, maxs, rT, (T#ST,LT))            = (G \<turnstile> T \<preceq> rT)"
"app' (Invoke C mn fpTs, G, maxs, rT, s)          = 
   (length fpTs < length (fst s) \<and> 
   (let apTs = rev (take (length fpTs) (fst s));
        X    = hd (drop (length fpTs) (fst s)) 
    in  
        G \<turnstile> X \<preceq> Class C \<and> is_class G C \<and> method (G,C) (mn,fpTs) \<noteq> None \<and> 
        (\<forall>(aT,fT)\<in>set(zip apTs fpTs). G \<turnstile> aT \<preceq> fT)))"

"app' (i,G,maxs,rT,s)                             = False"


constdefs
  app :: "instr => jvm_prog => nat => ty => state_type option => bool"
  "app i G maxs rT s == case s of None => True | Some t => app' (i,G,maxs,rT,t)"

text {* program counter of successor instructions: *}

consts
succs :: "instr => p_count => p_count list"

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


lemma 1: "Suc (Suc 0) < length a ==> (\<exists>l l' l'' ls. a = l#l'#l''#ls)"
proof (cases a)
  fix x xs assume "a = x#xs" "Suc (Suc 0) < length a"
  thus ?thesis by - (cases xs, simp, cases "tl xs", auto)
qed auto

lemma 2: "\<not>(Suc (Suc 0) < length a) ==> a = [] \<or> (\<exists> l. a = [l]) \<or> (\<exists> l l'. a = [l,l'])"
proof -;
  assume "\<not>(Suc (Suc 0) < length a)"
  hence "length a < Suc (Suc (Suc 0))" by simp
  hence * : "length a = 0 \<or> length a = Suc 0 \<or> length a = Suc (Suc 0)" 
    by (auto simp add: less_Suc_eq)

  { 
    fix x 
    assume "length x = Suc 0"
    hence "\<exists> l. x = [l]"  by - (cases x, auto)
  } note 0 = this

  have "length a = Suc (Suc 0) ==> \<exists>l l'. a = [l,l']" by (cases a, auto dest: 0)
  with * show ?thesis by (auto dest: 0)
qed

text {* 
\medskip
simp rules for @{term app}
*}
lemma appNone[simp]:
"app i G maxs rT None = True"
  by (simp add: app_def)


lemma appLoad[simp]:
"(app (Load idx) G maxs rT (Some s)) = (idx < length (snd s) \<and> (snd s) ! idx \<noteq> Err \<and> maxs < length (fst s))"
  by (simp add: app_def)

lemma appStore[simp]:
"(app (Store idx) G maxs rT (Some s)) = (\<exists> ts ST LT. s = (ts#ST,LT) \<and> idx < length LT)"
  by (cases s, cases "Suc (Suc 0) < length (fst s)", auto dest: 1 2 simp add: app_def)

lemma appLitPush[simp]:
"(app (LitPush v) G maxs rT (Some s)) = (maxs < length (fst s) \<and> typeof (\<lambda>v. None) v \<noteq> None)"
  by (cases s, simp add: app_def)

lemma appGetField[simp]:
"(app (Getfield F C) G maxs rT (Some s)) = 
 (\<exists> oT vT ST LT. s = (oT#ST, LT) \<and> is_class G C \<and>  
  field (G,C) F = Some (C,vT) \<and> G \<turnstile> oT \<preceq> (Class C))"
  by (cases s, cases "Suc (Suc 0) < length (fst s)", auto dest!: 1 2 simp add: app_def)

lemma appPutField[simp]:
"(app (Putfield F C) G maxs rT (Some s)) = 
 (\<exists> vT vT' oT ST LT. s = (vT#oT#ST, LT) \<and> is_class G C \<and> 
  field (G,C) F = Some (C, vT') \<and> G \<turnstile> oT \<preceq> (Class C) \<and> G \<turnstile> vT \<preceq> vT')"
  by (cases s, cases "Suc (Suc 0) < length (fst s)", auto dest!: 1 2 simp add: app_def)

lemma appNew[simp]:
"(app (New C) G maxs rT (Some s)) = (is_class G C \<and> maxs < length (fst s))"
  by (simp add: app_def)

lemma appCheckcast[simp]:
"(app (Checkcast C) G maxs rT (Some s)) = (\<exists>rT ST LT. s = (RefT rT#ST,LT) \<and> is_class G C)"
  by (cases s, cases "fst s", simp add: app_def)
     (cases "hd (fst s)", auto simp add: app_def)

lemma appPop[simp]:
"(app Pop G maxs rT (Some s)) = (\<exists>ts ST LT. s = (ts#ST,LT))" 
  by (cases s, cases "Suc (Suc 0) < length (fst s)", auto dest: 1 2 simp add: app_def)


lemma appDup[simp]:
"(app Dup G maxs rT (Some s)) = (\<exists>ts ST LT. s = (ts#ST,LT) \<and> maxs < Suc (length ST))" 
  by (cases s, cases "Suc (Suc 0) < length (fst s)", auto dest: 1 2 simp add: app_def)


lemma appDup_x1[simp]:
"(app Dup_x1 G maxs rT (Some s)) = (\<exists>ts1 ts2 ST LT. s = (ts1#ts2#ST,LT) \<and> maxs < Suc (Suc (length ST)))" 
  by (cases s, cases "Suc (Suc 0) < length (fst s)", auto dest: 1 2 simp add: app_def)


lemma appDup_x2[simp]:
"(app Dup_x2 G maxs rT (Some s)) = (\<exists>ts1 ts2 ts3 ST LT. s = (ts1#ts2#ts3#ST,LT) \<and> maxs < Suc (Suc (Suc (length ST))))"
  by (cases s, cases "Suc (Suc 0) < length (fst s)", auto dest: 1 2 simp add: app_def)


lemma appSwap[simp]:
"app Swap G maxs rT (Some s) = (\<exists>ts1 ts2 ST LT. s = (ts1#ts2#ST,LT))" 
  by (cases s, cases "Suc (Suc 0) < length (fst s)", auto dest: 1 2 simp add: app_def)


lemma appIAdd[simp]:
"app IAdd G maxs rT (Some s) = (\<exists> ST LT. s = (PrimT Integer#PrimT Integer#ST,LT))"  
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
            show ?thesis by - (cases p', auto simp add: app_def)
          qed (auto simp add: a p ip t' app_def)
        qed (auto simp add: a p ip app_def)
      qed (auto simp add: a p app_def)
    qed (auto simp add: a app_def)
  qed (auto simp add: app_def)
  with Pair show ?thesis by simp
qed


lemma appIfcmpeq[simp]:
"app (Ifcmpeq b) G maxs rT (Some s) = (\<exists>ts1 ts2 ST LT. s = (ts1#ts2#ST,LT) \<and> 
 ((\<exists> p. ts1 = PrimT p \<and> ts2 = PrimT p) \<or> (\<exists>r r'. ts1 = RefT r \<and> ts2 = RefT r')))" 
  by (cases s, cases "Suc (Suc 0) < length (fst s)", auto dest: 1 2 simp add: app_def)


lemma appReturn[simp]:
"app Return G maxs rT (Some s) = (\<exists>T ST LT. s = (T#ST,LT) \<and> (G \<turnstile> T \<preceq> rT))" 
  by (cases s, cases "Suc (Suc 0) < length (fst s)", auto dest: 1 2 simp add: app_def)

lemma appGoto[simp]:
"app (Goto branch) G maxs rT (Some s) = True"
  by (simp add: app_def)

lemma appInvoke[simp]:
"app (Invoke C mn fpTs) G maxs rT (Some s) = (\<exists>apTs X ST LT mD' rT' b'.
  s = ((rev apTs) @ (X # ST), LT) \<and> length apTs = length fpTs \<and> is_class G C \<and>
  G \<turnstile> X \<preceq> Class C \<and> (\<forall>(aT,fT)\<in>set(zip apTs fpTs). G \<turnstile> aT \<preceq> fT) \<and> 
  method (G,C) (mn,fpTs) = Some (mD', rT', b'))" (is "?app s = ?P s")
proof (cases (open) s)
  case Pair
  have "?app (a,b) ==> ?P (a,b)"
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
    show ?thesis 
      by (unfold app_def, clarsimp) blast
  qed
  with Pair 
  have "?app s ==> ?P s" by simp
  moreover
  have "?P s \<Longrightarrow> ?app s" by (unfold app_def) clarsimp
  ultimately
  show ?thesis by blast
qed 

lemma step_Some:
  "step i G (Some s) \<noteq> None"
  by (simp add: step_def)

lemma step_None [simp]:
  "step i G None = None"
  by (simp add: step_def)

end
