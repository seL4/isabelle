(*  Title:      HOL/MicroJava/BV/Step.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

header {* Effect of instructions on the state type *}


theory Step = Convert :


text "Effect of instruction on the state type"
consts 
step :: "instr \\<times> jvm_prog \\<times> state_type \\<Rightarrow> state_type option"

recdef step "{}"
"step (Load idx,  G, (ST, LT))          = Some (the (LT ! idx) # ST, LT)"
"step (Store idx, G, (ts#ST, LT))       = Some (ST, LT[idx:= Some ts])"
"step (Bipush i, G, (ST, LT))           = Some (PrimT Integer # ST, LT)"
"step (Aconst_null, G, (ST, LT))        = Some (NT#ST,LT)"
"step (Getfield F C, G, (oT#ST, LT))    = Some (snd (the (field (G,C) F)) # ST, LT)"
"step (Putfield F C, G, (vT#oT#ST, LT)) = Some (ST,LT)"
"step (New C, G, (ST,LT))               = Some (Class C # ST, LT)"
"step (Checkcast C, G, (RefT rt#ST,LT)) = Some (Class C # ST,LT)"
"step (Pop, G, (ts#ST,LT))              = Some (ST,LT)"
"step (Dup, G, (ts#ST,LT))              = Some (ts#ts#ST,LT)"
"step (Dup_x1, G, (ts1#ts2#ST,LT))      = Some (ts1#ts2#ts1#ST,LT)"
"step (Dup_x2, G, (ts1#ts2#ts3#ST,LT))  = Some (ts1#ts2#ts3#ts1#ST,LT)"
"step (Swap, G, (ts1#ts2#ST,LT))        = Some (ts2#ts1#ST,LT)"
"step (IAdd, G, (PrimT Integer#PrimT Integer#ST,LT)) 
                                          = Some (PrimT Integer#ST,LT)"
"step (Ifcmpeq b, G, (ts1#ts2#ST,LT))   = Some (ST,LT)"
"step (Goto b, G, s)                    = Some s"
"step (Return, G, (T#ST,LT))            = None"   (* Return has no successor instruction in the same method *)
"step (Invoke C mn fpTs, G, (ST,LT))    = (let ST' = drop (length fpTs) ST in
                                              Some (fst (snd (the (method (G,C) (mn,fpTs))))#(tl ST'),LT))" 

"step (i,G,s)                           = None"


text "Conditions under which step is applicable"
consts
app :: "instr \\<times> jvm_prog \\<times> ty \\<times> state_type \\<Rightarrow> bool"

recdef app "{}"
"app (Load idx, G, rT, s)                  = (idx < length (snd s) \\<and> (snd s) ! idx \\<noteq> None)"
"app (Store idx, G, rT, (ts#ST, LT))       = (idx < length LT)"
"app (Bipush i, G, rT, s)                  = True"
"app (Aconst_null, G, rT, s)               = True"
"app (Getfield F C, G, rT, (oT#ST, LT))    = (is_class G C \\<and> 
                                              field (G,C) F \\<noteq> None \\<and>
                                              fst (the (field (G,C) F)) = C \\<and>
                                              G \\<turnstile> oT \\<preceq> (Class C))"
"app (Putfield F C, G, rT, (vT#oT#ST, LT)) = (is_class G C \\<and> 
                                              field (G,C) F \\<noteq> None \\<and>
                                              fst (the (field (G,C) F)) = C \\<and>
                                              G \\<turnstile> oT \\<preceq> (Class C) \\<and>
                                              G \\<turnstile> vT \\<preceq> (snd (the (field (G,C) F))))" 
"app (New C, G, rT, s)                     = (is_class G C)"
"app (Checkcast C, G, rT, (RefT rt#ST,LT)) = (is_class G C)"
"app (Pop, G, rT, (ts#ST,LT))              = True"
"app (Dup, G, rT, (ts#ST,LT))              = True"
"app (Dup_x1, G, rT, (ts1#ts2#ST,LT))      = True"
"app (Dup_x2, G, rT, (ts1#ts2#ts3#ST,LT))  = True"
"app (Swap, G, rT, (ts1#ts2#ST,LT))        = True"
"app (IAdd, G, rT, (PrimT Integer#PrimT Integer#ST,LT)) 
                                           = True"
"app (Ifcmpeq b, G, rT, (ts1#ts2#ST,LT))   = ((\\<exists> p. ts1 = PrimT p \\<and> ts1 = PrimT p) \\<or> 
                                              (\\<exists>r r'. ts1 = RefT r \\<and> ts2 = RefT r'))"
"app (Goto b, G, rT, s)                    = True"
"app (Return, G, rT, (T#ST,LT))            = (G \\<turnstile> T \\<preceq> rT)"
app_invoke:
"app (Invoke C mn fpTs, G, rT, s)          = (length fpTs < length (fst s) \\<and> 
                                              (let 
                                                apTs = rev (take (length fpTs) (fst s));
                                                X    = hd (drop (length fpTs) (fst s)) 
                                              in
                                                G \\<turnstile> X \\<preceq> Class C \\<and> 
                                                (\\<forall>(aT,fT)\\<in>set(zip apTs fpTs). G \\<turnstile> aT \\<preceq> fT) \\<and>
                                                method (G,C) (mn,fpTs) \\<noteq> None
                                             ))"

"app (i,G,rT,s)                            = False"


text {* \isa{p_count} of successor instructions *}

consts
succs :: "instr \\<Rightarrow> p_count \\<Rightarrow> p_count set"

primrec 
"succs (Load idx) pc         = {pc+1}"
"succs (Store idx) pc        = {pc+1}"
"succs (Bipush i) pc         = {pc+1}"
"succs (Aconst_null) pc      = {pc+1}"
"succs (Getfield F C) pc     = {pc+1}"
"succs (Putfield F C) pc     = {pc+1}"
"succs (New C) pc            = {pc+1}"
"succs (Checkcast C) pc      = {pc+1}"
"succs Pop pc                = {pc+1}"
"succs Dup pc                = {pc+1}"
"succs Dup_x1 pc             = {pc+1}"
"succs Dup_x2 pc             = {pc+1}"
"succs Swap pc               = {pc+1}"
"succs IAdd pc               = {pc+1}"
"succs (Ifcmpeq b) pc        = {pc+1, nat (int pc + b)}"
"succs (Goto b) pc           = {nat (int pc + b)}"
"succs Return pc             = {}"  
"succs (Invoke C mn fpTs) pc = {pc+1}"


lemma 1: "2 < length a \\<Longrightarrow> (\\<exists>l l' l'' ls. a = l#l'#l''#ls)"
proof (cases a)
  fix x xs assume "a = x#xs" "2 < length a"
  thus ?thesis by - (cases xs, simp, cases "tl xs", auto)
qed auto

lemma 2: "\\<not>(2 < length a) \\<Longrightarrow> a = [] \\<or> (\\<exists> l. a = [l]) \\<or> (\\<exists> l l'. a = [l,l'])"
proof -;
  assume "\\<not>(2 < length a)"
  hence "length a < (Suc 2)" by simp
  hence * : "length a = 0 \\<or> length a = 1 \\<or> length a = 2" by (auto simp add: less_Suc_eq)

  { 
    fix x 
    assume "length x = 1"
    hence "\\<exists> l. x = [l]"  by - (cases x, auto)
  } note 0 = this

  have "length a = 2 \\<Longrightarrow> \\<exists>l l'. a = [l,l']" by (cases a, auto dest: 0)
  with * show ?thesis by (auto dest: 0)
qed

text {* 
\mdeskip
simp rules for \isa{app} without patterns, better suited for proofs
\medskip
*}

lemma appStore[simp]:
"app (Store idx, G, rT, s) = (\\<exists> ts ST LT. s = (ts#ST,LT) \\<and> idx < length LT)"
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appGetField[simp]:
"app (Getfield F C, G, rT, s) = (\\<exists> oT ST LT. s = (oT#ST, LT) \\<and> is_class G C \\<and> 
                                 fst (the (field (G,C) F)) = C \\<and>
                                 field (G,C) F \\<noteq> None \\<and> G \\<turnstile> oT \\<preceq> (Class C))"
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appPutField[simp]:
"app (Putfield F C, G, rT, s) = (\\<exists> vT oT ST LT. s = (vT#oT#ST, LT) \\<and> is_class G C \\<and> 
                                 field (G,C) F \\<noteq> None \\<and> fst (the (field (G,C) F)) = C \\<and>
                                 G \\<turnstile> oT \\<preceq> (Class C) \\<and>
                                 G \\<turnstile> vT \\<preceq> (snd (the (field (G,C) F))))" 
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appCheckcast[simp]:
"app (Checkcast C, G, rT, s) = (\\<exists>rT ST LT. s = (RefT rT#ST,LT) \\<and> is_class G C)"
by (cases s, cases "fst s", simp, cases "hd (fst s)", auto)

lemma appPop[simp]:
"app (Pop, G, rT, s) = (\\<exists>ts ST LT. s = (ts#ST,LT))" 
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appDup[simp]:
"app (Dup, G, rT, s) = (\\<exists>ts ST LT. s = (ts#ST,LT))" 
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appDup_x1[simp]:
"app (Dup_x1, G, rT, s) = (\\<exists>ts1 ts2 ST LT. s = (ts1#ts2#ST,LT))" 
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appDup_x2[simp]:
"app (Dup_x2, G, rT, s) = (\\<exists>ts1 ts2 ts3 ST LT. s = (ts1#ts2#ts3#ST,LT))"
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appSwap[simp]:
"app (Swap, G, rT, s) = (\\<exists>ts1 ts2 ST LT. s = (ts1#ts2#ST,LT))" 
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appIAdd[simp]:
"app (IAdd, G, rT, s) = (\\<exists> ST LT. s = (PrimT Integer#PrimT Integer#ST,LT))"  (is "?app s = ?P s")
proof (cases s)
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
"app (Ifcmpeq b, G, rT, s) = (\\<exists>ts1 ts2 ST LT. s = (ts1#ts2#ST,LT) \\<and> 
                              ((\\<exists> p. ts1 = PrimT p \\<and> ts1 = PrimT p) \\<or>  
                               (\\<exists>r r'. ts1 = RefT r \\<and> ts2 = RefT r')))" 
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appReturn[simp]:
"app (Return, G, rT, s) = (\\<exists>T ST LT. s = (T#ST,LT) \\<and> (G \\<turnstile> T \\<preceq> rT))" 
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appInvoke[simp]:
"app (Invoke C mn fpTs, G, rT, s) = (\\<exists>apTs X ST LT.
                                       s = ((rev apTs) @ (X # ST), LT) \\<and> 
                                       length apTs = length fpTs \\<and> 
                                       G \\<turnstile> X \\<preceq> Class C \\<and>  
                                       (\\<forall>(aT,fT)\\<in>set(zip apTs fpTs). G \\<turnstile> aT \\<preceq> fT) \\<and> 
                                       method (G,C) (mn,fpTs) \\<noteq> None)" (is "?app s = ?P s")
proof (cases s)
  case Pair
  have "?app (a,b) \\<Longrightarrow> ?P (a,b)"
  proof -
    assume app: "?app (a,b)"
    hence "a = (rev (rev (take (length fpTs) a))) @ (drop (length fpTs) a) \\<and> length fpTs < length a" 
      (is "?a \\<and> ?l") by auto    
    hence "?a \\<and> 0 < length (drop (length fpTs) a)" (is "?a \\<and> ?l") by auto
    hence "?a \\<and> ?l \\<and> length (rev (take (length fpTs) a)) = length fpTs" by (auto simp add: min_def)
    hence "\\<exists>apTs ST. a = rev apTs @ ST \\<and> length apTs = length fpTs \\<and> 0 < length ST" by blast
    hence "\\<exists>apTs ST. a = rev apTs @ ST \\<and> length apTs = length fpTs \\<and> ST \\<noteq> []" by blast        
    hence "\\<exists>apTs ST. a = rev apTs @ ST \\<and> length apTs = length fpTs \\<and> (\\<exists>X ST'. ST = X#ST')" by (simp add: neq_Nil_conv)
    hence "\\<exists>apTs X ST. a = rev apTs @ X # ST \\<and> length apTs = length fpTs" by blast
    with app
    show ?thesis by auto blast
  qed
  with Pair have "?app s \\<Longrightarrow> ?P s" by simp
  thus ?thesis by auto
qed 

lemmas [simp del] = app_invoke

end
