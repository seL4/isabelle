(*  Title:      HOL/MicroJava/BV/Step.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

header {* Effect of instructions on the state type *}


theory Step = Convert :


(* effect of instruction on the state type *)
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


(* conditions under which step is applicable *)
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


(* p_count of successor instructions *)
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

lemma appStore[simp]:
"app (Store idx, G, rT, s) = (\\<exists> ts ST LT. s = (ts#ST,LT) \\<and> idx < length LT)" (is "?app s = ?P s")
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appGetField[simp]:
"app (Getfield F C, G, rT, s) = (\\<exists> oT ST LT. s = (oT#ST, LT) \\<and> is_class G C \\<and> 
                                 fst (the (field (G,C) F)) = C \\<and>
                                 field (G,C) F \\<noteq> None \\<and> G \\<turnstile> oT \\<preceq> (Class C))" (is "?app s = ?P s")
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appPutField[simp]:
"app (Putfield F C, G, rT, s) = (\\<exists> vT oT ST LT. s = (vT#oT#ST, LT) \\<and> is_class G C \\<and> 
                                 field (G,C) F \\<noteq> None \\<and> fst (the (field (G,C) F)) = C \\<and>
                                 G \\<turnstile> oT \\<preceq> (Class C) \\<and>
                                 G \\<turnstile> vT \\<preceq> (snd (the (field (G,C) F))))" (is "?app s = ?P s")
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appCheckcast[simp]:
"app (Checkcast C, G, rT, s) = (\\<exists>rT ST LT. s = (RefT rT#ST,LT) \\<and> is_class G C)" (is "?app s = ?P s")
by (cases s, cases "fst s", simp, cases "hd (fst s)", auto)

lemma appPop[simp]:
"app (Pop, G, rT, s) = (\\<exists>ts ST LT. s = (ts#ST,LT))" (is "?app s = ?P s")
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appDup[simp]:
"app (Dup, G, rT, s) = (\\<exists>ts ST LT. s = (ts#ST,LT))" (is "?app s = ?P s")
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appDup_x1[simp]:
"app (Dup_x1, G, rT, s) = (\\<exists>ts1 ts2 ST LT. s = (ts1#ts2#ST,LT))" (is "?app s = ?P s")
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appDup_x2[simp]:
"app (Dup_x2, G, rT, s) = (\\<exists>ts1 ts2 ts3 ST LT. s = (ts1#ts2#ts3#ST,LT))"(is "?app s = ?P s")
by (cases s, cases "2 < length (fst s)", auto dest: 1 2)


lemma appSwap[simp]:
"app (Swap, G, rT, s) = (\\<exists>ts1 ts2 ST LT. s = (ts1#ts2#ST,LT))" (is "?app s = ?P s")
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
lemmas [trans] = sup_loc_trans

ML_setup {* bind_thm ("widen_RefT", widen_RefT) *}
ML_setup {* bind_thm ("widen_RefT2", widen_RefT2) *}



lemma app_step_some:
"\\<lbrakk>app (i,G,rT,s); succs i pc \\<noteq> {} \\<rbrakk> \\<Longrightarrow> step (i,G,s) \\<noteq> None";
by (cases s, cases i, auto)

lemma sup_state_length:
"G \\<turnstile> s2 <=s s1 \\<Longrightarrow> length (fst s2) = length (fst s1) \\<and> length (snd s2) = length (snd s1)"
  by (cases s1, cases s2, simp add: sup_state_length_fst sup_state_length_snd)
  
lemma PrimT_PrimT: "(G \\<turnstile> xb \\<preceq> PrimT p) = (xb = PrimT p)"
proof
  show "xb = PrimT p \\<Longrightarrow> G \\<turnstile> xb \\<preceq> PrimT p" by blast

  show "G\\<turnstile> xb \\<preceq> PrimT p \\<Longrightarrow> xb = PrimT p"
  proof (cases xb)
    fix prim
    assume "xb = PrimT prim" "G\\<turnstile>xb\\<preceq>PrimT p"
    thus ?thesis by simp
  next
    fix ref
    assume "G\\<turnstile>xb\\<preceq>PrimT p" "xb = RefT ref"
    thus ?thesis by simp (rule widen_RefT [elimify], auto)
  qed
qed

lemma sup_loc_some [rulify]:
"\\<forall> y n. (G \\<turnstile> b <=l y) \\<longrightarrow> n < length y \\<longrightarrow> y!n = Some t \\<longrightarrow> (\\<exists>t. b!n = Some t \\<and> (G \\<turnstile> (b!n) <=o (y!n)))" (is "?P b")
proof (induct "?P" b)
  show "?P []" by simp

  case Cons
  show "?P (a#list)"
  proof (clarsimp simp add: list_all2_Cons1 sup_loc_def)
    fix z zs n
    assume * : 
      "G \\<turnstile> a <=o z" "list_all2 (sup_ty_opt G) list zs" 
      "n < Suc (length zs)" "(z # zs) ! n = Some t"

    show "(\\<exists>t. (a # list) ! n = Some t) \\<and> G \\<turnstile>(a # list) ! n <=o Some t" 
    proof (cases n) 
      case 0
      with * show ?thesis by (simp add: sup_ty_opt_some)
    next
      case Suc
      with Cons *
      show ?thesis by (simp add: sup_loc_def)
    qed
  qed
qed
   

lemma all_widen_is_sup_loc:
"\\<forall>b. length a = length b \\<longrightarrow> (\\<forall>x\\<in>set (zip a b). x \\<in> widen G) = (G \\<turnstile> (map Some a) <=l (map Some b))" 
 (is "\\<forall>b. length a = length b \\<longrightarrow> ?Q a b" is "?P a")
proof (induct "a")
  show "?P []" by simp

  fix l ls assume Cons: "?P ls"

  show "?P (l#ls)" 
  proof (intro allI impI)
    fix b 
    assume "length (l # ls) = length (b::ty list)" 
    with Cons
    show "?Q (l # ls) b" by - (cases b, auto)
  qed
qed
 

lemma append_length_n: "\\<forall>n. n \\<le> length x \\<longrightarrow> (\\<exists>a b. x = a@b \\<and> length a = n)" (is "?P x")
proof (induct "?P" "x")
  show "?P []" by simp

  fix l ls assume Cons: "?P ls"

  show "?P (l#ls)"
  proof (intro allI impI)
    fix n
    assume l: "n \\<le> length (l # ls)"

    show "\\<exists>a b. l # ls = a @ b \\<and> length a = n" 
    proof (cases n)
      assume "n=0" thus ?thesis by simp
    next
      fix "n'" assume s: "n = Suc n'"
      with l 
      have  "n' \\<le> length ls" by simp 
      hence "\\<exists>a b. ls = a @ b \\<and> length a = n'" by (rule Cons [rulify])
      thus ?thesis
      proof elim
        fix a b 
        assume "ls = a @ b" "length a = n'"
        with s
        have "l # ls = (l#a) @ b \\<and> length (l#a) = n" by simp
        thus ?thesis by blast
      qed
    qed
  qed
qed



lemma rev_append_cons:
"\\<lbrakk>n < length x\\<rbrakk> \\<Longrightarrow> \\<exists>a b c. x = (rev a) @ b # c \\<and> length a = n"
proof -
  assume n: "n < length x"
  hence "n \\<le> length x" by simp
  hence "\\<exists>a b. x = a @ b \\<and> length a = n" by (rule append_length_n [rulify])
  thus ?thesis
  proof elim
    fix r d assume x: "x = r@d" "length r = n"
    with n
    have "\\<exists>b c. d = b#c" by (simp add: neq_Nil_conv)
    
    thus ?thesis 
    proof elim
      fix b c 
      assume "d = b#c"
      with x
      have "x = (rev (rev r)) @ b # c \\<and> length (rev r) = n" by simp
      thus ?thesis by blast
    qed
  qed
qed


lemma app_mono: 
"\\<lbrakk>G \\<turnstile> s2 <=s s1; app (i, G, rT, s1)\\<rbrakk> \\<Longrightarrow> app (i, G, rT, s2)";
proof -
  assume G:   "G \\<turnstile> s2 <=s s1"
  assume app: "app (i, G, rT, s1)"
  
  show ?thesis
  proof (cases i)
    case Load
    
    from G
    have l: "length (snd s1) = length (snd s2)" by (simp add: sup_state_length)

    from G Load app
    have "G \\<turnstile> snd s2 <=l snd s1" by (auto simp add: sup_state_def)
    
    with G Load app l
    show ?thesis by clarsimp (drule sup_loc_some, simp+)
  next
    case Store
    with G app
    show ?thesis
      by - (cases s2,
            auto dest: map_hd_tl simp add: sup_loc_Cons2 sup_loc_length sup_state_def)
  next
    case Bipush
    thus ?thesis by simp 
  next
    case Aconst_null
    thus ?thesis by simp
  next
    case New
    with app
    show ?thesis by simp
  next
    case Getfield
    with app G
    show ?thesis
      by - (cases s2, clarsimp simp add: sup_state_Cons2, rule widen_trans)
  next
    case Putfield

    with app 
    obtain vT oT ST LT b
      where s1: "s1 = (vT # oT # ST, LT)" and
                "field (G, cname) vname = Some (cname, b)" 
                "is_class G cname" and
            oT: "G\\<turnstile> oT\\<preceq> (Class cname)" and
            vT: "G\\<turnstile> vT\\<preceq> b"
      by simp (elim exE conjE, simp, rule that)
    moreover
    from s1 G
    obtain vT' oT' ST' LT'
      where s2:  "s2 = (vT' # oT' # ST', LT')" and
            oT': "G\\<turnstile> oT' \\<preceq> oT" and
            vT': "G\\<turnstile> vT' \\<preceq> vT"
      by - (cases s2, simp add: sup_state_Cons2, elim exE conjE, simp, rule that)
    moreover
    from vT' vT
    have "G \\<turnstile> vT' \\<preceq> b" by (rule widen_trans)
    moreover
    from oT' oT
    have "G\\<turnstile> oT' \\<preceq> (Class cname)" by (rule widen_trans)
    ultimately
    show ?thesis
      by (auto simp add: Putfield)
  next
    case Checkcast
    with app G
    show ?thesis 
      by - (cases s2, auto intro: widen_RefT2 simp add: sup_state_Cons2)
  next
    case Return
    with app G
    show ?thesis
      by - (cases s2, clarsimp simp add: sup_state_Cons2, rule widen_trans)
  next
    case Pop
    with app G
    show ?thesis
      by - (cases s2, clarsimp simp add: sup_state_Cons2)
  next
    case Dup
    with app G
    show ?thesis
      by - (cases s2, clarsimp simp add: sup_state_Cons2)
  next
    case Dup_x1
    with app G
    show ?thesis
      by - (cases s2, clarsimp simp add: sup_state_Cons2)
  next
    case Dup_x2
    with app G
    show ?thesis
      by - (cases s2, clarsimp simp add: sup_state_Cons2)
  next
    case Swap
    with app G
    show ?thesis
      by - (cases s2, clarsimp simp add: sup_state_Cons2)
  next
    case IAdd
    with app G
    show ?thesis
      by - (cases s2, auto simp add: sup_state_Cons2 PrimT_PrimT)
  next
    case Goto 
    with app
    show ?thesis by simp
  next
    case Ifcmpeq
    with app G
    show ?thesis
      by - (cases s2, auto simp add: sup_state_Cons2 PrimT_PrimT widen_RefT2)
  next
    case Invoke

    with app
    obtain apTs X ST LT where
      s1: "s1 = (rev apTs @ X # ST, LT)" and
      l:  "length apTs = length list" and
      C:  "G \\<turnstile> X \\<preceq> Class cname" and
      w:  "\\<forall>x \\<in> set (zip apTs list). x \\<in> widen G" and
      m:  "method (G, cname) (mname, list) \\<noteq> None"
      by (simp del: not_None_eq, elim exE conjE) (rule that)

    obtain apTs' X' ST' LT' where
      s2: "s2 = (rev apTs' @ X' # ST', LT')" and
      l': "length apTs' = length list"
    proof -
      from l s1 G 
      have "length list < length (fst s2)" 
        by (simp add: sup_state_length)
      hence "\\<exists>a b c. (fst s2) = rev a @ b # c \\<and> length a = length list"
        by (rule rev_append_cons [rulify])
      thus ?thesis
        by -  (cases s2, elim exE conjE, simp, rule that) 
    qed

    from l l'
    have "length (rev apTs') = length (rev apTs)" by simp
    
    from this s1 s2 G 
    obtain
      G': "G \\<turnstile> (apTs',LT') <=s (apTs,LT)" 
          "G \\<turnstile>  X' \\<preceq> X" "G \\<turnstile> (ST',LT') <=s (ST,LT)"
      by (simp add: sup_state_rev_fst sup_state_append_fst sup_state_Cons1);
        
    with C
    have C': "G \\<turnstile> X' \\<preceq> Class cname"
      by - (rule widen_trans, auto)
    
    from G'
    have "G \\<turnstile> map Some apTs' <=l map Some apTs"
      by (simp add: sup_state_def)
    also
    from l w
    have "G \\<turnstile> map Some apTs <=l map Some list" 
      by (simp add: all_widen_is_sup_loc)
    finally
    have "G \\<turnstile> map Some apTs' <=l map Some list" .

    with l'
    have w': "\\<forall>x \\<in> set (zip apTs' list). x \\<in> widen G"
      by (simp add: all_widen_is_sup_loc)

    from Invoke s2 l' w' C' m
    show ?thesis 
      by simp blast
  qed
qed
    

lemma step_mono:
"\\<lbrakk>succs i pc \\<noteq> {}; app (i,G,rT,s2); G \\<turnstile> s1 <=s s2\\<rbrakk> \\<Longrightarrow> 
  G \\<turnstile> the (step (i,G,s1)) <=s the (step (i,G,s2))"
proof (cases s1, cases s2) 
  fix a1 b1 a2 b2
  assume s: "s1 = (a1,b1)" "s2 = (a2,b2)"
  assume succs: "succs i pc \\<noteq> {}"
  assume app2: "app (i,G,rT,s2)"
  assume G: "G \\<turnstile> s1 <=s s2"

  from G app2
  have app1: "app (i,G,rT,s1)" by (rule app_mono)

  from app1 app2 succs
  obtain a1' b1' a2' b2'
    where step: "step (i,G,s1) = Some (a1',b1')" "step (i,G,s2) = Some (a2',b2')";
    by (auto dest: app_step_some);

  have "G \\<turnstile> (a1',b1') <=s (a2',b2')"
  proof (cases i)
    case Load

    with s app1
    obtain y where
       y:  "nat < length b1" "b1 ! nat = Some y" by clarsimp

    from Load s app2
    obtain y' where
       y': "nat < length b2" "b2 ! nat = Some y'" by clarsimp

    from G s 
    have "G \\<turnstile> b1 <=l b2" by (simp add: sup_state_def)

    with y y'
    have "G \\<turnstile> y \\<preceq> y'" 
      by - (drule sup_loc_some, simp+)
    
    with Load G y y' s step app1 app2 
    show ?thesis by (clarsimp simp add: sup_state_def)
  next
    case Store
    with G s step app1 app2
    show ?thesis
      by (clarsimp simp add: sup_state_def sup_loc_update)
  next
    case Bipush
    with G s step app1 app2
    show ?thesis
      by (clarsimp simp add: sup_state_Cons1)
  next
    case New
    with G s step app1 app2
    show ?thesis
      by (clarsimp simp add: sup_state_Cons1)
  next
    case Aconst_null
    with G s step app1 app2
    show ?thesis
      by (clarsimp simp add: sup_state_Cons1)
  next
    case Getfield
    with G s step app1 app2
    show ?thesis
      by (clarsimp simp add: sup_state_Cons1)
  next
    case Putfield
    with G s step app1 app2
    show ?thesis
      by (clarsimp simp add: sup_state_Cons1)
  next
    case Checkcast
    with G s step app1 app2
    show ?thesis
      by (clarsimp simp add: sup_state_Cons1)
  next
    case Invoke

    with s app1
    obtain a X ST where
      s1: "s1 = (a @ X # ST, b1)" and
      l:  "length a = length list"
      by (simp, elim exE conjE, simp)

    from Invoke s app2
    obtain a' X' ST' where
      s2: "s2 = (a' @ X' # ST', b2)" and
      l': "length a' = length list"
      by (simp, elim exE conjE, simp)

    from l l'
    have lr: "length a = length a'" by simp
      
    from lr G s s1 s2 
    have "G \\<turnstile> (ST, b1) <=s (ST', b2)"
      by (simp add: sup_state_append_fst sup_state_Cons1)
    
    moreover
    
    from Invoke G s step app1 app2
    have "b1 = b1' \\<and> b2 = b2'" by simp

    ultimately 

    have "G \\<turnstile> (ST, b1') <=s (ST', b2')" by simp

    with Invoke G s step app1 app2 s1 s2 l l'
    show ?thesis 
      by (clarsimp simp add: sup_state_def)
  next
    case Return
    with succs have "False" by simp
    thus ?thesis by blast
  next
    case Pop
    with G s step app1 app2
    show ?thesis
      by (clarsimp simp add: sup_state_Cons1)
  next
    case Dup
    with G s step app1 app2
    show ?thesis
      by (clarsimp simp add: sup_state_Cons1)
  next
    case Dup_x1
    with G s step app1 app2
    show ?thesis
      by (clarsimp simp add: sup_state_Cons1)
  next 
    case Dup_x2
    with G s step app1 app2
    show ?thesis
      by (clarsimp simp add: sup_state_Cons1)
  next
    case Swap
    with G s step app1 app2
    show ?thesis
      by (clarsimp simp add: sup_state_Cons1)
  next
    case IAdd
    with G s step app1 app2
    show ?thesis
      by (clarsimp simp add: sup_state_Cons1)
  next
    case Goto
    with G s step app1 app2
    show ?thesis by simp
  next
    case Ifcmpeq
    with G s step app1 app2
    show ?thesis
      by (clarsimp simp add: sup_state_Cons1)   
  qed

  with step
  show ?thesis by auto  
qed



end
