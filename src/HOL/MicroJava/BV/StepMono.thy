(*  Title:      HOL/MicroJava/BV/StepMono.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

header {* Monotonicity of step and app *}

theory StepMono = Step:


lemma PrimT_PrimT: "(G \<turnstile> xb \<preceq> PrimT p) = (xb = PrimT p)"
  by (auto elim: widen.elims)


lemma sup_loc_some [rulify]:
"\<forall> y n. (G \<turnstile> b <=l y) \<longrightarrow> n < length y \<longrightarrow> y!n = Some t \<longrightarrow> (\<exists>t. b!n = Some t \<and> (G \<turnstile> (b!n) <=o (y!n)))" (is "?P b")
proof (induct (open) ?P b)
  show "?P []" by simp

  case Cons
  show "?P (a#list)"
  proof (clarsimp simp add: list_all2_Cons1 sup_loc_def)
    fix z zs n
    assume * : 
      "G \<turnstile> a <=o z" "list_all2 (sup_ty_opt G) list zs" 
      "n < Suc (length zs)" "(z # zs) ! n = Some t"

    show "(\<exists>t. (a # list) ! n = Some t) \<and> G \<turnstile>(a # list) ! n <=o Some t" 
    proof (cases n) 
      case 0
      with * show ?thesis by (simp add: sup_ty_opt_Some)
    next
      case Suc
      with Cons *
      show ?thesis by (simp add: sup_loc_def)
    qed
  qed
qed
   

lemma all_widen_is_sup_loc:
"\<forall>b. length a = length b \<longrightarrow> (\<forall>x\<in>set (zip a b). x \<in> widen G) = (G \<turnstile> (map Some a) <=l (map Some b))" 
 (is "\<forall>b. length a = length b \<longrightarrow> ?Q a b" is "?P a")
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
 

lemma append_length_n [rulify]: 
"\<forall>n. n \<le> length x \<longrightarrow> (\<exists>a b. x = a@b \<and> length a = n)" (is "?P x")
proof (induct (open) ?P x)
  show "?P []" by simp

  fix l ls assume Cons: "?P ls"

  show "?P (l#ls)"
  proof (intro allI impI)
    fix n
    assume l: "n \<le> length (l # ls)"

    show "\<exists>a b. l # ls = a @ b \<and> length a = n" 
    proof (cases n)
      assume "n=0" thus ?thesis by simp
    next
      fix "n'" assume s: "n = Suc n'"
      with l 
      have  "n' \<le> length ls" by simp 
      hence "\<exists>a b. ls = a @ b \<and> length a = n'" by (rule Cons [rulify])
      thus ?thesis
      proof elim
        fix a b 
        assume "ls = a @ b" "length a = n'"
        with s
        have "l # ls = (l#a) @ b \<and> length (l#a) = n" by simp
        thus ?thesis by blast
      qed
    qed
  qed
qed



lemma rev_append_cons:
"\<lbrakk>n < length x\<rbrakk> \<Longrightarrow> \<exists>a b c. x = (rev a) @ b # c \<and> length a = n"
proof -
  assume n: "n < length x"
  hence "n \<le> length x" by simp
  hence "\<exists>a b. x = a @ b \<and> length a = n" by (rule append_length_n)
  thus ?thesis
  proof elim
    fix r d assume x: "x = r@d" "length r = n"
    with n
    have "\<exists>b c. d = b#c" by (simp add: neq_Nil_conv)
    
    thus ?thesis 
    proof elim
      fix b c 
      assume "d = b#c"
      with x
      have "x = (rev (rev r)) @ b # c \<and> length (rev r) = n" by simp
      thus ?thesis by blast
    qed
  qed
qed


lemma app_mono: 
"\<lbrakk>G \<turnstile> s2 <=s s1; app (i, G, rT, s1)\<rbrakk> \<Longrightarrow> app (i, G, rT, s2)";
proof -
  assume G:   "G \<turnstile> s2 <=s s1"
  assume app: "app (i, G, rT, s1)"
  
  show ?thesis
  proof (cases (open) i)
    case Load
    
    from G
    have l: "length (snd s1) = length (snd s2)" by (simp add: sup_state_length)

    from G Load app
    have "G \<turnstile> snd s2 <=l snd s1" by (auto simp add: sup_state_def)
    
    with G Load app l
    show ?thesis by clarsimp (drule sup_loc_some, simp+)
  next
    case Store
    with G app
    show ?thesis
      by - (cases s2,
            auto simp add: map_eq_Cons sup_loc_Cons2 sup_loc_length sup_state_def)
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
            oT: "G\<turnstile> oT\<preceq> (Class cname)" and
            vT: "G\<turnstile> vT\<preceq> b"
      by simp (elim exE conjE, simp, rule that)
    moreover
    from s1 G
    obtain vT' oT' ST' LT'
      where s2:  "s2 = (vT' # oT' # ST', LT')" and
            oT': "G\<turnstile> oT' \<preceq> oT" and
            vT': "G\<turnstile> vT' \<preceq> vT"
      by - (cases s2, simp add: sup_state_Cons2, elim exE conjE, simp, rule that)
    moreover
    from vT' vT
    have "G \<turnstile> vT' \<preceq> b" by (rule widen_trans)
    moreover
    from oT' oT
    have "G\<turnstile> oT' \<preceq> (Class cname)" by (rule widen_trans)
    ultimately
    show ?thesis
      by (auto simp add: Putfield)
  next
    case Checkcast
    with app G
    show ?thesis 
      by - (cases s2, auto intro!: widen_RefT2 simp add: sup_state_Cons2)
  next
    case Return
    with app G
    show ?thesis
      by - (cases s2, auto simp add: sup_state_Cons2, rule widen_trans)
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
      C:  "G \<turnstile> X \<preceq> Class cname" and
      w:  "\<forall>x \<in> set (zip apTs list). x \<in> widen G" and
      m:  "method (G, cname) (mname, list) \<noteq> None"
      by (simp del: not_None_eq, elim exE conjE) (rule that)

    obtain apTs' X' ST' LT' where
      s2: "s2 = (rev apTs' @ X' # ST', LT')" and
      l': "length apTs' = length list"
    proof -
      from l s1 G 
      have "length list < length (fst s2)" 
        by (simp add: sup_state_length)
      hence "\<exists>a b c. (fst s2) = rev a @ b # c \<and> length a = length list"
        by (rule rev_append_cons [rulify])
      thus ?thesis
        by -  (cases s2, elim exE conjE, simp, rule that) 
    qed

    from l l'
    have "length (rev apTs') = length (rev apTs)" by simp
    
    from this s1 s2 G 
    obtain
      G': "G \<turnstile> (apTs',LT') <=s (apTs,LT)" and
      X : "G \<turnstile>  X' \<preceq> X" and "G \<turnstile> (ST',LT') <=s (ST,LT)"
      by (simp add: sup_state_rev_fst sup_state_append_fst sup_state_Cons1);
        
    with C
    have C': "G \<turnstile> X' \<preceq> Class cname"
      by - (rule widen_trans, auto)
    
    from G'
    have "G \<turnstile> map Some apTs' <=l map Some apTs"
      by (simp add: sup_state_def)
    also
    from l w
    have "G \<turnstile> map Some apTs <=l map Some list" 
      by (simp add: all_widen_is_sup_loc)
    finally
    have "G \<turnstile> map Some apTs' <=l map Some list" .

    with l'
    have w': "\<forall>x \<in> set (zip apTs' list). x \<in> widen G"
      by (simp add: all_widen_is_sup_loc)

    from Invoke s2 l' w' C' m
    show ?thesis 
      by simp blast
  qed
qed
    

lemma step_mono:
"\<lbrakk>succs i pc \<noteq> {}; app (i,G,rT,s2); G \<turnstile> s1 <=s s2\<rbrakk> \<Longrightarrow> 
  G \<turnstile> the (step (i,G,s1)) <=s the (step (i,G,s2))"
proof (cases s1, cases s2) 
  fix a1 b1 a2 b2
  assume s: "s1 = (a1,b1)" "s2 = (a2,b2)"
  assume succs: "succs i pc \<noteq> {}"
  assume app2: "app (i,G,rT,s2)"
  assume G: "G \<turnstile> s1 <=s s2"

  from G app2
  have app1: "app (i,G,rT,s1)" by (rule app_mono)

  from app1 app2 succs
  obtain a1' b1' a2' b2'
    where step: "step (i,G,s1) = Some (a1',b1')" "step (i,G,s2) = Some (a2',b2')";
    by (auto dest!: app_step_some);

  have "G \<turnstile> (a1',b1') <=s (a2',b2')"
  proof (cases (open) i)
    case Load

    with s app1
    obtain y where
       y:  "nat < length b1" "b1 ! nat = Some y" by clarsimp

    from Load s app2
    obtain y' where
       y': "nat < length b2" "b2 ! nat = Some y'" by clarsimp

    from G s 
    have "G \<turnstile> b1 <=l b2" by (simp add: sup_state_def)

    with y y'
    have "G \<turnstile> y \<preceq> y'" 
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
    have "G \<turnstile> (ST, b1) <=s (ST', b2)"
      by (simp add: sup_state_append_fst sup_state_Cons1)
    
    moreover
    
    from Invoke G s step app1 app2
    have "b1 = b1' \<and> b2 = b2'" by simp

    ultimately 

    have "G \<turnstile> (ST, b1') <=s (ST', b2')" by simp

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
