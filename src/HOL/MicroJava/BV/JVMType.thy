(*  Title:      HOL/MicroJava/BV/JVM.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 TUM

*)

header {* \isaheader{The JVM Type System as Semilattice} *}

theory JVMType = Opt + Product + Listn + JType:

types
  locvars_type = "ty err list"
  opstack_type = "ty list"
  state_type   = "opstack_type \<times> locvars_type"
  state        = "state_type option err"    -- "for Kildall"
  method_type  = "state_type option list"   -- "for BVSpec"
  class_type   = "sig \<Rightarrow> method_type"
  prog_type    = "cname \<Rightarrow> class_type"


constdefs
  stk_esl :: "'c prog \<Rightarrow> nat \<Rightarrow> ty list esl"
  "stk_esl S maxs == upto_esl maxs (JType.esl S)"

  reg_sl :: "'c prog \<Rightarrow> nat \<Rightarrow> ty err list sl"
  "reg_sl S maxr == Listn.sl maxr (Err.sl (JType.esl S))"

  sl :: "'c prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state sl"
  "sl S maxs maxr ==
  Err.sl(Opt.esl(Product.esl (stk_esl S maxs) (Err.esl(reg_sl S maxr))))"

constdefs
  states :: "'c prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state set"
  "states S maxs maxr == fst(sl S maxs maxr)"

  le :: "'c prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state ord"
  "le S maxs maxr == fst(snd(sl S maxs maxr))"

  sup :: "'c prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state binop"
  "sup S maxs maxr == snd(snd(sl S maxs maxr))"


constdefs
  sup_ty_opt :: "['code prog,ty err,ty err] \<Rightarrow> bool" 
                 ("_ |- _ <=o _" [71,71] 70)
  "sup_ty_opt G == Err.le (subtype G)"

  sup_loc :: "['code prog,locvars_type,locvars_type] \<Rightarrow> bool" 
              ("_ |- _ <=l _"  [71,71] 70)
  "sup_loc G == Listn.le (sup_ty_opt G)"

  sup_state :: "['code prog,state_type,state_type] \<Rightarrow> bool"   
               ("_ |- _ <=s _"  [71,71] 70)
  "sup_state G == Product.le (Listn.le (subtype G)) (sup_loc G)"

  sup_state_opt :: "['code prog,state_type option,state_type option] \<Rightarrow> bool" 
                   ("_ |- _ <=' _"  [71,71] 70)
  "sup_state_opt G == Opt.le (sup_state G)"


syntax (xsymbols)
  sup_ty_opt    :: "['code prog,ty err,ty err] \<Rightarrow> bool" 
                   ("_ \<turnstile> _ <=o _" [71,71] 70)
  sup_loc       :: "['code prog,locvars_type,locvars_type] \<Rightarrow> bool" 
                   ("_ \<turnstile> _ <=l _" [71,71] 70)
  sup_state     :: "['code prog,state_type,state_type] \<Rightarrow> bool" 
                   ("_ \<turnstile> _ <=s _" [71,71] 70)
  sup_state_opt :: "['code prog,state_type option,state_type option] \<Rightarrow> bool"
                   ("_ \<turnstile> _ <=' _" [71,71] 70)
                   

lemma JVM_states_unfold: 
  "states S maxs maxr == err(opt((Union {list n (types S) |n. n <= maxs}) <*>
                                  list maxr (err(types S))))"
  apply (unfold states_def sl_def Opt.esl_def Err.sl_def
         stk_esl_def reg_sl_def Product.esl_def
         Listn.sl_def upto_esl_def JType.esl_def Err.esl_def)
  by simp


lemma JVM_le_unfold:
 "le S m n == 
  Err.le(Opt.le(Product.le(Listn.le(subtype S))(Listn.le(Err.le(subtype S)))))" 
  apply (unfold le_def sl_def Opt.esl_def Err.sl_def
         stk_esl_def reg_sl_def Product.esl_def  
         Listn.sl_def upto_esl_def JType.esl_def Err.esl_def) 
  by simp

lemma JVM_le_convert:
  "le G m n (OK t1) (OK t2) = G \<turnstile> t1 <=' t2"
  by (simp add: JVM_le_unfold Err.le_def lesub_def sup_state_opt_def 
                sup_state_def sup_loc_def sup_ty_opt_def)

lemma JVM_le_Err_conv:
  "le G m n = Err.le (sup_state_opt G)"
  by (unfold sup_state_opt_def sup_state_def sup_loc_def  
             sup_ty_opt_def JVM_le_unfold) simp

lemma zip_map [rule_format]:
  "\<forall>a. length a = length b \<longrightarrow> 
  zip (map f a) (map g b) = map (\<lambda>(x,y). (f x, g y)) (zip a b)"
  apply (induct b) 
   apply simp
  apply clarsimp
  apply (case_tac aa)
  apply simp+
  done

lemma [simp]: "Err.le r (OK a) (OK b) = r a b"
  by (simp add: Err.le_def lesub_def)

lemma stk_convert:
  "Listn.le (subtype G) a b = G \<turnstile> map OK a <=l map OK b"
proof 
  assume "Listn.le (subtype G) a b"

  hence le: "list_all2 (subtype G) a b"
    by (unfold Listn.le_def lesub_def)
  
  { fix x' y'
    assume "length a = length b"
           "(x',y') \<in> set (zip (map OK a) (map OK b))"
    then
    obtain x y where OK:
      "x' = OK x" "y' = OK y" "(x,y) \<in> set (zip a b)"
      by (auto simp add: zip_map)
    with le
    have "subtype G x y"
      by (simp add: list_all2_def Ball_def)
    with OK
    have "G \<turnstile> x' <=o y'"
      by (simp add: sup_ty_opt_def)
  }
  
  with le
  show "G \<turnstile> map OK a <=l map OK b"
    by (unfold sup_loc_def Listn.le_def lesub_def list_all2_def) auto
next
  assume "G \<turnstile> map OK a <=l map OK b"

  thus "Listn.le (subtype G) a b"
    apply (unfold sup_loc_def list_all2_def Listn.le_def lesub_def)
    apply (clarsimp simp add: zip_map)
    apply (drule bspec, assumption)
    apply (auto simp add: sup_ty_opt_def subtype_def)
    done
qed


lemma sup_state_conv:
  "(G \<turnstile> s1 <=s s2) == 
  (G \<turnstile> map OK (fst s1) <=l map OK (fst s2)) \<and> (G \<turnstile> snd s1 <=l snd s2)"
  by (auto simp add: sup_state_def stk_convert lesub_def Product.le_def split_beta)


lemma subtype_refl [simp]:
  "subtype G t t"
  by (simp add: subtype_def)

theorem sup_ty_opt_refl [simp]:
  "G \<turnstile> t <=o t"
  by (simp add: sup_ty_opt_def Err.le_def lesub_def split: err.split)

lemma le_list_refl2 [simp]: 
  "(\<And>xs. r xs xs) \<Longrightarrow> Listn.le r xs xs"
  by (induct xs, auto simp add: Listn.le_def lesub_def)

theorem sup_loc_refl [simp]:
  "G \<turnstile> t <=l t"
  by (simp add: sup_loc_def)

theorem sup_state_refl [simp]:
  "G \<turnstile> s <=s s"
  by (auto simp add: sup_state_def Product.le_def lesub_def)

theorem sup_state_opt_refl [simp]:
  "G \<turnstile> s <=' s"
  by (simp add: sup_state_opt_def Opt.le_def lesub_def split: option.split)
  

theorem anyConvErr [simp]:
  "(G \<turnstile> Err <=o any) = (any = Err)"
  by (simp add: sup_ty_opt_def Err.le_def split: err.split)

theorem OKanyConvOK [simp]:
  "(G \<turnstile> (OK ty') <=o (OK ty)) = (G \<turnstile> ty' \<preceq> ty)"
  by (simp add: sup_ty_opt_def Err.le_def lesub_def subtype_def)

theorem sup_ty_opt_OK:
  "G \<turnstile> a <=o (OK b) \<Longrightarrow> \<exists> x. a = OK x"
  by (clarsimp simp add: sup_ty_opt_def Err.le_def split: err.splits)

lemma widen_PrimT_conv1 [simp]:
  "\<lbrakk> G \<turnstile> S \<preceq> T; S = PrimT x\<rbrakk> \<Longrightarrow> T = PrimT x"
  by (auto elim: widen.elims)

theorem sup_PTS_eq:
  "(G \<turnstile> OK (PrimT p) <=o X) = (X=Err \<or> X = OK (PrimT p))"
  by (auto simp add: sup_ty_opt_def Err.le_def lesub_def subtype_def 
              split: err.splits)

theorem sup_loc_Nil [iff]:
  "(G \<turnstile> [] <=l XT) = (XT=[])"
  by (simp add: sup_loc_def Listn.le_def)

theorem sup_loc_Cons [iff]:
  "(G \<turnstile> (Y#YT) <=l XT) = (\<exists>X XT'. XT=X#XT' \<and> (G \<turnstile> Y <=o X) \<and> (G \<turnstile> YT <=l XT'))"
  by (simp add: sup_loc_def Listn.le_def lesub_def list_all2_Cons1)

theorem sup_loc_Cons2:
  "(G \<turnstile> YT <=l (X#XT)) = (\<exists>Y YT'. YT=Y#YT' \<and> (G \<turnstile> Y <=o X) \<and> (G \<turnstile> YT' <=l XT))"
  by (simp add: sup_loc_def Listn.le_def lesub_def list_all2_Cons2)

lemma sup_state_Cons:
  "(G \<turnstile> (x#xt, a) <=s (y#yt, b)) = 
   ((G \<turnstile> x \<preceq> y) \<and> (G \<turnstile> (xt,a) <=s (yt,b)))"
  by (auto simp add: sup_state_def stk_convert lesub_def Product.le_def)


theorem sup_loc_length:
  "G \<turnstile> a <=l b \<Longrightarrow> length a = length b"
proof -
  assume G: "G \<turnstile> a <=l b"
  have "\<forall>b. (G \<turnstile> a <=l b) \<longrightarrow> length a = length b"
    by (induct a, auto)
  with G
  show ?thesis by blast
qed

theorem sup_loc_nth:
  "\<lbrakk> G \<turnstile> a <=l b; n < length a \<rbrakk> \<Longrightarrow> G \<turnstile> (a!n) <=o (b!n)"
proof -
  assume a: "G \<turnstile> a <=l b" "n < length a"
  have "\<forall> n b. (G \<turnstile> a <=l b) \<longrightarrow> n < length a \<longrightarrow> (G \<turnstile> (a!n) <=o (b!n))"
    (is "?P a")
  proof (induct a)
    show "?P []" by simp
    
    fix x xs assume IH: "?P xs"

    show "?P (x#xs)"
    proof (intro strip)
      fix n b
      assume "G \<turnstile> (x # xs) <=l b" "n < length (x # xs)"
      with IH
      show "G \<turnstile> ((x # xs) ! n) <=o (b ! n)"
        by - (cases n, auto)
    qed
  qed
  with a
  show ?thesis by blast
qed

theorem all_nth_sup_loc:
  "\<forall>b. length a = length b \<longrightarrow> (\<forall> n. n < length a \<longrightarrow> (G \<turnstile> (a!n) <=o (b!n))) 
  \<longrightarrow> (G \<turnstile> a <=l b)" (is "?P a")
proof (induct a)
  show "?P []" by simp

  fix l ls assume IH: "?P ls"
  
  show "?P (l#ls)"
  proof (intro strip)
    fix b
    assume f: "\<forall>n. n < length (l # ls) \<longrightarrow> (G \<turnstile> ((l # ls) ! n) <=o (b ! n))"
    assume l: "length (l#ls) = length b"
    
    then obtain b' bs where b: "b = b'#bs"
      by - (cases b, simp, simp add: neq_Nil_conv, rule that)

    with f
    have "\<forall>n. n < length ls \<longrightarrow> (G \<turnstile> (ls!n) <=o (bs!n))"
      by auto

    with f b l IH
    show "G \<turnstile> (l # ls) <=l b"
      by auto
  qed
qed


theorem sup_loc_append:
  "length a = length b \<Longrightarrow> 
   (G \<turnstile> (a@x) <=l (b@y)) = ((G \<turnstile> a <=l b) \<and> (G \<turnstile> x <=l y))"
proof -
  assume l: "length a = length b"

  have "\<forall>b. length a = length b \<longrightarrow> (G \<turnstile> (a@x) <=l (b@y)) = ((G \<turnstile> a <=l b) \<and> 
            (G \<turnstile> x <=l y))" (is "?P a") 
  proof (induct a)
    show "?P []" by simp
    
    fix l ls assume IH: "?P ls"    
    show "?P (l#ls)" 
    proof (intro strip)
      fix b
      assume "length (l#ls) = length (b::ty err list)"
      with IH
      show "(G \<turnstile> ((l#ls)@x) <=l (b@y)) = ((G \<turnstile> (l#ls) <=l b) \<and> (G \<turnstile> x <=l y))"
        by - (cases b, auto)
    qed
  qed
  with l
  show ?thesis by blast
qed

theorem sup_loc_rev [simp]:
  "(G \<turnstile> (rev a) <=l rev b) = (G \<turnstile> a <=l b)"
proof -
  have "\<forall>b. (G \<turnstile> (rev a) <=l rev b) = (G \<turnstile> a <=l b)" (is "\<forall>b. ?Q a b" is "?P a")
  proof (induct a)
    show "?P []" by simp

    fix l ls assume IH: "?P ls"

    { 
      fix b
      have "?Q (l#ls) b"
      proof (cases (open) b)
        case Nil
        thus ?thesis by (auto dest: sup_loc_length)
      next
        case Cons 
        show ?thesis
        proof
          assume "G \<turnstile> (l # ls) <=l b"
          thus "G \<turnstile> rev (l # ls) <=l rev b"
            by (clarsimp simp add: Cons IH sup_loc_length sup_loc_append)
        next
          assume "G \<turnstile> rev (l # ls) <=l rev b"
          hence G: "G \<turnstile> (rev ls @ [l]) <=l (rev list @ [a])"
            by (simp add: Cons)          
          
          hence "length (rev ls) = length (rev list)"
            by (auto dest: sup_loc_length)

          from this G
          obtain "G \<turnstile> rev ls <=l rev list" "G \<turnstile> l <=o a"
            by (simp add: sup_loc_append)

          thus "G \<turnstile> (l # ls) <=l b"
            by (simp add: Cons IH)
        qed
      qed    
    }
    thus "?P (l#ls)" by blast
  qed

  thus ?thesis by blast
qed


theorem sup_loc_update [rule_format]:
  "\<forall> n y. (G \<turnstile> a <=o b) \<longrightarrow> n < length y \<longrightarrow> (G \<turnstile> x <=l y) \<longrightarrow> 
          (G \<turnstile> x[n := a] <=l y[n := b])" (is "?P x")
proof (induct x)
  show "?P []" by simp

  fix l ls assume IH: "?P ls"
  show "?P (l#ls)"
  proof (intro strip)
    fix n y
    assume "G \<turnstile>a <=o b" "G \<turnstile> (l # ls) <=l y" "n < length y"
    with IH
    show "G \<turnstile> (l # ls)[n := a] <=l y[n := b]"
      by - (cases n, auto simp add: sup_loc_Cons2 list_all2_Cons1)
  qed
qed


theorem sup_state_length [simp]:
  "G \<turnstile> s2 <=s s1 \<Longrightarrow> 
   length (fst s2) = length (fst s1) \<and> length (snd s2) = length (snd s1)"
  by (auto dest: sup_loc_length simp add: sup_state_def stk_convert lesub_def Product.le_def);

theorem sup_state_append_snd:
  "length a = length b \<Longrightarrow> 
  (G \<turnstile> (i,a@x) <=s (j,b@y)) = ((G \<turnstile> (i,a) <=s (j,b)) \<and> (G \<turnstile> (i,x) <=s (j,y)))"
  by (auto simp add: sup_state_def stk_convert lesub_def Product.le_def sup_loc_append)

theorem sup_state_append_fst:
  "length a = length b \<Longrightarrow> 
  (G \<turnstile> (a@x,i) <=s (b@y,j)) = ((G \<turnstile> (a,i) <=s (b,j)) \<and> (G \<turnstile> (x,i) <=s (y,j)))"
  by (auto simp add: sup_state_def stk_convert lesub_def Product.le_def sup_loc_append)

theorem sup_state_Cons1:
  "(G \<turnstile> (x#xt, a) <=s (yt, b)) = 
   (\<exists>y yt'. yt=y#yt' \<and> (G \<turnstile> x \<preceq> y) \<and> (G \<turnstile> (xt,a) <=s (yt',b)))"
  by (auto simp add: sup_state_def stk_convert lesub_def Product.le_def)

theorem sup_state_Cons2:
  "(G \<turnstile> (xt, a) <=s (y#yt, b)) = 
   (\<exists>x xt'. xt=x#xt' \<and> (G \<turnstile> x \<preceq> y) \<and> (G \<turnstile> (xt',a) <=s (yt,b)))"
  by (auto simp add: sup_state_def stk_convert lesub_def Product.le_def sup_loc_Cons2)

theorem sup_state_ignore_fst:  
  "G \<turnstile> (a, x) <=s (b, y) \<Longrightarrow> G \<turnstile> (c, x) <=s (c, y)"
  by (simp add: sup_state_def lesub_def Product.le_def)

theorem sup_state_rev_fst:
  "(G \<turnstile> (rev a, x) <=s (rev b, y)) = (G \<turnstile> (a, x) <=s (b, y))"
proof -
  have m: "\<And>f x. map f (rev x) = rev (map f x)" by (simp add: rev_map)
  show ?thesis by (simp add: m sup_state_def stk_convert lesub_def Product.le_def)
qed
  

lemma sup_state_opt_None_any [iff]:
  "(G \<turnstile> None <=' any) = True"
  by (simp add: sup_state_opt_def Opt.le_def split: option.split)

lemma sup_state_opt_any_None [iff]:
  "(G \<turnstile> any <=' None) = (any = None)"
  by (simp add: sup_state_opt_def Opt.le_def split: option.split)

lemma sup_state_opt_Some_Some [iff]:
  "(G \<turnstile> (Some a) <=' (Some b)) = (G \<turnstile> a <=s b)"
  by (simp add: sup_state_opt_def Opt.le_def lesub_def del: split_paired_Ex)

lemma sup_state_opt_any_Some [iff]:
  "(G \<turnstile> (Some a) <=' any) = (\<exists>b. any = Some b \<and> G \<turnstile> a <=s b)"
  by (simp add: sup_state_opt_def Opt.le_def lesub_def split: option.split)

lemma sup_state_opt_Some_any:
  "(G \<turnstile> any <=' (Some b)) = (any = None \<or> (\<exists>a. any = Some a \<and> G \<turnstile> a <=s b))"
  by (simp add: sup_state_opt_def Opt.le_def lesub_def split: option.split)


theorem sup_ty_opt_trans [trans]:
  "\<lbrakk>G \<turnstile> a <=o b; G \<turnstile> b <=o c\<rbrakk> \<Longrightarrow> G \<turnstile> a <=o c"
  by (auto intro: widen_trans 
           simp add: sup_ty_opt_def Err.le_def lesub_def subtype_def 
           split: err.splits)

theorem sup_loc_trans [trans]:
  "\<lbrakk>G \<turnstile> a <=l b; G \<turnstile> b <=l c\<rbrakk> \<Longrightarrow> G \<turnstile> a <=l c"
proof -
  assume G: "G \<turnstile> a <=l b" "G \<turnstile> b <=l c"
 
  hence "\<forall> n. n < length a \<longrightarrow> (G \<turnstile> (a!n) <=o (c!n))"
  proof (intro strip)
    fix n 
    assume n: "n < length a"
    with G
    have "G \<turnstile> (a!n) <=o (b!n)"
      by - (rule sup_loc_nth)
    also 
    from n G
    have "G \<turnstile> \<dots> <=o (c!n)"
      by - (rule sup_loc_nth, auto dest: sup_loc_length)
    finally
    show "G \<turnstile> (a!n) <=o (c!n)" .
  qed

  with G
  show ?thesis 
    by (auto intro!: all_nth_sup_loc [rule_format] dest!: sup_loc_length) 
qed
  

theorem sup_state_trans [trans]:
  "\<lbrakk>G \<turnstile> a <=s b; G \<turnstile> b <=s c\<rbrakk> \<Longrightarrow> G \<turnstile> a <=s c"
  by (auto intro: sup_loc_trans simp add: sup_state_def stk_convert Product.le_def lesub_def)

theorem sup_state_opt_trans [trans]:
  "\<lbrakk>G \<turnstile> a <=' b; G \<turnstile> b <=' c\<rbrakk> \<Longrightarrow> G \<turnstile> a <=' c"
  by (auto intro: sup_state_trans 
           simp add: sup_state_opt_def Opt.le_def lesub_def 
           split: option.splits)

end
