(*  Title:      HOL/MicroJava/BV/Convert.thy
    ID:         $Id$
    Author:     Cornelia Pusch and Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header "Lifted Type Relations"

theory Convert = JVMExec:

text "The supertype relation lifted to type err, type lists and state types."

datatype 'a err = Err | Ok 'a

types
 locvars_type = "ty err list"
 opstack_type = "ty list"
 state_type   = "opstack_type \<times> locvars_type"


consts
  strict  :: "('a \<Rightarrow> 'b err) \<Rightarrow> ('a err \<Rightarrow> 'b err)"
primrec
  "strict f Err    = Err"
  "strict f (Ok x) = f x"

consts
  opt_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a option \<Rightarrow> 'b option)"
primrec
  "opt_map f None     = None"
  "opt_map f (Some x) = Some (f x)"

consts
  val :: "'a err \<Rightarrow> 'a"
primrec
  "val (Ok s) = s"

  
constdefs
  (* lifts a relation to err with Err as top element *)
  lift_top :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a err \<Rightarrow> 'b err \<Rightarrow> bool)"
  "lift_top P a' a \<equiv> case a of 
                       Err  \<Rightarrow> True
                     | Ok t \<Rightarrow> (case a' of Err \<Rightarrow> False | Ok t' \<Rightarrow> P t' t)"

  (* lifts a relation to option with None as bottom element *)
  lift_bottom :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a option \<Rightarrow> 'b option \<Rightarrow> bool)"
  "lift_bottom P a' a \<equiv> case a' of 
                          None    \<Rightarrow> True 
                        | Some t' \<Rightarrow> (case a of None \<Rightarrow> False | Some t \<Rightarrow> P t' t)"

  sup_ty_opt :: "['code prog,ty err,ty err] \<Rightarrow> bool" ("_ \<turnstile>_ <=o _")
  "sup_ty_opt G \<equiv> lift_top (\<lambda>t t'. G \<turnstile> t \<preceq> t')"

  sup_loc :: "['code prog,locvars_type,locvars_type] \<Rightarrow> bool" 
             ("_ \<turnstile> _ <=l _"  [71,71] 70)
  "G \<turnstile> LT <=l LT' \<equiv> list_all2 (\<lambda>t t'. (G \<turnstile> t <=o t')) LT LT'"

  sup_state :: "['code prog,state_type,state_type] \<Rightarrow> bool"	  
               ("_ \<turnstile> _ <=s _"  [71,71] 70)
  "G \<turnstile> s <=s s' \<equiv> (G \<turnstile> map Ok (fst s) <=l map Ok (fst s')) \<and> G \<turnstile> snd s <=l snd s'"

  sup_state_opt :: "['code prog,state_type option,state_type option] \<Rightarrow> bool" 
                   ("_ \<turnstile> _ <=' _"  [71,71] 70)
  "sup_state_opt G \<equiv> lift_bottom (\<lambda>t t'. G \<turnstile> t <=s t')"


lemma not_Err_eq [iff]:
  "(x \<noteq> Err) = (\<exists>a. x = Ok a)" 
  by (cases x) auto

lemma not_Some_eq [iff]:
  "(\<forall>y. x \<noteq> Ok y) = (x = Err)"
  by (cases x) auto  


lemma lift_top_refl [simp]:
  "[| !!x. P x x |] ==> lift_top P x x"
  by (simp add: lift_top_def split: err.splits)

lemma lift_top_trans [trans]:
  "[| !!x y z. [| P x y; P y z |] ==> P x z; lift_top P x y; lift_top P y z |] 
  ==> lift_top P x z"
proof -
  assume [trans]: "!!x y z. [| P x y; P y z |] ==> P x z"
  assume a: "lift_top P x y"
  assume b: "lift_top P y z"

  { assume "z = Err" 
    hence ?thesis by (simp add: lift_top_def)
  } note z_none = this

  { assume "x = Err"
    with a b
    have ?thesis
      by (simp add: lift_top_def split: err.splits)
  } note x_none = this
  
  { fix r t
    assume x: "x = Ok r" and z: "z = Ok t"    
    with a b
    obtain s where y: "y = Ok s" 
      by (simp add: lift_top_def split: err.splits)
    
    from a x y
    have "P r s" by (simp add: lift_top_def)
    also
    from b y z
    have "P s t" by (simp add: lift_top_def)
    finally 
    have "P r t" .

    with x z
    have ?thesis by (simp add: lift_top_def)
  } 

  with x_none z_none
  show ?thesis by blast
qed

lemma lift_top_Err_any [simp]:
  "lift_top P Err any = (any = Err)"
  by (simp add: lift_top_def split: err.splits)

lemma lift_top_Ok_Ok [simp]:
  "lift_top P (Ok a) (Ok b) = P a b"
  by (simp add: lift_top_def split: err.splits)

lemma lift_top_any_Ok [simp]:
  "lift_top P any (Ok b) = (\<exists>a. any = Ok a \<and> P a b)"
  by (simp add: lift_top_def split: err.splits)

lemma lift_top_Ok_any:
  "lift_top P (Ok a) any = (any = Err \<or> (\<exists>b. any = Ok b \<and> P a b))"
  by (simp add: lift_top_def split: err.splits)


lemma lift_bottom_refl [simp]:
  "[| !!x. P x x |] ==> lift_bottom P x x"
  by (simp add: lift_bottom_def split: option.splits)

lemma lift_bottom_trans [trans]:
  "[| !!x y z. [| P x y; P y z |] ==> P x z; lift_bottom P x y; lift_bottom P y z |]
  ==> lift_bottom P x z"
proof -
  assume [trans]: "!!x y z. [| P x y; P y z |] ==> P x z"
  assume a: "lift_bottom P x y"
  assume b: "lift_bottom P y z"

  { assume "x = None" 
    hence ?thesis by (simp add: lift_bottom_def)
  } note z_none = this

  { assume "z = None"
    with a b
    have ?thesis
      by (simp add: lift_bottom_def split: option.splits)
  } note x_none = this
  
  { fix r t
    assume x: "x = Some r" and z: "z = Some t"    
    with a b
    obtain s where y: "y = Some s" 
      by (simp add: lift_bottom_def split: option.splits)
    
    from a x y
    have "P r s" by (simp add: lift_bottom_def)
    also
    from b y z
    have "P s t" by (simp add: lift_bottom_def)
    finally 
    have "P r t" .

    with x z
    have ?thesis by (simp add: lift_bottom_def)
  } 

  with x_none z_none
  show ?thesis by blast
qed

lemma lift_bottom_any_None [simp]:
  "lift_bottom P any None = (any = None)"
  by (simp add: lift_bottom_def split: option.splits)

lemma lift_bottom_Some_Some [simp]:
  "lift_bottom P (Some a) (Some b) = P a b"
  by (simp add: lift_bottom_def split: option.splits)

lemma lift_bottom_any_Some [simp]:
  "lift_bottom P (Some a) any = (\<exists>b. any = Some b \<and> P a b)"
  by (simp add: lift_bottom_def split: option.splits)

lemma lift_bottom_Some_any:
  "lift_bottom P any (Some b) = (any = None \<or> (\<exists>a. any = Some a \<and> P a b))"
  by (simp add: lift_bottom_def split: option.splits)



theorem sup_ty_opt_refl [simp]:
  "G \<turnstile> t <=o t"
  by (simp add: sup_ty_opt_def)

theorem sup_loc_refl [simp]:
  "G \<turnstile> t <=l t"
  by (induct t, auto simp add: sup_loc_def)

theorem sup_state_refl [simp]:
  "G \<turnstile> s <=s s"
  by (simp add: sup_state_def)

theorem sup_state_opt_refl [simp]:
  "G \<turnstile> s <=' s"
  by (simp add: sup_state_opt_def)


theorem anyConvErr [simp]:
  "(G \<turnstile> Err <=o any) = (any = Err)"
  by (simp add: sup_ty_opt_def)

theorem OkanyConvOk [simp]:
  "(G \<turnstile> (Ok ty') <=o (Ok ty)) = (G \<turnstile> ty' \<preceq> ty)"
  by (simp add: sup_ty_opt_def)

theorem sup_ty_opt_Ok:
  "G \<turnstile> a <=o (Ok b) \<Longrightarrow> \<exists> x. a = Ok x"
  by (clarsimp simp add: sup_ty_opt_def)

lemma widen_PrimT_conv1 [simp]:
  "[| G \<turnstile> S \<preceq> T; S = PrimT x|] ==> T = PrimT x"
  by (auto elim: widen.elims)

theorem sup_PTS_eq:
  "(G \<turnstile> Ok (PrimT p) <=o X) = (X=Err \<or> X = Ok (PrimT p))"
  by (auto simp add: sup_ty_opt_def lift_top_Ok_any)



theorem sup_loc_Nil [iff]:
  "(G \<turnstile> [] <=l XT) = (XT=[])"
  by (simp add: sup_loc_def)

theorem sup_loc_Cons [iff]:
  "(G \<turnstile> (Y#YT) <=l XT) = (\<exists>X XT'. XT=X#XT' \<and> (G \<turnstile> Y <=o X) \<and> (G \<turnstile> YT <=l XT'))"
  by (simp add: sup_loc_def list_all2_Cons1)

theorem sup_loc_Cons2:
  "(G \<turnstile> YT <=l (X#XT)) = (\<exists>Y YT'. YT=Y#YT' \<and> (G \<turnstile> Y <=o X) \<and> (G \<turnstile> YT' <=l XT))"
  by (simp add: sup_loc_def list_all2_Cons2)


theorem sup_loc_length:
  "G \<turnstile> a <=l b \<Longrightarrow> length a = length b"
proof -
  assume G: "G \<turnstile> a <=l b"
  have "\<forall> b. (G \<turnstile> a <=l b) \<longrightarrow> length a = length b"
    by (induct a, auto)
  with G
  show ?thesis by blast
qed

theorem sup_loc_nth:
  "[| G \<turnstile> a <=l b; n < length a |] ==> G \<turnstile> (a!n) <=o (b!n)"
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
  "\<forall>b. length a = length b \<longrightarrow> (\<forall> n. n < length a \<longrightarrow> (G \<turnstile> (a!n) <=o (b!n))) \<longrightarrow> 
       (G \<turnstile> a <=l b)" (is "?P a")
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
  "length a = length b ==> 
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


theorem sup_loc_update [rulified]:
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
  "G \<turnstile> s2 <=s s1 ==> 
   length (fst s2) = length (fst s1) \<and> length (snd s2) = length (snd s1)"
  by (auto dest: sup_loc_length simp add: sup_state_def);

theorem sup_state_append_snd:
  "length a = length b ==> 
  (G \<turnstile> (i,a@x) <=s (j,b@y)) = ((G \<turnstile> (i,a) <=s (j,b)) \<and> (G \<turnstile> (i,x) <=s (j,y)))"
  by (auto simp add: sup_state_def sup_loc_append)

theorem sup_state_append_fst:
  "length a = length b ==> 
  (G \<turnstile> (a@x,i) <=s (b@y,j)) = ((G \<turnstile> (a,i) <=s (b,j)) \<and> (G \<turnstile> (x,i) <=s (y,j)))"
  by (auto simp add: sup_state_def sup_loc_append)

theorem sup_state_Cons1:
  "(G \<turnstile> (x#xt, a) <=s (yt, b)) = 
   (\<exists>y yt'. yt=y#yt' \<and> (G \<turnstile> x \<preceq> y) \<and> (G \<turnstile> (xt,a) <=s (yt',b)))"
  by (auto simp add: sup_state_def map_eq_Cons)

theorem sup_state_Cons2:
  "(G \<turnstile> (xt, a) <=s (y#yt, b)) = 
   (\<exists>x xt'. xt=x#xt' \<and> (G \<turnstile> x \<preceq> y) \<and> (G \<turnstile> (xt',a) <=s (yt,b)))"
  by (auto simp add: sup_state_def map_eq_Cons sup_loc_Cons2)

theorem sup_state_ignore_fst:  
  "G \<turnstile> (a, x) <=s (b, y) \<Longrightarrow> G \<turnstile> (c, x) <=s (c, y)"
  by (simp add: sup_state_def)

theorem sup_state_rev_fst:
  "(G \<turnstile> (rev a, x) <=s (rev b, y)) = (G \<turnstile> (a, x) <=s (b, y))"
proof -
  have m: "!!f x. map f (rev x) = rev (map f x)" by (simp add: rev_map)
  show ?thesis by (simp add: m sup_state_def)
qed
  

lemma sup_state_opt_None_any [iff]:
  "(G \<turnstile> None <=' any) = True"
  by (simp add: sup_state_opt_def lift_bottom_def)

lemma sup_state_opt_any_None [iff]:
  "(G \<turnstile> any <=' None) = (any = None)"
  by (simp add: sup_state_opt_def)

lemma sup_state_opt_Some_Some [iff]:
  "(G \<turnstile> (Some a) <=' (Some b)) = (G \<turnstile> a <=s b)"
  by (simp add: sup_state_opt_def del: split_paired_Ex)

lemma sup_state_opt_any_Some [iff]:
  "(G \<turnstile> (Some a) <=' any) = (\<exists>b. any = Some b \<and> G \<turnstile> a <=s b)"
  by (simp add: sup_state_opt_def)

lemma sup_state_opt_Some_any:
  "(G \<turnstile> any <=' (Some b)) = (any = None \<or> (\<exists>a. any = Some a \<and> G \<turnstile> a <=s b))"
  by (simp add: sup_state_opt_def lift_bottom_Some_any)


theorem sup_ty_opt_trans [trans]:
  "\<lbrakk>G \<turnstile> a <=o b; G \<turnstile> b <=o c\<rbrakk> \<Longrightarrow> G \<turnstile> a <=o c"
  by (auto intro: lift_top_trans widen_trans simp add: sup_ty_opt_def)

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
    have "G \<turnstile> ... <=o (c!n)"
      by - (rule sup_loc_nth, auto dest: sup_loc_length)
    finally
    show "G \<turnstile> (a!n) <=o (c!n)" .
  qed

  with G
  show ?thesis 
    by (auto intro!: all_nth_sup_loc [rulified] dest!: sup_loc_length) 
qed
  

theorem sup_state_trans [trans]:
  "\<lbrakk>G \<turnstile> a <=s b; G \<turnstile> b <=s c\<rbrakk> \<Longrightarrow> G \<turnstile> a <=s c"
  by (auto intro: sup_loc_trans simp add: sup_state_def)

theorem sup_state_opt_trans [trans]:
  "\<lbrakk>G \<turnstile> a <=' b; G \<turnstile> b <=' c\<rbrakk> \<Longrightarrow> G \<turnstile> a <=' c"
  by (auto intro: lift_bottom_trans sup_state_trans simp add: sup_state_opt_def)


end
