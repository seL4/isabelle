(*  Title:      HOL/MicroJava/BV/LBVSpec.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{The Lightweight Bytecode Verifier} *}

theory LBVSpec = SemilatAlg + Opt:


syntax
  "@lesuberropt" :: "'a option err \<Rightarrow> 'a ord \<Rightarrow> 'a option err \<Rightarrow> 'a option err ord"
  ("_ \<le>|_ _" [50,50,51] 50) 

  "@superropt" :: "'a option err \<Rightarrow> 'a ebinop \<Rightarrow> 'a option err \<Rightarrow> 'a option err binop"
  ("_ +|_ _" [50,50,51] 50)
  
  "@supsuperropt" :: "'a option err list \<Rightarrow> 'a ebinop \<Rightarrow> 'a option err \<Rightarrow> 'a option err binop"
  ("_ ++|_ _" [50,50,51] 50)

translations
  "a \<le>|r b" == "a <=_(Err.le (Opt.le r)) b"  
  "a +|f b" == "a +_(Err.lift2 (Opt.sup f)) b"
  "a ++|f b" == "a ++_(Err.lift2 (Opt.sup f)) b"


types
  's certificate = "'s option list"   
  's steptype    = "'s option err step_type"

consts
merge :: "'s certificate \<Rightarrow> 's ebinop \<Rightarrow> 's ord \<Rightarrow> nat \<Rightarrow> 
          (nat \<times> 's option err) list \<Rightarrow> 's option err \<Rightarrow> 's option err"
primrec
"merge cert f r pc []     x = x"
"merge cert f r pc (s#ss) x = (let (pc',s') = s in
                               merge cert f r pc ss (if pc'=pc+1 then (s' +|f x)
                                                     else if s' \<le>|r (OK (cert!pc')) then x
                                                     else Err))"

constdefs
wtl_inst :: "'s certificate \<Rightarrow> 's ebinop \<Rightarrow> 's ord \<Rightarrow> 
             's steptype \<Rightarrow> nat \<Rightarrow> 's option \<Rightarrow> 's option err"
"wtl_inst cert f r step pc s \<equiv> merge cert f r pc (step pc (OK s)) (OK (cert!(pc+1)))"

wtl_cert :: "'s certificate \<Rightarrow> 's ebinop \<Rightarrow> 's ord \<Rightarrow> 
             's steptype \<Rightarrow> nat \<Rightarrow> 's option \<Rightarrow> 's option err"
"wtl_cert cert f r step pc s \<equiv>
  case cert!pc of 
    None    \<Rightarrow> wtl_inst cert f r step pc s
  | Some s' \<Rightarrow> if OK s \<le>|r (OK (Some s')) then wtl_inst cert f r step pc (Some s') else Err"

consts 
wtl_inst_list :: "'a list \<Rightarrow> 's certificate \<Rightarrow> 's ebinop \<Rightarrow> 's ord \<Rightarrow> 
                  's steptype \<Rightarrow> nat \<Rightarrow> 's option \<Rightarrow> 's option err"
primrec
"wtl_inst_list []      cert f r step pc s = OK s"
"wtl_inst_list (i#ins) cert f r step pc s = 
  (let s' = wtl_cert cert f r step pc s in
   strict (wtl_inst_list ins cert f r step (pc+1)) s')"



constdefs
  cert_ok :: "'s certificate \<Rightarrow> nat \<Rightarrow> 's set \<Rightarrow> bool"
  "cert_ok cert n A \<equiv> (\<forall>i < n. cert!i \<in> opt A) \<and> (cert!n = None)"

lemma cert_okD1:
  "cert_ok cert n A \<Longrightarrow> pc < n \<Longrightarrow> cert!pc \<in> opt A"
  by (unfold cert_ok_def) fast

lemma cert_okD2:
  "cert_ok cert n A \<Longrightarrow> cert!n = None"
  by (simp add: cert_ok_def)

lemma cert_okD3:
  "cert_ok cert n A \<Longrightarrow> pc < n \<Longrightarrow> cert!Suc pc \<in> opt A"
  by (drule Suc_leI) (auto simp add: le_eq_less_or_eq dest: cert_okD1 cert_okD2)


declare Let_def [simp]

section "more semilattice lemmas"

(*
lemma sup_top [simp]:
  assumes sl:  "semilat (A,r,f)" 
  assumes set: "x \<in> A"  "t \<in> A"  
  assumes top: "top r t" 
  shows "x +_f t = t"
proof -
  from sl have "order r" ..
  moreover from top have "x +_f t <=_r t" ..
  moreover from sl set have "t <=_r x +_f t" by simp 
  ultimately show ?thesis by (rule order_antisym)
qed
  
lemma plusplussup_top:
  "semilat (A,r,f) \<Longrightarrow> top r Err \<Longrightarrow> set xs \<subseteq> A \<Longrightarrow> Err \<in> A \<Longrightarrow> xs ++_f Err = Err"
  by (induct xs) auto
*)

lemma err_semilatDorderI [simp, intro]:
  "err_semilat (A,r,f) \<Longrightarrow> order r"
  apply (simp add: Err.sl_def)
  apply (rule order_le_err [THEN iffD1])
  apply (rule semilatDorderI)
  apply assumption
  done

lemma err_opt_semilat [simp,elim]:
  "err_semilat (A,r,f) \<Longrightarrow> semilat (err (opt A), Err.le (Opt.le r), lift2 (Opt.sup f))"
proof -
  assume "err_semilat (A,r,f)"
  hence "err_semilat (Opt.esl (A,r,f))" ..
  thus ?thesis by (simp add: Err.sl_def Opt.esl_def)
qed

lemma plusplus_erropt_Err [simp]:
  "xs ++|f Err = Err"
  by (induct xs) auto


section "merge"

lemma merge_Err [simp]:
  "merge cert f r pc ss Err = Err"
  by (induct ss) auto

lemma merge_ok:
  "\<And>x. merge cert f r pc ss x = OK s \<Longrightarrow> 
  \<forall>(pc',s') \<in> set ss. (pc' \<noteq> pc+1 \<longrightarrow> s' \<le>|r (OK (cert!pc')))"
  (is "\<And>x. ?merge ss x \<Longrightarrow> ?P ss")
proof (induct ss)
  show "?P []" by simp
next
  fix x l ls assume merge: "?merge (l#ls) x"
  moreover
  obtain pc' s' where [simp]: "l = (pc',s')" by (cases l)
  ultimately
  obtain x' where "?merge ls x'" by simp  
  assume "\<And>x. ?merge ls x \<Longrightarrow> ?P ls" hence "?P ls" .
  moreover
  from merge
  have "pc' \<noteq> pc+1 \<longrightarrow> s' \<le>|r (OK (cert!pc'))" by (simp split: split_if_asm)
  ultimately
  show "?P (l#ls)" by simp
qed


lemma merge_def:
  assumes semi: "err_semilat (A,r,f)" 
  shows 
  "\<And>x. x \<in> err (opt A) \<Longrightarrow> \<forall>(pc', s') \<in> set ss. s' \<in> err (opt A) \<Longrightarrow>
  merge cert f r pc ss x = 
  (if \<forall>(pc',s') \<in> set ss. (pc' \<noteq> pc+1 \<longrightarrow> s' \<le>|r (OK (cert!pc'))) then
    map snd [(p',t') \<in> ss. p'=pc+1] ++|f x
  else Err)" 
  (is "\<And>x. _ \<Longrightarrow> _ \<Longrightarrow> ?merge ss x = ?if ss x" is "\<And>x. _ \<Longrightarrow> _ \<Longrightarrow> ?P ss x")
proof (induct ss)
  fix x show "?P [] x" by simp
next 
  fix x assume x: "x \<in> err (opt A)" 
  fix l::"nat \<times> 'a option err" and ls  
  assume "\<forall>(pc', s') \<in> set (l#ls). s' \<in> err (opt A)"
  then obtain l: "snd l \<in> err (opt A)" and ls: "\<forall>(pc', s') \<in> set ls. s' \<in> err (opt A)" by auto
  assume "\<And>x. x \<in> err (opt A) \<Longrightarrow> \<forall>(pc',s') \<in> set ls. s' \<in> err (opt A) \<Longrightarrow> ?P ls x" 
  hence IH: "\<And>x. x \<in> err (opt A) \<Longrightarrow> ?P ls x" .
  obtain pc' s' where [simp]: "l = (pc',s')" by (cases l)
  hence "?merge (l#ls) x = ?merge ls 
    (if pc'=pc+1 then s' +|f x else if s' \<le>|r (OK (cert!pc')) then x else Err)"
    (is "?merge (l#ls) x = ?merge ls ?if'")
    by simp 
  also have "\<dots> = ?if ls ?if'" 
  proof -
    from l have "s' \<in> err (opt A)" by simp
    with x semi have "(s' +|f x) \<in> err (opt A)" by (fast intro: closedD)
    with x have "?if' \<in> err (opt A)" by auto
    hence "?P ls ?if'" by (rule IH) thus ?thesis by simp
  qed
  also have "\<dots> = ?if (l#ls) x"
    proof (cases "\<forall>(pc', s')\<in>set (l#ls). pc' \<noteq> pc + 1 \<longrightarrow> s' \<le>|r OK (cert ! pc')")
      case True
      hence "\<forall>(pc', s')\<in>set ls. pc' \<noteq> pc + 1 \<longrightarrow> s' \<le>|r (OK (cert ! pc'))" by auto
      moreover
      from True have 
        "map snd [(p',t')\<in>ls . p'=pc+1] ++|f ?if' = 
        (map snd [(p',t')\<in>l#ls . p'=pc+1] ++|f x)"
        by simp
      ultimately
      show ?thesis using True by simp
    next
      case False thus ?thesis by auto
    qed
  finally show "?P (l#ls) x" .
qed

lemma merge_ok_s:
  assumes sl: "err_semilat (A,r,f)" 
  assumes x:  "x \<in> err (opt A)"
  assumes ss: "\<forall>(pc', s') \<in> set ss. s' \<in> err (opt A)"
  assumes m:  "merge cert f r pc ss x = OK s"
  shows "merge cert f r pc ss x = (map snd [(p',t') \<in> ss. p'=pc+1] ++|f x)"
proof -
  from m have "\<forall>(pc',s') \<in> set ss. (pc' \<noteq> pc+1 \<longrightarrow> s' \<le>|r (OK (cert!pc')))" 
    by (rule merge_ok)
  with sl x ss m show ?thesis by - (drule merge_def, auto split: split_if_asm)
qed

section "wtl-inst-list"

lemmas [iff] = not_Err_eq

lemma wtl_Cons:
  "wtl_inst_list (i#is) cert f r step pc s \<noteq> Err = 
  (\<exists>s'. wtl_cert cert f r step pc s = OK s' \<and> 
        wtl_inst_list is cert f r step (pc+1) s' \<noteq> Err)"
  by (auto simp del: split_paired_Ex)

lemma wtl_append:
"\<forall>s pc. (wtl_inst_list (a@b) cert f r step pc s = OK s') =
   (\<exists>s''. wtl_inst_list a cert f r step pc s = OK s'' \<and> 
          wtl_inst_list b cert f r step (pc+length a) s'' = OK s')" 
  (is "\<forall>s pc. ?C s pc a" is "?P a")
proof (induct ?P a)
  show "?P []" by simp
next
  fix x xs  assume IH: "?P xs"
  show "?P (x#xs)"
  proof (intro allI)
    fix s pc 
    show "?C s pc (x#xs)"
    proof (cases "wtl_cert cert f r step pc s")
      case Err thus ?thesis by simp
    next
      case (OK s0)
      with IH have "?C s0 (pc+1) xs" by blast
      thus ?thesis by (simp!)
    qed
  qed
qed

lemma wtl_take:
  "wtl_inst_list is cert f r step pc s = OK s'' \<Longrightarrow>
   \<exists>s'. wtl_inst_list (take pc' is) cert f r step pc s = OK s'"
  (is "?wtl is = _ \<Longrightarrow> _")
proof -
  assume "?wtl is = OK s''"
  hence "?wtl (take pc' is @ drop pc' is) = OK s''" by simp
  thus ?thesis by (auto simp add: wtl_append simp del: append_take_drop_id)
qed

lemma take_Suc:
  "\<forall>n. n < length l --> take (Suc n) l = (take n l)@[l!n]" (is "?P l")
proof (induct l)
  show "?P []" by simp
next
  fix x xs assume IH: "?P xs"  
  show "?P (x#xs)"
  proof (intro strip)
    fix n assume "n < length (x#xs)"
    with IH show "take (Suc n) (x # xs) = take n (x # xs) @ [(x # xs) ! n]" 
      by (cases n, auto)
  qed
qed

lemma wtl_Suc:
  assumes "wtl_inst_list (take pc is) cert f r step 0 s = OK s'"
           "wtl_cert cert f r step pc s' = OK s''" and
      suc: "pc+1 < length is"
  shows "wtl_inst_list (take (pc+1) is) cert f r step 0 s = OK s''"    
proof -
  from suc have "take (pc+1) is=(take pc is)@[is!pc]" by (simp add: take_Suc)
  thus ?thesis by (simp! add: wtl_append min_def)
qed

lemma wtl_all:
  assumes
  all: "wtl_inst_list is cert f r step 0 s \<noteq> Err" (is "?wtl is \<noteq> _") and
  pc:  "pc < length is"
  shows
  "\<exists>s' s''. wtl_inst_list (take pc is) cert f r step 0 s = OK s' \<and> 
            wtl_cert cert f r step pc s' = OK s''"
proof -
  from pc have "0 < length (drop pc is)" by simp
  then  obtain i r where Cons: "drop pc is = i#r" 
    by (auto simp add: neq_Nil_conv simp del: length_drop)
  hence "i#r = drop pc is" ..
  with all have take: "?wtl (take pc is@i#r) \<noteq> Err" by simp 
  from pc have "is!pc = drop pc is ! 0" by simp
  with Cons have "is!pc = i" by simp
  with take pc show ?thesis by (auto simp add: wtl_append min_def)
qed

section "preserves-type"

lemma merge_pres:
  assumes semi: "err_semilat (A,r,f)"
  assumes s0_A: "\<forall>(pc', s')\<in>set ss. s' \<in> err (opt A)"
  assumes x_A:  "x \<in> err (opt A)"
  assumes merge:"merge cert f r pc ss x = OK s'"
  shows "s' \<in> opt A"
proof -
  from s0_A
  have "set (map snd [(p', t')\<in>ss . p'=pc+1]) \<subseteq> err (opt A)" by auto
  with semi x_A
  have "(map snd [(p', t')\<in>ss . p'=pc+1] ++|f x) \<in> err (opt A)"
    by (auto intro!: plusplus_closed)
  also {
    note merge
    also from semi x_A s0_A
    have "merge cert f r pc ss x = 
      (if \<forall>(pc', s')\<in>set ss. pc' \<noteq> pc + 1 \<longrightarrow> s' \<le>|r (OK (cert!pc'))
      then map snd [(p', t')\<in>ss . p'=pc+1] ++|f x else Err)"
      by (rule merge_def)
    finally have "(map snd [(p', t')\<in>ss . p'=pc+1] ++|f x) = OK s'" 
      by (simp split: split_if_asm)
  } 
  finally show ?thesis by simp
qed
  


lemma wtl_inst_pres [intro?]:
  assumes semi: "err_semilat (A,r,f)"
  assumes pres: "pres_type step n (err (opt A))" 
  assumes cert: "cert!(pc+1) \<in> opt A"
  assumes s_A:  "s \<in> opt A"
  assumes pc:   "pc < n"
  assumes wtl:  "wtl_inst cert f r step pc s = OK s'"
  shows "s' \<in> opt A"
proof -
  from pres pc s_A
  have "\<forall>(q, s')\<in>set (step pc (OK s)). s' \<in> err (opt A)"
    by (unfold pres_type_def) blast
  moreover
  from cert have "OK (cert!(pc+1)) \<in> err (opt A)" by simp
  moreover
  from wtl
  have "merge cert f r pc (step pc (OK s)) (OK (cert!(pc+1))) = OK s'"  
    by (unfold wtl_inst_def) simp
  ultimately
  show "s' \<in> opt A" using semi by - (rule merge_pres)
qed


lemma wtl_cert_pres:
  assumes "err_semilat (A,r,f)"
  assumes "pres_type step n (err (opt A))"
  assumes "cert!pc \<in> opt A" and "cert!(pc+1) \<in> opt A"
  assumes "s \<in> opt A" and "pc < n"
  assumes wtc: "wtl_cert cert f r step pc s = OK s'"
  shows "s' \<in> opt A"            
proof -
  have "wtl_inst cert f r step pc s = OK s' \<Longrightarrow> s' \<in> opt A" ..
  moreover
  have "wtl_inst cert f r step pc (cert!pc) = OK s' \<Longrightarrow> s' \<in> opt A" ..
  ultimately
  show ?thesis using wtc
    by (unfold wtl_cert_def) (simp split: option.splits split_if_asm)
qed

lemma wtl_inst_list_pres:
  assumes semi: "err_semilat (A,r,f)"
  assumes pres: "pres_type step (length is) (err (opt A))"
  assumes cert: "cert_ok cert (length is) A"
  assumes s:    "s \<in> opt A" 
  assumes all:  "wtl_inst_list is cert f r step 0 s \<noteq> Err"
  shows "\<And>s'. pc < length is \<Longrightarrow> wtl_inst_list (take pc is) cert f r step 0 s = OK s'
         \<Longrightarrow> s' \<in> opt A" (is "\<And>s'. ?len pc \<Longrightarrow> ?wtl pc s' \<Longrightarrow> ?A s'")
proof (induct pc)
  from s show "\<And>s'. ?wtl 0 s' \<Longrightarrow> ?A s'" by simp
next
  fix s' n
  assume "Suc n < length is" 
  then obtain "n < length is" by simp  
  with all obtain s1 s2 where
    "wtl_inst_list (take n is) cert f r step 0 s = OK s1" 
    "wtl_cert cert f r step n s1 = OK s2"
    by - (drule wtl_all, auto)
    
  assume "?wtl (Suc n) s'"
  moreover
  have n1: "n+1 < length is" by simp
  hence "?wtl (n+1) s2" by - (rule wtl_Suc)
  ultimately
  have [simp]: "s2 = s'" by simp
  
  assume IH: "\<And>s'. n < length is \<Longrightarrow> ?wtl n s' \<Longrightarrow> s' \<in> opt A"
  hence "s1 \<in> opt A" .
  moreover
  from cert have "cert!n \<in> opt A" by (rule cert_okD1)
  moreover
  from cert n1 have "cert!(n+1) \<in> opt A" by (rule cert_okD1)
  ultimately
  have "s2 \<in> opt A" using semi pres by - (rule wtl_cert_pres)
  thus "s' \<in> opt A" by simp
qed


end
