(*  Title:      HOL/Extraction/Warshall.thy
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* Warshall's algorithm *}

theory Warshall = Main:

text {*
  Derivation of Warshall's algorithm using program extraction,
  based on Berger, Schwichtenberg and Seisenberger \cite{Berger-JAR-2001}.
*}

datatype b = T | F

consts
  is_path' :: "('a \<Rightarrow> 'a \<Rightarrow> b) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool"

primrec
  "is_path' r x [] z = (r x z = T)"
  "is_path' r x (y # ys) z = (r x y = T \<and> is_path' r y ys z)"

constdefs
  is_path :: "(nat \<Rightarrow> nat \<Rightarrow> b) \<Rightarrow> (nat * nat list * nat) \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  "is_path r p i j k == fst p = j \<and> snd (snd p) = k \<and>
     list_all (\<lambda>x. x < i) (fst (snd p)) \<and>
     is_path' r (fst p) (fst (snd p)) (snd (snd p))"

  conc :: "('a * 'a list * 'a) \<Rightarrow> ('a * 'a list * 'a) \<Rightarrow> ('a * 'a list * 'a)"
  "conc p q == (fst p, fst (snd p) @ fst q # fst (snd q), snd (snd q))"

theorem is_path'_snoc [simp]:
  "\<And>x. is_path' r x (ys @ [y]) z = (is_path' r x ys y \<and> r y z = T)"
  by (induct ys) simp+

theorem list_all_scoc [simp]: "list_all P (xs @ [x]) = (P x \<and> list_all P xs)"
  by (induct xs, simp+, rules)

theorem list_all_lemma: 
  "list_all P xs \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> list_all Q xs"
proof -
  assume PQ: "\<And>x. P x \<Longrightarrow> Q x"
  show "list_all P xs \<Longrightarrow> list_all Q xs"
  proof (induct xs)
    case Nil
    show ?case by simp
  next
    case (Cons y ys)
    hence Py: "P y" by simp
    from Cons have Pys: "list_all P ys" by simp
    show ?case
      by simp (rule conjI PQ Py Cons Pys)+
  qed
qed

theorem lemma1: "\<And>p. is_path r p i j k \<Longrightarrow> is_path r p (Suc i) j k"
  apply (unfold is_path_def)
  apply (simp cong add: conj_cong add: split_paired_all)
  apply (erule conjE)+
  apply (erule list_all_lemma)
  apply simp
  done

theorem lemma2: "\<And>p. is_path r p 0 j k \<Longrightarrow> r j k = T"
  apply (unfold is_path_def)
  apply (simp cong add: conj_cong add: split_paired_all)
  apply (case_tac "aa")
  apply simp+
  done

theorem is_path'_conc: "is_path' r j xs i \<Longrightarrow> is_path' r i ys k \<Longrightarrow>
  is_path' r j (xs @ i # ys) k"
proof -
  assume pys: "is_path' r i ys k"
  show "\<And>j. is_path' r j xs i \<Longrightarrow> is_path' r j (xs @ i # ys) k"
  proof (induct xs)
    case (Nil j)
    hence "r j i = T" by simp
    with pys show ?case by simp
  next
    case (Cons z zs j)
    hence jzr: "r j z = T" by simp
    from Cons have pzs: "is_path' r z zs i" by simp
    show ?case
      by simp (rule conjI jzr Cons pzs)+
  qed
qed

theorem lemma3:
  "\<And>p q. is_path r p i j i \<Longrightarrow> is_path r q i i k \<Longrightarrow>
   is_path r (conc p q) (Suc i) j k"
  apply (unfold is_path_def conc_def)
  apply (simp cong add: conj_cong add: split_paired_all)
  apply (erule conjE)+
  apply (rule conjI)
  apply (erule list_all_lemma)
  apply simp
  apply (rule conjI)
  apply (erule list_all_lemma)
  apply simp
  apply (rule is_path'_conc)
  apply assumption+
  done

theorem lemma5:
  "\<And>p. is_path r p (Suc i) j k \<Longrightarrow> ~ is_path r p i j k \<Longrightarrow>
   (\<exists>q. is_path r q i j i) \<and> (\<exists>q'. is_path r q' i i k)"
proof (simp cong add: conj_cong add: split_paired_all is_path_def, (erule conjE)+)
  fix xs
  assume "list_all (\<lambda>x. x < Suc i) xs"
  assume "is_path' r j xs k"
  assume "\<not> list_all (\<lambda>x. x < i) xs"
  show "(\<exists>ys. list_all (\<lambda>x. x < i) ys \<and> is_path' r j ys i) \<and>
    (\<exists>ys. list_all (\<lambda>x. x < i) ys \<and> is_path' r i ys k)"
  proof
    show "\<And>j. list_all (\<lambda>x. x < Suc i) xs \<Longrightarrow> is_path' r j xs k \<Longrightarrow>
      \<not> list_all (\<lambda>x. x < i) xs \<Longrightarrow>
    \<exists>ys. list_all (\<lambda>x. x < i) ys \<and> is_path' r j ys i" (is "PROP ?ih xs")
    proof (induct xs)
      case Nil
      thus ?case by simp
    next
      case (Cons a as j)
      show ?case
      proof (cases "a=i")
      	case True
      	show ?thesis
      	proof
	  from True and Cons have "r j i = T" by simp
	  thus "list_all (\<lambda>x. x < i) [] \<and> is_path' r j [] i" by simp
      	qed
      next
      	case False
      	have "PROP ?ih as" by (rule Cons)
      	then obtain ys where ys: "list_all (\<lambda>x. x < i) ys \<and> is_path' r a ys i"
      	proof
	  from Cons show "list_all (\<lambda>x. x < Suc i) as" by simp
	  from Cons show "is_path' r a as k" by simp
	  from Cons and False show "\<not> list_all (\<lambda>x. x < i) as"
	    by (simp, arith)
      	qed
      	show ?thesis
      	proof
	  from Cons False ys
	  show "list_all (\<lambda>x. x < i) (a # ys) \<and> is_path' r j (a # ys) i"
	    by (simp, arith)
      	qed
      qed
    qed
    show "\<And>k. list_all (\<lambda>x. x < Suc i) xs \<Longrightarrow> is_path' r j xs k \<Longrightarrow>
      \<not> list_all (\<lambda>x. x < i) xs \<Longrightarrow>
      \<exists>ys. list_all (\<lambda>x. x < i) ys \<and> is_path' r i ys k" (is "PROP ?ih xs")
    proof (induct xs rule: rev_induct)
      case Nil
      thus ?case by simp
    next
      case (snoc a as k)
      show ?case
      proof (cases "a=i")
      	case True
      	show ?thesis
      	proof
	  from True and snoc have "r i k = T" by simp
	  thus "list_all (\<lambda>x. x < i) [] \<and> is_path' r i [] k" by simp
      	qed
      next
      	case False
      	have "PROP ?ih as" by (rule snoc)
      	then obtain ys where ys: "list_all (\<lambda>x. x < i) ys \<and> is_path' r i ys a"
      	proof
	  from snoc show "list_all (\<lambda>x. x < Suc i) as" by simp
	  from snoc show "is_path' r j as a" by simp
	  from snoc and False show "\<not> list_all (\<lambda>x. x < i) as"
	    by (simp, arith)
      	qed
      	show ?thesis
      	proof
	  from snoc False ys
	  show "list_all (\<lambda>x. x < i) (ys @ [a]) \<and> is_path' r i (ys @ [a]) k"
	    by (simp, arith)  
      	qed
      qed
    qed
  qed
qed

theorem lemma5':
  "\<And>p. is_path r p (Suc i) j k \<Longrightarrow> \<not> is_path r p i j k \<Longrightarrow>
   \<not> (\<forall>q. \<not> is_path r q i j i) \<and> \<not> (\<forall>q'. \<not> is_path r q' i i k)"
  by (rules dest: lemma5)

theorem warshall: 
  "\<And>j k. \<not> (\<exists>p. is_path r p i j k) \<or> (\<exists>p. is_path r p i j k)"
proof (induct i)
  case (0 j k)
  show ?case
  proof (cases "r j k")
    assume "r j k = T"
    hence "is_path r (j, [], k) 0 j k"
      by (simp add: is_path_def)
    hence "\<exists>p. is_path r p 0 j k" ..
    thus ?thesis ..
  next
    assume "r j k = F"
    hence "r j k ~= T" by simp
    hence "\<not> (\<exists>p. is_path r p 0 j k)"
      by (rules dest: lemma2)
    thus ?thesis ..
  qed
next
  case (Suc i j k)
  thus ?case
  proof
    assume h1: "\<not> (\<exists>p. is_path r p i j k)"
    from Suc show ?case
    proof
      assume "\<not> (\<exists>p. is_path r p i j i)"
      with h1 have "\<not> (\<exists>p. is_path r p (Suc i) j k)"
	by (rules dest: lemma5')
      thus ?case ..
    next
      assume "\<exists>p. is_path r p i j i"
      then obtain p where h2: "is_path r p i j i" ..
      from Suc show ?case
      proof
	assume "\<not> (\<exists>p. is_path r p i i k)"
	with h1 have "\<not> (\<exists>p. is_path r p (Suc i) j k)"
	  by (rules dest: lemma5')
	thus ?case ..
      next
	assume "\<exists>q. is_path r q i i k"
	then obtain q where "is_path r q i i k" ..
	with h2 have "is_path r (conc p q) (Suc i) j k" 
	  by (rule lemma3)
	hence "\<exists>pq. is_path r pq (Suc i) j k" ..
	thus ?case ..
      qed
    qed
  next
    assume "\<exists>p. is_path r p i j k"
    hence "\<exists>p. is_path r p (Suc i) j k"
      by (rules intro: lemma1)
    thus ?case ..
  qed
qed

extract warshall

text {*
  The program extracted from the above proof looks as follows
  @{thm [display] warshall_def [no_vars]}
  The corresponding correctness theorem is
  @{thm [display] warshall_correctness [no_vars]}
*}

end

