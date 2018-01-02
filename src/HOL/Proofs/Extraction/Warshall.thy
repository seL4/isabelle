(*  Title:      HOL/Proofs/Extraction/Warshall.thy
    Author:     Stefan Berghofer, TU Muenchen
*)

section \<open>Warshall's algorithm\<close>

theory Warshall
imports "HOL-Library.Realizers"
begin

text \<open>
  Derivation of Warshall's algorithm using program extraction,
  based on Berger, Schwichtenberg and Seisenberger @{cite "Berger-JAR-2001"}.
\<close>

datatype b = T | F

primrec is_path' :: "('a \<Rightarrow> 'a \<Rightarrow> b) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool"
where
  "is_path' r x [] z \<longleftrightarrow> r x z = T"
| "is_path' r x (y # ys) z \<longleftrightarrow> r x y = T \<and> is_path' r y ys z"

definition is_path :: "(nat \<Rightarrow> nat \<Rightarrow> b) \<Rightarrow> (nat * nat list * nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "is_path r p i j k \<longleftrightarrow>
    fst p = j \<and> snd (snd p) = k \<and>
    list_all (\<lambda>x. x < i) (fst (snd p)) \<and>
    is_path' r (fst p) (fst (snd p)) (snd (snd p))"

definition conc :: "'a \<times> 'a list \<times> 'a \<Rightarrow> 'a \<times> 'a list \<times> 'a \<Rightarrow> 'a \<times> 'a list * 'a"
  where "conc p q = (fst p, fst (snd p) @ fst q # fst (snd q), snd (snd q))"

theorem is_path'_snoc [simp]: "\<And>x. is_path' r x (ys @ [y]) z = (is_path' r x ys y \<and> r y z = T)"
  by (induct ys) simp+

theorem list_all_scoc [simp]: "list_all P (xs @ [x]) \<longleftrightarrow> P x \<and> list_all P xs"
  by (induct xs) (simp+, iprover)

theorem list_all_lemma: "list_all P xs \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> list_all Q xs"
proof -
  assume PQ: "\<And>x. P x \<Longrightarrow> Q x"
  show "list_all P xs \<Longrightarrow> list_all Q xs"
  proof (induct xs)
    case Nil
    show ?case by simp
  next
    case (Cons y ys)
    then have Py: "P y" by simp
    from Cons have Pys: "list_all P ys" by simp
    show ?case
      by simp (rule conjI PQ Py Cons Pys)+
  qed
qed

theorem lemma1: "\<And>p. is_path r p i j k \<Longrightarrow> is_path r p (Suc i) j k"
  unfolding is_path_def
  apply (simp cong add: conj_cong add: split_paired_all)
  apply (erule conjE)+
  apply (erule list_all_lemma)
  apply simp
  done

theorem lemma2: "\<And>p. is_path r p 0 j k \<Longrightarrow> r j k = T"
  unfolding is_path_def
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
    then have "r j i = T" by simp
    with pys show ?case by simp
  next
    case (Cons z zs j)
    then have jzr: "r j z = T" by simp
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
  "\<And>p. is_path r p (Suc i) j k \<Longrightarrow> \<not> is_path r p i j k \<Longrightarrow>
    (\<exists>q. is_path r q i j i) \<and> (\<exists>q'. is_path r q' i i k)"
proof (simp cong add: conj_cong add: split_paired_all is_path_def, (erule conjE)+)
  fix xs
  assume asms:
    "list_all (\<lambda>x. x < Suc i) xs"
    "is_path' r j xs k"
    "\<not> list_all (\<lambda>x. x < i) xs"
  show "(\<exists>ys. list_all (\<lambda>x. x < i) ys \<and> is_path' r j ys i) \<and>
    (\<exists>ys. list_all (\<lambda>x. x < i) ys \<and> is_path' r i ys k)"
  proof
    have "\<And>j. list_all (\<lambda>x. x < Suc i) xs \<Longrightarrow> is_path' r j xs k \<Longrightarrow>
      \<not> list_all (\<lambda>x. x < i) xs \<Longrightarrow>
    \<exists>ys. list_all (\<lambda>x. x < i) ys \<and> is_path' r j ys i" (is "PROP ?ih xs")
    proof (induct xs)
      case Nil
      then show ?case by simp
    next
      case (Cons a as j)
      show ?case
      proof (cases "a=i")
        case True
        show ?thesis
        proof
          from True and Cons have "r j i = T" by simp
          then show "list_all (\<lambda>x. x < i) [] \<and> is_path' r j [] i" by simp
        qed
      next
        case False
        have "PROP ?ih as" by (rule Cons)
        then obtain ys where ys: "list_all (\<lambda>x. x < i) ys \<and> is_path' r a ys i"
        proof
          from Cons show "list_all (\<lambda>x. x < Suc i) as" by simp
          from Cons show "is_path' r a as k" by simp
          from Cons and False show "\<not> list_all (\<lambda>x. x < i) as" by (simp)
        qed
        show ?thesis
        proof
          from Cons False ys
          show "list_all (\<lambda>x. x<i) (a#ys) \<and> is_path' r j (a#ys) i" by simp
        qed
      qed
    qed
    from this asms show "\<exists>ys. list_all (\<lambda>x. x < i) ys \<and> is_path' r j ys i" .
    have "\<And>k. list_all (\<lambda>x. x < Suc i) xs \<Longrightarrow> is_path' r j xs k \<Longrightarrow>
      \<not> list_all (\<lambda>x. x < i) xs \<Longrightarrow>
      \<exists>ys. list_all (\<lambda>x. x < i) ys \<and> is_path' r i ys k" (is "PROP ?ih xs")
    proof (induct xs rule: rev_induct)
      case Nil
      then show ?case by simp
    next
      case (snoc a as k)
      show ?case
      proof (cases "a=i")
        case True
        show ?thesis
        proof
          from True and snoc have "r i k = T" by simp
          then show "list_all (\<lambda>x. x < i) [] \<and> is_path' r i [] k" by simp
        qed
      next
        case False
        have "PROP ?ih as" by (rule snoc)
        then obtain ys where ys: "list_all (\<lambda>x. x < i) ys \<and> is_path' r i ys a"
        proof
          from snoc show "list_all (\<lambda>x. x < Suc i) as" by simp
          from snoc show "is_path' r j as a" by simp
          from snoc and False show "\<not> list_all (\<lambda>x. x < i) as" by simp
        qed
        show ?thesis
        proof
          from snoc False ys
          show "list_all (\<lambda>x. x < i) (ys @ [a]) \<and> is_path' r i (ys @ [a]) k"
            by simp
        qed
      qed
    qed
    from this asms show "\<exists>ys. list_all (\<lambda>x. x < i) ys \<and> is_path' r i ys k" .
  qed
qed

theorem lemma5':
  "\<And>p. is_path r p (Suc i) j k \<Longrightarrow> \<not> is_path r p i j k \<Longrightarrow>
    \<not> (\<forall>q. \<not> is_path r q i j i) \<and> \<not> (\<forall>q'. \<not> is_path r q' i i k)"
  by (iprover dest: lemma5)

theorem warshall: "\<And>j k. \<not> (\<exists>p. is_path r p i j k) \<or> (\<exists>p. is_path r p i j k)"
proof (induct i)
  case (0 j k)
  show ?case
  proof (cases "r j k")
    assume "r j k = T"
    then have "is_path r (j, [], k) 0 j k"
      by (simp add: is_path_def)
    then have "\<exists>p. is_path r p 0 j k" ..
    then show ?thesis ..
  next
    assume "r j k = F"
    then have "r j k \<noteq> T" by simp
    then have "\<not> (\<exists>p. is_path r p 0 j k)"
      by (iprover dest: lemma2)
    then show ?thesis ..
  qed
next
  case (Suc i j k)
  then show ?case
  proof
    assume h1: "\<not> (\<exists>p. is_path r p i j k)"
    from Suc show ?case
    proof
      assume "\<not> (\<exists>p. is_path r p i j i)"
      with h1 have "\<not> (\<exists>p. is_path r p (Suc i) j k)"
        by (iprover dest: lemma5')
      then show ?case ..
    next
      assume "\<exists>p. is_path r p i j i"
      then obtain p where h2: "is_path r p i j i" ..
      from Suc show ?case
      proof
        assume "\<not> (\<exists>p. is_path r p i i k)"
        with h1 have "\<not> (\<exists>p. is_path r p (Suc i) j k)"
          by (iprover dest: lemma5')
        then show ?case ..
      next
        assume "\<exists>q. is_path r q i i k"
        then obtain q where "is_path r q i i k" ..
        with h2 have "is_path r (conc p q) (Suc i) j k" 
          by (rule lemma3)
        then have "\<exists>pq. is_path r pq (Suc i) j k" ..
        then show ?case ..
      qed
    qed
  next
    assume "\<exists>p. is_path r p i j k"
    then have "\<exists>p. is_path r p (Suc i) j k"
      by (iprover intro: lemma1)
    then show ?case ..
  qed
qed

extract warshall

text \<open>
  The program extracted from the above proof looks as follows
  @{thm [display, eta_contract=false] warshall_def [no_vars]}
  The corresponding correctness theorem is
  @{thm [display] warshall_correctness [no_vars]}
\<close>

ML_val "@{code warshall}"

end
