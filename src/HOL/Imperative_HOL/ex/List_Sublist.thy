(*  Title:      HOL/Imperative_HOL/ex/List_Sublist.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

section \<open>Slices of lists\<close>

theory List_Sublist
imports "HOL-Library.Multiset"
begin

lemma nths_split: "i \<le> j \<and> j \<le> k \<Longrightarrow> nths xs {i..<j} @ nths xs {j..<k} = nths xs {i..<k}" 
apply (induct xs arbitrary: i j k)
apply simp
apply (simp only: nths_Cons)
apply simp
apply safe
apply simp
apply (erule_tac x="0" in meta_allE)
apply (erule_tac x="j - 1" in meta_allE)
apply (erule_tac x="k - 1" in meta_allE)
apply (subgoal_tac "0 \<le> j - 1 \<and> j - 1 \<le> k - 1")
apply simp
apply (subgoal_tac "{ja. Suc ja < j} = {0..<j - Suc 0}")
apply (subgoal_tac "{ja. j \<le> Suc ja \<and> Suc ja < k} = {j - Suc 0..<k - Suc 0}")
apply (subgoal_tac "{j. Suc j < k} = {0..<k - Suc 0}")
apply simp
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply (erule_tac x="i - 1" in meta_allE)
apply (erule_tac x="j - 1" in meta_allE)
apply (erule_tac x="k - 1" in meta_allE)
apply (subgoal_tac " {ja. i \<le> Suc ja \<and> Suc ja < j} = {i - 1 ..<j - 1}")
apply (subgoal_tac " {ja. j \<le> Suc ja \<and> Suc ja < k} = {j - 1..<k - 1}")
apply (subgoal_tac "{j. i \<le> Suc j \<and> Suc j < k} = {i - 1..<k - 1}")
apply (subgoal_tac " i - 1 \<le> j - 1 \<and> j - 1 \<le> k - 1")
apply simp
apply fastforce
apply fastforce
apply fastforce
apply fastforce
done

lemma nths_update1: "i \<notin> inds \<Longrightarrow> nths (xs[i := v]) inds = nths xs inds"
apply (induct xs arbitrary: i inds)
apply simp
apply (case_tac i)
apply (simp add: nths_Cons)
apply (simp add: nths_Cons)
done

lemma nths_update2: "i \<in> inds \<Longrightarrow> nths (xs[i := v]) inds = (nths xs inds)[(card {k \<in> inds. k < i}):= v]"
proof (induct xs arbitrary: i inds)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  thus ?case
  proof (cases i)
    case 0 with Cons show ?thesis by (simp add: nths_Cons)
  next
    case (Suc i')
    with Cons show ?thesis
      apply simp
      apply (simp add: nths_Cons)
      apply auto
      apply (auto simp add: nat.split)
      apply (simp add: card_less_Suc[symmetric])
      apply (simp add: card_less_Suc2)
      done
  qed
qed

lemma nths_update: "nths (xs[i := v]) inds = (if i \<in> inds then (nths xs inds)[(card {k \<in> inds. k < i}) := v] else nths xs inds)"
by (simp add: nths_update1 nths_update2)

lemma nths_take: "nths xs {j. j < m} = take m xs"
apply (induct xs arbitrary: m)
apply simp
apply (case_tac m)
apply simp
apply (simp add: nths_Cons)
done

lemma nths_take': "nths xs {0..<m} = take m xs"
apply (induct xs arbitrary: m)
apply simp
apply (case_tac m)
apply simp
apply (simp add: nths_Cons nths_take)
done

lemma nths_all[simp]: "nths xs {j. j < length xs} = xs"
apply (induct xs)
apply simp
apply (simp add: nths_Cons)
done

lemma nths_all'[simp]: "nths xs {0..<length xs} = xs"
apply (induct xs)
apply simp
apply (simp add: nths_Cons)
done

lemma nths_single: "a < length xs \<Longrightarrow> nths xs {a} = [xs ! a]"
apply (induct xs arbitrary: a)
apply simp
apply(case_tac aa)
apply simp
apply (simp add: nths_Cons)
apply simp
apply (simp add: nths_Cons)
done

lemma nths_is_Nil: "\<forall>i \<in> inds. i \<ge> length xs \<Longrightarrow> nths xs inds = []" 
apply (induct xs arbitrary: inds)
apply simp
apply (simp add: nths_Cons)
apply auto
apply (erule_tac x="{j. Suc j \<in> inds}" in meta_allE)
apply auto
done

lemma nths_Nil': "nths xs inds = [] \<Longrightarrow> \<forall>i \<in> inds. i \<ge> length xs"
apply (induct xs arbitrary: inds)
apply simp
apply (simp add: nths_Cons)
apply (auto split: if_splits)
apply (erule_tac x="{j. Suc j \<in> inds}" in meta_allE)
apply (case_tac x, auto)
done

lemma nths_Nil[simp]: "(nths xs inds = []) = (\<forall>i \<in> inds. i \<ge> length xs)"
apply (induct xs arbitrary: inds)
apply simp
apply (simp add: nths_Cons)
apply auto
apply (erule_tac x="{j. Suc j \<in> inds}" in meta_allE)
apply (case_tac x, auto)
done

lemma nths_eq_subseteq: " \<lbrakk> inds' \<subseteq> inds; nths xs inds = nths ys inds \<rbrakk> \<Longrightarrow> nths xs inds' = nths ys inds'"
apply (induct xs arbitrary: ys inds inds')
apply simp
apply (drule sym, rule sym)
apply (simp add: nths_Nil, fastforce)
apply (case_tac ys)
apply (simp add: nths_Nil, fastforce)
apply (auto simp add: nths_Cons)
apply (erule_tac x="list" in meta_allE)
apply (erule_tac x="{j. Suc j \<in> inds}" in meta_allE)
apply (erule_tac x="{j. Suc j \<in> inds'}" in meta_allE)
apply fastforce
apply (erule_tac x="list" in meta_allE)
apply (erule_tac x="{j. Suc j \<in> inds}" in meta_allE)
apply (erule_tac x="{j. Suc j \<in> inds'}" in meta_allE)
apply fastforce
done

lemma nths_eq: "\<lbrakk> \<forall>i \<in> inds. ((i < length xs) \<and> (i < length ys)) \<or> ((i \<ge> length xs ) \<and> (i \<ge> length ys)); \<forall>i \<in> inds. xs ! i = ys ! i \<rbrakk> \<Longrightarrow> nths xs inds = nths ys inds"
apply (induct xs arbitrary: ys inds)
apply simp
apply (rule sym, simp add: nths_Nil)
apply (case_tac ys)
apply (simp add: nths_Nil)
apply (auto simp add: nths_Cons)
apply (erule_tac x="list" in meta_allE)
apply (erule_tac x="{j. Suc j \<in> inds}" in meta_allE)
apply fastforce
apply (erule_tac x="list" in meta_allE)
apply (erule_tac x="{j. Suc j \<in> inds}" in meta_allE)
apply fastforce
done

lemma nths_eq_samelength: "\<lbrakk> length xs = length ys; \<forall>i \<in> inds. xs ! i = ys ! i \<rbrakk> \<Longrightarrow> nths xs inds = nths ys inds"
by (rule nths_eq, auto)

lemma nths_eq_samelength_iff: "length xs = length ys \<Longrightarrow> (nths xs inds = nths ys inds) = (\<forall>i \<in> inds. xs ! i = ys ! i)"
apply (induct xs arbitrary: ys inds)
apply simp
apply (rule sym, simp add: nths_Nil)
apply (case_tac ys)
apply (simp add: nths_Nil)
apply (auto simp add: nths_Cons)
apply (case_tac i)
apply auto
apply (case_tac i)
apply auto
done

section \<open>Another nths function\<close>

function nths' :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "nths' n m [] = []"
| "nths' n 0 xs = []"
| "nths' 0 (Suc m) (x#xs) = (x#nths' 0 m xs)"
| "nths' (Suc n) (Suc m) (x#xs) = nths' n m xs"
by pat_completeness auto
termination by lexicographic_order

subsection \<open>Proving equivalence to the other nths command\<close>

lemma nths'_nths: "nths' n m xs = nths xs {j. n \<le> j \<and> j < m}"
apply (induct xs arbitrary: n m)
apply simp
apply (case_tac n)
apply (case_tac m)
apply simp
apply (simp add: nths_Cons)
apply (case_tac m)
apply simp
apply (simp add: nths_Cons)
done


lemma "nths' n m xs = nths xs {n..<m}"
apply (induct xs arbitrary: n m)
apply simp
apply (case_tac n, case_tac m)
apply simp
apply simp
apply (simp add: nths_take')
apply (case_tac m)
apply simp
apply (simp add: nths_Cons nths'_nths)
done


subsection \<open>Showing equivalence to use of drop and take for definition\<close>

lemma "nths' n m xs = take (m - n) (drop n xs)"
apply (induct xs arbitrary: n m)
apply simp
apply (case_tac m)
apply simp
apply (case_tac n)
apply simp
apply simp
done

subsection \<open>General lemma about nths\<close>

lemma nths'_Nil[simp]: "nths' i j [] = []"
by simp

lemma nths'_Cons[simp]: "nths' i (Suc j) (x#xs) = (case i of 0 \<Rightarrow> (x # nths' 0 j xs) | Suc i' \<Rightarrow>  nths' i' j xs)"
by (cases i) auto

lemma nths'_Cons2[simp]: "nths' i j (x#xs) = (if (j = 0) then [] else ((if (i = 0) then [x] else []) @ nths' (i - 1) (j - 1) xs))"
apply (cases j)
apply auto
apply (cases i)
apply auto
done

lemma nths_n_0: "nths' n 0 xs = []"
by (induct xs, auto)

lemma nths'_Nil': "n \<ge> m \<Longrightarrow> nths' n m xs = []"
apply (induct xs arbitrary: n m)
apply simp
apply (case_tac m)
apply simp
apply (case_tac n)
apply simp
apply simp
done

lemma nths'_Nil2: "n \<ge> length xs \<Longrightarrow> nths' n m xs = []"
apply (induct xs arbitrary: n m)
apply simp
apply (case_tac m)
apply simp
apply (case_tac n)
apply simp
apply simp
done

lemma nths'_Nil3: "(nths' n m xs = []) = ((n \<ge> m) \<or> (n \<ge> length xs))"
apply (induct xs arbitrary: n m)
apply simp
apply (case_tac m)
apply simp
apply (case_tac n)
apply simp
apply simp
done

lemma nths'_notNil: "\<lbrakk> n < length xs; n < m \<rbrakk> \<Longrightarrow> nths' n m xs \<noteq> []"
apply (induct xs arbitrary: n m)
apply simp
apply (case_tac m)
apply simp
apply (case_tac n)
apply simp
apply simp
done

lemma nths'_single: "n < length xs \<Longrightarrow> nths' n (Suc n) xs = [xs ! n]"
apply (induct xs arbitrary: n)
apply simp
apply simp
apply (case_tac n)
apply (simp add: nths_n_0)
apply simp
done

lemma nths'_update1: "i \<ge> m \<Longrightarrow> nths' n m (xs[i:=v]) = nths' n m xs"
apply (induct xs arbitrary: n m i)
apply simp
apply simp
apply (case_tac i)
apply simp
apply simp
done

lemma nths'_update2: "i < n \<Longrightarrow> nths' n m (xs[i:=v]) = nths' n m xs"
apply (induct xs arbitrary: n m i)
apply simp
apply simp
apply (case_tac i)
apply simp
apply simp
done

lemma nths'_update3: "\<lbrakk>n \<le> i; i < m\<rbrakk> \<Longrightarrow> nths' n m (xs[i := v]) = (nths' n m xs)[i - n := v]"
proof (induct xs arbitrary: n m i)
  case Nil thus ?case by auto
next
  case (Cons x xs)
  thus ?case
    apply -
    apply auto
    apply (cases i)
    apply auto
    apply (cases i)
    apply auto
    done
qed

lemma "\<lbrakk> nths' i j xs = nths' i j ys; n \<ge> i; m \<le> j \<rbrakk> \<Longrightarrow> nths' n m xs = nths' n m ys"
proof (induct xs arbitrary: i j ys n m)
  case Nil
  thus ?case
    apply -
    apply (rule sym, drule sym)
    apply (simp add: nths'_Nil)
    apply (simp add: nths'_Nil3)
    apply arith
    done
next
  case (Cons x xs i j ys n m)
  note c = this
  thus ?case
  proof (cases m)
    case 0 thus ?thesis by (simp add: nths_n_0)
  next
    case (Suc m')
    note a = this
    thus ?thesis
    proof (cases n)
      case 0 note b = this
      show ?thesis
      proof (cases ys)
        case Nil  with a b Cons.prems show ?thesis by (simp add: nths'_Nil3)
      next
        case (Cons y ys)
        show ?thesis
        proof (cases j)
          case 0 with a b Cons.prems show ?thesis by simp
        next
          case (Suc j') with a b Cons.prems Cons show ?thesis 
            apply -
            apply (simp, rule Cons.hyps [of "0" "j'" "ys" "0" "m'"], auto)
            done
        qed
      qed
    next
      case (Suc n')
      show ?thesis
      proof (cases ys)
        case Nil with Suc a Cons.prems show ?thesis by (auto simp add: nths'_Nil3)
      next
        case (Cons y ys) with Suc a Cons.prems show ?thesis
          apply -
          apply simp
          apply (cases j)
          apply simp
          apply (cases i)
          apply simp
          apply (rule_tac j="nat" in Cons.hyps [of "0" _ "ys" "n'" "m'"])
          apply simp
          apply simp
          apply simp
          apply simp
          apply (rule_tac i="nata" and j="nat" in Cons.hyps [of _ _ "ys" "n'" "m'"])
          apply simp
          apply simp
          apply simp
          done
      qed
    qed
  qed
qed

lemma length_nths': "j \<le> length xs \<Longrightarrow> length (nths' i j xs) = j - i"
by (induct xs arbitrary: i j, auto)

lemma nths'_front: "\<lbrakk> i < j; i < length xs \<rbrakk> \<Longrightarrow> nths' i j xs = xs ! i # nths' (Suc i) j xs"
apply (induct xs arbitrary: i j)
apply simp
apply (case_tac j)
apply simp
apply (case_tac i)
apply simp
apply simp
done

lemma nths'_back: "\<lbrakk> i < j; j \<le> length xs \<rbrakk> \<Longrightarrow> nths' i j xs = nths' i (j - 1) xs @ [xs ! (j - 1)]"
apply (induct xs arbitrary: i j)
apply simp
apply simp
done

(* suffices that j \<le> length xs and length ys *) 
lemma nths'_eq_samelength_iff: "length xs = length ys \<Longrightarrow> (nths' i j xs  = nths' i j ys) = (\<forall>i'. i \<le> i' \<and> i' < j \<longrightarrow> xs ! i' = ys ! i')"
proof (induct xs arbitrary: ys i j)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  thus ?case
    apply -
    apply (cases ys)
    apply simp
    apply simp
    apply auto
    apply (case_tac i', auto)
    apply (erule_tac x="Suc i'" in allE, auto)
    apply (erule_tac x="i' - 1" in allE, auto)
    apply (erule_tac x="Suc i'" in allE, auto)
    done
qed

lemma nths'_all[simp]: "nths' 0 (length xs) xs = xs"
by (induct xs, auto)

lemma nths'_nths': "nths' n m (nths' i j xs) = nths' (i + n) (min (i + m) j) xs" 
by (induct xs arbitrary: i j n m) (auto simp add: min_diff)

lemma nths'_append: "\<lbrakk> i \<le> j; j \<le> k \<rbrakk> \<Longrightarrow>(nths' i j xs) @ (nths' j k xs) = nths' i k xs"
by (induct xs arbitrary: i j k) auto

lemma nth_nths': "\<lbrakk> k < j - i; j \<le> length xs \<rbrakk> \<Longrightarrow> (nths' i j xs) ! k = xs ! (i + k)"
apply (induct xs arbitrary: i j k)
apply simp
apply (case_tac k)
apply auto
done

lemma set_nths': "set (nths' i j xs) = {x. \<exists>k. i \<le> k \<and> k < j \<and> k < List.length xs \<and> x = xs ! k}"
apply (simp add: nths'_nths)
apply (simp add: set_nths)
apply auto
done

lemma all_in_set_nths'_conv: "(\<forall>j. j \<in> set (nths' l r xs) \<longrightarrow> P j) = (\<forall>k. l \<le> k \<and> k < r \<and> k < List.length xs \<longrightarrow> P (xs ! k))"
unfolding set_nths' by blast

lemma ball_in_set_nths'_conv: "(\<forall>j \<in> set (nths' l r xs). P j) = (\<forall>k. l \<le> k \<and> k < r \<and> k < List.length xs \<longrightarrow> P (xs ! k))"
unfolding set_nths' by blast


lemma mset_nths:
assumes l_r: "l \<le> r \<and> r \<le> List.length xs"
assumes left: "\<forall> i. i < l \<longrightarrow> (xs::'a list) ! i = ys ! i"
assumes right: "\<forall> i. i \<ge> r \<longrightarrow> (xs::'a list) ! i = ys ! i"
assumes multiset: "mset xs = mset ys"
  shows "mset (nths' l r xs) = mset (nths' l r ys)"
proof -
  from l_r have xs_def: "xs = (nths' 0 l xs) @ (nths' l r xs) @ (nths' r (List.length xs) xs)" (is "_ = ?xs_long") 
    by (simp add: nths'_append)
  from multiset have length_eq: "List.length xs = List.length ys" by (rule mset_eq_length)
  with l_r have ys_def: "ys = (nths' 0 l ys) @ (nths' l r ys) @ (nths' r (List.length ys) ys)" (is "_ = ?ys_long") 
    by (simp add: nths'_append)
  from xs_def ys_def multiset have "mset ?xs_long = mset ?ys_long" by simp
  moreover
  from left l_r length_eq have "nths' 0 l xs = nths' 0 l ys"
    by (auto simp add: length_nths' nth_nths' intro!: nth_equalityI)
  moreover
  from right l_r length_eq have "nths' r (List.length xs) xs = nths' r (List.length ys) ys"
    by (auto simp add: length_nths' nth_nths' intro!: nth_equalityI)
  ultimately show ?thesis by (simp add: mset_append)
qed


end
