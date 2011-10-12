(*  Title:      HOL/Imperative_HOL/ex/Sublist.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

header {* Slices of lists *}

theory Sublist
imports "~~/src/HOL/Library/Multiset"
begin

lemma sublist_split: "i \<le> j \<and> j \<le> k \<Longrightarrow> sublist xs {i..<j} @ sublist xs {j..<k} = sublist xs {i..<k}" 
apply (induct xs arbitrary: i j k)
apply simp
apply (simp only: sublist_Cons)
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

lemma sublist_update1: "i \<notin> inds \<Longrightarrow> sublist (xs[i := v]) inds = sublist xs inds"
apply (induct xs arbitrary: i inds)
apply simp
apply (case_tac i)
apply (simp add: sublist_Cons)
apply (simp add: sublist_Cons)
done

lemma sublist_update2: "i \<in> inds \<Longrightarrow> sublist (xs[i := v]) inds = (sublist xs inds)[(card {k \<in> inds. k < i}):= v]"
proof (induct xs arbitrary: i inds)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  thus ?case
  proof (cases i)
    case 0 with Cons show ?thesis by (simp add: sublist_Cons)
  next
    case (Suc i')
    with Cons show ?thesis
      apply simp
      apply (simp add: sublist_Cons)
      apply auto
      apply (auto simp add: nat.split)
      apply (simp add: card_less_Suc[symmetric])
      apply (simp add: card_less_Suc2)
      done
  qed
qed

lemma sublist_update: "sublist (xs[i := v]) inds = (if i \<in> inds then (sublist xs inds)[(card {k \<in> inds. k < i}) := v] else sublist xs inds)"
by (simp add: sublist_update1 sublist_update2)

lemma sublist_take: "sublist xs {j. j < m} = take m xs"
apply (induct xs arbitrary: m)
apply simp
apply (case_tac m)
apply simp
apply (simp add: sublist_Cons)
done

lemma sublist_take': "sublist xs {0..<m} = take m xs"
apply (induct xs arbitrary: m)
apply simp
apply (case_tac m)
apply simp
apply (simp add: sublist_Cons sublist_take)
done

lemma sublist_all[simp]: "sublist xs {j. j < length xs} = xs"
apply (induct xs)
apply simp
apply (simp add: sublist_Cons)
done

lemma sublist_all'[simp]: "sublist xs {0..<length xs} = xs"
apply (induct xs)
apply simp
apply (simp add: sublist_Cons)
done

lemma sublist_single: "a < length xs \<Longrightarrow> sublist xs {a} = [xs ! a]"
apply (induct xs arbitrary: a)
apply simp
apply(case_tac aa)
apply simp
apply (simp add: sublist_Cons)
apply simp
apply (simp add: sublist_Cons)
done

lemma sublist_is_Nil: "\<forall>i \<in> inds. i \<ge> length xs \<Longrightarrow> sublist xs inds = []" 
apply (induct xs arbitrary: inds)
apply simp
apply (simp add: sublist_Cons)
apply auto
apply (erule_tac x="{j. Suc j \<in> inds}" in meta_allE)
apply auto
done

lemma sublist_Nil': "sublist xs inds = [] \<Longrightarrow> \<forall>i \<in> inds. i \<ge> length xs"
apply (induct xs arbitrary: inds)
apply simp
apply (simp add: sublist_Cons)
apply (auto split: if_splits)
apply (erule_tac x="{j. Suc j \<in> inds}" in meta_allE)
apply (case_tac x, auto)
done

lemma sublist_Nil[simp]: "(sublist xs inds = []) = (\<forall>i \<in> inds. i \<ge> length xs)"
apply (induct xs arbitrary: inds)
apply simp
apply (simp add: sublist_Cons)
apply auto
apply (erule_tac x="{j. Suc j \<in> inds}" in meta_allE)
apply (case_tac x, auto)
done

lemma sublist_eq_subseteq: " \<lbrakk> inds' \<subseteq> inds; sublist xs inds = sublist ys inds \<rbrakk> \<Longrightarrow> sublist xs inds' = sublist ys inds'"
apply (induct xs arbitrary: ys inds inds')
apply simp
apply (drule sym, rule sym)
apply (simp add: sublist_Nil, fastforce)
apply (case_tac ys)
apply (simp add: sublist_Nil, fastforce)
apply (auto simp add: sublist_Cons)
apply (erule_tac x="list" in meta_allE)
apply (erule_tac x="{j. Suc j \<in> inds}" in meta_allE)
apply (erule_tac x="{j. Suc j \<in> inds'}" in meta_allE)
apply fastforce
apply (erule_tac x="list" in meta_allE)
apply (erule_tac x="{j. Suc j \<in> inds}" in meta_allE)
apply (erule_tac x="{j. Suc j \<in> inds'}" in meta_allE)
apply fastforce
done

lemma sublist_eq: "\<lbrakk> \<forall>i \<in> inds. ((i < length xs) \<and> (i < length ys)) \<or> ((i \<ge> length xs ) \<and> (i \<ge> length ys)); \<forall>i \<in> inds. xs ! i = ys ! i \<rbrakk> \<Longrightarrow> sublist xs inds = sublist ys inds"
apply (induct xs arbitrary: ys inds)
apply simp
apply (rule sym, simp add: sublist_Nil)
apply (case_tac ys)
apply (simp add: sublist_Nil)
apply (auto simp add: sublist_Cons)
apply (erule_tac x="list" in meta_allE)
apply (erule_tac x="{j. Suc j \<in> inds}" in meta_allE)
apply fastforce
apply (erule_tac x="list" in meta_allE)
apply (erule_tac x="{j. Suc j \<in> inds}" in meta_allE)
apply fastforce
done

lemma sublist_eq_samelength: "\<lbrakk> length xs = length ys; \<forall>i \<in> inds. xs ! i = ys ! i \<rbrakk> \<Longrightarrow> sublist xs inds = sublist ys inds"
by (rule sublist_eq, auto)

lemma sublist_eq_samelength_iff: "length xs = length ys \<Longrightarrow> (sublist xs inds = sublist ys inds) = (\<forall>i \<in> inds. xs ! i = ys ! i)"
apply (induct xs arbitrary: ys inds)
apply simp
apply (rule sym, simp add: sublist_Nil)
apply (case_tac ys)
apply (simp add: sublist_Nil)
apply (auto simp add: sublist_Cons)
apply (case_tac i)
apply auto
apply (case_tac i)
apply auto
done

section {* Another sublist function *}

function sublist' :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "sublist' n m [] = []"
| "sublist' n 0 xs = []"
| "sublist' 0 (Suc m) (x#xs) = (x#sublist' 0 m xs)"
| "sublist' (Suc n) (Suc m) (x#xs) = sublist' n m xs"
by pat_completeness auto
termination by lexicographic_order

subsection {* Proving equivalence to the other sublist command *}

lemma sublist'_sublist: "sublist' n m xs = sublist xs {j. n \<le> j \<and> j < m}"
apply (induct xs arbitrary: n m)
apply simp
apply (case_tac n)
apply (case_tac m)
apply simp
apply (simp add: sublist_Cons)
apply (case_tac m)
apply simp
apply (simp add: sublist_Cons)
done


lemma "sublist' n m xs = sublist xs {n..<m}"
apply (induct xs arbitrary: n m)
apply simp
apply (case_tac n, case_tac m)
apply simp
apply simp
apply (simp add: sublist_take')
apply (case_tac m)
apply simp
apply (simp add: sublist_Cons sublist'_sublist)
done


subsection {* Showing equivalence to use of drop and take for definition *}

lemma "sublist' n m xs = take (m - n) (drop n xs)"
apply (induct xs arbitrary: n m)
apply simp
apply (case_tac m)
apply simp
apply (case_tac n)
apply simp
apply simp
done

subsection {* General lemma about sublist *}

lemma sublist'_Nil[simp]: "sublist' i j [] = []"
by simp

lemma sublist'_Cons[simp]: "sublist' i (Suc j) (x#xs) = (case i of 0 \<Rightarrow> (x # sublist' 0 j xs) | Suc i' \<Rightarrow>  sublist' i' j xs)"
by (cases i) auto

lemma sublist'_Cons2[simp]: "sublist' i j (x#xs) = (if (j = 0) then [] else ((if (i = 0) then [x] else []) @ sublist' (i - 1) (j - 1) xs))"
apply (cases j)
apply auto
apply (cases i)
apply auto
done

lemma sublist_n_0: "sublist' n 0 xs = []"
by (induct xs, auto)

lemma sublist'_Nil': "n \<ge> m \<Longrightarrow> sublist' n m xs = []"
apply (induct xs arbitrary: n m)
apply simp
apply (case_tac m)
apply simp
apply (case_tac n)
apply simp
apply simp
done

lemma sublist'_Nil2: "n \<ge> length xs \<Longrightarrow> sublist' n m xs = []"
apply (induct xs arbitrary: n m)
apply simp
apply (case_tac m)
apply simp
apply (case_tac n)
apply simp
apply simp
done

lemma sublist'_Nil3: "(sublist' n m xs = []) = ((n \<ge> m) \<or> (n \<ge> length xs))"
apply (induct xs arbitrary: n m)
apply simp
apply (case_tac m)
apply simp
apply (case_tac n)
apply simp
apply simp
done

lemma sublist'_notNil: "\<lbrakk> n < length xs; n < m \<rbrakk> \<Longrightarrow> sublist' n m xs \<noteq> []"
apply (induct xs arbitrary: n m)
apply simp
apply (case_tac m)
apply simp
apply (case_tac n)
apply simp
apply simp
done

lemma sublist'_single: "n < length xs \<Longrightarrow> sublist' n (Suc n) xs = [xs ! n]"
apply (induct xs arbitrary: n)
apply simp
apply simp
apply (case_tac n)
apply (simp add: sublist_n_0)
apply simp
done

lemma sublist'_update1: "i \<ge> m \<Longrightarrow> sublist' n m (xs[i:=v]) = sublist' n m xs"
apply (induct xs arbitrary: n m i)
apply simp
apply simp
apply (case_tac i)
apply simp
apply simp
done

lemma sublist'_update2: "i < n \<Longrightarrow> sublist' n m (xs[i:=v]) = sublist' n m xs"
apply (induct xs arbitrary: n m i)
apply simp
apply simp
apply (case_tac i)
apply simp
apply simp
done

lemma sublist'_update3: "\<lbrakk>n \<le> i; i < m\<rbrakk> \<Longrightarrow> sublist' n m (xs[i := v]) = (sublist' n m xs)[i - n := v]"
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

lemma "\<lbrakk> sublist' i j xs = sublist' i j ys; n \<ge> i; m \<le> j \<rbrakk> \<Longrightarrow> sublist' n m xs = sublist' n m ys"
proof (induct xs arbitrary: i j ys n m)
  case Nil
  thus ?case
    apply -
    apply (rule sym, drule sym)
    apply (simp add: sublist'_Nil)
    apply (simp add: sublist'_Nil3)
    apply arith
    done
next
  case (Cons x xs i j ys n m)
  note c = this
  thus ?case
  proof (cases m)
    case 0 thus ?thesis by (simp add: sublist_n_0)
  next
    case (Suc m')
    note a = this
    thus ?thesis
    proof (cases n)
      case 0 note b = this
      show ?thesis
      proof (cases ys)
        case Nil  with a b Cons.prems show ?thesis by (simp add: sublist'_Nil3)
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
        case Nil with Suc a Cons.prems show ?thesis by (auto simp add: sublist'_Nil3)
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

lemma length_sublist': "j \<le> length xs \<Longrightarrow> length (sublist' i j xs) = j - i"
by (induct xs arbitrary: i j, auto)

lemma sublist'_front: "\<lbrakk> i < j; i < length xs \<rbrakk> \<Longrightarrow> sublist' i j xs = xs ! i # sublist' (Suc i) j xs"
apply (induct xs arbitrary: i j)
apply simp
apply (case_tac j)
apply simp
apply (case_tac i)
apply simp
apply simp
done

lemma sublist'_back: "\<lbrakk> i < j; j \<le> length xs \<rbrakk> \<Longrightarrow> sublist' i j xs = sublist' i (j - 1) xs @ [xs ! (j - 1)]"
apply (induct xs arbitrary: i j)
apply simp
apply simp
done

(* suffices that j \<le> length xs and length ys *) 
lemma sublist'_eq_samelength_iff: "length xs = length ys \<Longrightarrow> (sublist' i j xs  = sublist' i j ys) = (\<forall>i'. i \<le> i' \<and> i' < j \<longrightarrow> xs ! i' = ys ! i')"
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

lemma sublist'_all[simp]: "sublist' 0 (length xs) xs = xs"
by (induct xs, auto)

lemma sublist'_sublist': "sublist' n m (sublist' i j xs) = sublist' (i + n) (min (i + m) j) xs" 
by (induct xs arbitrary: i j n m) (auto simp add: min_diff)

lemma sublist'_append: "\<lbrakk> i \<le> j; j \<le> k \<rbrakk> \<Longrightarrow>(sublist' i j xs) @ (sublist' j k xs) = sublist' i k xs"
by (induct xs arbitrary: i j k) auto

lemma nth_sublist': "\<lbrakk> k < j - i; j \<le> length xs \<rbrakk> \<Longrightarrow> (sublist' i j xs) ! k = xs ! (i + k)"
apply (induct xs arbitrary: i j k)
apply simp
apply (case_tac k)
apply auto
done

lemma set_sublist': "set (sublist' i j xs) = {x. \<exists>k. i \<le> k \<and> k < j \<and> k < List.length xs \<and> x = xs ! k}"
apply (simp add: sublist'_sublist)
apply (simp add: set_sublist)
apply auto
done

lemma all_in_set_sublist'_conv: "(\<forall>j. j \<in> set (sublist' l r xs) \<longrightarrow> P j) = (\<forall>k. l \<le> k \<and> k < r \<and> k < List.length xs \<longrightarrow> P (xs ! k))"
unfolding set_sublist' by blast

lemma ball_in_set_sublist'_conv: "(\<forall>j \<in> set (sublist' l r xs). P j) = (\<forall>k. l \<le> k \<and> k < r \<and> k < List.length xs \<longrightarrow> P (xs ! k))"
unfolding set_sublist' by blast


lemma multiset_of_sublist:
assumes l_r: "l \<le> r \<and> r \<le> List.length xs"
assumes left: "\<forall> i. i < l \<longrightarrow> (xs::'a list) ! i = ys ! i"
assumes right: "\<forall> i. i \<ge> r \<longrightarrow> (xs::'a list) ! i = ys ! i"
assumes multiset: "multiset_of xs = multiset_of ys"
  shows "multiset_of (sublist' l r xs) = multiset_of (sublist' l r ys)"
proof -
  from l_r have xs_def: "xs = (sublist' 0 l xs) @ (sublist' l r xs) @ (sublist' r (List.length xs) xs)" (is "_ = ?xs_long") 
    by (simp add: sublist'_append)
  from multiset have length_eq: "List.length xs = List.length ys" by (rule multiset_of_eq_length)
  with l_r have ys_def: "ys = (sublist' 0 l ys) @ (sublist' l r ys) @ (sublist' r (List.length ys) ys)" (is "_ = ?ys_long") 
    by (simp add: sublist'_append)
  from xs_def ys_def multiset have "multiset_of ?xs_long = multiset_of ?ys_long" by simp
  moreover
  from left l_r length_eq have "sublist' 0 l xs = sublist' 0 l ys"
    by (auto simp add: length_sublist' nth_sublist' intro!: nth_equalityI)
  moreover
  from right l_r length_eq have "sublist' r (List.length xs) xs = sublist' r (List.length ys) ys"
    by (auto simp add: length_sublist' nth_sublist' intro!: nth_equalityI)
  moreover
  ultimately show ?thesis by (simp add: multiset_of_append)
qed


end
