(*  Title:      HOL/Library/DAList_Multiset.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

section \<open>Multisets partially implemented by association lists\<close>

theory DAList_Multiset
imports Multiset DAList
begin

text \<open>Delete prexisting code equations\<close>

declare [[code drop: "{#}" Multiset.is_empty add_mset
  "plus :: 'a multiset \<Rightarrow> _" "minus :: 'a multiset \<Rightarrow> _"
  inter_mset union_mset image_mset filter_mset count
  "size :: _ multiset \<Rightarrow> nat" sum_mset prod_mset
  set_mset sorted_list_of_multiset subset_mset subseteq_mset
  equal_multiset_inst.equal_multiset]]
    

text \<open>Raw operations on lists\<close>

definition join_raw ::
    "('key \<Rightarrow> 'val \<times> 'val \<Rightarrow> 'val) \<Rightarrow>
      ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
  where "join_raw f xs ys = foldr (\<lambda>(k, v). map_default k v (\<lambda>v'. f k (v', v))) ys xs"

lemma join_raw_Nil [simp]: "join_raw f xs [] = xs"
  by (simp add: join_raw_def)

lemma join_raw_Cons [simp]:
  "join_raw f xs ((k, v) # ys) = map_default k v (\<lambda>v'. f k (v', v)) (join_raw f xs ys)"
  by (simp add: join_raw_def)

lemma map_of_join_raw:
  assumes "distinct (map fst ys)"
  shows "map_of (join_raw f xs ys) x =
    (case map_of xs x of
      None \<Rightarrow> map_of ys x
    | Some v \<Rightarrow> (case map_of ys x of None \<Rightarrow> Some v | Some v' \<Rightarrow> Some (f x (v, v'))))"
  using assms
  apply (induct ys)
  apply (auto simp add: map_of_map_default split: option.split)
  apply (metis map_of_eq_None_iff option.simps(2) weak_map_of_SomeI)
  apply (metis Some_eq_map_of_iff map_of_eq_None_iff option.simps(2))
  done

lemma distinct_join_raw:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (join_raw f xs ys))"
  using assms
proof (induct ys)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case by (cases y) (simp add: distinct_map_default)
qed

definition "subtract_entries_raw xs ys = foldr (\<lambda>(k, v). AList.map_entry k (\<lambda>v'. v' - v)) ys xs"

lemma map_of_subtract_entries_raw:
  assumes "distinct (map fst ys)"
  shows "map_of (subtract_entries_raw xs ys) x =
    (case map_of xs x of
      None \<Rightarrow> None
    | Some v \<Rightarrow> (case map_of ys x of None \<Rightarrow> Some v | Some v' \<Rightarrow> Some (v - v')))"
  using assms
  unfolding subtract_entries_raw_def
  apply (induct ys)
  apply auto
  apply (simp split: option.split)
  apply (simp add: map_of_map_entry)
  apply (auto split: option.split)
  apply (metis map_of_eq_None_iff option.simps(3) option.simps(4))
  apply (metis map_of_eq_None_iff option.simps(4) option.simps(5))
  done

lemma distinct_subtract_entries_raw:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (subtract_entries_raw xs ys))"
  using assms
  unfolding subtract_entries_raw_def
  by (induct ys) (auto simp add: distinct_map_entry)


text \<open>Operations on alists with distinct keys\<close>

lift_definition join :: "('a \<Rightarrow> 'b \<times> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) alist \<Rightarrow> ('a, 'b) alist \<Rightarrow> ('a, 'b) alist"
  is join_raw
  by (simp add: distinct_join_raw)

lift_definition subtract_entries :: "('a, ('b :: minus)) alist \<Rightarrow> ('a, 'b) alist \<Rightarrow> ('a, 'b) alist"
  is subtract_entries_raw
  by (simp add: distinct_subtract_entries_raw)


text \<open>Implementing multisets by means of association lists\<close>

definition count_of :: "('a \<times> nat) list \<Rightarrow> 'a \<Rightarrow> nat"
  where "count_of xs x = (case map_of xs x of None \<Rightarrow> 0 | Some n \<Rightarrow> n)"

lemma count_of_multiset: "finite {x. 0 < count_of xs x}"
proof -
  let ?A = "{x::'a. 0 < (case map_of xs x of None \<Rightarrow> 0::nat | Some n \<Rightarrow> n)}"
  have "?A \<subseteq> dom (map_of xs)"
  proof
    fix x
    assume "x \<in> ?A"
    then have "0 < (case map_of xs x of None \<Rightarrow> 0::nat | Some n \<Rightarrow> n)"
      by simp
    then have "map_of xs x \<noteq> None"
      by (cases "map_of xs x") auto
    then show "x \<in> dom (map_of xs)"
      by auto
  qed
  with finite_dom_map_of [of xs] have "finite ?A"
    by (auto intro: finite_subset)
  then show ?thesis
    by (simp add: count_of_def fun_eq_iff)
qed

lemma count_simps [simp]:
  "count_of [] = (\<lambda>_. 0)"
  "count_of ((x, n) # xs) = (\<lambda>y. if x = y then n else count_of xs y)"
  by (simp_all add: count_of_def fun_eq_iff)

lemma count_of_empty: "x \<notin> fst ` set xs \<Longrightarrow> count_of xs x = 0"
  by (induct xs) (simp_all add: count_of_def)

lemma count_of_filter: "count_of (List.filter (P \<circ> fst) xs) x = (if P x then count_of xs x else 0)"
  by (induct xs) auto

lemma count_of_map_default [simp]:
  "count_of (map_default x b (\<lambda>x. x + b) xs) y =
    (if x = y then count_of xs x + b else count_of xs y)"
  unfolding count_of_def by (simp add: map_of_map_default split: option.split)

lemma count_of_join_raw:
  "distinct (map fst ys) \<Longrightarrow>
    count_of xs x + count_of ys x = count_of (join_raw (\<lambda>x (x, y). x + y) xs ys) x"
  unfolding count_of_def by (simp add: map_of_join_raw split: option.split)

lemma count_of_subtract_entries_raw:
  "distinct (map fst ys) \<Longrightarrow>
    count_of xs x - count_of ys x = count_of (subtract_entries_raw xs ys) x"
  unfolding count_of_def by (simp add: map_of_subtract_entries_raw split: option.split)


text \<open>Code equations for multiset operations\<close>

definition Bag :: "('a, nat) alist \<Rightarrow> 'a multiset"
  where "Bag xs = Abs_multiset (count_of (DAList.impl_of xs))"

code_datatype Bag

lemma count_Bag [simp, code]: "count (Bag xs) = count_of (DAList.impl_of xs)"
  by (simp add: Bag_def count_of_multiset)

lemma Mempty_Bag [code]: "{#} = Bag (DAList.empty)"
  by (simp add: multiset_eq_iff alist.Alist_inverse DAList.empty_def)

lift_definition is_empty_Bag_impl :: "('a, nat) alist \<Rightarrow> bool" is
  "\<lambda>xs. list_all (\<lambda>x. snd x = 0) xs" .

lemma is_empty_Bag [code]: "Multiset.is_empty (Bag xs) \<longleftrightarrow> is_empty_Bag_impl xs"
proof -
  have "Multiset.is_empty (Bag xs) \<longleftrightarrow> (\<forall>x. count (Bag xs) x = 0)"
    unfolding Multiset.is_empty_def multiset_eq_iff by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>x\<in>fst ` set (alist.impl_of xs). count (Bag xs) x = 0)"
  proof (intro iffI allI ballI)
    fix x assume A: "\<forall>x\<in>fst ` set (alist.impl_of xs). count (Bag xs) x = 0"
    thus "count (Bag xs) x = 0"
    proof (cases "x \<in> fst ` set (alist.impl_of xs)")
      case False
      thus ?thesis by (force simp: count_of_def split: option.splits)
    qed (insert A, auto)
  qed simp_all
  also have "\<dots> \<longleftrightarrow> list_all (\<lambda>x. snd x = 0) (alist.impl_of xs)" 
    by (auto simp: count_of_def list_all_def)
  finally show ?thesis by (simp add: is_empty_Bag_impl.rep_eq)
qed

lemma union_Bag [code]: "Bag xs + Bag ys = Bag (join (\<lambda>x (n1, n2). n1 + n2) xs ys)"
  by (rule multiset_eqI)
    (simp add: count_of_join_raw alist.Alist_inverse distinct_join_raw join_def)

lemma add_mset_Bag [code]: "add_mset x (Bag xs) =
    Bag (join (\<lambda>x (n1, n2). n1 + n2) (DAList.update x 1 DAList.empty) xs)"
  unfolding add_mset_add_single[of x "Bag xs"] union_Bag[symmetric]
  by (simp add: multiset_eq_iff update.rep_eq empty.rep_eq)

lemma minus_Bag [code]: "Bag xs - Bag ys = Bag (subtract_entries xs ys)"
  by (rule multiset_eqI)
    (simp add: count_of_subtract_entries_raw alist.Alist_inverse
      distinct_subtract_entries_raw subtract_entries_def)

lemma filter_Bag [code]: "filter_mset P (Bag xs) = Bag (DAList.filter (P \<circ> fst) xs)"
  by (rule multiset_eqI) (simp add: count_of_filter DAList.filter.rep_eq)


lemma mset_eq [code]: "HOL.equal (m1::'a::equal multiset) m2 \<longleftrightarrow> m1 \<subseteq># m2 \<and> m2 \<subseteq># m1"
  by (metis equal_multiset_def subset_mset.eq_iff)

text \<open>By default the code for \<open><\<close> is \<^prop>\<open>xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> xs = ys\<close>.
With equality implemented by \<open>\<le>\<close>, this leads to three calls of  \<open>\<le>\<close>.
Here is a more efficient version:\<close>
lemma mset_less[code]: "xs \<subset># (ys :: 'a multiset) \<longleftrightarrow> xs \<subseteq># ys \<and> \<not> ys \<subseteq># xs"
  by (rule subset_mset.less_le_not_le)

lemma mset_less_eq_Bag0:
  "Bag xs \<subseteq># A \<longleftrightarrow> (\<forall>(x, n) \<in> set (DAList.impl_of xs). count_of (DAList.impl_of xs) x \<le> count A x)"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs by (auto simp add: subseteq_mset_def)
next
  assume ?rhs
  show ?lhs
  proof (rule mset_subset_eqI)
    fix x
    from \<open>?rhs\<close> have "count_of (DAList.impl_of xs) x \<le> count A x"
      by (cases "x \<in> fst ` set (DAList.impl_of xs)") (auto simp add: count_of_empty)
    then show "count (Bag xs) x \<le> count A x" by (simp add: subset_mset_def)
  qed
qed

lemma mset_less_eq_Bag [code]:
  "Bag xs \<subseteq># (A :: 'a multiset) \<longleftrightarrow> (\<forall>(x, n) \<in> set (DAList.impl_of xs). n \<le> count A x)"
proof -
  {
    fix x n
    assume "(x,n) \<in> set (DAList.impl_of xs)"
    then have "count_of (DAList.impl_of xs) x = n"
    proof transfer
      fix x n
      fix xs :: "('a \<times> nat) list"
      show "(distinct \<circ> map fst) xs \<Longrightarrow> (x, n) \<in> set xs \<Longrightarrow> count_of xs x = n"
      proof (induct xs)
        case Nil
        then show ?case by simp
      next
        case (Cons ym ys)
        obtain y m where ym: "ym = (y,m)" by force
        note Cons = Cons[unfolded ym]
        show ?case
        proof (cases "x = y")
          case False
          with Cons show ?thesis
            unfolding ym by auto
        next
          case True
          with Cons(2-3) have "m = n" by force
          with True show ?thesis
            unfolding ym by auto
        qed
      qed
    qed
  }
  then show ?thesis
    unfolding mset_less_eq_Bag0 by auto
qed

declare inter_mset_def [code]
declare union_mset_def [code]
declare mset.simps [code]


fun fold_impl :: "('a \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('a \<times> nat) list \<Rightarrow> 'b"
where
  "fold_impl fn e ((a,n) # ms) = (fold_impl fn ((fn a n) e) ms)"
| "fold_impl fn e [] = e"

context
begin

qualified definition fold :: "('a \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('a, nat) alist \<Rightarrow> 'b"
  where "fold f e al = fold_impl f e (DAList.impl_of al)"

end

context comp_fun_commute
begin

lemma DAList_Multiset_fold:
  assumes fn: "\<And>a n x. fn a n x = (f a ^^ n) x"
  shows "fold_mset f e (Bag al) = DAList_Multiset.fold fn e al"
  unfolding DAList_Multiset.fold_def
proof (induct al)
  fix ys
  let ?inv = "{xs :: ('a \<times> nat) list. (distinct \<circ> map fst) xs}"
  note cs[simp del] = count_simps
  have count[simp]: "\<And>x. count (Abs_multiset (count_of x)) = count_of x"
    by (rule Abs_multiset_inverse) (simp add: count_of_multiset)
  assume ys: "ys \<in> ?inv"
  then show "fold_mset f e (Bag (Alist ys)) = fold_impl fn e (DAList.impl_of (Alist ys))"
    unfolding Bag_def unfolding Alist_inverse[OF ys]
  proof (induct ys arbitrary: e rule: list.induct)
    case Nil
    show ?case
      by (rule trans[OF arg_cong[of _ "{#}" "fold_mset f e", OF multiset_eqI]])
         (auto, simp add: cs)
  next
    case (Cons pair ys e)
    obtain a n where pair: "pair = (a,n)"
      by force
    from fn[of a n] have [simp]: "fn a n = (f a ^^ n)"
      by auto
    have inv: "ys \<in> ?inv"
      using Cons(2) by auto
    note IH = Cons(1)[OF inv]
    define Ys where "Ys = Abs_multiset (count_of ys)"
    have id: "Abs_multiset (count_of ((a, n) # ys)) = (((+) {# a #}) ^^ n) Ys"
      unfolding Ys_def
    proof (rule multiset_eqI, unfold count)
      fix c
      show "count_of ((a, n) # ys) c =
        count (((+) {#a#} ^^ n) (Abs_multiset (count_of ys))) c" (is "?l = ?r")
      proof (cases "c = a")
        case False
        then show ?thesis
          unfolding cs by (induct n) auto
      next
        case True
        then have "?l = n" by (simp add: cs)
        also have "n = ?r" unfolding True
        proof (induct n)
          case 0
          from Cons(2)[unfolded pair] have "a \<notin> fst ` set ys" by auto
          then show ?case by (induct ys) (simp, auto simp: cs)
        next
          case Suc
          then show ?case by simp
        qed
        finally show ?thesis .
      qed
    qed
    show ?case
      unfolding pair
      apply (simp add: IH[symmetric])
      unfolding id Ys_def[symmetric]
      apply (induct n)
      apply (auto simp: fold_mset_fun_left_comm[symmetric])
      done
  qed
qed

end

context
begin

private lift_definition single_alist_entry :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) alist" is "\<lambda>a b. [(a, b)]"
  by auto

lemma image_mset_Bag [code]:
  "image_mset f (Bag ms) =
    DAList_Multiset.fold (\<lambda>a n m. Bag (single_alist_entry (f a) n) + m) {#} ms"
  unfolding image_mset_def
proof (rule comp_fun_commute.DAList_Multiset_fold, unfold_locales, (auto simp: ac_simps)[1])
  fix a n m
  show "Bag (single_alist_entry (f a) n) + m = ((add_mset \<circ> f) a ^^ n) m" (is "?l = ?r")
  proof (rule multiset_eqI)
    fix x
    have "count ?r x = (if x = f a then n + count m x else count m x)"
      by (induct n) auto
    also have "\<dots> = count ?l x"
      by (simp add: single_alist_entry.rep_eq)
    finally show "count ?l x = count ?r x" ..
  qed
qed

end

\<comment> \<open>we cannot use \<open>\<lambda>a n. (+) (a * n)\<close> for folding, since \<open>(*)\<close> is not defined in \<open>comm_monoid_add\<close>\<close>
lemma sum_mset_Bag[code]: "sum_mset (Bag ms) = DAList_Multiset.fold (\<lambda>a n. (((+) a) ^^ n)) 0 ms"
  unfolding sum_mset.eq_fold
  apply (rule comp_fun_commute.DAList_Multiset_fold)
  apply unfold_locales
  apply (auto simp: ac_simps)
  done

\<comment> \<open>we cannot use \<open>\<lambda>a n. (*) (a ^ n)\<close> for folding, since \<open>(^)\<close> is not defined in \<open>comm_monoid_mult\<close>\<close>
lemma prod_mset_Bag[code]: "prod_mset (Bag ms) = DAList_Multiset.fold (\<lambda>a n. (((*) a) ^^ n)) 1 ms"
  unfolding prod_mset.eq_fold
  apply (rule comp_fun_commute.DAList_Multiset_fold)
  apply unfold_locales
  apply (auto simp: ac_simps)
  done

lemma size_fold: "size A = fold_mset (\<lambda>_. Suc) 0 A" (is "_ = fold_mset ?f _ _")
proof -
  interpret comp_fun_commute ?f by standard auto
  show ?thesis by (induct A) auto
qed

lemma size_Bag[code]: "size (Bag ms) = DAList_Multiset.fold (\<lambda>a n. (+) n) 0 ms"
  unfolding size_fold
proof (rule comp_fun_commute.DAList_Multiset_fold, unfold_locales, simp)
  fix a n x
  show "n + x = (Suc ^^ n) x"
    by (induct n) auto
qed


lemma set_mset_fold: "set_mset A = fold_mset insert {} A" (is "_ = fold_mset ?f _ _")
proof -
  interpret comp_fun_commute ?f by standard auto
  show ?thesis by (induct A) auto
qed

lemma set_mset_Bag[code]:
  "set_mset (Bag ms) = DAList_Multiset.fold (\<lambda>a n. (if n = 0 then (\<lambda>m. m) else insert a)) {} ms"
  unfolding set_mset_fold
proof (rule comp_fun_commute.DAList_Multiset_fold, unfold_locales, (auto simp: ac_simps)[1])
  fix a n x
  show "(if n = 0 then \<lambda>m. m else insert a) x = (insert a ^^ n) x" (is "?l n = ?r n")
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    then have "?l n = insert a x" by simp
    moreover have "?r n = insert a x" unfolding Suc by (induct m) auto
    ultimately show ?thesis by auto
  qed
qed


instantiation multiset :: (exhaustive) exhaustive
begin

definition exhaustive_multiset ::
  "('a multiset \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
  where "exhaustive_multiset f i = Quickcheck_Exhaustive.exhaustive (\<lambda>xs. f (Bag xs)) i"

instance ..

end

end

