(*  Title:      HOL/Library/DAList_Multiset.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

section \<open>Multisets partially implemented by association lists\<close>

theory DAList_Multiset
imports Multiset DAList
begin

text \<open>Delete prexisting code equations\<close>

lemma [code, code del]: "{#} = {#}" ..

lemma [code, code del]: "single = single" ..

lemma [code, code del]: "plus = (plus :: 'a multiset \<Rightarrow> _)" ..

lemma [code, code del]: "minus = (minus :: 'a multiset \<Rightarrow> _)" ..

lemma [code, code del]: "inf = (inf :: 'a multiset \<Rightarrow> _)" ..

lemma [code, code del]: "sup = (sup :: 'a multiset \<Rightarrow> _)" ..

lemma [code, code del]: "image_mset = image_mset" ..

lemma [code, code del]: "Multiset.filter = Multiset.filter" ..

lemma [code, code del]: "count = count" ..

lemma [code, code del]: "size = (size :: _ multiset \<Rightarrow> nat)" ..

lemma [code, code del]: "msetsum = msetsum" ..

lemma [code, code del]: "msetprod = msetprod" ..

lemma [code, code del]: "set_of = set_of" ..

lemma [code, code del]: "sorted_list_of_multiset = sorted_list_of_multiset" ..

lemma [code, code del]: "ord_multiset_inst.less_eq_multiset = ord_multiset_inst.less_eq_multiset" ..

lemma [code, code del]: "ord_multiset_inst.less_multiset = ord_multiset_inst.less_multiset" ..

lemma [code, code del]: "equal_multiset_inst.equal_multiset = equal_multiset_inst.equal_multiset" ..


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

lemma count_of_multiset: "count_of xs \<in> multiset"
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
    by (simp add: count_of_def fun_eq_iff multiset_def)
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

lemma single_Bag [code]: "{#x#} = Bag (DAList.update x 1 DAList.empty)"
  by (simp add: multiset_eq_iff alist.Alist_inverse update.rep_eq empty.rep_eq)

lemma union_Bag [code]: "Bag xs + Bag ys = Bag (join (\<lambda>x (n1, n2). n1 + n2) xs ys)"
  by (rule multiset_eqI)
    (simp add: count_of_join_raw alist.Alist_inverse distinct_join_raw join_def)

lemma minus_Bag [code]: "Bag xs - Bag ys = Bag (subtract_entries xs ys)"
  by (rule multiset_eqI)
    (simp add: count_of_subtract_entries_raw alist.Alist_inverse
      distinct_subtract_entries_raw subtract_entries_def)

lemma filter_Bag [code]: "Multiset.filter P (Bag xs) = Bag (DAList.filter (P \<circ> fst) xs)"
  by (rule multiset_eqI) (simp add: count_of_filter DAList.filter.rep_eq)


lemma mset_eq [code]: "HOL.equal (m1::'a::equal multiset) m2 \<longleftrightarrow> m1 \<le> m2 \<and> m2 \<le> m1"
  by (metis equal_multiset_def eq_iff)

text \<open>By default the code for @{text "<"} is @{prop"xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> xs = ys"}.
With equality implemented by @{text"\<le>"}, this leads to three calls of  @{text"\<le>"}.
Here is a more efficient version:\<close>
lemma mset_less[code]: "xs < (ys :: 'a multiset) \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs"
  by (rule less_le_not_le)

lemma mset_less_eq_Bag0:
  "Bag xs \<le> A \<longleftrightarrow> (\<forall>(x, n) \<in> set (DAList.impl_of xs). count_of (DAList.impl_of xs) x \<le> count A x)"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs by (auto simp add: mset_le_def)
next
  assume ?rhs
  show ?lhs
  proof (rule mset_less_eqI)
    fix x
    from \<open>?rhs\<close> have "count_of (DAList.impl_of xs) x \<le> count A x"
      by (cases "x \<in> fst ` set (DAList.impl_of xs)") (auto simp add: count_of_empty)
    then show "count (Bag xs) x \<le> count A x" by (simp add: mset_le_def)
  qed
qed

lemma mset_less_eq_Bag [code]:
  "Bag xs \<le> (A :: 'a multiset) \<longleftrightarrow> (\<forall>(x, n) \<in> set (DAList.impl_of xs). n \<le> count A x)"
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

declare multiset_inter_def [code]
declare sup_multiset_def [code]
declare multiset_of.simps [code]


fun fold_impl :: "('a \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('a \<times> nat) list \<Rightarrow> 'b"
where
  "fold_impl fn e ((a,n) # ms) = (fold_impl fn ((fn a n) e) ms)"
| "fold_impl fn e [] = e"

definition fold :: "('a \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('a, nat) alist \<Rightarrow> 'b"
  where "fold f e al = fold_impl f e (DAList.impl_of al)"

hide_const (open) fold

context comp_fun_commute
begin

lemma DAList_Multiset_fold:
  assumes fn: "\<And>a n x. fn a n x = (f a ^^ n) x"
  shows "Multiset.fold f e (Bag al) = DAList_Multiset.fold fn e al"
  unfolding DAList_Multiset.fold_def
proof (induct al)
  fix ys
  let ?inv = "{xs :: ('a \<times> nat) list. (distinct \<circ> map fst) xs}"
  note cs[simp del] = count_simps
  have count[simp]: "\<And>x. count (Abs_multiset (count_of x)) = count_of x"
    by (rule Abs_multiset_inverse[OF count_of_multiset])
  assume ys: "ys \<in> ?inv"
  then show "Multiset.fold f e (Bag (Alist ys)) = fold_impl fn e (DAList.impl_of (Alist ys))"
    unfolding Bag_def unfolding Alist_inverse[OF ys]
  proof (induct ys arbitrary: e rule: list.induct)
    case Nil
    show ?case
      by (rule trans[OF arg_cong[of _ "{#}" "Multiset.fold f e", OF multiset_eqI]])
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
    def Ys \<equiv> "Abs_multiset (count_of ys)"
    have id: "Abs_multiset (count_of ((a, n) # ys)) = ((op + {# a #}) ^^ n) Ys"
      unfolding Ys_def
    proof (rule multiset_eqI, unfold count)
      fix c
      show "count_of ((a, n) # ys) c =
        count ((op + {#a#} ^^ n) (Abs_multiset (count_of ys))) c" (is "?l = ?r")
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

lift_definition single_alist_entry :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) alist" is "\<lambda>a b. [(a, b)]"
  by auto

lemma image_mset_Bag [code]:
  "image_mset f (Bag ms) =
    DAList_Multiset.fold (\<lambda>a n m. Bag (single_alist_entry (f a) n) + m) {#} ms"
  unfolding image_mset_def
proof (rule comp_fun_commute.DAList_Multiset_fold, unfold_locales, (auto simp: ac_simps)[1])
  fix a n m
  show "Bag (single_alist_entry (f a) n) + m = ((op + \<circ> single \<circ> f) a ^^ n) m" (is "?l = ?r")
  proof (rule multiset_eqI)
    fix x
    have "count ?r x = (if x = f a then n + count m x else count m x)"
      by (induct n) auto
    also have "\<dots> = count ?l x"
      by (simp add: single_alist_entry.rep_eq)
    finally show "count ?l x = count ?r x" ..
  qed
qed

hide_const single_alist_entry

(* we cannot use (\<lambda>a n. op + (a * n)) for folding, since * is not defined
   in comm_monoid_add *)
lemma msetsum_Bag[code]: "msetsum (Bag ms) = DAList_Multiset.fold (\<lambda>a n. ((op + a) ^^ n)) 0 ms"
  unfolding msetsum.eq_fold
  apply (rule comp_fun_commute.DAList_Multiset_fold)
  apply unfold_locales
  apply (auto simp: ac_simps)
  done

(* we cannot use (\<lambda>a n. op * (a ^ n)) for folding, since ^ is not defined
   in comm_monoid_mult *)
lemma msetprod_Bag[code]: "msetprod (Bag ms) = DAList_Multiset.fold (\<lambda>a n. ((op * a) ^^ n)) 1 ms"
  unfolding msetprod.eq_fold
  apply (rule comp_fun_commute.DAList_Multiset_fold)
  apply unfold_locales
  apply (auto simp: ac_simps)
  done

lemma size_fold: "size A = Multiset.fold (\<lambda>_. Suc) 0 A" (is "_ = Multiset.fold ?f _ _")
proof -
  interpret comp_fun_commute ?f by default auto
  show ?thesis by (induct A) auto
qed

lemma size_Bag[code]: "size (Bag ms) = DAList_Multiset.fold (\<lambda>a n. op + n) 0 ms"
  unfolding size_fold
proof (rule comp_fun_commute.DAList_Multiset_fold, unfold_locales, simp)
  fix a n x
  show "n + x = (Suc ^^ n) x"
    by (induct n) auto
qed


lemma set_of_fold: "set_of A = Multiset.fold insert {} A" (is "_ = Multiset.fold ?f _ _")
proof -
  interpret comp_fun_commute ?f by default auto
  show ?thesis by (induct A) auto
qed

lemma set_of_Bag[code]:
  "set_of (Bag ms) = DAList_Multiset.fold (\<lambda>a n. (if n = 0 then (\<lambda>m. m) else insert a)) {} ms"
  unfolding set_of_fold
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

