(*  Title:      HOL/Alethe_Rare_Nary_Ops.thy
    Author:     Hanna Lachnitt, Stanford University
*)
theory Alethe_Rare_Nary_Ops
  imports HOL.List
begin

datatype 'a cvc_ListVar = ListVar "'a list"
datatype ('a,'b) cvc_ListOp = ListOp "'a \<Rightarrow> 'b \<Rightarrow> 'b" "'a"

fun cvc_isListOp where
 "cvc_isListOp (ListOp op neutralElement) =
 ((\<forall>x. op x neutralElement = x) \<and> (\<forall>x. op neutralElement x = x))"

(*

Standard operators. If operator is not part of those the user has to add a custom lemma here by
explicitly stating the neutral element of their operation
There are some operators which have no neutral element, e.g, and on bitvectors. In that case an
additional assumption should be added to the lemma making sure that not all operands can be empty
at the same time and a lemma should be proven below with the same assumption.

*)

named_theorems cvc_ListOp_neutral \<open>neutral elements for cvc_ListOps\<close>

lemma [cvc_ListOp_neutral]:
  shows cvc_ListOp_neutral_and: "cvc_isListOp (ListOp (\<and>) True)"
  and cvc_ListOp_neutral_or: "cvc_isListOp (ListOp (\<or>) False)"
  and cvc_ListOp_neutral_plus: "cvc_isListOp (ListOp (+) (0::'a::monoid_add))"
  and cvc_ListOp_neutral_plus_int: "cvc_isListOp (ListOp (+) (0::int))"
  and cvc_ListOp_neutral_mult: "cvc_isListOp (ListOp (*) (1::int))"
  and cvc_ListOp_neutral_append: "cvc_isListOp (ListOp (@) [])"
  by (simp_all)

(*Since the SMT-LIB term parser in Isabelle parses all operators as right-associative we assume
that this is the case. Further testing is needed to see if this is enough. *)

fun cvc_nary_op_fold :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a" where
 cvc_nary_op_fold_Nil: "cvc_nary_op_fold op [x] = x" |
 cvc_nary_op_fold_Cons: "cvc_nary_op_fold op (x#xs) = (op x (cvc_nary_op_fold op xs))"

fun cvc_bin_op_fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
 cvc_bin_op_fold_Nil: "cvc_bin_op_fold op [] y = y" |
 cvc_bin_op_fold_Cons: "cvc_bin_op_fold op (x#xs) y = (op x (cvc_bin_op_fold op xs y))"

(*
definitions instead of functions are used to make sure unfolding can be done precisely.
*)

(*For cvc_list_left and cvc_list_right we always know that we'll have at least one element*)
fun cvc_bin_op :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a cvc_ListVar \<Rightarrow> 'b \<Rightarrow> 'b" where
 "cvc_bin_op op (ListVar xs) y = cvc_bin_op_fold op xs y"
definition cvc_list_left where "cvc_list_left op lv y = cvc_bin_op op lv y"

fun cvc_bin_op2 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a cvc_ListVar \<Rightarrow> 'a" where
 "cvc_bin_op2 op y (ListVar xs) = (if xs = [] then y else op y (cvc_nary_op_fold op xs))"
definition cvc_list_right where "cvc_list_right op y lv = cvc_bin_op2 op y lv"

(*
If both arguments are lists that is not always the case. If there is a neutral element
we can use that. In the cvc5 proof certificate itself that case should not appear.
However, if we'd put that restriction into the Isabelle lemma it would be necessary to prove
it each time a rewrite step of that rule is reconstructed.

If there is no constant neutral element the restriction should be added and cvc_list_both' should be used.
Examples are bvxor and bvconcat.
*)
fun cvc_bin_op3 where
  "cvc_bin_op3 op (ListVar []) (ListVar []) neutral = neutral" |
  "cvc_bin_op3 op (ListVar xs) (ListVar []) neutral = cvc_nary_op_fold op xs" |
  "cvc_bin_op3 op (ListVar xs) (ListVar ys) neutral = cvc_bin_op_fold op xs (cvc_nary_op_fold op ys)"
definition cvc_list_both where "cvc_list_both op neutral lv1 lv2 = cvc_bin_op3 op lv1 lv2 neutral"

fun cvc_bin_op3' where
  "cvc_bin_op3' op (ListVar xs) (ListVar []) = cvc_nary_op_fold op xs" |
  "cvc_bin_op3' op (ListVar xs) (ListVar ys) = cvc_bin_op_fold op xs (cvc_nary_op_fold op ys)"
definition cvc_list_both' where "cvc_list_both' op lv1 lv2 = cvc_bin_op3' op lv1 lv2"

(*Pairwise*)

(*
Similar to chainable operators, a pairwise operator applied to a single argument reduces to the
neutral element of the combining operator.
E.g., (distinct x) --> True
E.g., (distinct x y z) --> (and (distinct x y) (distinct x z) (distinct y z))

TODO: This is not finished yet.
*)

fun cvc_pairwise_op :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a cvc_ListVar \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> bool" where
 "cvc_pairwise_op op (ListVar []) y neutral = neutral" |
 "cvc_pairwise_op op (ListVar [x]) y neutral = (op x y)" |
 "cvc_pairwise_op op (ListVar (x#xs)) y neutral = ((op x y) \<and> cvc_pairwise_op op (ListVar xs) y neutral)"
definition cvc_pairwise_list_left where "cvc_pairwise_list_left op lv y = cvc_pairwise_op op lv y"

fun cvc_pairwise_op2 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a cvc_ListVar \<Rightarrow> bool \<Rightarrow> bool" where
 "cvc_pairwise_op2 op x (ListVar []) neutral = neutral" |
 "cvc_pairwise_op2 op x (ListVar [y]) neutral = (op x y)" |
 "cvc_pairwise_op2 op x (ListVar (y#ys)) neutral = ((op x y) \<and> cvc_pairwise_op op (ListVar ys) y neutral)"
definition cvc_pairwise_list_right where "cvc_pairwise_list_right op lv y = cvc_pairwise_op2 op lv y"

fun cvc_pairwise_fold :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
 cvc_pairwise_fold_Nil: "cvc_pairwise_fold op x [] = True" |
 cvc_pairwise_fold_Cons: "cvc_pairwise_fold op x (y#ys) = ((op x y) \<and> (cvc_pairwise_fold op x ys))"

fun cvc_pairwise_fold2 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
 cvc_pairwise_fold2_Nil: "cvc_pairwise_fold2 op [] = True" |
 cvc_pairwise_fold2_Cons: "cvc_pairwise_fold2 op (x#xs) = (cvc_pairwise_fold op x xs \<and> cvc_pairwise_fold2 op xs)"

lemma cvc_nary_op_fold_transfer_h1:
  assumes "1 \<le> n" "cvc_isListOp (ListOp op neutral)"
  shows "\<forall>xs. n = length xs \<longrightarrow> cvc_nary_op_fold op xs = foldr op xs neutral"
  apply (induct_tac rule: nat_induct_at_least[of 1])
  subgoal
    using assms(1) by simp
  subgoal
    proof(rule allI,rule impI)
    fix xs::"'a list"
    assume a0: "1 = length xs"
    obtain x where t0: "[x] = xs"
      by (metis One_nat_def Suc_length_conv a0 length_0_conv)
    have "cvc_nary_op_fold op xs = x"
      using t0 cvc_nary_op_fold_Nil by force
    moreover have "foldr op xs neutral = (op x neutral)"
      using t0 by force
    ultimately show "cvc_nary_op_fold op xs = foldr op xs neutral"
      using assms(2) by auto
  qed
  subgoal for n
  proof(rule allI, rule impI)
    fix xs::"'a list"
    assume a0: "1 \<le> n"
    assume a1: "\<forall>xs. n = length xs \<longrightarrow> cvc_nary_op_fold op xs = foldr op xs neutral"
    assume a2: "Suc n = length xs"
    then obtain x xss where t0: "xs = x#xss"
      by (meson Suc_length_conv)
    show "cvc_nary_op_fold op xs = foldr op xs neutral"
    proof(cases "xss = []")
      assume a00: "xss = []"
      then show "cvc_nary_op_fold op xs = foldr op xs neutral"
        using a0 a00 a2 t0 by auto
    next
      assume a01: "xss \<noteq> []"
      then have "cvc_nary_op_fold op xs = op x (cvc_nary_op_fold op xss)"
        using cvc_nary_op_fold.elims(1) t0
        by (metis list.inject list.simps(3))
      then have "cvc_nary_op_fold op xs = op x (foldr op xss neutral)"
        using a1 a2 t0 by fastforce
      then show "cvc_nary_op_fold op xs = (foldr op xs neutral)"
        by (simp add: t0)
    qed
  qed
done

lemma cvc_nary_op_fold_transfer:
  assumes "1 \<le> length xs" "cvc_isListOp (ListOp op neutral)"
  shows "cvc_nary_op_fold op xs = foldr op xs neutral"
  by (meson assms(1) assms(2) cvc_nary_op_fold_transfer_h1)

lemma cvc_bin_op_fold_transfer: "cvc_bin_op_fold op xs y = foldr op xs y"
  apply (induction xs)
  by auto

(*Left Transfer*)

lemma cvc_list_left_transfer:
  shows "cvc_list_left op (ListVar xs) y = foldr op xs y"
  by (simp add: cvc_list_left_def cvc_bin_op_fold_transfer)

(*Right Transfer*)

lemma cvc_list_right_transfer_neutral1:
  assumes "cvc_isListOp (ListOp op neutral)"
  shows "cvc_list_right op y (ListVar xs) = op y (foldr op xs neutral)"
  using assms
  unfolding cvc_list_right_def
  apply (cases xs)
  by (simp_all add: cvc_nary_op_fold_transfer)

lemma cvc_list_right_transfer_neutral2:
  assumes "cvc_isListOp (ListOp op neutral)"
  shows "cvc_list_right op y (ListVar xs) = (foldr op (y#xs) neutral)"
  using assms
  unfolding cvc_list_right_def
  apply (cases xs)
  by (simp_all add: cvc_nary_op_fold_transfer)

lemma cvc_list_right_transfer:
  "cvc_list_right op y (ListVar (xs @ [xn])) = op y (foldr op xs xn)"
  apply (induction xs arbitrary: y)
  unfolding cvc_list_right_def
  apply simp
  subgoal for x1 xss yshows
    apply (cases xss)
    by simp_all
  done

lemma cvc_list_right_transfer_2:
  assumes "xs \<noteq> []"
  shows "cvc_list_right op y (ListVar xs) = (foldr op (y # butlast xs) (last xs))"
  apply (cases "rev xs")
  using assms apply force
  by (simp add: cvc_list_right_transfer)

(*TODO: Hopefully these can be safely deleted after testing is complete*)
named_theorems cvc_list_right_transfer_op \<open>cvc_list_right_transfer instantiated with operator\<close>

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (\<and>) y (ListVar xs) = (\<and>) y (foldr (\<and>) xs True)"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (\<or>) y (ListVar xs) = (\<or>) y (foldr (\<or>) xs False)"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (+) y (ListVar xs) = (+) y (foldr (+) xs (0::int))"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (+) y (ListVar xs) = (+) y (foldr (+) xs (0::'a::monoid_add))"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (*) y (ListVar xs) = (*) y (foldr (*) xs (1::int))"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (*) y (ListVar xs) = (*) y (foldr (*) xs (1::'a::monoid_mult))"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (@) y (ListVar xs) = (@) y (foldr (@) xs [])"
  by (simp add: cvc_list_right_transfer_neutral1)

(*Both Transfer*)

lemma cvc_list_both_transfer:
  assumes "cvc_isListOp (ListOp op neutral)"
  shows "cvc_list_both op neutral (ListVar ys) (ListVar xs) = foldr op ys (foldr op xs neutral)"
  using assms
  unfolding cvc_list_both_def
  apply(cases \<open>(op,(ListVar ys),(ListVar xs),neutral)\<close> rule: cvc_bin_op3.cases)
  by (simp_all add: cvc_bin_op_fold_transfer cvc_nary_op_fold_transfer)

lemma cvc_list_both_transfer':
  assumes "xs \<noteq> []" "ys \<noteq> []"
  shows "cvc_list_both' op (ListVar ys) (ListVar xs) = foldr op ys (foldr op (butlast xs) (last xs))"
  apply (cases xs)
  apply (case_tac[!] ys)
  apply simp_all
  using assms
  unfolding cvc_list_both'_def
     apply simp_all
  subgoal for x xss y yss
  apply (induction yss)
     apply simp_all
     apply (metis append_butlast_last_id assms(1) cvc_bin_op2.simps cvc_list_right_def cvc_list_right_transfer cvc_nary_op_fold.elims list.inject)
    by (metis cvc_nary_op_fold_Cons cvc_bin_op2.simps cvc_bin_op_fold_transfer cvc_list_right_def cvc_list_right_transfer list.exhaust snoc_eq_iff_butlast)
  done

(*TODO: Hopefully these can be safely deleted after testing is complete*)

named_theorems cvc_list_both_transfer_op \<open>cvc_list_both_transfer instantiated with operator\<close>

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (\<and>) True (ListVar ys) (ListVar xs) = foldr (\<and>) ys (foldr (\<and>) xs True)"
  by (simp add: cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (\<or>) False (ListVar ys) (ListVar xs) = foldr (\<or>) ys (foldr (\<or>) xs False)"
  by (simp add: cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (+) (0::'a::{linordered_field}) (ListVar ys) (ListVar xs) = foldr (+) ys (foldr (+) xs 0)"
  by (simp add: cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (*) (1::'a::{linordered_field}) (ListVar ys) (ListVar xs) = foldr (*) ys (foldr (*) xs 1)"
  by (simp add: cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (+) (0::int) (ListVar ys) (ListVar xs) = foldr (+) ys (foldr (+) xs 0)"
  by (simp add: cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (*) (1::int) (ListVar ys) (ListVar xs) = foldr (*) ys (foldr (*) xs 1)"
  by (simp add: cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (@) [] (ListVar ys) (ListVar xs) = foldr (@) ys (foldr (@) xs [])"
  by (simp add: cvc_list_both_transfer)

lemma cvc_list_left_Nil: "cvc_list_left op (ListVar []) y = y"
  unfolding cvc_list_left_def
  by simp

lemma cvc_list_right_Nil: "cvc_list_right op y (ListVar []) = y"
  unfolding cvc_list_right_def
  by simp

(*Note that: "cvc_list_both (\<and>) (ListVar []) (ListVar []) = y" is forbidden and should be ruled out
by parsing*)
lemma cvc_list_both_Singleton: "cvc_list_both op neutral (ListVar [x]) (ListVar []) = x"
                     "cvc_list_both op neutral (ListVar []) (ListVar [x]) = x"
  unfolding cvc_list_both_def
  by auto

lemma cvc_list_left_Cons: "cvc_list_left op (ListVar (x#xs)) y
    = op x (cvc_list_left op (ListVar xs) y)"
  unfolding cvc_list_left_def
  apply (induction xs)
  by auto

lemma cvc_list_right_Cons: "cvc_list_right op y (ListVar (x#xs))
       = op y (cvc_list_right op x (ListVar xs))"
  unfolding cvc_list_right_def
  apply (induction xs)
  by auto

lemma cvc_list_both_Cons_0: "cvc_list_both op neutral (ListVar (x#xs)) (ListVar [])
       = cvc_list_right op x (ListVar xs)"
  by (metis cvc_nary_op_fold_Cons cvc_nary_op_fold_Nil cvc_bin_op2.simps cvc_bin_op3.simps(2) cvc_list_both_def cvc_list_right_def list.exhaust)

lemma cvc_list_both_Cons_1: "cvc_list_both op neutral (ListVar []) (ListVar (y#ys))
       = cvc_list_right op y (ListVar ys)"
  by (metis cvc_bin_op_fold_Nil cvc_bin_op3.simps(2) cvc_bin_op3.simps(4) cvc_list_both_Cons_0 cvc_list_both_def)

lemma cvc_list_both_Cons: "cvc_list_both op neutral (ListVar (x#xs)) (ListVar (y#ys))
       = op x (cvc_list_both op neutral (ListVar xs) (ListVar (y#ys)))"
  unfolding cvc_list_both_def
  apply (induction xs)
  by auto

(*Tests*)

lemma bool_and_flatten_test_help:
  shows "foldr (\<and>) xss ((b \<and> foldr (\<and>) yss True) \<and> foldr (\<and>) zss True) = foldr (\<and>) xss (foldr (\<and>) zss (b \<and> foldr (\<and>) yss True))"
  apply (induction xss)
   apply simp_all
   apply (induct_tac[!] yss)
   apply simp_all
   apply (induct_tac[!] zss)
     apply simp_all
  apply blast
  by blast

lemma bool_and_flatten_test:
  fixes xs ys zs :: "bool cvc_ListVar"
  shows "(cvc_list_left (\<and>) xs (cvc_list_right (\<and>) (cvc_list_right (\<and>) b ys) zs))
 = (cvc_list_left (\<and>) xs (cvc_list_left (\<and>) zs (cvc_list_right (\<and>) b ys)))"
  apply (cases xs)
  apply (cases ys)
  apply (cases zs)
  subgoal for xss yss zss
    apply simp
    unfolding cvc_list_left_transfer
    unfolding cvc_list_right_transfer_op
    using bool_and_flatten_test_help by auto
  done

lemma bool_and_flatten_test_reconstruction: "a \<and> (c \<and> (b \<and> d)) \<longrightarrow> (a \<and> (c \<and> (b \<and> d)))"
  using bool_and_flatten_test[of "ListVar [a,c]" b "ListVar [d]" "ListVar []"]
  unfolding cvc_list_right_Nil cvc_list_left_Nil
  unfolding cvc_list_right_Cons cvc_list_left_Cons
  unfolding cvc_list_right_Nil cvc_list_left_Nil
  by simp

lemma foldr_or_neutral [simp]: "foldr (\<or>) xs True = True"
  apply (induction xs)
  by auto

lemma foldr_and_neutral [simp]: "foldr (\<and>) xs False = False"
  apply (induction xs)
  by auto

lemmas cvc_rewrites_fold = append.right_neutral append_Nil
 append.assoc append.right_neutral fold_append_concat_rev foldr_conv_fold
 append_eq_append_conv concat_append append.left_neutral append_Nil2

end
