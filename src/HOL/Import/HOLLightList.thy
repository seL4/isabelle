(*  Title:      HOL/Import/HOLLightList.thy
    Author:     Cezary Kaliszyk
*)

header {* Compatibility theorems for HOL Light lists *}

theory HOLLightList
imports List
begin

lemma FINITE_SET_OF_LIST:
  "finite (set l)"
  by simp

lemma AND_ALL2:
  "(list_all2 P l m \<and> list_all2 Q l m) = list_all2 (\<lambda>x y. P x y \<and> Q x y) l m"
  by (induct l m rule: list_induct2') auto

lemma MEM_EXISTS_EL:
  "(x \<in> set l) = (\<exists>i<length l. x = l ! i)"
  by (auto simp add: in_set_conv_nth)

lemma INJECTIVE_MAP:
  "(\<forall>l m. map f l = map f m --> l = m) = (\<forall>x y. f x = f y --> x = y)"
proof (intro iffI allI impI)
  fix x y
  assume "\<forall>l m. map f l = map f m \<longrightarrow> l = m" "f x = f y"
  then show "x = y"
    by (drule_tac x="[x]" in spec) (drule_tac x="[y]" in spec, simp)
next
  fix l m
  assume a: "\<forall>x y. f x = f y \<longrightarrow> x = y"
  assume "map f l = map f m"
  then show "l = m"
    by (induct l m rule: list_induct2') (simp_all add: a)
qed

lemma SURJECTIVE_MAP:
  "(\<forall>m. EX l. map f l = m) = (\<forall>y. EX x. f x = y)"
  apply (intro iffI allI)
  apply (drule_tac x="[y]" in spec)
  apply (elim exE)
  apply (case_tac l)
  apply simp
  apply (rule_tac x="a" in exI)
  apply simp
  apply (induct_tac m)
  apply simp
  apply (drule_tac x="a" in spec)
  apply (elim exE)
  apply (rule_tac x="x # l" in exI)
  apply simp
  done

lemma LENGTH_TL:
  "l \<noteq> [] \<longrightarrow> length (tl l) = length l - 1"
  by simp

lemma DEF_APPEND:
  "op @ = (SOME APPEND. (\<forall>l. APPEND [] l = l) \<and> (\<forall>h t l. APPEND (h # t) l = h # APPEND t l))"
  apply (rule some_equality[symmetric])
  apply (auto simp add: fun_eq_iff)
  apply (induct_tac x)
  apply simp_all
  done

lemma DEF_REVERSE:
  "rev = (SOME REVERSE. REVERSE [] = [] \<and> (\<forall>l x. REVERSE (x # l) = (REVERSE l) @ [x]))"
  apply (rule some_equality[symmetric])
  apply (auto simp add: fun_eq_iff)
  apply (induct_tac x)
  apply simp_all
  done

lemma DEF_LENGTH:
  "length = (SOME LENGTH. LENGTH [] = 0 \<and> (\<forall>h t. LENGTH (h # t) = Suc (LENGTH t)))"
  apply (rule some_equality[symmetric])
  apply (auto simp add: fun_eq_iff)
  apply (induct_tac x)
  apply simp_all
  done

lemma DEF_MAP:
  "map = (SOME MAP. (\<forall>f. MAP f [] = []) \<and> (\<forall>f h t. MAP f (h # t) = f h # MAP f t))"
  apply (rule some_equality[symmetric])
  apply (auto simp add: fun_eq_iff)
  apply (induct_tac xa)
  apply simp_all
  done

lemma DEF_REPLICATE:
  "replicate =
    (SOME REPLICATE. (\<forall>x. REPLICATE 0 x = []) \<and> (\<forall>n x. REPLICATE (Suc n) x = x # REPLICATE n x))"
  apply (rule some_equality[symmetric])
  apply (auto simp add: fun_eq_iff)
  apply (induct_tac x)
  apply simp_all
  done

lemma DEF_ITLIST:
  "foldr = (SOME ITLIST. (\<forall>f b. ITLIST f [] b = b) \<and> (\<forall>h f t b. ITLIST f (h # t) b = f h (ITLIST f t b)))"
  apply (rule some_equality[symmetric])
  apply (auto simp add: fun_eq_iff)
  apply (induct_tac xa)
  apply simp_all
  done

lemma DEF_ALL2: "list_all2 =
  (SOME ALL2.
    (\<forall>P l2. ALL2 P [] l2 = (l2 = [])) \<and>
    (\<forall>h1 P t1 l2.
      ALL2 P (h1 # t1) l2 = (if l2 = [] then False else P h1 (hd l2) \<and> ALL2 P t1 (tl l2))))"
  apply (rule some_equality[symmetric])
  apply (auto)
  apply (case_tac l2, simp_all)
  apply (case_tac l2, simp_all)
  apply (case_tac l2, simp_all)
  apply (simp add: fun_eq_iff)
  apply (intro allI)
  apply (induct_tac xa xb rule: list_induct2')
  apply simp_all
  done

lemma ALL2:
 "list_all2 P [] [] = True \<and>
  list_all2 P (h1 # t1) [] = False \<and>
  list_all2 P [] (h2 # t2) = False \<and>
  list_all2 P (h1 # t1) (h2 # t2) = (P h1 h2 \<and> list_all2 P t1 t2)"
  by simp

lemma DEF_FILTER:
  "filter = (SOME FILTER. (\<forall>P. FILTER P [] = []) \<and>
     (\<forall>h P t. FILTER P (h # t) = (if P h then h # FILTER P t else FILTER P t)))"
  apply (rule some_equality[symmetric])
  apply (auto simp add: fun_eq_iff)
  apply (induct_tac xa)
  apply simp_all
  done

fun map2 where
  "map2 f [] [] = []"
| "map2 f (h1 # t1) (h2 # t2) = (f h1 h2) # (map2 f t1 t2)"

lemma MAP2:
  "map2 f [] [] = [] \<and> map2 f (h1 # t1) (h2 # t2) = f h1 h2 # map2 f t1 t2"
  by simp

fun fold2 where
  "fold2 f [] [] b = b"
| "fold2 f (h1 # t1) (h2 # t2) b = f h1 h2 (fold2 f t1 t2 b)"

lemma ITLIST2:
  "fold2 f [] [] b = b \<and> fold2 f (h1 # t1) (h2 # t2) b = f h1 h2 (fold2 f t1 t2 b)"
  by simp

definition [simp]: "list_el x xs = nth xs x"

lemma ZIP:
  "zip [] [] = [] \<and> zip (h1 # t1) (h2 # t2) = (h1, h2) # (zip t1 t2)"
  by simp

lemma LAST_CLAUSES:
  "last [h] = h \<and> last (h # k # t) = last (k # t)"
  by simp

lemma DEF_NULL:
  "List.null = (SOME NULL. NULL [] = True \<and> (\<forall>h t. NULL (h # t) = False))"
  apply (rule some_equality[symmetric])
  apply (auto simp add: fun_eq_iff null_def)
  apply (case_tac x)
  apply simp_all
  done

lemma DEF_ALL:
  "list_all = (SOME u. (\<forall>P. u P [] = True) \<and> (\<forall>h P t. u P (h # t) = (P h \<and> u P t)))"
  apply (rule some_equality[symmetric])
  apply auto[1]
  apply (simp add: fun_eq_iff)
  apply (intro allI)
  apply (induct_tac xa)
  apply simp_all
  done

lemma MAP_EQ:
  "list_all (\<lambda>x. f x = g x) l \<longrightarrow> map f l = map g l"
  by (induct l) auto

definition [simp]: "list_mem x xs = List.member xs x"

lemma DEF_MEM:
  "list_mem = (SOME MEM. (\<forall>x. MEM x [] = False) \<and> (\<forall>h x t. MEM x (h # t) = (x = h \<or> MEM x t)))"
  apply (rule some_equality[symmetric])
  apply (auto simp add: member_def)[1]
  apply (simp add: fun_eq_iff)
  apply (intro allI)
  apply (induct_tac xa)
  apply (simp_all add: member_def)
  done

lemma DEF_EX:
  "list_ex = (SOME u. (\<forall>P. u P [] = False) \<and> (\<forall>h P t. u P (h # t) = (P h \<or> u P t)))"
  apply (rule some_equality[symmetric])
  apply (auto)
  apply (simp add: fun_eq_iff)
  apply (intro allI)
  apply (induct_tac xa)
  apply (simp_all)
  done

lemma ALL_IMP:
  "(\<forall>x. x \<in> set l \<and> P x \<longrightarrow> Q x) \<and> list_all P l \<longrightarrow> list_all Q l"
  by (simp add: list_all_iff)

lemma NOT_EX: "(\<not> list_ex P l) = list_all (\<lambda>x. \<not> P x) l"
  by (simp add: list_all_iff list_ex_iff)

lemma NOT_ALL: "(\<not> list_all P l) = list_ex (\<lambda>x. \<not> P x) l"
  by (simp add: list_all_iff list_ex_iff)

lemma ALL_MAP: "list_all P (map f l) = list_all (P o f) l"
  by (simp add: list_all_iff)

lemma ALL_T: "list_all (\<lambda>x. True) l"
  by (simp add: list_all_iff)

lemma MAP_EQ_ALL2: "list_all2 (\<lambda>x y. f x = f y) l m \<longrightarrow> map f l = map f m"
  by (induct l m rule: list_induct2') simp_all

lemma ALL2_MAP: "list_all2 P (map f l) l = list_all (\<lambda>a. P (f a) a) l"
  by (induct l) simp_all

lemma MAP_EQ_DEGEN: "list_all (\<lambda>x. f x = x) l --> map f l = l"
  by (induct l) simp_all

lemma ALL2_AND_RIGHT:
   "list_all2 (\<lambda>x y. P x \<and> Q x y) l m = (list_all P l \<and> list_all2 Q l m)"
  by (induct l m rule: list_induct2') auto

lemma ITLIST_EXTRA:
  "foldr f (l @ [a]) b = foldr f l (f a b)"
  by simp

lemma ALL_MP:
  "list_all (\<lambda>x. P x \<longrightarrow> Q x) l \<and> list_all P l \<longrightarrow> list_all Q l"
  by (simp add: list_all_iff)

lemma AND_ALL:
  "(list_all P l \<and> list_all Q l) = list_all (\<lambda>x. P x \<and> Q x) l"
  by (auto simp add: list_all_iff)

lemma EX_IMP:
  "(\<forall>x. x\<in>set l \<and> P x \<longrightarrow> Q x) \<and> list_ex P l \<longrightarrow> list_ex Q l"
  by (auto simp add: list_ex_iff)

lemma ALL_MEM:
  "(\<forall>x. x\<in>set l \<longrightarrow> P x) = list_all P l"
  by (auto simp add: list_all_iff)

lemma EX_MAP:
  "ALL P f l. list_ex P (map f l) = list_ex (P o f) l"
  by (simp add: list_ex_iff)

lemma EXISTS_EX:
  "\<forall>P l. (EX x. list_ex (P x) l) = list_ex (\<lambda>s. EX x. P x s) l"
  by (auto simp add: list_ex_iff)

lemma FORALL_ALL:
  "\<forall>P l. (\<forall>x. list_all (P x) l) = list_all (\<lambda>s. \<forall>x. P x s) l"
  by (auto simp add: list_all_iff)

lemma MEM_APPEND: "\<forall>x l1 l2. (x\<in>set (l1 @ l2)) = (x\<in>set l1 \<or> x\<in>set l2)"
  by simp

lemma MEM_MAP: "\<forall>f y l. (y\<in>set (map f l)) = (EX x. x\<in>set l \<and> y = f x)"
  by auto

lemma MEM_FILTER: "\<forall>P l x. (x\<in>set (filter P l)) = (P x \<and> x\<in>set l)"
  by auto

lemma EX_MEM: "(EX x. P x \<and> x\<in>set l) = list_ex P l"
  by (auto simp add: list_ex_iff)

lemma ALL2_MAP2:
  "list_all2 P (map f l) (map g m) = list_all2 (\<lambda>x y. P (f x) (g y)) l m"
  by (simp add: list_all2_map1 list_all2_map2)

lemma ALL2_ALL:
  "list_all2 P l l = list_all (\<lambda>x. P x x) l"
  by (induct l) simp_all

lemma LENGTH_MAP2:
  "length l = length m \<longrightarrow> length (map2 f l m) = length m"
  by (induct l m rule: list_induct2') simp_all

lemma DEF_set_of_list:
  "set = (SOME sol. sol [] = {} \<and> (\<forall>h t. sol (h # t) = insert h (sol t)))"
  apply (rule some_equality[symmetric])
  apply (simp_all)
  apply (rule ext)
  apply (induct_tac x)
  apply simp_all
  done

lemma IN_SET_OF_LIST:
  "(x : set l) = (x : set l)"
  by simp

lemma DEF_BUTLAST:
  "butlast = (SOME B. B [] = [] \<and> (\<forall>h t. B (h # t) = (if t = [] then [] else h # B t)))"
  apply (rule some_equality[symmetric])
  apply auto
  apply (rule ext)
  apply (induct_tac x)
  apply auto
  done

lemma MONO_ALL:
  "(ALL x. P x \<longrightarrow> Q x) \<longrightarrow> list_all P l \<longrightarrow> list_all Q l"
  by (simp add: list_all_iff)

lemma EL_TL: "l \<noteq> [] \<Longrightarrow> tl l ! x = l ! (x + 1)"
  by (induct l) (simp_all)

(* Assume the same behaviour outside of the usual domain.
   For HD, LAST, EL it follows from "undefined = SOME _. False".

   The definitions of TL and ZIP are different for empty lists.
 *)
axiomatization where
  DEF_HD: "hd = (SOME HD. \<forall>t h. HD (h # t) = h)"

axiomatization where
  DEF_LAST: "last =
    (SOME LAST. \<forall>h t. LAST (h # t) = (if t = [] then h else LAST t))"

axiomatization where
  DEF_EL: "list_el =
    (SOME EL. (\<forall>l. EL 0 l = hd l) \<and> (\<forall>n l. EL (Suc n) l = EL n (tl l)))"

end
