(*  Title:      HOL/Import/HOL_Light_Maps.thy
    Author:     Cezary Kaliszyk, University of Innsbruck
    Author:     Alexander Krauss, QAware GmbH

Based on earlier code by Steven Obua and Sebastian Skalberg
*)

header {* Type and constant mappings of HOL Light importer *}

theory HOL_Light_Maps
imports Import_Setup
begin

lemma [import_const T]:
  "True = ((\<lambda>p :: bool. p) = (\<lambda>p. p))"
  by simp

lemma [import_const "/\\"]:
  "(op \<and>) = (\<lambda>p q. (\<lambda>f. f p q \<Colon> bool) = (\<lambda>f. f True True))"
  by metis

lemma [import_const "==>"]:
  "(op \<longrightarrow>) = (\<lambda>(p\<Colon>bool) q\<Colon>bool. (p \<and> q) = p)"
  by auto

lemma [import_const "!"]:
  "All = (\<lambda>P\<Colon>'A \<Rightarrow> bool. P = (\<lambda>x\<Colon>'A. True))"
  by auto

lemma [import_const "?"]:
  "Ex = (\<lambda>P\<Colon>'A \<Rightarrow> bool. All (\<lambda>q\<Colon>bool. (All (\<lambda>x\<Colon>'A\<Colon>type. (P x) \<longrightarrow> q)) \<longrightarrow> q))"
  by auto

lemma [import_const "\\/"]:
  "(op \<or>) = (\<lambda>p q. \<forall>r. (p \<longrightarrow> r) \<longrightarrow> (q \<longrightarrow> r) \<longrightarrow> r)"
  by auto

lemma [import_const F]:
  "False = (\<forall>p. p)"
  by auto

lemma [import_const "~"]:
  "Not = (\<lambda>p. p \<longrightarrow> False)"
  by simp

lemma [import_const "?!"]:
  "Ex1 = (\<lambda>P\<Colon>'A \<Rightarrow> bool. Ex P \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> x = y))"
  by auto

lemma [import_const "_FALSITY_"]: "False = False"
  by simp

lemma hl_ax1: "\<forall>t\<Colon>'A \<Rightarrow> 'B. (\<lambda>x. t x) = t"
  by metis

lemma hl_ax2: "\<forall>P x\<Colon>'A. P x \<longrightarrow> P (Eps P)"
  by (auto intro: someI)

lemma [import_const COND]:
  "If = (\<lambda>t (t1 :: 'A) t2. SOME x. (t = True \<longrightarrow> x = t1) \<and> (t = False \<longrightarrow> x = t2))"
  unfolding fun_eq_iff by auto

lemma [import_const o]:
  "(op \<circ>) = (\<lambda>(f\<Colon>'B \<Rightarrow> 'C) g x\<Colon>'A. f (g x))"
  unfolding fun_eq_iff by simp

lemma [import_const I]: "id = (\<lambda>x\<Colon>'A. x)"
  by auto

lemma [import_type 1 one_ABS one_REP]:
  "type_definition Rep_unit Abs_unit (Collect (\<lambda>b. b))"
  by (metis (full_types) Collect_cong singleton_conv2 type_definition_unit)

lemma [import_const one]: "() = (SOME x\<Colon>unit. True)"
  by auto

lemma [import_const mk_pair]:
  "Pair_Rep = (\<lambda>(x\<Colon>'A) (y\<Colon>'B) (a\<Colon>'A) b\<Colon>'B. a = x \<and> b = y)"
  by (simp add: Pair_Rep_def fun_eq_iff)

lemma [import_type prod ABS_prod REP_prod]:
  "type_definition Rep_prod Abs_prod (Collect (\<lambda>x\<Colon>'A \<Rightarrow> 'B \<Rightarrow> bool. \<exists>a b. x = Pair_Rep a b))"
  using type_definition_prod[unfolded Product_Type.prod_def] by simp

lemma [import_const ","]: "Pair = (\<lambda>(x\<Colon>'A) y\<Colon>'B. Abs_prod (Pair_Rep x y))"
  by (metis Pair_def)

lemma [import_const FST]:
  "fst = (\<lambda>p\<Colon>'A \<times> 'B. SOME x\<Colon>'A. \<exists>y\<Colon>'B. p = (x, y))"
  by auto

lemma [import_const SND]:
  "snd = (\<lambda>p\<Colon>'A \<times> 'B. SOME y\<Colon>'B. \<exists>x\<Colon>'A. p = (x, y))"
  by auto

(*lemma [import_const CURRY]:
  "curry = (\<lambda>(f\<Colon>'A \<times> 'B \<Rightarrow> 'C) x y. f (x, y))"
  using curry_def .*)

lemma [import_const ONE_ONE : Fun.inj]:
  "inj = (\<lambda>(f\<Colon>'A \<Rightarrow> 'B). \<forall>x1 x2. f x1 = f x2 \<longrightarrow> x1 = x2)"
  by (auto simp add: fun_eq_iff inj_on_def)

lemma [import_const ONTO : Fun.surj]:
  "surj = (\<lambda>(f\<Colon>'A \<Rightarrow> 'B). \<forall>y. \<exists>x. y = f x)"
  by (auto simp add: fun_eq_iff)

lemma hl_ax3: "\<exists>f\<Colon>ind \<Rightarrow> ind. inj f \<and> \<not> surj f"
  by (rule_tac x="Suc_Rep" in exI)
     (metis Suc_Rep_inject' injI Suc_Rep_not_Zero_Rep surjD)

import_type_map num : Nat.nat
import_const_map "_0" : Groups.zero_class.zero
import_const_map SUC : Nat.Suc

lemma NOT_SUC: "\<forall>n. Suc n \<noteq> 0"
  by simp

lemma SUC_INJ: "\<forall>m n. (Suc m = Suc n) = (m = n)"
  by simp

lemma num_INDUCTION:
  "\<forall>P. P 0 \<and> (\<forall>n. P n \<longrightarrow> P (Suc n)) \<longrightarrow> (\<forall>n. P n)"
  by (auto intro: nat.induct)

lemma [import_const NUMERAL]: "id = (\<lambda>x :: nat. x)"
  by auto

definition [simp]: "bit0 n = 2 * n"

lemma [import_const BIT0]:
  "bit0 = (SOME fn. fn (id 0) = id 0 \<and> (\<forall>n. fn (Suc n) = Suc (Suc (fn n))))"
  apply (auto intro!: some_equality[symmetric])
  apply (auto simp add: fun_eq_iff)
  apply (induct_tac x)
  apply auto
  done

definition [import_const BIT1, simp]:
  "bit1 = (\<lambda>x. Suc (bit0 x))"

definition [simp]: "pred n = n - 1"

lemma PRE[import_const PRE : HOL_Light_Maps.pred]:
  "pred (id (0\<Colon>nat)) = id (0\<Colon>nat) \<and> (\<forall>n\<Colon>nat. pred (Suc n) = n)"
  by simp

lemma ADD[import_const "+" : Groups.plus_class.plus]:
  "(\<forall>n :: nat. (id 0) + n = n) \<and> (\<forall>m n. (Suc m) + n = Suc (m + n))"
  by simp

lemma MULT[import_const "*" : Groups.times_class.times]:
  "(\<forall>n :: nat. (id 0) * n = id 0) \<and> (\<forall>m n. (Suc m) * n = (m * n) + n)"
  by simp

lemma EXP[import_const EXP : Power.power_class.power]:
  "(\<forall>m. m ^ (id 0) = id (bit1 0)) \<and> (\<forall>(m :: nat) n. m ^ (Suc n) = m * (m ^ n))"
  by simp

lemma LE[import_const "<=" : Orderings.ord_class.less_eq]:
  "(\<forall>m :: nat. m \<le> (id 0) = (m = id 0)) \<and> (\<forall>m n. m \<le> (Suc n) = (m = Suc n \<or> m \<le> n))"
  by auto

lemma LT[import_const "<" : Orderings.ord_class.less]:
  "(\<forall>m :: nat. m < (id 0) = False) \<and> (\<forall>m n. m < (Suc n) = (m = n \<or> m < n))"
  by auto

lemma DEF_GE[import_const ">=" : "Orderings.ord_class.greater_eq"]:
  "(op \<ge>) = (\<lambda>x y :: nat. y \<le> x)"
  by simp

lemma DEF_GT[import_const ">" : "Orderings.ord_class.greater"]:
  "(op >) = (\<lambda>x y :: nat. y < x)"
  by simp

lemma DEF_MAX[import_const "MAX"]:
  "max = (\<lambda>x y :: nat. if x \<le> y then y else x)"
  by (auto simp add: min_max.le_iff_sup fun_eq_iff)

lemma DEF_MIN[import_const "MIN"]:
  "min = (\<lambda>x y :: nat. if x \<le> y then x else y)"
  by (auto simp add: min_max.le_iff_inf fun_eq_iff)

lemma EVEN[import_const "EVEN" : "Parity.even_odd_class.even"]:
  "even (id 0\<Colon>nat) = True \<and> (\<forall>n. even (Suc n) = (\<not> even n))"
  by simp

lemma SUB[import_const "-" : "Groups.minus_class.minus"]:
  "(\<forall>m\<Colon>nat. m - (id 0) = m) \<and> (\<forall>m n. m - (Suc n) = pred (m - n))"
  by simp

lemma FACT[import_const "FACT" : "Fact.fact_class.fact"]:
  "fact (id 0) = id (bit1 0) \<and> (\<forall>n. fact (Suc n) = Suc n * fact n)"
  by simp

import_const_map MOD : Divides.div_class.mod
import_const_map DIV : Divides.div_class.div

lemma DIVISION_0:
  "\<forall>m n\<Colon>nat. if n = id 0 then m div n = id 0 \<and> m mod n = m else m = m div n * n + m mod n \<and> m mod n < n"
  by simp

lemmas [import_type sum "_dest_sum" "_mk_sum"] = type_definition_sum
import_const_map INL : Sum_Type.Inl
import_const_map INR : Sum_Type.Inr

lemma sum_INDUCT:
  "\<forall>P. (\<forall>a. P (Inl a)) \<and> (\<forall>a. P (Inr a)) \<longrightarrow> (\<forall>x. P x)"
  by (auto intro: sum.induct)

lemma sum_RECURSION:
  "\<forall>Inl' Inr'. \<exists>fn. (\<forall>a. fn (Inl a) = Inl' a) \<and> (\<forall>a. fn (Inr a) = Inr' a)"
  by (intro allI, rule_tac x="sum_case Inl' Inr'" in exI) auto

lemma OUTL[import_const "OUTL" : "Sum_Type.Projl"]:
  "Sum_Type.Projl (Inl x) = x"
  by simp

lemma OUTR[import_const "OUTR" : "Sum_Type.Projr"]:
  "Sum_Type.Projr (Inr y) = y"
  by simp

import_type_map list : List.list
import_const_map NIL : List.list.Nil
import_const_map CONS : List.list.Cons

lemma list_INDUCT:
  "\<forall>P\<Colon>'A list \<Rightarrow> bool. P [] \<and> (\<forall>a0 a1. P a1 \<longrightarrow> P (a0 # a1)) \<longrightarrow> (\<forall>x. P x)"
  using list.induct by auto

lemma list_RECURSION:
 "\<forall>nil' cons'. \<exists>fn\<Colon>'A list \<Rightarrow> 'Z. fn [] = nil' \<and> (\<forall>(a0\<Colon>'A) a1\<Colon>'A list. fn (a0 # a1) = cons' a0 a1 (fn a1))"
  by (intro allI, rule_tac x="list_rec nil' cons'" in exI) auto

lemma HD[import_const HD : List.hd]:
  "hd ((h\<Colon>'A) # t) = h"
  by simp

lemma TL[import_const TL : List.tl]:
  "tl ((h\<Colon>'A) # t) = t"
  by simp

lemma APPEND[import_const APPEND : List.append]:
  "(\<forall>l\<Colon>'A list. [] @ l = l) \<and> (\<forall>(h\<Colon>'A) t l. (h # t) @ l = h # t @ l)"
  by simp

lemma REVERSE[import_const REVERSE : List.rev]:
  "rev [] = ([] :: 'A list) \<and> rev ((x\<Colon>'A) # l) = rev l @ [x]"
  by simp

lemma LENGTH[import_const LENGTH : List.length]:
  "length [] = id 0 \<and> (\<forall>(h\<Colon>'A) t. length (h # t) = Suc (length t))"
  by simp

lemma MAP[import_const MAP : List.map]:
  "(\<forall>f\<Colon>'A \<Rightarrow> 'B. map f [] = []) \<and>
       (\<forall>(f\<Colon>'A \<Rightarrow> 'B) h t. map f (h # t) = f h # map f t)"
  by simp

lemma LAST[import_const LAST : List.last]:
  "last ((h\<Colon>'A) # t) = (if t = [] then h else last t)"
  by simp

lemma BUTLAST[import_const BUTLAST : List.butlast]:
    "butlast [] = ([] :: 't18337 list) \<and>
     butlast ((h :: 't18337) # t) = (if t = [] then [] else h # butlast t)"
  by simp

lemma REPLICATE[import_const REPLICATE : List.replicate]:
  "replicate (id (0\<Colon>nat)) (x\<Colon>'t18358) = [] \<and>
   replicate (Suc n) x = x # replicate n x"
  by simp

lemma NULL[import_const NULL : List.null]:
  "List.null ([]\<Colon>'t18373 list) = True \<and> List.null ((h\<Colon>'t18373) # t) = False"
  unfolding null_def by simp

lemma ALL[import_const ALL : List.list_all]:
  "list_all (P\<Colon>'t18393 \<Rightarrow> bool) [] = True \<and>
  list_all P (h # t) = (P h \<and> list_all P t)"
  by simp

lemma EX[import_const EX : List.list_ex]:
  "list_ex (P\<Colon>'t18414 \<Rightarrow> bool) [] = False \<and>
  list_ex P (h # t) = (P h \<or> list_ex P t)"
  by simp

lemma ITLIST[import_const ITLIST : List.foldr]:
  "foldr (f\<Colon>'t18437 \<Rightarrow> 't18436 \<Rightarrow> 't18436) [] b = b \<and>
  foldr f (h # t) b = f h (foldr f t b)"
  by simp

lemma ALL2_DEF[import_const ALL2 : List.list_all2]:
  "list_all2 (P\<Colon>'t18495 \<Rightarrow> 't18502 \<Rightarrow> bool) [] (l2\<Colon>'t18502 list) = (l2 = []) \<and>
  list_all2 P ((h1\<Colon>'t18495) # (t1\<Colon>'t18495 list)) l2 =
  (if l2 = [] then False else P h1 (hd l2) \<and> list_all2 P t1 (tl l2))"
  by simp (induct_tac l2, simp_all)

lemma FILTER[import_const FILTER : List.filter]:
  "filter (P\<Colon>'t18680 \<Rightarrow> bool) [] = [] \<and>
  filter P ((h\<Colon>'t18680) # t) = (if P h then h # filter P t else filter P t)"
  by simp

lemma ZIP[import_const ZIP : List.zip]:
 "zip [] [] = ([] :: ('t18824 \<times> 't18825) list) \<and>
  zip ((h1\<Colon>'t18849) # t1) ((h2\<Colon>'t18850) # t2) = (h1, h2) # zip t1 t2"
  by simp

lemma WF[import_const WF : Wellfounded.wfP]:
  "wfP u \<longleftrightarrow> (\<forall>P. (\<exists>x :: 'A. P x) \<longrightarrow> (\<exists>x. P x \<and> (\<forall>y. u y x \<longrightarrow> \<not> P y)))"
proof (intro allI iffI impI wfI_min[to_pred], elim exE wfE_min[to_pred])
  fix x :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and xa :: "'a" and Q
  assume a: "xa \<in> Q"
  assume "\<forall>P. Ex P \<longrightarrow> (\<exists>xa. P xa \<and> (\<forall>y. x y xa \<longrightarrow> \<not> P y))"
  then have "Ex (\<lambda>x. x \<in> Q) \<longrightarrow> (\<exists>xa. (\<lambda>x. x \<in> Q) xa \<and> (\<forall>y. x y xa \<longrightarrow> \<not> (\<lambda>x. x \<in> Q) y))" by auto
  then show "\<exists>z\<in>Q. \<forall>y. x y z \<longrightarrow> y \<notin> Q" using a by auto
next
  fix x P and xa :: 'A and z
  assume "P xa" "z \<in> {a. P a}" "\<And>y. x y z \<Longrightarrow> y \<notin> {a. P a}"
  then show "\<exists>xa. P xa \<and> (\<forall>y. x y xa \<longrightarrow> \<not> P y)" by auto
qed auto

end

