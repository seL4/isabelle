(*  Title:      HOL/Import/HOL_Light_Maps.thy
    Author:     Cezary Kaliszyk, University of Innsbruck
    Author:     Alexander Krauss, QAware GmbH

Based on earlier code by Steven Obua and Sebastian Skalberg
*)

section \<open>Type and constant mappings of HOL Light importer\<close>

theory HOL_Light_Maps
imports Import_Setup
begin

lemma [import_const T]:
  "True = ((\<lambda>p :: bool. p) = (\<lambda>p. p))"
  by simp

lemma [import_const "/\\"]:
  "(\<and>) = (\<lambda>p q. (\<lambda>f. f p q :: bool) = (\<lambda>f. f True True))"
  by metis

lemma [import_const "==>"]:
  "(\<longrightarrow>) = (\<lambda>(p::bool) q::bool. (p \<and> q) = p)"
  by auto

lemma [import_const "!"]:
  "All = (\<lambda>P::'A \<Rightarrow> bool. P = (\<lambda>x::'A. True))"
  by auto

lemma [import_const "?"]:
  "Ex = (\<lambda>P::'A \<Rightarrow> bool. All (\<lambda>q::bool. (All (\<lambda>x::'A::type. (P x) \<longrightarrow> q)) \<longrightarrow> q))"
  by auto

lemma [import_const "\\/"]:
  "(\<or>) = (\<lambda>p q. \<forall>r. (p \<longrightarrow> r) \<longrightarrow> (q \<longrightarrow> r) \<longrightarrow> r)"
  by auto

lemma [import_const F]:
  "False = (\<forall>p. p)"
  by auto

lemma [import_const "~"]:
  "Not = (\<lambda>p. p \<longrightarrow> False)"
  by simp

lemma [import_const "?!"]:
  "Ex1 = (\<lambda>P::'A \<Rightarrow> bool. Ex P \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> x = y))"
  by auto

lemma [import_const "_FALSITY_"]: "False = False"
  by simp

lemma hl_ax1: "\<forall>t::'A \<Rightarrow> 'B. (\<lambda>x. t x) = t"
  by metis

lemma hl_ax2: "\<forall>P x::'A. P x \<longrightarrow> P (Eps P)"
  by (auto intro: someI)

lemma [import_const COND]:
  "If = (\<lambda>t (t1 :: 'A) t2. SOME x. (t = True \<longrightarrow> x = t1) \<and> (t = False \<longrightarrow> x = t2))"
  unfolding fun_eq_iff by auto

lemma [import_const o]:
  "(\<circ>) = (\<lambda>(f::'B \<Rightarrow> 'C) g x::'A. f (g x))"
  unfolding fun_eq_iff by simp

lemma [import_const I]: "id = (\<lambda>x::'A. x)"
  by auto

lemma [import_type 1 one_ABS one_REP]:
  "type_definition Rep_unit Abs_unit (Collect (\<lambda>b. b))"
  by (metis (full_types) Collect_cong singleton_conv2 type_definition_unit)

lemma [import_const one]: "() = (SOME x::unit. True)"
  by auto

lemma [import_const mk_pair]:
  "Pair_Rep = (\<lambda>(x::'A) (y::'B) (a::'A) b::'B. a = x \<and> b = y)"
  by (simp add: Pair_Rep_def fun_eq_iff)

lemma [import_type prod ABS_prod REP_prod]:
  "type_definition Rep_prod Abs_prod (Collect (\<lambda>x::'A \<Rightarrow> 'B \<Rightarrow> bool. \<exists>a b. x = Pair_Rep a b))"
  using type_definition_prod[unfolded Product_Type.prod_def] by simp

lemma [import_const ","]: "Pair = (\<lambda>(x::'A) y::'B. Abs_prod (Pair_Rep x y))"
  by (metis Pair_def)

lemma [import_const FST]:
  "fst = (\<lambda>p::'A \<times> 'B. SOME x::'A. \<exists>y::'B. p = (x, y))"
  by auto

lemma [import_const SND]:
  "snd = (\<lambda>p::'A \<times> 'B. SOME y::'B. \<exists>x::'A. p = (x, y))"
  by auto

lemma CURRY_DEF[import_const CURRY]:
  "curry = (\<lambda>(f::'A \<times> 'B \<Rightarrow> 'C) x y. f (x, y))"
  using curry_def .

lemma [import_const ONE_ONE : inj]:
  "inj = (\<lambda>(f::'A \<Rightarrow> 'B). \<forall>x1 x2. f x1 = f x2 \<longrightarrow> x1 = x2)"
  by (auto simp add: fun_eq_iff inj_on_def)

lemma [import_const ONTO : surj]:
  "surj = (\<lambda>(f::'A \<Rightarrow> 'B). \<forall>y. \<exists>x. y = f x)"
  by (auto simp add: fun_eq_iff)

lemma hl_ax3: "\<exists>f::ind \<Rightarrow> ind. inj f \<and> \<not> surj f"
  by (rule_tac x="Suc_Rep" in exI)
     (metis Suc_Rep_inject' injI Suc_Rep_not_Zero_Rep surjD)

import_type_map num : nat
import_const_map "_0" : zero_class.zero
import_const_map SUC : Suc

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

lemma PRE[import_const PRE : pred]:
  "pred (id (0::nat)) = id (0::nat) \<and> (\<forall>n::nat. pred (Suc n) = n)"
  by simp

lemma ADD[import_const "+" : plus]:
  "(\<forall>n :: nat. (id 0) + n = n) \<and> (\<forall>m n. (Suc m) + n = Suc (m + n))"
  by simp

lemma MULT[import_const "*" : times]:
  "(\<forall>n :: nat. (id 0) * n = id 0) \<and> (\<forall>m n. (Suc m) * n = (m * n) + n)"
  by simp

lemma EXP[import_const EXP : power]:
  "(\<forall>m. m ^ (id 0) = id (bit1 0)) \<and> (\<forall>(m :: nat) n. m ^ (Suc n) = m * (m ^ n))"
  by simp

lemma LE[import_const "<=" : less_eq]:
  "(\<forall>m :: nat. m \<le> (id 0) = (m = id 0)) \<and> (\<forall>m n. m \<le> (Suc n) = (m = Suc n \<or> m \<le> n))"
  by auto

lemma LT[import_const "<" : less]:
  "(\<forall>m :: nat. m < (id 0) = False) \<and> (\<forall>m n. m < (Suc n) = (m = n \<or> m < n))"
  by auto

lemma DEF_GE[import_const ">=" : greater_eq]:
  "(\<ge>) = (\<lambda>x y :: nat. y \<le> x)"
  by simp

lemma DEF_GT[import_const ">" : greater]:
  "(>) = (\<lambda>x y :: nat. y < x)"
  by simp

lemma DEF_MAX[import_const "MAX"]:
  "max = (\<lambda>x y :: nat. if x \<le> y then y else x)"
  by (simp add: fun_eq_iff)

lemma DEF_MIN[import_const "MIN"]:
  "min = (\<lambda>x y :: nat. if x \<le> y then x else y)"
  by (simp add: fun_eq_iff)

definition even
where
  "even = Parity.even"
  
lemma EVEN[import_const "EVEN" : even]:
  "even (id 0::nat) = True \<and> (\<forall>n. even (Suc n) = (\<not> even n))"
  by (simp add: even_def)

lemma SUB[import_const "-" : minus]:
  "(\<forall>m::nat. m - (id 0) = m) \<and> (\<forall>m n. m - (Suc n) = pred (m - n))"
  by simp

lemma FACT[import_const "FACT" : fact]:
  "fact (id 0) = id (bit1 0) \<and> (\<forall>n. fact (Suc n) = Suc n * fact n)"
  by simp

import_const_map MOD : modulo
import_const_map DIV : divide

lemma DIVISION_0:
  "\<forall>m n::nat. if n = id 0 then m div n = id 0 \<and> m mod n = m else m = m div n * n + m mod n \<and> m mod n < n"
  by simp

lemmas [import_type sum "_dest_sum" "_mk_sum"] = type_definition_sum[where 'a="'A" and 'b="'B"]
import_const_map INL : Inl
import_const_map INR : Inr

lemma sum_INDUCT:
  "\<forall>P. (\<forall>a :: 'A. P (Inl a)) \<and> (\<forall>a :: 'B. P (Inr a)) \<longrightarrow> (\<forall>x. P x)"
  by (auto intro: sum.induct)

lemma sum_RECURSION:
  "\<forall>Inl' Inr'. \<exists>fn. (\<forall>a :: 'A. fn (Inl a) = (Inl' a :: 'Z)) \<and> (\<forall>a :: 'B. fn (Inr a) = Inr' a)"
  by (intro allI, rule_tac x="case_sum Inl' Inr'" in exI) auto

lemma OUTL[import_const "OUTL" : projl]:
  "Sum_Type.projl (Inl x) = x"
  by simp

lemma OUTR[import_const "OUTR" : projr]:
  "Sum_Type.projr (Inr y) = y"
  by simp

import_type_map list : list
import_const_map NIL : Nil
import_const_map CONS : Cons

lemma list_INDUCT:
  "\<forall>P::'A list \<Rightarrow> bool. P [] \<and> (\<forall>a0 a1. P a1 \<longrightarrow> P (a0 # a1)) \<longrightarrow> (\<forall>x. P x)"
  using list.induct by auto

lemma list_RECURSION:
 "\<forall>nil' cons'. \<exists>fn::'A list \<Rightarrow> 'Z. fn [] = nil' \<and> (\<forall>(a0::'A) a1::'A list. fn (a0 # a1) = cons' a0 a1 (fn a1))"
  by (intro allI, rule_tac x="rec_list nil' cons'" in exI) auto

lemma HD[import_const HD : hd]:
  "hd ((h::'A) # t) = h"
  by simp

lemma TL[import_const TL : tl]:
  "tl ((h::'A) # t) = t"
  by simp

lemma APPEND[import_const APPEND : append]:
  "(\<forall>l::'A list. [] @ l = l) \<and> (\<forall>(h::'A) t l. (h # t) @ l = h # t @ l)"
  by simp

lemma REVERSE[import_const REVERSE : rev]:
  "rev [] = ([] :: 'A list) \<and> rev ((x::'A) # l) = rev l @ [x]"
  by simp

lemma LENGTH[import_const LENGTH : length]:
  "length ([] :: 'A list) = id 0 \<and> (\<forall>(h::'A) t. length (h # t) = Suc (length t))"
  by simp

lemma MAP[import_const MAP : map]:
  "(\<forall>f::'A \<Rightarrow> 'B. map f [] = []) \<and>
       (\<forall>(f::'A \<Rightarrow> 'B) h t. map f (h # t) = f h # map f t)"
  by simp

lemma LAST[import_const LAST : last]:
  "last ((h::'A) # t) = (if t = [] then h else last t)"
  by simp

lemma BUTLAST[import_const BUTLAST : butlast]:
    "butlast [] = ([] :: 't18337 list) \<and>
     butlast ((h :: 't18337) # t) = (if t = [] then [] else h # butlast t)"
  by simp

lemma REPLICATE[import_const REPLICATE : replicate]:
  "replicate (id (0::nat)) (x::'t18358) = [] \<and>
   replicate (Suc n) x = x # replicate n x"
  by simp

lemma NULL[import_const NULL : List.null]:
  "List.null ([]::'t18373 list) = True \<and> List.null ((h::'t18373) # t) = False"
  unfolding null_def by simp

lemma ALL[import_const ALL : list_all]:
  "list_all (P::'t18393 \<Rightarrow> bool) [] = True \<and>
  list_all P (h # t) = (P h \<and> list_all P t)"
  by simp

lemma EX[import_const EX : list_ex]:
  "list_ex (P::'t18414 \<Rightarrow> bool) [] = False \<and>
  list_ex P (h # t) = (P h \<or> list_ex P t)"
  by simp

lemma ITLIST[import_const ITLIST : foldr]:
  "foldr (f::'t18437 \<Rightarrow> 't18436 \<Rightarrow> 't18436) [] b = b \<and>
  foldr f (h # t) b = f h (foldr f t b)"
  by simp

lemma ALL2_DEF[import_const ALL2 : list_all2]:
  "list_all2 (P::'t18495 \<Rightarrow> 't18502 \<Rightarrow> bool) [] (l2::'t18502 list) = (l2 = []) \<and>
  list_all2 P ((h1::'t18495) # (t1::'t18495 list)) l2 =
  (if l2 = [] then False else P h1 (hd l2) \<and> list_all2 P t1 (tl l2))"
  by simp (induct_tac l2, simp_all)

lemma FILTER[import_const FILTER : filter]:
  "filter (P::'t18680 \<Rightarrow> bool) [] = [] \<and>
  filter P ((h::'t18680) # t) = (if P h then h # filter P t else filter P t)"
  by simp

lemma ZIP[import_const ZIP : zip]:
 "zip [] [] = ([] :: ('t18824 \<times> 't18825) list) \<and>
  zip ((h1::'t18849) # t1) ((h2::'t18850) # t2) = (h1, h2) # zip t1 t2"
  by simp

lemma WF[import_const WF : wfP]:
  "\<forall>u. wfP u \<longleftrightarrow> (\<forall>P. (\<exists>x :: 'A. P x) \<longrightarrow> (\<exists>x. P x \<and> (\<forall>y. u y x \<longrightarrow> \<not> P y)))"
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

