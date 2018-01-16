(*  Title:      HOL/HOLCF/Cont.thy
    Author:     Franz Regensburger
    Author:     Brian Huffman
*)

section \<open>Continuity and monotonicity\<close>

theory Cont
  imports Pcpo
begin

text \<open>
   Now we change the default class! Form now on all untyped type variables are
   of default class po
\<close>

default_sort po

subsection \<open>Definitions\<close>

definition monofun :: "('a \<Rightarrow> 'b) \<Rightarrow> bool"  \<comment> \<open>monotonicity\<close>
  where "monofun f \<longleftrightarrow> (\<forall>x y. x \<sqsubseteq> y \<longrightarrow> f x \<sqsubseteq> f y)"

definition cont :: "('a::cpo \<Rightarrow> 'b::cpo) \<Rightarrow> bool"
  where "cont f = (\<forall>Y. chain Y \<longrightarrow> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i))"

lemma contI: "(\<And>Y. chain Y \<Longrightarrow> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)) \<Longrightarrow> cont f"
  by (simp add: cont_def)

lemma contE: "cont f \<Longrightarrow> chain Y \<Longrightarrow> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)"
  by (simp add: cont_def)

lemma monofunI: "(\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y) \<Longrightarrow> monofun f"
  by (simp add: monofun_def)

lemma monofunE: "monofun f \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
  by (simp add: monofun_def)


subsection \<open>Equivalence of alternate definition\<close>

text \<open>monotone functions map chains to chains\<close>

lemma ch2ch_monofun: "monofun f \<Longrightarrow> chain Y \<Longrightarrow> chain (\<lambda>i. f (Y i))"
  apply (rule chainI)
  apply (erule monofunE)
  apply (erule chainE)
  done

text \<open>monotone functions map upper bound to upper bounds\<close>

lemma ub2ub_monofun: "monofun f \<Longrightarrow> range Y <| u \<Longrightarrow> range (\<lambda>i. f (Y i)) <| f u"
  apply (rule ub_rangeI)
  apply (erule monofunE)
  apply (erule ub_rangeD)
  done

text \<open>a lemma about binary chains\<close>

lemma binchain_cont: "cont f \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> range (\<lambda>i::nat. f (if i = 0 then x else y)) <<| f y"
  apply (subgoal_tac "f (\<Squnion>i::nat. if i = 0 then x else y) = f y")
   apply (erule subst)
   apply (erule contE)
   apply (erule bin_chain)
  apply (rule_tac f=f in arg_cong)
  apply (erule is_lub_bin_chain [THEN lub_eqI])
  done

text \<open>continuity implies monotonicity\<close>

lemma cont2mono: "cont f \<Longrightarrow> monofun f"
  apply (rule monofunI)
  apply (drule (1) binchain_cont)
  apply (drule_tac i=0 in is_lub_rangeD1)
  apply simp
  done

lemmas cont2monofunE = cont2mono [THEN monofunE]

lemmas ch2ch_cont = cont2mono [THEN ch2ch_monofun]

text \<open>continuity implies preservation of lubs\<close>

lemma cont2contlubE: "cont f \<Longrightarrow> chain Y \<Longrightarrow> f (\<Squnion>i. Y i) = (\<Squnion>i. f (Y i))"
  apply (rule lub_eqI [symmetric])
  apply (erule (1) contE)
  done

lemma contI2:
  fixes f :: "'a::cpo \<Rightarrow> 'b::cpo"
  assumes mono: "monofun f"
  assumes below: "\<And>Y. \<lbrakk>chain Y; chain (\<lambda>i. f (Y i))\<rbrakk> \<Longrightarrow> f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i))"
  shows "cont f"
proof (rule contI)
  fix Y :: "nat \<Rightarrow> 'a"
  assume Y: "chain Y"
  with mono have fY: "chain (\<lambda>i. f (Y i))"
    by (rule ch2ch_monofun)
  have "(\<Squnion>i. f (Y i)) = f (\<Squnion>i. Y i)"
    apply (rule below_antisym)
     apply (rule lub_below [OF fY])
     apply (rule monofunE [OF mono])
     apply (rule is_ub_thelub [OF Y])
    apply (rule below [OF Y fY])
    done
  with fY show "range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)"
    by (rule thelubE)
qed


subsection \<open>Collection of continuity rules\<close>

named_theorems cont2cont "continuity intro rule"


subsection \<open>Continuity of basic functions\<close>

text \<open>The identity function is continuous\<close>

lemma cont_id [simp, cont2cont]: "cont (\<lambda>x. x)"
  apply (rule contI)
  apply (erule cpo_lubI)
  done

text \<open>constant functions are continuous\<close>

lemma cont_const [simp, cont2cont]: "cont (\<lambda>x. c)"
  using is_lub_const by (rule contI)

text \<open>application of functions is continuous\<close>

lemma cont_apply:
  fixes f :: "'a::cpo \<Rightarrow> 'b::cpo \<Rightarrow> 'c::cpo" and t :: "'a \<Rightarrow> 'b"
  assumes 1: "cont (\<lambda>x. t x)"
  assumes 2: "\<And>x. cont (\<lambda>y. f x y)"
  assumes 3: "\<And>y. cont (\<lambda>x. f x y)"
  shows "cont (\<lambda>x. (f x) (t x))"
proof (rule contI2 [OF monofunI])
  fix x y :: "'a"
  assume "x \<sqsubseteq> y"
  then show "f x (t x) \<sqsubseteq> f y (t y)"
    by (auto intro: cont2monofunE [OF 1]
        cont2monofunE [OF 2]
        cont2monofunE [OF 3]
        below_trans)
next
  fix Y :: "nat \<Rightarrow> 'a"
  assume "chain Y"
  then show "f (\<Squnion>i. Y i) (t (\<Squnion>i. Y i)) \<sqsubseteq> (\<Squnion>i. f (Y i) (t (Y i)))"
    by (simp only: cont2contlubE [OF 1] ch2ch_cont [OF 1]
        cont2contlubE [OF 2] ch2ch_cont [OF 2]
        cont2contlubE [OF 3] ch2ch_cont [OF 3]
        diag_lub below_refl)
qed

lemma cont_compose: "cont c \<Longrightarrow> cont (\<lambda>x. f x) \<Longrightarrow> cont (\<lambda>x. c (f x))"
  by (rule cont_apply [OF _ _ cont_const])

text \<open>Least upper bounds preserve continuity\<close>

lemma cont2cont_lub [simp]:
  assumes chain: "\<And>x. chain (\<lambda>i. F i x)"
    and cont: "\<And>i. cont (\<lambda>x. F i x)"
  shows "cont (\<lambda>x. \<Squnion>i. F i x)"
  apply (rule contI2)
   apply (simp add: monofunI cont2monofunE [OF cont] lub_mono chain)
  apply (simp add: cont2contlubE [OF cont])
  apply (simp add: diag_lub ch2ch_cont [OF cont] chain)
  done

text \<open>if-then-else is continuous\<close>

lemma cont_if [simp, cont2cont]: "cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda>x. if b then f x else g x)"
  by (induct b) simp_all


subsection \<open>Finite chains and flat pcpos\<close>

text \<open>Monotone functions map finite chains to finite chains.\<close>

lemma monofun_finch2finch: "monofun f \<Longrightarrow> finite_chain Y \<Longrightarrow> finite_chain (\<lambda>n. f (Y n))"
  by (force simp add: finite_chain_def ch2ch_monofun max_in_chain_def)

text \<open>The same holds for continuous functions.\<close>

lemma cont_finch2finch: "cont f \<Longrightarrow> finite_chain Y \<Longrightarrow> finite_chain (\<lambda>n. f (Y n))"
  by (rule cont2mono [THEN monofun_finch2finch])

text \<open>All monotone functions with chain-finite domain are continuous.\<close>

lemma chfindom_monofun2cont: "monofun f \<Longrightarrow> cont f"
  for f :: "'a::chfin \<Rightarrow> 'b::cpo"
  apply (erule contI2)
  apply (frule chfin2finch)
  apply (clarsimp simp add: finite_chain_def)
  apply (subgoal_tac "max_in_chain i (\<lambda>i. f (Y i))")
   apply (simp add: maxinch_is_thelub ch2ch_monofun)
  apply (force simp add: max_in_chain_def)
  done

text \<open>All strict functions with flat domain are continuous.\<close>

lemma flatdom_strict2mono: "f \<bottom> = \<bottom> \<Longrightarrow> monofun f"
  for f :: "'a::flat \<Rightarrow> 'b::pcpo"
  apply (rule monofunI)
  apply (drule ax_flat)
  apply auto
  done

lemma flatdom_strict2cont: "f \<bottom> = \<bottom> \<Longrightarrow> cont f"
  for f :: "'a::flat \<Rightarrow> 'b::pcpo"
  by (rule flatdom_strict2mono [THEN chfindom_monofun2cont])

text \<open>All functions with discrete domain are continuous.\<close>

lemma cont_discrete_cpo [simp, cont2cont]: "cont f"
  for f :: "'a::discrete_cpo \<Rightarrow> 'b::cpo"
  apply (rule contI)
  apply (drule discrete_chain_const, clarify)
  apply (simp add: is_lub_const)
  done

end
