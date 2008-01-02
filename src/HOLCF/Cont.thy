(*  Title:      HOLCF/Cont.thy
    ID:         $Id$
    Author:     Franz Regensburger

Results about continuity and monotonicity.
*)

header {* Continuity and monotonicity *}

theory Cont
imports Pcpo
begin

text {*
   Now we change the default class! Form now on all untyped type variables are
   of default class po
*}

defaultsort po

subsection {* Definitions *}

definition
  monofun :: "('a \<Rightarrow> 'b) \<Rightarrow> bool"  -- "monotonicity"  where
  "monofun f = (\<forall>x y. x \<sqsubseteq> y \<longrightarrow> f x \<sqsubseteq> f y)"

definition
  contlub :: "('a::cpo \<Rightarrow> 'b::cpo) \<Rightarrow> bool"  -- "first cont. def" where
  "contlub f = (\<forall>Y. chain Y \<longrightarrow> f (\<Squnion>i. Y i) = (\<Squnion>i. f (Y i)))"

definition
  cont :: "('a::cpo \<Rightarrow> 'b::cpo) \<Rightarrow> bool"  -- "secnd cont. def" where
  "cont f = (\<forall>Y. chain Y \<longrightarrow> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i))"

lemma contlubI:
  "\<lbrakk>\<And>Y. chain Y \<Longrightarrow> f (\<Squnion>i. Y i) = (\<Squnion>i. f (Y i))\<rbrakk> \<Longrightarrow> contlub f"
by (simp add: contlub_def)

lemma contlubE: 
  "\<lbrakk>contlub f; chain Y\<rbrakk> \<Longrightarrow> f (\<Squnion>i. Y i) = (\<Squnion>i. f (Y i))" 
by (simp add: contlub_def)

lemma contI:
  "\<lbrakk>\<And>Y. chain Y \<Longrightarrow> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)\<rbrakk> \<Longrightarrow> cont f"
by (simp add: cont_def)

lemma contE:
  "\<lbrakk>cont f; chain Y\<rbrakk> \<Longrightarrow> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)"
by (simp add: cont_def)

lemma monofunI: 
  "\<lbrakk>\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y\<rbrakk> \<Longrightarrow> monofun f"
by (simp add: monofun_def)

lemma monofunE: 
  "\<lbrakk>monofun f; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq> f y"
by (simp add: monofun_def)


subsection {* @{prop "monofun f \<and> contlub f \<equiv> cont f"} *}

text {* monotone functions map chains to chains *}

lemma ch2ch_monofun: "\<lbrakk>monofun f; chain Y\<rbrakk> \<Longrightarrow> chain (\<lambda>i. f (Y i))"
apply (rule chainI)
apply (erule monofunE)
apply (erule chainE)
done

text {* monotone functions map upper bound to upper bounds *}

lemma ub2ub_monofun: 
  "\<lbrakk>monofun f; range Y <| u\<rbrakk> \<Longrightarrow> range (\<lambda>i. f (Y i)) <| f u"
apply (rule ub_rangeI)
apply (erule monofunE)
apply (erule ub_rangeD)
done

lemma ub2ub_monofun':
  "\<lbrakk>monofun f; S <| u\<rbrakk> \<Longrightarrow> f ` S <| f u"
apply (rule ub_imageI)
apply (erule monofunE)
apply (erule (1) is_ubD)
done

text {* monotone functions map directed sets to directed sets *}

lemma dir2dir_monofun:
  assumes f: "monofun f"
  assumes S: "directed S"
  shows "directed (f ` S)"
proof (rule directedI)
  from directedD1 [OF S]
  obtain x where "x \<in> S" ..
  hence "f x \<in> f ` S" by simp
  thus "\<exists>x. x \<in> f ` S" ..
next
  fix x assume "x \<in> f ` S"
  then obtain a where x: "x = f a" and a: "a \<in> S" ..
  fix y assume "y \<in> f ` S"
  then obtain b where y: "y = f b" and b: "b \<in> S" ..
  from directedD2 [OF S a b]
  obtain c where "c \<in> S" and "a \<sqsubseteq> c \<and> b \<sqsubseteq> c" ..
  hence "f c \<in> f ` S" and "x \<sqsubseteq> f c \<and> y \<sqsubseteq> f c"
    using monofunE [OF f] x y by simp_all
  thus "\<exists>z\<in>f ` S. x \<sqsubseteq> z \<and> y \<sqsubseteq> z" ..
qed

text {* left to right: @{prop "monofun f \<and> contlub f \<Longrightarrow> cont f"} *}

lemma monocontlub2cont: "\<lbrakk>monofun f; contlub f\<rbrakk> \<Longrightarrow> cont f"
apply (rule contI)
apply (rule thelubE)
apply (erule (1) ch2ch_monofun)
apply (erule (1) contlubE [symmetric])
done

text {* first a lemma about binary chains *}

lemma binchain_cont:
  "\<lbrakk>cont f; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> range (\<lambda>i::nat. f (if i = 0 then x else y)) <<| f y"
apply (subgoal_tac "f (\<Squnion>i::nat. if i = 0 then x else y) = f y")
apply (erule subst)
apply (erule contE)
apply (erule bin_chain)
apply (rule_tac f=f in arg_cong)
apply (erule lub_bin_chain [THEN thelubI])
done

text {* right to left: @{prop "cont f \<Longrightarrow> monofun f \<and> contlub f"} *}
text {* part1: @{prop "cont f \<Longrightarrow> monofun f"} *}

lemma cont2mono: "cont f \<Longrightarrow> monofun f"
apply (rule monofunI)
apply (drule (1) binchain_cont)
apply (drule_tac i=0 in is_ub_lub)
apply simp
done

lemmas ch2ch_cont = cont2mono [THEN ch2ch_monofun]

text {* right to left: @{prop "cont f \<Longrightarrow> monofun f \<and> contlub f"} *}
text {* part2: @{prop "cont f \<Longrightarrow> contlub f"} *}

lemma cont2contlub: "cont f \<Longrightarrow> contlub f"
apply (rule contlubI)
apply (rule thelubI [symmetric])
apply (erule (1) contE)
done

lemmas cont2contlubE = cont2contlub [THEN contlubE]

subsection {* Continuity of basic functions *}

text {* The identity function is continuous *}

lemma cont_id: "cont (\<lambda>x. x)"
apply (rule contI)
apply (erule thelubE)
apply (rule refl)
done

text {* constant functions are continuous *}

lemma cont_const: "cont (\<lambda>x. c)"
apply (rule contI)
apply (rule lub_const)
done

text {* if-then-else is continuous *}

lemma cont_if: "\<lbrakk>cont f; cont g\<rbrakk> \<Longrightarrow> cont (\<lambda>x. if b then f x else g x)"
by (induct b) simp_all

subsection {* Finite chains and flat pcpos *}

text {* monotone functions map finite chains to finite chains *}

lemma monofun_finch2finch:
  "\<lbrakk>monofun f; finite_chain Y\<rbrakk> \<Longrightarrow> finite_chain (\<lambda>n. f (Y n))"
apply (unfold finite_chain_def)
apply (simp add: ch2ch_monofun)
apply (force simp add: max_in_chain_def)
done

text {* The same holds for continuous functions *}

lemma cont_finch2finch:
  "\<lbrakk>cont f; finite_chain Y\<rbrakk> \<Longrightarrow> finite_chain (\<lambda>n. f (Y n))"
by (rule cont2mono [THEN monofun_finch2finch])

lemma chfindom_monofun2cont: "monofun f \<Longrightarrow> cont (f::'a::chfin \<Rightarrow> 'b::pcpo)"
apply (rule monocontlub2cont)
apply assumption
apply (rule contlubI)
apply (frule chfin2finch)
apply (clarsimp simp add: finite_chain_def)
apply (subgoal_tac "max_in_chain i (\<lambda>i. f (Y i))")
apply (simp add: maxinch_is_thelub ch2ch_monofun)
apply (force simp add: max_in_chain_def)
done

text {* some properties of flat *}

lemma flatdom_strict2mono: "f \<bottom> = \<bottom> \<Longrightarrow> monofun (f::'a::flat \<Rightarrow> 'b::pcpo)"
apply (rule monofunI)
apply (drule ax_flat [rule_format])
apply auto
done

lemma flatdom_strict2cont: "f \<bottom> = \<bottom> \<Longrightarrow> cont (f::'a::flat \<Rightarrow> 'b::pcpo)"
by (rule flatdom_strict2mono [THEN chfindom_monofun2cont])

end
