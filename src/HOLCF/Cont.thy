(*  Title:      HOLCF/Cont.thy
    ID:         $Id$
    Author:     Franz Regensburger

Results about continuity and monotonicity.
*)

header {* Continuity and monotonicity *}

theory Cont
imports Ffun
begin

text {*
   Now we change the default class! Form now on all untyped type variables are
   of default class po
*}

defaultsort po

subsection {* Definitions *}

constdefs
  monofun :: "('a \<Rightarrow> 'b) \<Rightarrow> bool"  -- "monotonicity"
  "monofun f \<equiv> \<forall>x y. x \<sqsubseteq> y \<longrightarrow> f x \<sqsubseteq> f y"

  contlub :: "('a::cpo \<Rightarrow> 'b::cpo) \<Rightarrow> bool"  -- "first cont. def"
  "contlub f \<equiv> \<forall>Y. chain Y \<longrightarrow> f (\<Squnion>i. Y i) = (\<Squnion>i. f (Y i))"

  cont    :: "('a::cpo \<Rightarrow> 'b::cpo) \<Rightarrow> bool"  -- "secnd cont. def"
  "cont f    \<equiv> \<forall>Y. chain Y \<longrightarrow> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)"

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

text {*
  The following results are about application for functions in @{typ "'a=>'b"}
*}

lemma monofun_fun_fun: "f \<sqsubseteq> g \<Longrightarrow> f x \<sqsubseteq> g x"
by (simp add: less_fun_def)

lemma monofun_fun_arg: "\<lbrakk>monofun f; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq> f y"
by (rule monofunE)

lemma monofun_fun: "\<lbrakk>monofun f; monofun g; f \<sqsubseteq> g; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq> g y"
by (rule trans_less [OF monofun_fun_arg monofun_fun_fun])


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

text {* left to right: @{prop "monofun f \<and> contlub f \<Longrightarrow> cont f"} *}

lemma monocontlub2cont: "\<lbrakk>monofun f; contlub f\<rbrakk> \<Longrightarrow> cont f"
apply (rule contI)
apply (rule thelubE)
apply (erule ch2ch_monofun)
apply assumption
apply (erule contlubE [symmetric])
apply assumption
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
apply (drule binchain_cont, assumption)
apply (drule_tac i=0 in is_ub_lub)
apply simp
done

lemmas ch2ch_cont = cont2mono [THEN ch2ch_monofun]

text {* right to left: @{prop "cont f \<Longrightarrow> monofun f \<and> contlub f"} *}
text {* part2: @{prop "cont f \<Longrightarrow> contlub f"} *}

lemma cont2contlub: "cont f \<Longrightarrow> contlub f"
apply (rule contlubI)
apply (rule thelubI [symmetric])
apply (erule contE)
apply assumption
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

subsection {* Propagation of monotonicity and continuity *}

text {* the lub of a chain of monotone functions is monotone *}

lemma monofun_lub_fun:
  "\<lbrakk>chain (F::nat \<Rightarrow> 'a \<Rightarrow> 'b::cpo); \<forall>i. monofun (F i)\<rbrakk>
    \<Longrightarrow> monofun (\<Squnion>i. F i)"
apply (rule monofunI)
apply (simp add: thelub_fun)
apply (rule lub_mono [rule_format])
apply (erule ch2ch_fun)
apply (erule ch2ch_fun)
apply (simp add: monofunE)
done

text {* the lub of a chain of continuous functions is continuous *}

declare range_composition [simp del]

lemma contlub_lub_fun:
  "\<lbrakk>chain F; \<forall>i. cont (F i)\<rbrakk> \<Longrightarrow> contlub (\<Squnion>i. F i)"
apply (rule contlubI)
apply (simp add: thelub_fun)
apply (simp add: cont2contlubE)
apply (rule ex_lub)
apply (erule ch2ch_fun)
apply (simp add: ch2ch_cont)
done

lemma cont_lub_fun:
  "\<lbrakk>chain F; \<forall>i. cont (F i)\<rbrakk> \<Longrightarrow> cont (\<Squnion>i. F i)"
apply (rule monocontlub2cont)
apply (erule monofun_lub_fun)
apply (simp add: cont2mono)
apply (erule contlub_lub_fun)
apply assumption
done

lemma cont2cont_lub:
  "\<lbrakk>chain F; \<And>i. cont (F i)\<rbrakk> \<Longrightarrow> cont (\<lambda>x. \<Squnion>i. F i x)"
by (simp add: thelub_fun [symmetric] cont_lub_fun)

lemma mono2mono_MF1L: "monofun f \<Longrightarrow> monofun (\<lambda>x. f x y)"
apply (rule monofunI)
apply (erule (1) monofun_fun_arg [THEN monofun_fun_fun])
done

lemma cont2cont_CF1L: "cont f \<Longrightarrow> cont (\<lambda>x. f x y)"
apply (rule monocontlub2cont)
apply (erule cont2mono [THEN mono2mono_MF1L])
apply (rule contlubI)
apply (simp add: cont2contlubE)
apply (simp add: thelub_fun ch2ch_cont)
done

text {* Note @{text "(\<lambda>x. \<lambda>y. f x y) = f"} *}

lemma mono2mono_MF1L_rev: "\<forall>y. monofun (\<lambda>x. f x y) \<Longrightarrow> monofun f"
apply (rule monofunI)
apply (rule less_fun_ext)
apply (blast dest: monofunE)
done

lemma cont2cont_CF1L_rev: "\<forall>y. cont (\<lambda>x. f x y) \<Longrightarrow> cont f"
apply (subgoal_tac "monofun f")
apply (rule monocontlub2cont)
apply assumption
apply (rule contlubI)
apply (rule ext)
apply (simp add: thelub_fun ch2ch_monofun)
apply (blast dest: cont2contlubE)
apply (simp add: mono2mono_MF1L_rev cont2mono)
done

lemma cont2cont_lambda: "(\<And>y. cont (\<lambda>x. f x y)) \<Longrightarrow> cont (\<lambda>x. (\<lambda>y. f x y))"
apply (rule cont2cont_CF1L_rev)
apply simp
done

text {* What D.A.Schmidt calls continuity of abstraction; never used here *}

lemma contlub_abstraction:
  "\<lbrakk>chain Y; \<forall>y. cont (\<lambda>x.(c::'a::cpo\<Rightarrow>'b::type\<Rightarrow>'c::cpo) x y)\<rbrakk> \<Longrightarrow>
    (\<lambda>y. \<Squnion>i. c (Y i) y) = (\<Squnion>i. (\<lambda>y. c (Y i) y))"
apply (rule thelub_fun [symmetric])
apply (rule ch2ch_cont)
apply (erule (1) cont2cont_CF1L_rev)
done

lemma mono2mono_app:
  "\<lbrakk>monofun f; \<forall>x. monofun (f x); monofun t\<rbrakk> \<Longrightarrow> monofun (\<lambda>x. (f x) (t x))"
apply (rule monofunI)
apply (simp add: monofun_fun monofunE)
done

lemma cont2contlub_app:
  "\<lbrakk>cont f; \<forall>x. cont (f x); cont t\<rbrakk> \<Longrightarrow> contlub (\<lambda>x. (f x) (t x))"
apply (rule contlubI)
apply (subgoal_tac "chain (\<lambda>i. f (Y i))")
apply (subgoal_tac "chain (\<lambda>i. t (Y i))")
apply (simp add: cont2contlubE thelub_fun)
apply (rule diag_lub)
apply (erule ch2ch_fun)
apply (drule spec)
apply (erule (1) ch2ch_cont)
apply (erule (1) ch2ch_cont)
apply (erule (1) ch2ch_cont)
done

lemma cont2cont_app:
  "\<lbrakk>cont f; \<forall>x. cont (f x); cont t\<rbrakk> \<Longrightarrow> cont (\<lambda>x. (f x) (t x))"
by (blast intro: monocontlub2cont mono2mono_app cont2mono cont2contlub_app)

lemmas cont2cont_app2 = cont2cont_app [rule_format]

lemma cont2cont_app3: "\<lbrakk>cont f; cont t\<rbrakk> \<Longrightarrow> cont (\<lambda>x. f (t x))"
by (rule cont2cont_app2 [OF cont_const])

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
