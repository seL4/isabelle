(*  Title:      HOLCF/FunCpo.thy
    Author:     Franz Regensburger
*)

header {* Class instances for the full function space *}

theory Ffun
imports Cont
begin

subsection {* Full function space is a partial order *}

instantiation "fun"  :: (type, below) below
begin

definition
  below_fun_def: "(op \<sqsubseteq>) \<equiv> (\<lambda>f g. \<forall>x. f x \<sqsubseteq> g x)"

instance ..
end

instance "fun" :: (type, po) po
proof
  fix f :: "'a \<Rightarrow> 'b"
  show "f \<sqsubseteq> f"
    by (simp add: below_fun_def)
next
  fix f g :: "'a \<Rightarrow> 'b"
  assume "f \<sqsubseteq> g" and "g \<sqsubseteq> f" thus "f = g"
    by (simp add: below_fun_def expand_fun_eq below_antisym)
next
  fix f g h :: "'a \<Rightarrow> 'b"
  assume "f \<sqsubseteq> g" and "g \<sqsubseteq> h" thus "f \<sqsubseteq> h"
    unfolding below_fun_def by (fast elim: below_trans)
qed

text {* make the symbol @{text "<<"} accessible for type fun *}

lemma expand_fun_below: "(f \<sqsubseteq> g) = (\<forall>x. f x \<sqsubseteq> g x)"
by (simp add: below_fun_def)

lemma below_fun_ext: "(\<And>x. f x \<sqsubseteq> g x) \<Longrightarrow> f \<sqsubseteq> g"
by (simp add: below_fun_def)

subsection {* Full function space is chain complete *}

text {* function application is monotone *}

lemma monofun_app: "monofun (\<lambda>f. f x)"
by (rule monofunI, simp add: below_fun_def)

text {* chains of functions yield chains in the po range *}

lemma ch2ch_fun: "chain S \<Longrightarrow> chain (\<lambda>i. S i x)"
by (simp add: chain_def below_fun_def)

lemma ch2ch_lambda: "(\<And>x. chain (\<lambda>i. S i x)) \<Longrightarrow> chain S"
by (simp add: chain_def below_fun_def)

text {* upper bounds of function chains yield upper bound in the po range *}

lemma ub2ub_fun:
  "range S <| u \<Longrightarrow> range (\<lambda>i. S i x) <| u x"
by (auto simp add: is_ub_def below_fun_def)

text {* Type @{typ "'a::type => 'b::cpo"} is chain complete *}

lemma is_lub_lambda:
  assumes f: "\<And>x. range (\<lambda>i. Y i x) <<| f x"
  shows "range Y <<| f"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (rule below_fun_ext)
apply (rule is_ub_lub [OF f])
apply (rule below_fun_ext)
apply (rule is_lub_lub [OF f])
apply (erule ub2ub_fun)
done

lemma lub_fun:
  "chain (S::nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo)
    \<Longrightarrow> range S <<| (\<lambda>x. \<Squnion>i. S i x)"
apply (rule is_lub_lambda)
apply (rule cpo_lubI)
apply (erule ch2ch_fun)
done

lemma thelub_fun:
  "chain (S::nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo)
    \<Longrightarrow> (\<Squnion>i. S i) = (\<lambda>x. \<Squnion>i. S i x)"
by (rule lub_fun [THEN thelubI])

lemma cpo_fun:
  "chain (S::nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo) \<Longrightarrow> \<exists>x. range S <<| x"
by (rule exI, erule lub_fun)

instance "fun"  :: (type, cpo) cpo
by intro_classes (rule cpo_fun)

instance "fun" :: (finite, finite_po) finite_po ..

instance "fun" :: (type, discrete_cpo) discrete_cpo
proof
  fix f g :: "'a \<Rightarrow> 'b"
  show "f \<sqsubseteq> g \<longleftrightarrow> f = g" 
    unfolding expand_fun_below expand_fun_eq
    by simp
qed

text {* chain-finite function spaces *}

lemma maxinch2maxinch_lambda:
  "(\<And>x. max_in_chain n (\<lambda>i. S i x)) \<Longrightarrow> max_in_chain n S"
unfolding max_in_chain_def expand_fun_eq by simp

lemma maxinch_mono:
  "\<lbrakk>max_in_chain i Y; i \<le> j\<rbrakk> \<Longrightarrow> max_in_chain j Y"
unfolding max_in_chain_def
proof (intro allI impI)
  fix k
  assume Y: "\<forall>n\<ge>i. Y i = Y n"
  assume ij: "i \<le> j"
  assume jk: "j \<le> k"
  from ij jk have ik: "i \<le> k" by simp
  from Y ij have Yij: "Y i = Y j" by simp
  from Y ik have Yik: "Y i = Y k" by simp
  from Yij Yik show "Y j = Y k" by auto
qed

instance "fun" :: (finite, chfin) chfin
proof
  fix Y :: "nat \<Rightarrow> 'a \<Rightarrow> 'b"
  let ?n = "\<lambda>x. LEAST n. max_in_chain n (\<lambda>i. Y i x)"
  assume "chain Y"
  hence "\<And>x. chain (\<lambda>i. Y i x)"
    by (rule ch2ch_fun)
  hence "\<And>x. \<exists>n. max_in_chain n (\<lambda>i. Y i x)"
    by (rule chfin)
  hence "\<And>x. max_in_chain (?n x) (\<lambda>i. Y i x)"
    by (rule LeastI_ex)
  hence "\<And>x. max_in_chain (Max (range ?n)) (\<lambda>i. Y i x)"
    by (rule maxinch_mono [OF _ Max_ge], simp_all)
  hence "max_in_chain (Max (range ?n)) Y"
    by (rule maxinch2maxinch_lambda)
  thus "\<exists>n. max_in_chain n Y" ..
qed

subsection {* Full function space is pointed *}

lemma minimal_fun: "(\<lambda>x. \<bottom>) \<sqsubseteq> f"
by (simp add: below_fun_def)

lemma least_fun: "\<exists>x::'a::type \<Rightarrow> 'b::pcpo. \<forall>y. x \<sqsubseteq> y"
apply (rule_tac x = "\<lambda>x. \<bottom>" in exI)
apply (rule minimal_fun [THEN allI])
done

instance "fun"  :: (type, pcpo) pcpo
by intro_classes (rule least_fun)

text {* for compatibility with old HOLCF-Version *}
lemma inst_fun_pcpo: "\<bottom> = (\<lambda>x. \<bottom>)"
by (rule minimal_fun [THEN UU_I, symmetric])

text {* function application is strict in the left argument *}
lemma app_strict [simp]: "\<bottom> x = \<bottom>"
by (simp add: inst_fun_pcpo)

text {*
  The following results are about application for functions in @{typ "'a=>'b"}
*}

lemma monofun_fun_fun: "f \<sqsubseteq> g \<Longrightarrow> f x \<sqsubseteq> g x"
by (simp add: below_fun_def)

lemma monofun_fun_arg: "\<lbrakk>monofun f; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq> f y"
by (rule monofunE)

lemma monofun_fun: "\<lbrakk>monofun f; monofun g; f \<sqsubseteq> g; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq> g y"
by (rule below_trans [OF monofun_fun_arg monofun_fun_fun])

subsection {* Propagation of monotonicity and continuity *}

text {* the lub of a chain of monotone functions is monotone *}

lemma monofun_lub_fun:
  "\<lbrakk>chain (F::nat \<Rightarrow> 'a \<Rightarrow> 'b::cpo); \<forall>i. monofun (F i)\<rbrakk>
    \<Longrightarrow> monofun (\<Squnion>i. F i)"
apply (rule monofunI)
apply (simp add: thelub_fun)
apply (rule lub_mono)
apply (erule ch2ch_fun)
apply (erule ch2ch_fun)
apply (simp add: monofunE)
done

text {* the lub of a chain of continuous functions is continuous *}

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
apply (erule (1) contlub_lub_fun)
done

lemma cont2cont_lub:
  "\<lbrakk>chain F; \<And>i. cont (F i)\<rbrakk> \<Longrightarrow> cont (\<lambda>x. \<Squnion>i. F i x)"
by (simp add: thelub_fun [symmetric] cont_lub_fun)

lemma mono2mono_fun: "monofun f \<Longrightarrow> monofun (\<lambda>x. f x y)"
apply (rule monofunI)
apply (erule (1) monofun_fun_arg [THEN monofun_fun_fun])
done

lemma cont2cont_fun: "cont f \<Longrightarrow> cont (\<lambda>x. f x y)"
apply (rule monocontlub2cont)
apply (erule cont2mono [THEN mono2mono_fun])
apply (rule contlubI)
apply (simp add: cont2contlubE)
apply (simp add: thelub_fun ch2ch_cont)
done

text {* Note @{text "(\<lambda>x. \<lambda>y. f x y) = f"} *}

lemma mono2mono_lambda:
  assumes f: "\<And>y. monofun (\<lambda>x. f x y)" shows "monofun f"
apply (rule monofunI)
apply (rule below_fun_ext)
apply (erule monofunE [OF f])
done

lemma cont2cont_lambda [simp]:
  assumes f: "\<And>y. cont (\<lambda>x. f x y)" shows "cont f"
apply (subgoal_tac "monofun f")
apply (rule monocontlub2cont)
apply assumption
apply (rule contlubI)
apply (rule ext)
apply (simp add: thelub_fun ch2ch_monofun)
apply (erule cont2contlubE [OF f])
apply (simp add: mono2mono_lambda cont2mono f)
done

text {* What D.A.Schmidt calls continuity of abstraction; never used here *}

lemma contlub_lambda:
  "(\<And>x::'a::type. chain (\<lambda>i. S i x::'b::cpo))
    \<Longrightarrow> (\<lambda>x. \<Squnion>i. S i x) = (\<Squnion>i. (\<lambda>x. S i x))"
by (simp add: thelub_fun ch2ch_lambda)

lemma contlub_abstraction:
  "\<lbrakk>chain Y; \<forall>y. cont (\<lambda>x.(c::'a::cpo\<Rightarrow>'b::type\<Rightarrow>'c::cpo) x y)\<rbrakk> \<Longrightarrow>
    (\<lambda>y. \<Squnion>i. c (Y i) y) = (\<Squnion>i. (\<lambda>y. c (Y i) y))"
apply (rule thelub_fun [symmetric])
apply (simp add: ch2ch_cont)
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

end
