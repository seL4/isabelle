(* Title:    HOL/Partial_Function.thy
   Author:   Alexander Krauss, TU Muenchen
*)

header {* Partial Function Definitions *}

theory Partial_Function
imports Complete_Partial_Order Option
keywords "partial_function" :: thy_decl
uses 
  "Tools/Function/function_lib.ML" 
  "Tools/Function/partial_function.ML" 
begin

setup Partial_Function.setup

subsection {* Axiomatic setup *}

text {* This techical locale constains the requirements for function
  definitions with ccpo fixed points. *}

definition "fun_ord ord f g \<longleftrightarrow> (\<forall>x. ord (f x) (g x))"
definition "fun_lub L A = (\<lambda>x. L {y. \<exists>f\<in>A. y = f x})"
definition "img_ord f ord = (\<lambda>x y. ord (f x) (f y))"
definition "img_lub f g Lub = (\<lambda>A. g (Lub (f ` A)))"

lemma chain_fun: 
  assumes A: "chain (fun_ord ord) A"
  shows "chain ord {y. \<exists>f\<in>A. y = f a}" (is "chain ord ?C")
proof (rule chainI)
  fix x y assume "x \<in> ?C" "y \<in> ?C"
  then obtain f g where fg: "f \<in> A" "g \<in> A" 
    and [simp]: "x = f a" "y = g a" by blast
  from chainD[OF A fg]
  show "ord x y \<or> ord y x" unfolding fun_ord_def by auto
qed

lemma call_mono[partial_function_mono]: "monotone (fun_ord ord) ord (\<lambda>f. f t)"
by (rule monotoneI) (auto simp: fun_ord_def)

lemma let_mono[partial_function_mono]:
  "(\<And>x. monotone orda ordb (\<lambda>f. b f x))
  \<Longrightarrow> monotone orda ordb (\<lambda>f. Let t (b f))"
by (simp add: Let_def)

lemma if_mono[partial_function_mono]: "monotone orda ordb F 
\<Longrightarrow> monotone orda ordb G
\<Longrightarrow> monotone orda ordb (\<lambda>f. if c then F f else G f)"
unfolding monotone_def by simp

definition "mk_less R = (\<lambda>x y. R x y \<and> \<not> R y x)"

locale partial_function_definitions = 
  fixes leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes lub :: "'a set \<Rightarrow> 'a"
  assumes leq_refl: "leq x x"
  assumes leq_trans: "leq x y \<Longrightarrow> leq y z \<Longrightarrow> leq x z"
  assumes leq_antisym: "leq x y \<Longrightarrow> leq y x \<Longrightarrow> x = y"
  assumes lub_upper: "chain leq A \<Longrightarrow> x \<in> A \<Longrightarrow> leq x (lub A)"
  assumes lub_least: "chain leq A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> leq x z) \<Longrightarrow> leq (lub A) z"

lemma partial_function_lift:
  assumes "partial_function_definitions ord lb"
  shows "partial_function_definitions (fun_ord ord) (fun_lub lb)" (is "partial_function_definitions ?ordf ?lubf")
proof -
  interpret partial_function_definitions ord lb by fact

  show ?thesis
  proof
    fix x show "?ordf x x"
      unfolding fun_ord_def by (auto simp: leq_refl)
  next
    fix x y z assume "?ordf x y" "?ordf y z"
    thus "?ordf x z" unfolding fun_ord_def 
      by (force dest: leq_trans)
  next
    fix x y assume "?ordf x y" "?ordf y x"
    thus "x = y" unfolding fun_ord_def
      by (force intro!: dest: leq_antisym)
  next
    fix A f assume f: "f \<in> A" and A: "chain ?ordf A"
    thus "?ordf f (?lubf A)"
      unfolding fun_lub_def fun_ord_def
      by (blast intro: lub_upper chain_fun[OF A] f)
  next
    fix A :: "('b \<Rightarrow> 'a) set" and g :: "'b \<Rightarrow> 'a"
    assume A: "chain ?ordf A" and g: "\<And>f. f \<in> A \<Longrightarrow> ?ordf f g"
    show "?ordf (?lubf A) g" unfolding fun_lub_def fun_ord_def
      by (blast intro: lub_least chain_fun[OF A] dest: g[unfolded fun_ord_def])
   qed
qed

lemma ccpo: assumes "partial_function_definitions ord lb"
  shows "class.ccpo lb ord (mk_less ord)"
using assms unfolding partial_function_definitions_def mk_less_def
by unfold_locales blast+

lemma partial_function_image:
  assumes "partial_function_definitions ord Lub"
  assumes inj: "\<And>x y. f x = f y \<Longrightarrow> x = y"
  assumes inv: "\<And>x. f (g x) = x"
  shows "partial_function_definitions (img_ord f ord) (img_lub f g Lub)"
proof -
  let ?iord = "img_ord f ord"
  let ?ilub = "img_lub f g Lub"

  interpret partial_function_definitions ord Lub by fact
  show ?thesis
  proof
    fix A x assume "chain ?iord A" "x \<in> A"
    then have "chain ord (f ` A)" "f x \<in> f ` A"
      by (auto simp: img_ord_def intro: chainI dest: chainD)
    thus "?iord x (?ilub A)"
      unfolding inv img_lub_def img_ord_def by (rule lub_upper)
  next
    fix A x assume "chain ?iord A"
      and 1: "\<And>z. z \<in> A \<Longrightarrow> ?iord z x"
    then have "chain ord (f ` A)"
      by (auto simp: img_ord_def intro: chainI dest: chainD)
    thus "?iord (?ilub A) x"
      unfolding inv img_lub_def img_ord_def
      by (rule lub_least) (auto dest: 1[unfolded img_ord_def])
  qed (auto simp: img_ord_def intro: leq_refl dest: leq_trans leq_antisym inj)
qed

context partial_function_definitions
begin

abbreviation "le_fun \<equiv> fun_ord leq"
abbreviation "lub_fun \<equiv> fun_lub lub"
abbreviation "fixp_fun \<equiv> ccpo.fixp lub_fun le_fun"
abbreviation "mono_body \<equiv> monotone le_fun leq"
abbreviation "admissible \<equiv> ccpo.admissible lub_fun le_fun"

text {* Interpret manually, to avoid flooding everything with facts about
  orders *}

lemma ccpo: "class.ccpo lub_fun le_fun (mk_less le_fun)"
apply (rule ccpo)
apply (rule partial_function_lift)
apply (rule partial_function_definitions_axioms)
done

text {* The crucial fixed-point theorem *}

lemma mono_body_fixp: 
  "(\<And>x. mono_body (\<lambda>f. F f x)) \<Longrightarrow> fixp_fun F = F (fixp_fun F)"
by (rule ccpo.fixp_unfold[OF ccpo]) (auto simp: monotone_def fun_ord_def)

text {* Version with curry/uncurry combinators, to be used by package *}

lemma fixp_rule_uc:
  fixes F :: "'c \<Rightarrow> 'c" and
    U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a" and
    C :: "('b \<Rightarrow> 'a) \<Rightarrow> 'c"
  assumes mono: "\<And>x. mono_body (\<lambda>f. U (F (C f)) x)"
  assumes eq: "f \<equiv> C (fixp_fun (\<lambda>f. U (F (C f))))"
  assumes inverse: "\<And>f. C (U f) = f"
  shows "f = F f"
proof -
  have "f = C (fixp_fun (\<lambda>f. U (F (C f))))" by (simp add: eq)
  also have "... = C (U (F (C (fixp_fun (\<lambda>f. U (F (C f)))))))"
    by (subst mono_body_fixp[of "%f. U (F (C f))", OF mono]) (rule refl)
  also have "... = F (C (fixp_fun (\<lambda>f. U (F (C f)))))" by (rule inverse)
  also have "... = F f" by (simp add: eq)
  finally show "f = F f" .
qed

text {* Fixpoint induction rule *}

lemma fixp_induct_uc:
  fixes F :: "'c \<Rightarrow> 'c" and
    U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a" and
    C :: "('b \<Rightarrow> 'a) \<Rightarrow> 'c" and
    P :: "('b \<Rightarrow> 'a) \<Rightarrow> bool"
  assumes mono: "\<And>x. mono_body (\<lambda>f. U (F (C f)) x)"
  assumes eq: "f \<equiv> C (fixp_fun (\<lambda>f. U (F (C f))))"
  assumes inverse: "\<And>f. U (C f) = f"
  assumes adm: "ccpo.admissible lub_fun le_fun P"
  assumes step: "\<And>f. P (U f) \<Longrightarrow> P (U (F f))"
  shows "P (U f)"
unfolding eq inverse
apply (rule ccpo.fixp_induct[OF ccpo adm])
apply (insert mono, auto simp: monotone_def fun_ord_def)[1]
by (rule_tac f="C x" in step, simp add: inverse)


text {* Rules for @{term mono_body}: *}

lemma const_mono[partial_function_mono]: "monotone ord leq (\<lambda>f. c)"
by (rule monotoneI) (rule leq_refl)

end


subsection {* Flat interpretation: tailrec and option *}

definition 
  "flat_ord b x y \<longleftrightarrow> x = b \<or> x = y"

definition 
  "flat_lub b A = (if A \<subseteq> {b} then b else (THE x. x \<in> A - {b}))"

lemma flat_interpretation:
  "partial_function_definitions (flat_ord b) (flat_lub b)"
proof
  fix A x assume 1: "chain (flat_ord b) A" "x \<in> A"
  show "flat_ord b x (flat_lub b A)"
  proof cases
    assume "x = b"
    thus ?thesis by (simp add: flat_ord_def)
  next
    assume "x \<noteq> b"
    with 1 have "A - {b} = {x}"
      by (auto elim: chainE simp: flat_ord_def)
    then have "flat_lub b A = x"
      by (auto simp: flat_lub_def)
    thus ?thesis by (auto simp: flat_ord_def)
  qed
next
  fix A z assume A: "chain (flat_ord b) A"
    and z: "\<And>x. x \<in> A \<Longrightarrow> flat_ord b x z"
  show "flat_ord b (flat_lub b A) z"
  proof cases
    assume "A \<subseteq> {b}"
    thus ?thesis
      by (auto simp: flat_lub_def flat_ord_def)
  next
    assume nb: "\<not> A \<subseteq> {b}"
    then obtain y where y: "y \<in> A" "y \<noteq> b" by auto
    with A have "A - {b} = {y}"
      by (auto elim: chainE simp: flat_ord_def)
    with nb have "flat_lub b A = y"
      by (auto simp: flat_lub_def)
    with z y show ?thesis by auto    
  qed
qed (auto simp: flat_ord_def)

interpretation tailrec!:
  partial_function_definitions "flat_ord undefined" "flat_lub undefined"
by (rule flat_interpretation)

interpretation option!:
  partial_function_definitions "flat_ord None" "flat_lub None"
by (rule flat_interpretation)


abbreviation "option_ord \<equiv> flat_ord None"
abbreviation "mono_option \<equiv> monotone (fun_ord option_ord) option_ord"

lemma bind_mono[partial_function_mono]:
assumes mf: "mono_option B" and mg: "\<And>y. mono_option (\<lambda>f. C y f)"
shows "mono_option (\<lambda>f. Option.bind (B f) (\<lambda>y. C y f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b option" assume fg: "fun_ord option_ord f g"
  with mf
  have "option_ord (B f) (B g)" by (rule monotoneD[of _ _ _ f g])
  then have "option_ord (Option.bind (B f) (\<lambda>y. C y f)) (Option.bind (B g) (\<lambda>y. C y f))"
    unfolding flat_ord_def by auto    
  also from mg
  have "\<And>y'. option_ord (C y' f) (C y' g)"
    by (rule monotoneD) (rule fg)
  then have "option_ord (Option.bind (B g) (\<lambda>y'. C y' f)) (Option.bind (B g) (\<lambda>y'. C y' g))"
    unfolding flat_ord_def by (cases "B g") auto
  finally (option.leq_trans)
  show "option_ord (Option.bind (B f) (\<lambda>y. C y f)) (Option.bind (B g) (\<lambda>y'. C y' g))" .
qed

lemma flat_lub_in_chain:
  assumes ch: "chain (flat_ord b) A "
  assumes lub: "flat_lub b A = a"
  shows "a = b \<or> a \<in> A"
proof (cases "A \<subseteq> {b}")
  case True
  then have "flat_lub b A = b" unfolding flat_lub_def by simp
  with lub show ?thesis by simp
next
  case False
  then obtain c where "c \<in> A" and "c \<noteq> b" by auto
  { fix z assume "z \<in> A"
    from chainD[OF ch `c \<in> A` this] have "z = c \<or> z = b"
      unfolding flat_ord_def using `c \<noteq> b` by auto }
  with False have "A - {b} = {c}" by auto
  with False have "flat_lub b A = c" by (auto simp: flat_lub_def)
  with `c \<in> A` lub show ?thesis by simp
qed

lemma option_admissible: "option.admissible (%(f::'a \<Rightarrow> 'b option).
  (\<forall>x y. f x = Some y \<longrightarrow> P x y))"
proof (rule ccpo.admissibleI[OF option.ccpo])
  fix A :: "('a \<Rightarrow> 'b option) set"
  assume ch: "chain option.le_fun A"
    and IH: "\<forall>f\<in>A. \<forall>x y. f x = Some y \<longrightarrow> P x y"
  from ch have ch': "\<And>x. chain option_ord {y. \<exists>f\<in>A. y = f x}" by (rule chain_fun)
  show "\<forall>x y. option.lub_fun A x = Some y \<longrightarrow> P x y"
  proof (intro allI impI)
    fix x y assume "option.lub_fun A x = Some y"
    from flat_lub_in_chain[OF ch' this[unfolded fun_lub_def]]
    have "Some y \<in> {y. \<exists>f\<in>A. y = f x}" by simp
    then have "\<exists>f\<in>A. f x = Some y" by auto
    with IH show "P x y" by auto
  qed
qed

lemma fixp_induct_option:
  fixes F :: "'c \<Rightarrow> 'c" and
    U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a option" and
    C :: "('b \<Rightarrow> 'a option) \<Rightarrow> 'c" and
    P :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono: "\<And>x. mono_option (\<lambda>f. U (F (C f)) x)"
  assumes eq: "f \<equiv> C (ccpo.fixp (fun_lub (flat_lub None)) (fun_ord option_ord) (\<lambda>f. U (F (C f))))"
  assumes inverse2: "\<And>f. U (C f) = f"
  assumes step: "\<And>f x y. (\<And>x y. U f x = Some y \<Longrightarrow> P x y) \<Longrightarrow> U (F f) x = Some y \<Longrightarrow> P x y"
  assumes defined: "U f x = Some y"
  shows "P x y"
  using step defined option.fixp_induct_uc[of U F C, OF mono eq inverse2 option_admissible]
  by blast

declaration {* Partial_Function.init "tailrec" @{term tailrec.fixp_fun}
  @{term tailrec.mono_body} @{thm tailrec.fixp_rule_uc} NONE *}

declaration {* Partial_Function.init "option" @{term option.fixp_fun}
  @{term option.mono_body} @{thm option.fixp_rule_uc} 
  (SOME @{thm fixp_induct_option}) *}


hide_const (open) chain

end
