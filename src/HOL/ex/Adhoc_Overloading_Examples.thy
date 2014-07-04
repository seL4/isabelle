(*  Title:      HOL/ex/Adhoc_Overloading_Examples.thy
    Author:     Christian Sternagel
*)

header {* Ad Hoc Overloading *}

theory Adhoc_Overloading_Examples
imports
  Main
  "~~/src/Tools/Adhoc_Overloading"
  "~~/src/HOL/Library/Infinite_Set"
begin

text {*Adhoc overloading allows to overload a constant depending on
its type. Typically this involves to introduce an uninterpreted
constant (used for input and output) and then add some variants (used
internally).*}

subsection {* Plain Ad Hoc Overloading *}

text {*Consider the type of first-order terms.*}
datatype ('a, 'b) "term" =
  Var 'b |
  Fun 'a "('a, 'b) term list"

text {*The set of variables of a term might be computed as follows.*}
fun term_vars :: "('a, 'b) term \<Rightarrow> 'b set" where
  "term_vars (Var x) = {x}" |
  "term_vars (Fun f ts) = \<Union>set (map term_vars ts)"

text {*However, also for \emph{rules} (i.e., pairs of terms) and term
rewrite systems (i.e., sets of rules), the set of variables makes
sense. Thus we introduce an unspecified constant @{text vars}.*}

consts vars :: "'a \<Rightarrow> 'b set"

text {*Which is then overloaded with variants for terms, rules, and TRSs.*}
adhoc_overloading
  vars term_vars

value "vars (Fun ''f'' [Var 0, Var 1])"

fun rule_vars :: "('a, 'b) term \<times> ('a, 'b) term \<Rightarrow> 'b set" where
  "rule_vars (l, r) = vars l \<union> vars r"

adhoc_overloading
  vars rule_vars

value "vars (Var 1, Var 0)"

definition trs_vars :: "(('a, 'b) term \<times> ('a, 'b) term) set \<Rightarrow> 'b set" where
  "trs_vars R = \<Union>(rule_vars ` R)"

adhoc_overloading
  vars trs_vars

value "vars {(Var 1, Var 0)}"

text {*Sometimes it is necessary to add explicit type constraints
before a variant can be determined.*}
(*value "vars R" (*has multiple instances*)*)
value "vars (R :: (('a, 'b) term \<times> ('a, 'b) term) set)"

text {*It is also possible to remove variants.*}
no_adhoc_overloading
  vars term_vars rule_vars 

(*value "vars (Var 1)" (*does not have an instance*)*)

text {*As stated earlier, the overloaded constant is only used for
input and output. Internally, always a variant is used, as can be
observed by the configuration option @{text show_variants}.*}

adhoc_overloading
  vars term_vars

declare [[show_variants]]

term "vars (Var 1)" (*which yields: "term_vars (Var 1)"*)


subsection {* Adhoc Overloading inside Locales *}

text {*As example we use permutations that are parametrized over an
atom type @{typ "'a"}.*}

definition perms :: "('a \<Rightarrow> 'a) set" where
  "perms = {f. bij f \<and> finite {x. f x \<noteq> x}}"

typedef 'a perm = "perms :: ('a \<Rightarrow> 'a) set"
  by (default) (auto simp: perms_def)

text {*First we need some auxiliary lemmas.*}
lemma permsI [Pure.intro]:
  assumes "bij f" and "MOST x. f x = x"
  shows "f \<in> perms"
  using assms by (auto simp: perms_def) (metis MOST_iff_finiteNeg)

lemma perms_imp_bij:
  "f \<in> perms \<Longrightarrow> bij f"
  by (simp add: perms_def)

lemma perms_imp_MOST_eq:
  "f \<in> perms \<Longrightarrow> MOST x. f x = x"
  by (simp add: perms_def) (metis MOST_iff_finiteNeg)

lemma id_perms [simp]:
  "id \<in> perms"
  "(\<lambda>x. x) \<in> perms"
  by (auto simp: perms_def bij_def)

lemma perms_comp [simp]:
  assumes f: "f \<in> perms" and g: "g \<in> perms"
  shows "(f \<circ> g) \<in> perms"
  apply (intro permsI bij_comp)
  apply (rule perms_imp_bij [OF g])
  apply (rule perms_imp_bij [OF f])
  apply (rule MOST_rev_mp [OF perms_imp_MOST_eq [OF g]])
  apply (rule MOST_rev_mp [OF perms_imp_MOST_eq [OF f]])
  by simp

lemma perms_inv:
  assumes f: "f \<in> perms"
  shows "inv f \<in> perms"
  apply (rule permsI)
  apply (rule bij_imp_bij_inv)
  apply (rule perms_imp_bij [OF f])
  apply (rule MOST_mono [OF perms_imp_MOST_eq [OF f]])
  apply (erule subst, rule inv_f_f)
  apply (rule bij_is_inj [OF perms_imp_bij [OF f]])
  done

lemma bij_Rep_perm: "bij (Rep_perm p)"
  using Rep_perm [of p] unfolding perms_def by simp

instantiation perm :: (type) group_add
begin

definition "0 = Abs_perm id"
definition "- p = Abs_perm (inv (Rep_perm p))"
definition "p + q = Abs_perm (Rep_perm p \<circ> Rep_perm q)"
definition "(p1::'a perm) - p2 = p1 + - p2"

lemma Rep_perm_0: "Rep_perm 0 = id"
  unfolding zero_perm_def by (simp add: Abs_perm_inverse)

lemma Rep_perm_add:
  "Rep_perm (p1 + p2) = Rep_perm p1 \<circ> Rep_perm p2"
  unfolding plus_perm_def by (simp add: Abs_perm_inverse Rep_perm)

lemma Rep_perm_uminus:
  "Rep_perm (- p) = inv (Rep_perm p)"
  unfolding uminus_perm_def by (simp add: Abs_perm_inverse perms_inv Rep_perm)

instance
  apply default
  unfolding Rep_perm_inject [symmetric]
  unfolding minus_perm_def
  unfolding Rep_perm_add
  unfolding Rep_perm_uminus
  unfolding Rep_perm_0
  by (simp_all add: o_assoc inv_o_cancel [OF bij_is_inj [OF bij_Rep_perm]])

end

lemmas Rep_perm_simps =
  Rep_perm_0
  Rep_perm_add
  Rep_perm_uminus


section {* Permutation Types *}

text {*We want to be able to apply permutations to arbitrary types. To
this end we introduce a constant @{text PERMUTE} together with
convenient infix syntax.*}

consts PERMUTE :: "'a perm \<Rightarrow> 'b \<Rightarrow> 'b" (infixr "\<bullet>" 75)

text {*Then we add a locale for types @{typ 'b} that support
appliciation of permutations.*}
locale permute =
  fixes permute :: "'a perm \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes permute_zero [simp]: "permute 0 x = x"
    and permute_plus [simp]: "permute (p + q) x = permute p (permute q x)"
begin

adhoc_overloading
  PERMUTE permute

end

text {*Permuting atoms.*}
definition permute_atom :: "'a perm \<Rightarrow> 'a \<Rightarrow> 'a" where
  "permute_atom p a = (Rep_perm p) a"

adhoc_overloading
  PERMUTE permute_atom

interpretation atom_permute: permute permute_atom
  by (default) (simp add: permute_atom_def Rep_perm_simps)+

text {*Permuting permutations.*}
definition permute_perm :: "'a perm \<Rightarrow> 'a perm \<Rightarrow> 'a perm" where
  "permute_perm p q = p + q - p"

adhoc_overloading
  PERMUTE permute_perm

interpretation perm_permute: permute permute_perm
  apply default
  unfolding permute_perm_def
  apply simp
  apply (simp only: diff_conv_add_uminus minus_add add.assoc)
  done

text {*Permuting functions.*}
locale fun_permute =
  dom: permute perm1 + ran: permute perm2
  for perm1 :: "'a perm \<Rightarrow> 'b \<Rightarrow> 'b"
  and perm2 :: "'a perm \<Rightarrow> 'c \<Rightarrow> 'c"
begin

adhoc_overloading
  PERMUTE perm1 perm2

definition permute_fun :: "'a perm \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c)" where
  "permute_fun p f = (\<lambda>x. p \<bullet> (f (-p \<bullet> x)))"

adhoc_overloading
  PERMUTE permute_fun

end

sublocale fun_permute \<subseteq> permute permute_fun
  by (unfold_locales, auto simp: permute_fun_def)
     (metis dom.permute_plus minus_add)

lemma "(Abs_perm id :: nat perm) \<bullet> Suc 0 = Suc 0"
  unfolding permute_atom_def
  by (metis Rep_perm_0 id_apply zero_perm_def)

interpretation atom_fun_permute: fun_permute permute_atom permute_atom
  by (unfold_locales)

adhoc_overloading
  PERMUTE atom_fun_permute.permute_fun

lemma "(Abs_perm id :: 'a perm) \<bullet> id = id"
  unfolding atom_fun_permute.permute_fun_def
  unfolding permute_atom_def
  by (metis Rep_perm_0 id_def inj_imp_inv_eq inj_on_id uminus_perm_def zero_perm_def)

end

