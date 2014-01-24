(*  Title:      HOL/BNF_Examples/Lambda_Term.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Lambda-terms.
*)

header {* Lambda-Terms *}

theory Lambda_Term
imports "~~/src/HOL/Library/FSet"
begin

section {* Datatype definition *}

datatype_new 'a trm =
  Var 'a |
  App "'a trm" "'a trm" |
  Lam 'a "'a trm" |
  Lt "('a \<times> 'a trm) fset" "'a trm"


subsection {* Example: The set of all variables varsOf and free variables fvarsOf of a term *}

primrec_new varsOf :: "'a trm \<Rightarrow> 'a set" where
  "varsOf (Var a) = {a}"
| "varsOf (App f x) = varsOf f \<union> varsOf x"
| "varsOf (Lam x b) = {x} \<union> varsOf b"
| "varsOf (Lt F t) = varsOf t \<union> (\<Union> { {x} \<union> X | x X. (x,X) |\<in>| fimage (map_pair id varsOf) F})"

primrec_new fvarsOf :: "'a trm \<Rightarrow> 'a set" where
  "fvarsOf (Var x) = {x}"
| "fvarsOf (App t1 t2) = fvarsOf t1 \<union> fvarsOf t2"
| "fvarsOf (Lam x t) = fvarsOf t - {x}"
| "fvarsOf (Lt xts t) = fvarsOf t - {x | x X. (x,X) |\<in>| fimage (map_pair id varsOf) xts} \<union>
    (\<Union> {X | x X. (x,X) |\<in>| fimage (map_pair id varsOf) xts})"

lemma diff_Un_incl_triv: "\<lbrakk>A \<subseteq> D; C \<subseteq> E\<rbrakk> \<Longrightarrow> A - B \<union> C \<subseteq> D \<union> E" by blast

lemma in_fimage_map_pair_fset_iff[simp]:
  "(x, y) |\<in>| fimage (map_pair f g) xts \<longleftrightarrow> (\<exists> t1 t2. (t1, t2) |\<in>| xts \<and> x = f t1 \<and> y = g t2)"
  by force

lemma fvarsOf_varsOf: "fvarsOf t \<subseteq> varsOf t"
proof induct
  case (Lt xts t) thus ?case unfolding fvarsOf.simps varsOf.simps by (elim diff_Un_incl_triv) auto
qed auto

end
