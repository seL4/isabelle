(*  Title:      HOL/Transitive_Closure.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Relfexive and Transitive closure of a relation

rtrancl is reflexive/transitive closure;
trancl  is transitive closure
reflcl  is reflexive closure

These postfix operators have MAXIMUM PRIORITY, forcing their operands
to be atomic.
*)

theory Transitive_Closure = Lfp + Relation
files ("Transitive_Closure_lemmas.ML"):

constdefs
  rtrancl :: "('a * 'a) set => ('a * 'a) set"    ("(_^*)" [1000] 999)
  "r^* == lfp (%s. Id Un (r O s))"

  trancl :: "('a * 'a) set => ('a * 'a) set"    ("(_^+)" [1000] 999)
  "r^+ ==  r O rtrancl r"

syntax
  "_reflcl" :: "('a * 'a) set => ('a * 'a) set"    ("(_^=)" [1000] 999)
translations
  "r^=" == "r Un Id"

syntax (xsymbols)
  rtrancl :: "('a * 'a) set => ('a * 'a) set"    ("(_\\<^sup>*)" [1000] 999)
  trancl :: "('a * 'a) set => ('a * 'a) set"    ("(_\\<^sup>+)" [1000] 999)
  "_reflcl" :: "('a * 'a) set => ('a * 'a) set"    ("(_\\<^sup>=)" [1000] 999)

use "Transitive_Closure_lemmas.ML"


lemma reflcl_trancl[simp]: "(r\<^sup>+)\<^sup>= = r\<^sup>*"
apply safe;
apply (erule trancl_into_rtrancl);
by (blast elim:rtranclE dest:rtrancl_into_trancl1)

lemma trancl_reflcl[simp]: "(r\<^sup>=)\<^sup>+ = r\<^sup>*"
apply safe
 apply (drule trancl_into_rtrancl)
 apply simp;
apply (erule rtranclE)
 apply safe
 apply(rule r_into_trancl)
 apply simp
apply(rule rtrancl_into_trancl1)
 apply(erule rtrancl_reflcl[THEN equalityD2, THEN subsetD])
apply fast
done

lemma trancl_empty[simp]: "{}\<^sup>+ = {}"
by (auto elim:trancl_induct)

lemma rtrancl_empty[simp]: "{}\<^sup>* = Id"
by(rule subst[OF reflcl_trancl], simp)

lemma rtranclD: "(a,b) \<in> R\<^sup>* \<Longrightarrow> a=b \<or> a\<noteq>b \<and> (a,b) \<in> R\<^sup>+"
by(force simp add: reflcl_trancl[THEN sym] simp del: reflcl_trancl)

(* should be merged with the main body of lemmas: *)

lemma Domain_rtrancl[simp]: "Domain(R\<^sup>*) = UNIV"
by blast

lemma Range_rtrancl[simp]: "Range(R\<^sup>*) = UNIV"
by blast

lemma rtrancl_Un_subset: "(R\<^sup>* \<union> S\<^sup>*) \<subseteq> (R Un S)\<^sup>*"
by(rule rtrancl_Un_rtrancl[THEN subst], fast)

lemma in_rtrancl_UnI: "x \<in> R\<^sup>* \<or> x \<in> S\<^sup>* \<Longrightarrow> x \<in> (R \<union> S)\<^sup>*"
by (blast intro: subsetD[OF rtrancl_Un_subset])

lemma trancl_domain [simp]: "Domain (r\<^sup>+) = Domain r"
by (unfold Domain_def, blast dest:tranclD)

lemma trancl_range [simp]: "Range (r\<^sup>+) = Range r"
by (simp add:Range_def trancl_converse[THEN sym])

end
