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

theory Transitive_Closure = Inductive
files ("Transitive_Closure_lemmas.ML"):

consts
  rtrancl :: "('a * 'a) set => ('a * 'a) set"    ("(_^*)" [1000] 999)

inductive "r^*"
intros
  rtrancl_refl [intro!, simp]: "(a, a) : r^*"
  rtrancl_into_rtrancl:        "[| (a,b) : r^*; (b,c) : r |] ==> (a,c) : r^*"

constdefs
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


lemma reflcl_trancl [simp]: "(r^+)^= = r^*"
  apply safe
  apply (erule trancl_into_rtrancl)
  apply (blast elim: rtranclE dest: rtrancl_into_trancl1)
  done

lemma trancl_reflcl [simp]: "(r^=)^+ = r^*"
  apply safe
   apply (drule trancl_into_rtrancl)
   apply simp
  apply (erule rtranclE)
   apply safe
   apply (rule r_into_trancl)
   apply simp
  apply (rule rtrancl_into_trancl1)
   apply (erule rtrancl_reflcl [THEN equalityD2, THEN subsetD])
  apply fast
  done

lemma trancl_empty [simp]: "{}^+ = {}"
  by (auto elim: trancl_induct)

lemma rtrancl_empty [simp]: "{}^* = Id"
  by (rule subst [OF reflcl_trancl]) simp

lemma rtranclD: "(a, b) \<in> R^* ==> a = b \<or> a \<noteq> b \<and> (a, b) \<in> R^+"
  by (force simp add: reflcl_trancl [symmetric] simp del: reflcl_trancl)


(* should be merged with the main body of lemmas: *)

lemma Domain_rtrancl [simp]: "Domain (R^*) = UNIV"
  by blast

lemma Range_rtrancl [simp]: "Range (R^*) = UNIV"
  by blast

lemma rtrancl_Un_subset: "(R^* \<union> S^*) \<subseteq> (R Un S)^*"
  by (rule rtrancl_Un_rtrancl [THEN subst]) fast

lemma in_rtrancl_UnI: "x \<in> R^* \<or> x \<in> S^* ==> x \<in> (R \<union> S)^*"
  by (blast intro: subsetD [OF rtrancl_Un_subset])

lemma trancl_domain [simp]: "Domain (r^+) = Domain r"
  by (unfold Domain_def) (blast dest: tranclD)

lemma trancl_range [simp]: "Range (r^+) = Range r"
  by (simp add: Range_def trancl_converse [symmetric])

lemma Not_Domain_rtrancl:
	"x ~: Domain R ==> ((x, y) : R^*) = (x = y)"
 apply (auto)
 by (erule rev_mp, erule rtrancl_induct, auto)

(* more about converse rtrancl and trancl, should be merged with main body *)

lemma converse_rtrancl_into_rtrancl: "(a,b) \<in> R \<Longrightarrow> (b,c) \<in> R^* \<Longrightarrow> (a,c) \<in> R^*"
  by (erule rtrancl_induct) (fast intro: rtrancl_into_rtrancl)+

lemma r_r_into_trancl: "(a,b) \<in> R \<Longrightarrow> (b,c) \<in> R \<Longrightarrow> (a,c) \<in> R^+"
  by (fast intro: trancl_trans)

lemma trancl_into_trancl [rule_format]:
  "(a,b) \<in> r\<^sup>+ \<Longrightarrow> (b,c) \<in> r \<longrightarrow> (a,c) \<in> r\<^sup>+"
  apply (erule trancl_induct)   
   apply (fast intro: r_r_into_trancl)
  apply (fast intro: r_r_into_trancl trancl_trans)
  done

lemma trancl_rtrancl_trancl:
  "(a,b) \<in> r\<^sup>+ \<Longrightarrow> (b,c) \<in> r\<^sup>* \<Longrightarrow> (a,c) \<in> r\<^sup>+"
  apply (drule tranclD)
  apply (erule exE, erule conjE)
  apply (drule rtrancl_trans, assumption)
  apply (drule rtrancl_into_trancl2, assumption)
  apply assumption
  done

lemmas [trans] = r_r_into_trancl trancl_trans rtrancl_trans 
                 trancl_into_trancl trancl_into_trancl2
                 rtrancl_into_rtrancl converse_rtrancl_into_rtrancl
                 rtrancl_trancl_trancl trancl_rtrancl_trancl

declare trancl_into_rtrancl [elim]

declare rtrancl_induct [induct set: rtrancl]
declare rtranclE [cases set: rtrancl]
declare trancl_induct [induct set: trancl]
declare tranclE [cases set: trancl]

end
