(*  Title:      HOL/Transitive_Closure.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* Reflexive and Transitive closure of a relation *}

theory Transitive_Closure = Inductive:

text {*
  @{text rtrancl} is reflexive/transitive closure,
  @{text trancl} is transitive closure,
  @{text reflcl} is reflexive closure.

  These postfix operators have \emph{maximum priority}, forcing their
  operands to be atomic.
*}

consts
  rtrancl :: "('a \<times> 'a) set => ('a \<times> 'a) set"    ("(_^*)" [1000] 999)

inductive "r^*"
  intros
    rtrancl_refl [intro!, CPure.intro!, simp]: "(a, a) : r^*"
    rtrancl_into_rtrancl [CPure.intro]: "(a, b) : r^* ==> (b, c) : r ==> (a, c) : r^*"

consts
  trancl :: "('a \<times> 'a) set => ('a \<times> 'a) set"    ("(_^+)" [1000] 999)

inductive "r^+"
  intros
    r_into_trancl [intro, CPure.intro]: "(a, b) : r ==> (a, b) : r^+"
    trancl_into_trancl [CPure.intro]: "(a, b) : r^+ ==> (b, c) : r ==> (a,c) : r^+"

syntax
  "_reflcl" :: "('a \<times> 'a) set => ('a \<times> 'a) set"    ("(_^=)" [1000] 999)
translations
  "r^=" == "r \<union> Id"

syntax (xsymbols)
  rtrancl :: "('a \<times> 'a) set => ('a \<times> 'a) set"    ("(_\\<^sup>*)" [1000] 999)
  trancl :: "('a \<times> 'a) set => ('a \<times> 'a) set"    ("(_\\<^sup>+)" [1000] 999)
  "_reflcl" :: "('a \<times> 'a) set => ('a \<times> 'a) set"    ("(_\\<^sup>=)" [1000] 999)


subsection {* Reflexive-transitive closure *}

lemma r_into_rtrancl [intro]: "!!p. p \<in> r ==> p \<in> r^*"
  -- {* @{text rtrancl} of @{text r} contains @{text r} *}
  apply (simp only: split_tupled_all)
  apply (erule rtrancl_refl [THEN rtrancl_into_rtrancl])
  done

lemma rtrancl_mono: "r \<subseteq> s ==> r^* \<subseteq> s^*"
  -- {* monotonicity of @{text rtrancl} *}
  apply (rule subsetI)
  apply (simp only: split_tupled_all)
  apply (erule rtrancl.induct)
   apply (rule_tac [2] rtrancl_into_rtrancl)
    apply blast+
  done

theorem rtrancl_induct [consumes 1, induct set: rtrancl]:
  assumes a: "(a, b) : r^*"
    and cases: "P a" "!!y z. [| (a, y) : r^*; (y, z) : r; P y |] ==> P z"
  shows "P b"
proof -
  from a have "a = a --> P b"
    by (induct "%x y. x = a --> P y" a b) (rules intro: cases)+
  thus ?thesis by rules
qed

ML_setup {*
  bind_thm ("rtrancl_induct2", split_rule
    (read_instantiate [("a","(ax,ay)"), ("b","(bx,by)")] (thm "rtrancl_induct")));
*}

lemma trans_rtrancl: "trans(r^*)"
  -- {* transitivity of transitive closure!! -- by induction *}
proof (rule transI)
  fix x y z
  assume "(x, y) \<in> r\<^sup>*"
  assume "(y, z) \<in> r\<^sup>*"
  thus "(x, z) \<in> r\<^sup>*" by induct (rules!)+
qed

lemmas rtrancl_trans = trans_rtrancl [THEN transD, standard]

lemma rtranclE:
  "[| (a::'a,b) : r^*;  (a = b) ==> P;
      !!y.[| (a,y) : r^*; (y,b) : r |] ==> P
   |] ==> P"
  -- {* elimination of @{text rtrancl} -- by induction on a special formula *}
proof -
  assume major: "(a::'a,b) : r^*"
  case rule_context
  show ?thesis
    apply (subgoal_tac "(a::'a) = b | (EX y. (a,y) : r^* & (y,b) : r)")
     apply (rule_tac [2] major [THEN rtrancl_induct])
      prefer 2 apply (blast!)
      prefer 2 apply (blast!)
    apply (erule asm_rl exE disjE conjE prems)+
    done
qed

lemma converse_rtrancl_into_rtrancl:
  "(a, b) \<in> r \<Longrightarrow> (b, c) \<in> r\<^sup>* \<Longrightarrow> (a, c) \<in> r\<^sup>*"
  by (rule rtrancl_trans) rules+

text {*
  \medskip More @{term "r^*"} equations and inclusions.
*}

lemma rtrancl_idemp [simp]: "(r^*)^* = r^*"
  apply auto
  apply (erule rtrancl_induct)
   apply (rule rtrancl_refl)
  apply (blast intro: rtrancl_trans)
  done

lemma rtrancl_idemp_self_comp [simp]: "R^* O R^* = R^*"
  apply (rule set_ext)
  apply (simp only: split_tupled_all)
  apply (blast intro: rtrancl_trans)
  done

lemma rtrancl_subset_rtrancl: "r \<subseteq> s^* ==> r^* \<subseteq> s^*"
  apply (drule rtrancl_mono)
  apply simp
  done

lemma rtrancl_subset: "R \<subseteq> S ==> S \<subseteq> R^* ==> S^* = R^*"
  apply (drule rtrancl_mono)
  apply (drule rtrancl_mono)
  apply simp
  apply blast
  done

lemma rtrancl_Un_rtrancl: "(R^* \<union> S^*)^* = (R \<union> S)^*"
  by (blast intro!: rtrancl_subset intro: r_into_rtrancl rtrancl_mono [THEN subsetD])

lemma rtrancl_reflcl [simp]: "(R^=)^* = R^*"
  by (blast intro!: rtrancl_subset intro: r_into_rtrancl)

lemma rtrancl_r_diff_Id: "(r - Id)^* = r^*"
  apply (rule sym)
  apply (rule rtrancl_subset)
   apply blast
  apply clarify
  apply (rename_tac a b)
  apply (case_tac "a = b")
   apply blast
  apply (blast intro!: r_into_rtrancl)
  done

theorem rtrancl_converseD:
  assumes r: "(x, y) \<in> (r^-1)^*"
  shows "(y, x) \<in> r^*"
proof -
  from r show ?thesis
    by induct (rules intro: rtrancl_trans dest!: converseD)+
qed

theorem rtrancl_converseI:
  assumes r: "(y, x) \<in> r^*"
  shows "(x, y) \<in> (r^-1)^*"
proof -
  from r show ?thesis
    by induct (rules intro: rtrancl_trans converseI)+
qed

lemma rtrancl_converse: "(r^-1)^* = (r^*)^-1"
  by (fast dest!: rtrancl_converseD intro!: rtrancl_converseI)

theorem converse_rtrancl_induct:
  assumes major: "(a, b) : r^*"
    and cases: "P b" "!!y z. [| (y, z) : r; (z, b) : r^*; P z |] ==> P y"
  shows "P a"
proof -
  from rtrancl_converseI [OF major]
  show ?thesis
    by induct (rules intro: cases dest!: converseD rtrancl_converseD)+
qed

ML_setup {*
  bind_thm ("converse_rtrancl_induct2", split_rule
    (read_instantiate [("a","(ax,ay)"),("b","(bx,by)")] (thm "converse_rtrancl_induct")));
*}

lemma converse_rtranclE:
  "[| (x,z):r^*;
      x=z ==> P;
      !!y. [| (x,y):r; (y,z):r^* |] ==> P
   |] ==> P"
proof -
  assume major: "(x,z):r^*"
  case rule_context
  show ?thesis
    apply (subgoal_tac "x = z | (EX y. (x,y) : r & (y,z) : r^*)")
     apply (rule_tac [2] major [THEN converse_rtrancl_induct])
      prefer 2 apply rules
     prefer 2 apply rules
    apply (erule asm_rl exE disjE conjE prems)+
    done
qed

ML_setup {*
  bind_thm ("converse_rtranclE2", split_rule
    (read_instantiate [("x","(xa,xb)"), ("z","(za,zb)")] (thm "converse_rtranclE")));
*}

lemma r_comp_rtrancl_eq: "r O r^* = r^* O r"
  by (blast elim: rtranclE converse_rtranclE
    intro: rtrancl_into_rtrancl converse_rtrancl_into_rtrancl)


subsection {* Transitive closure *}

lemma trancl_mono: "!!p. p \<in> r^+ ==> r \<subseteq> s ==> p \<in> s^+"
  apply (simp only: split_tupled_all)
  apply (erule trancl.induct)
  apply (rules dest: subsetD)+
  done

lemma r_into_trancl': "!!p. p : r ==> p : r^+"
  by (simp only: split_tupled_all) (erule r_into_trancl)

text {*
  \medskip Conversions between @{text trancl} and @{text rtrancl}.
*}

lemma trancl_into_rtrancl: "(a, b) \<in> r^+ ==> (a, b) \<in> r^*"
  by (erule trancl.induct) rules+

lemma rtrancl_into_trancl1: assumes r: "(a, b) \<in> r^*"
  shows "!!c. (b, c) \<in> r ==> (a, c) \<in> r^+" using r
  by induct rules+

lemma rtrancl_into_trancl2: "[| (a,b) : r;  (b,c) : r^* |]   ==>  (a,c) : r^+"
  -- {* intro rule from @{text r} and @{text rtrancl} *}
  apply (erule rtranclE)
   apply rules
  apply (rule rtrancl_trans [THEN rtrancl_into_trancl1])
   apply (assumption | rule r_into_rtrancl)+
  done

lemma trancl_induct [consumes 1, induct set: trancl]:
  assumes a: "(a,b) : r^+"
  and cases: "!!y. (a, y) : r ==> P y"
    "!!y z. (a,y) : r^+ ==> (y, z) : r ==> P y ==> P z"
  shows "P b"
  -- {* Nice induction rule for @{text trancl} *}
proof -
  from a have "a = a --> P b"
    by (induct "%x y. x = a --> P y" a b) (rules intro: cases)+
  thus ?thesis by rules
qed

lemma trancl_trans_induct:
  "[| (x,y) : r^+;
      !!x y. (x,y) : r ==> P x y;
      !!x y z. [| (x,y) : r^+; P x y; (y,z) : r^+; P y z |] ==> P x z
   |] ==> P x y"
  -- {* Another induction rule for trancl, incorporating transitivity *}
proof -
  assume major: "(x,y) : r^+"
  case rule_context
  show ?thesis
    by (rules intro: r_into_trancl major [THEN trancl_induct] prems)
qed

inductive_cases tranclE: "(a, b) : r^+"

lemma trans_trancl: "trans(r^+)"
  -- {* Transitivity of @{term "r^+"} *}
proof (rule transI)
  fix x y z
  assume "(x, y) \<in> r^+"
  assume "(y, z) \<in> r^+"
  thus "(x, z) \<in> r^+" by induct (rules!)+
qed

lemmas trancl_trans = trans_trancl [THEN transD, standard]

lemma rtrancl_trancl_trancl: assumes r: "(x, y) \<in> r^*"
  shows "!!z. (y, z) \<in> r^+ ==> (x, z) \<in> r^+" using r
  by induct (rules intro: trancl_trans)+

lemma trancl_into_trancl2: "(a, b) \<in> r ==> (b, c) \<in> r^+ ==> (a, c) \<in> r^+"
  by (erule transD [OF trans_trancl r_into_trancl])

lemma trancl_insert:
  "(insert (y, x) r)^+ = r^+ \<union> {(a, b). (a, y) \<in> r^* \<and> (x, b) \<in> r^*}"
  -- {* primitive recursion for @{text trancl} over finite relations *}
  apply (rule equalityI)
   apply (rule subsetI)
   apply (simp only: split_tupled_all)
   apply (erule trancl_induct)
    apply blast
   apply (blast intro: rtrancl_into_trancl1 trancl_into_rtrancl r_into_trancl trancl_trans)
  apply (rule subsetI)
  apply (blast intro: trancl_mono rtrancl_mono
    [THEN [2] rev_subsetD] rtrancl_trancl_trancl rtrancl_into_trancl2)
  done

lemma trancl_converseI: "(x, y) \<in> (r^+)^-1 ==> (x, y) \<in> (r^-1)^+"
  apply (drule converseD)
  apply (erule trancl.induct)
  apply (rules intro: converseI trancl_trans)+
  done

lemma trancl_converseD: "(x, y) \<in> (r^-1)^+ ==> (x, y) \<in> (r^+)^-1"
  apply (rule converseI)
  apply (erule trancl.induct)
  apply (rules dest: converseD intro: trancl_trans)+
  done

lemma trancl_converse: "(r^-1)^+ = (r^+)^-1"
  by (fastsimp simp add: split_tupled_all
    intro!: trancl_converseI trancl_converseD)

lemma converse_trancl_induct:
  "[| (a,b) : r^+; !!y. (y,b) : r ==> P(y);
      !!y z.[| (y,z) : r;  (z,b) : r^+;  P(z) |] ==> P(y) |]
    ==> P(a)"
proof -
  assume major: "(a,b) : r^+"
  case rule_context
  show ?thesis
    apply (rule major [THEN converseI, THEN trancl_converseI [THEN trancl_induct]])
     apply (rule prems)
     apply (erule converseD)
    apply (blast intro: prems dest!: trancl_converseD)
    done
qed

lemma tranclD: "(x, y) \<in> R^+ ==> EX z. (x, z) \<in> R \<and> (z, y) \<in> R^*"
  apply (erule converse_trancl_induct)
   apply auto
  apply (blast intro: rtrancl_trans)
  done

lemma irrefl_tranclI: "r^-1 \<inter> r^+ = {} ==> (x, x) \<notin> r^+"
  apply (subgoal_tac "ALL y. (x, y) : r^+ --> x \<noteq> y")
   apply fast
  apply (intro strip)
  apply (erule trancl_induct)
   apply (auto intro: r_into_trancl)
  done

lemma irrefl_trancl_rD: "!!X. ALL x. (x, x) \<notin> r^+ ==> (x, y) \<in> r ==> x \<noteq> y"
  by (blast dest: r_into_trancl)

lemma trancl_subset_Sigma_aux:
    "(a, b) \<in> r^* ==> r \<subseteq> A \<times> A ==> a = b \<or> a \<in> A"
  apply (erule rtrancl_induct)
   apply auto
  done

lemma trancl_subset_Sigma: "r \<subseteq> A \<times> A ==> r^+ \<subseteq> A \<times> A"
  apply (rule subsetI)
  apply (simp only: split_tupled_all)
  apply (erule tranclE)
  apply (blast dest!: trancl_into_rtrancl trancl_subset_Sigma_aux)+
  done

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


text {* @{text Domain} and @{text Range} *}

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
  apply auto
  by (erule rev_mp, erule rtrancl_induct, auto)


text {* More about converse @{text rtrancl} and @{text trancl}, should
  be merged with main body. *}

lemma r_r_into_trancl: "(a, b) \<in> R ==> (b, c) \<in> R ==> (a, c) \<in> R^+"
  by (fast intro: trancl_trans)

lemma trancl_into_trancl [rule_format]:
    "(a, b) \<in> r\<^sup>+ ==> (b, c) \<in> r --> (a,c) \<in> r\<^sup>+"
  apply (erule trancl_induct)
   apply (fast intro: r_r_into_trancl)
  apply (fast intro: r_r_into_trancl trancl_trans)
  done

lemma trancl_rtrancl_trancl:
    "(a, b) \<in> r\<^sup>+ ==> (b, c) \<in> r\<^sup>* ==> (a, c) \<in> r\<^sup>+"
  apply (drule tranclD)
  apply (erule exE, erule conjE)
  apply (drule rtrancl_trans, assumption)
  apply (drule rtrancl_into_trancl2, assumption)
  apply assumption
  done

lemmas transitive_closure_trans [trans] =
  r_r_into_trancl trancl_trans rtrancl_trans
  trancl_into_trancl trancl_into_trancl2
  rtrancl_into_rtrancl converse_rtrancl_into_rtrancl
  rtrancl_trancl_trancl trancl_rtrancl_trancl

declare trancl_into_rtrancl [elim]

declare rtranclE [cases set: rtrancl]
declare tranclE [cases set: trancl]

end
