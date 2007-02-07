(*  Title:      HOL/Transitive_Closure.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* Reflexive and Transitive closure of a relation *}

theory Transitive_Closure
imports Predicate
uses "~~/src/Provers/trancl.ML"
begin

text {*
  @{text rtrancl} is reflexive/transitive closure,
  @{text trancl} is transitive closure,
  @{text reflcl} is reflexive closure.

  These postfix operators have \emph{maximum priority}, forcing their
  operands to be atomic.
*}

inductive2
  rtrancl :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"   ("(_^**)" [1000] 1000)
  for r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
    rtrancl_refl [intro!, Pure.intro!, simp]: "r^** a a"
  | rtrancl_into_rtrancl [Pure.intro]: "r^** a b ==> r b c ==> r^** a c"

inductive2
  trancl :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  ("(_^++)" [1000] 1000)
  for r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
    r_into_trancl [intro, Pure.intro]: "r a b ==> r^++ a b"
  | trancl_into_trancl [Pure.intro]: "r^++ a b ==> r b c ==> r^++ a c"

constdefs
  rtrancl_set :: "('a \<times> 'a) set => ('a \<times> 'a) set"    ("(_^*)" [1000] 999)
  "r^* == Collect2 (member2 r)^**"

  trancl_set :: "('a \<times> 'a) set => ('a \<times> 'a) set"    ("(_^+)" [1000] 999)
  "r^+ == Collect2 (member2 r)^++"

abbreviation
  reflcl :: "('a => 'a => bool) => 'a => 'a => bool"  ("(_^==)" [1000] 1000) where
  "r^== == join r op ="

abbreviation
  reflcl_set :: "('a \<times> 'a) set => ('a \<times> 'a) set"  ("(_^=)" [1000] 999) where
  "r^= == r \<union> Id"

notation (xsymbols)
  rtrancl  ("(_\<^sup>*\<^sup>*)" [1000] 1000) and
  trancl  ("(_\<^sup>+\<^sup>+)" [1000] 1000) and
  reflcl  ("(_\<^sup>=\<^sup>=)" [1000] 1000) and
  rtrancl_set  ("(_\<^sup>*)" [1000] 999) and
  trancl_set  ("(_\<^sup>+)" [1000] 999) and
  reflcl_set  ("(_\<^sup>=)" [1000] 999)

notation (HTML output)
  rtrancl  ("(_\<^sup>*\<^sup>*)" [1000] 1000) and
  trancl  ("(_\<^sup>+\<^sup>+)" [1000] 1000) and
  reflcl  ("(_\<^sup>=\<^sup>=)" [1000] 1000) and
  rtrancl_set  ("(_\<^sup>*)" [1000] 999) and
  trancl_set  ("(_\<^sup>+)" [1000] 999) and
  reflcl_set  ("(_\<^sup>=)" [1000] 999)


subsection {* Reflexive-transitive closure *}

lemma rtrancl_set_eq [pred_set_conv]: "(member2 r)^** = member2 (r^*)"
  by (simp add: rtrancl_set_def)

lemma reflcl_set_eq [pred_set_conv]: "(join (member2 r) op =) = member2 (r Un Id)"
  by (simp add: expand_fun_eq)

lemmas rtrancl_refl [intro!, Pure.intro!, simp] = rtrancl_refl [to_set]
lemmas rtrancl_into_rtrancl [Pure.intro] = rtrancl_into_rtrancl [to_set]

lemma r_into_rtrancl [intro]: "!!p. p \<in> r ==> p \<in> r^*"
  -- {* @{text rtrancl} of @{text r} contains @{text r} *}
  apply (simp only: split_tupled_all)
  apply (erule rtrancl_refl [THEN rtrancl_into_rtrancl])
  done

lemma r_into_rtrancl' [intro]: "r x y ==> r^** x y"
  -- {* @{text rtrancl} of @{text r} contains @{text r} *}
  by (erule rtrancl.rtrancl_refl [THEN rtrancl.rtrancl_into_rtrancl])

lemma rtrancl_mono': "r \<le> s ==> r^** \<le> s^**"
  -- {* monotonicity of @{text rtrancl} *}
  apply (rule predicate2I)
  apply (erule rtrancl.induct)
   apply (rule_tac [2] rtrancl.rtrancl_into_rtrancl, blast+)
  done

lemmas rtrancl_mono = rtrancl_mono' [to_set]

theorem rtrancl_induct' [consumes 1, induct set: rtrancl]:
  assumes a: "r^** a b"
    and cases: "P a" "!!y z. [| r^** a y; r y z; P y |] ==> P z"
  shows "P b"
proof -
  from a have "a = a --> P b"
    by (induct "%x y. x = a --> P y" a b) (iprover intro: cases)+
  thus ?thesis by iprover
qed

lemmas rtrancl_induct [consumes 1, induct set: rtrancl_set] = rtrancl_induct' [to_set]

lemmas rtrancl_induct2' =
  rtrancl_induct'[of _ "(ax,ay)" "(bx,by)", split_rule,
                 consumes 1, case_names refl step]

lemmas rtrancl_induct2 =
  rtrancl_induct[of "(ax,ay)" "(bx,by)", split_format (complete),
                 consumes 1, case_names refl step]

lemma reflexive_rtrancl: "reflexive (r^*)"
  by (unfold refl_def) fast

lemma trans_rtrancl: "trans(r^*)"
  -- {* transitivity of transitive closure!! -- by induction *}
proof (rule transI)
  fix x y z
  assume "(x, y) \<in> r\<^sup>*"
  assume "(y, z) \<in> r\<^sup>*"
  thus "(x, z) \<in> r\<^sup>*" by induct (iprover!)+
qed

lemmas rtrancl_trans = trans_rtrancl [THEN transD, standard]

lemma rtrancl_trans':
  assumes xy: "r^** x y"
  and yz: "r^** y z"
  shows "r^** x z" using yz xy
  by induct iprover+

lemma rtranclE:
  assumes major: "(a::'a,b) : r^*"
    and cases: "(a = b) ==> P"
      "!!y. [| (a,y) : r^*; (y,b) : r |] ==> P"
  shows P
  -- {* elimination of @{text rtrancl} -- by induction on a special formula *}
  apply (subgoal_tac "(a::'a) = b | (EX y. (a,y) : r^* & (y,b) : r)")
   apply (rule_tac [2] major [THEN rtrancl_induct])
    prefer 2 apply blast
   prefer 2 apply blast
  apply (erule asm_rl exE disjE conjE cases)+
  done

lemma rtrancl_Int_subset: "[| Id \<subseteq> s; r O (r^* \<inter> s) \<subseteq> s|] ==> r^* \<subseteq> s"
  apply (rule subsetI)
  apply (rule_tac p="x" in PairE, clarify)
  apply (erule rtrancl_induct, auto) 
  done

lemma converse_rtrancl_into_rtrancl':
  "r a b \<Longrightarrow> r\<^sup>*\<^sup>* b c \<Longrightarrow> r\<^sup>*\<^sup>* a c"
  by (rule rtrancl_trans') iprover+

lemmas converse_rtrancl_into_rtrancl = converse_rtrancl_into_rtrancl' [to_set]

text {*
  \medskip More @{term "r^*"} equations and inclusions.
*}

lemma rtrancl_idemp' [simp]: "(r^**)^** = r^**"
  apply (auto intro!: order_antisym)
  apply (erule rtrancl_induct')
   apply (rule rtrancl.rtrancl_refl)
  apply (blast intro: rtrancl_trans')
  done

lemmas rtrancl_idemp [simp] = rtrancl_idemp' [to_set]

lemma rtrancl_idemp_self_comp [simp]: "R^* O R^* = R^*"
  apply (rule set_ext)
  apply (simp only: split_tupled_all)
  apply (blast intro: rtrancl_trans)
  done

lemma rtrancl_subset_rtrancl: "r \<subseteq> s^* ==> r^* \<subseteq> s^*"
by (drule rtrancl_mono, simp)

lemma rtrancl_subset': "R \<le> S ==> S \<le> R^** ==> S^** = R^**"
  apply (drule rtrancl_mono')
  apply (drule rtrancl_mono', simp)
  done

lemmas rtrancl_subset = rtrancl_subset' [to_set]

lemma rtrancl_Un_rtrancl': "(join (R^**) (S^**))^** = (join R S)^**"
  by (blast intro!: rtrancl_subset' intro: rtrancl_mono' [THEN predicate2D])

lemmas rtrancl_Un_rtrancl = rtrancl_Un_rtrancl' [to_set]

lemma rtrancl_reflcl' [simp]: "(R^==)^** = R^**"
  by (blast intro!: rtrancl_subset')

lemmas rtrancl_reflcl [simp] = rtrancl_reflcl' [to_set]

lemma rtrancl_r_diff_Id: "(r - Id)^* = r^*"
  apply (rule sym)
  apply (rule rtrancl_subset, blast, clarify)
  apply (rename_tac a b)
  apply (case_tac "a = b", blast)
  apply (blast intro!: r_into_rtrancl)
  done

lemma rtrancl_r_diff_Id': "(meet r op ~=)^** = r^**"
  apply (rule sym)
  apply (rule rtrancl_subset')
  apply blast+
  done

theorem rtrancl_converseD':
  assumes r: "(r^--1)^** x y"
  shows "r^** y x"
proof -
  from r show ?thesis
    by induct (iprover intro: rtrancl_trans' dest!: conversepD)+
qed

lemmas rtrancl_converseD = rtrancl_converseD' [to_set]

theorem rtrancl_converseI':
  assumes r: "r^** y x"
  shows "(r^--1)^** x y"
proof -
  from r show ?thesis
    by induct (iprover intro: rtrancl_trans' conversepI)+
qed

lemmas rtrancl_converseI = rtrancl_converseI' [to_set]

lemma rtrancl_converse: "(r^-1)^* = (r^*)^-1"
  by (fast dest!: rtrancl_converseD intro!: rtrancl_converseI)

lemma sym_rtrancl: "sym r ==> sym (r^*)"
  by (simp only: sym_conv_converse_eq rtrancl_converse [symmetric])

theorem converse_rtrancl_induct'[consumes 1]:
  assumes major: "r^** a b"
    and cases: "P b" "!!y z. [| r y z; r^** z b; P z |] ==> P y"
  shows "P a"
proof -
  from rtrancl_converseI' [OF major]
  show ?thesis
    by induct (iprover intro: cases dest!: conversepD rtrancl_converseD')+
qed

lemmas converse_rtrancl_induct[consumes 1] = converse_rtrancl_induct' [to_set]

lemmas converse_rtrancl_induct2' =
  converse_rtrancl_induct'[of _ "(ax,ay)" "(bx,by)", split_rule,
                 consumes 1, case_names refl step]

lemmas converse_rtrancl_induct2 =
  converse_rtrancl_induct[of "(ax,ay)" "(bx,by)", split_format (complete),
                 consumes 1, case_names refl step]

lemma converse_rtranclE':
  assumes major: "r^** x z"
    and cases: "x=z ==> P"
      "!!y. [| r x y; r^** y z |] ==> P"
  shows P
  apply (subgoal_tac "x = z | (EX y. r x y & r^** y z)")
   apply (rule_tac [2] major [THEN converse_rtrancl_induct'])
    prefer 2 apply iprover
   prefer 2 apply iprover
  apply (erule asm_rl exE disjE conjE cases)+
  done

lemmas converse_rtranclE = converse_rtranclE' [to_set]

lemmas converse_rtranclE2' = converse_rtranclE' [of _ "(xa,xb)" "(za,zb)", split_rule]

lemmas converse_rtranclE2 = converse_rtranclE [of "(xa,xb)" "(za,zb)", split_rule]

lemma r_comp_rtrancl_eq: "r O r^* = r^* O r"
  by (blast elim: rtranclE converse_rtranclE
    intro: rtrancl_into_rtrancl converse_rtrancl_into_rtrancl)

lemma rtrancl_unfold: "r^* = Id Un r O r^*"
  by (auto intro: rtrancl_into_rtrancl elim: rtranclE)


subsection {* Transitive closure *}

lemma trancl_set_eq [pred_set_conv]: "(member2 r)^++ = member2 (r^+)"
  by (simp add: trancl_set_def)

lemmas r_into_trancl [intro, Pure.intro] = r_into_trancl [to_set]
lemmas trancl_into_trancl [Pure.intro] = trancl_into_trancl [to_set]

lemma trancl_mono: "!!p. p \<in> r^+ ==> r \<subseteq> s ==> p \<in> s^+"
  apply (simp add: split_tupled_all trancl_set_def)
  apply (erule trancl.induct)
  apply (iprover dest: subsetD)+
  done

lemma r_into_trancl': "!!p. p : r ==> p : r^+"
  by (simp only: split_tupled_all) (erule r_into_trancl)

text {*
  \medskip Conversions between @{text trancl} and @{text rtrancl}.
*}

lemma trancl_into_rtrancl': "r^++ a b ==> r^** a b"
  by (erule trancl.induct) iprover+

lemmas trancl_into_rtrancl = trancl_into_rtrancl' [to_set]

lemma rtrancl_into_trancl1': assumes r: "r^** a b"
  shows "!!c. r b c ==> r^++ a c" using r
  by induct iprover+

lemmas rtrancl_into_trancl1 = rtrancl_into_trancl1' [to_set]

lemma rtrancl_into_trancl2': "[| r a b; r^** b c |] ==> r^++ a c"
  -- {* intro rule from @{text r} and @{text rtrancl} *}
  apply (erule rtrancl.cases, iprover)
  apply (rule rtrancl_trans' [THEN rtrancl_into_trancl1'])
   apply (simp | rule r_into_rtrancl')+
  done

lemmas rtrancl_into_trancl2 = rtrancl_into_trancl2' [to_set]

lemma trancl_induct' [consumes 1, induct set: trancl]:
  assumes a: "r^++ a b"
  and cases: "!!y. r a y ==> P y"
    "!!y z. r^++ a y ==> r y z ==> P y ==> P z"
  shows "P b"
  -- {* Nice induction rule for @{text trancl} *}
proof -
  from a have "a = a --> P b"
    by (induct "%x y. x = a --> P y" a b) (iprover intro: cases)+
  thus ?thesis by iprover
qed

lemmas trancl_induct [consumes 1, induct set: trancl_set] = trancl_induct' [to_set]

lemmas trancl_induct2' =
  trancl_induct'[of _ "(ax,ay)" "(bx,by)", split_rule,
                 consumes 1, case_names base step]

lemmas trancl_induct2 =
  trancl_induct[of "(ax,ay)" "(bx,by)", split_format (complete),
                 consumes 1, case_names base step]

lemma trancl_trans_induct':
  assumes major: "r^++ x y"
    and cases: "!!x y. r x y ==> P x y"
      "!!x y z. [| r^++ x y; P x y; r^++ y z; P y z |] ==> P x z"
  shows "P x y"
  -- {* Another induction rule for trancl, incorporating transitivity *}
  by (iprover intro: major [THEN trancl_induct'] cases)

lemmas trancl_trans_induct = trancl_trans_induct' [to_set]

lemma tranclE:
  assumes H: "(a, b) : r^+"
  and cases: "(a, b) : r ==> P" "\<And>c. (a, c) : r^+ ==> (c, b) : r ==> P"
  shows P
  using H [simplified trancl_set_def, simplified]
  by cases (auto intro: cases [simplified trancl_set_def, simplified])

lemma trancl_Int_subset: "[| r \<subseteq> s; r O (r^+ \<inter> s) \<subseteq> s|] ==> r^+ \<subseteq> s"
  apply (rule subsetI)
  apply (rule_tac p="x" in PairE, clarify)
  apply (erule trancl_induct, auto) 
  done

lemma trancl_unfold: "r^+ = r Un r O r^+"
  by (auto intro: trancl_into_trancl elim: tranclE)

lemma trans_trancl[simp]: "trans(r^+)"
  -- {* Transitivity of @{term "r^+"} *}
proof (rule transI)
  fix x y z
  assume xy: "(x, y) \<in> r^+"
  assume "(y, z) \<in> r^+"
  thus "(x, z) \<in> r^+" by induct (insert xy, iprover)+
qed

lemmas trancl_trans = trans_trancl [THEN transD, standard]

lemma trancl_trans':
  assumes xy: "r^++ x y"
  and yz: "r^++ y z"
  shows "r^++ x z" using yz xy
  by induct iprover+

lemma trancl_id[simp]: "trans r \<Longrightarrow> r^+ = r"
apply(auto)
apply(erule trancl_induct)
apply assumption
apply(unfold trans_def)
apply(blast)
done

lemma rtrancl_trancl_trancl': assumes r: "r^** x y"
  shows "!!z. r^++ y z ==> r^++ x z" using r
  by induct (iprover intro: trancl_trans')+

lemmas rtrancl_trancl_trancl = rtrancl_trancl_trancl' [to_set]

lemma trancl_into_trancl2': "r a b ==> r^++ b c ==> r^++ a c"
  by (erule trancl_trans' [OF trancl.r_into_trancl])

lemmas trancl_into_trancl2 = trancl_into_trancl2' [to_set]

lemma trancl_insert:
  "(insert (y, x) r)^+ = r^+ \<union> {(a, b). (a, y) \<in> r^* \<and> (x, b) \<in> r^*}"
  -- {* primitive recursion for @{text trancl} over finite relations *}
  apply (rule equalityI)
   apply (rule subsetI)
   apply (simp only: split_tupled_all)
   apply (erule trancl_induct, blast)
   apply (blast intro: rtrancl_into_trancl1 trancl_into_rtrancl r_into_trancl trancl_trans)
  apply (rule subsetI)
  apply (blast intro: trancl_mono rtrancl_mono
    [THEN [2] rev_subsetD] rtrancl_trancl_trancl rtrancl_into_trancl2)
  done

lemma trancl_converseI': "(r^++)^--1 x y ==> (r^--1)^++ x y"
  apply (drule conversepD)
  apply (erule trancl_induct')
  apply (iprover intro: conversepI trancl_trans')+
  done

lemmas trancl_converseI = trancl_converseI' [to_set]

lemma trancl_converseD': "(r^--1)^++ x y ==> (r^++)^--1 x y"
  apply (rule conversepI)
  apply (erule trancl_induct')
  apply (iprover dest: conversepD intro: trancl_trans')+
  done

lemmas trancl_converseD = trancl_converseD' [to_set]

lemma trancl_converse': "(r^--1)^++ = (r^++)^--1"
  by (fastsimp simp add: expand_fun_eq
    intro!: trancl_converseI' dest!: trancl_converseD')

lemmas trancl_converse = trancl_converse' [to_set]

lemma sym_trancl: "sym r ==> sym (r^+)"
  by (simp only: sym_conv_converse_eq trancl_converse [symmetric])

lemma converse_trancl_induct':
  assumes major: "r^++ a b"
    and cases: "!!y. r y b ==> P(y)"
      "!!y z.[| r y z;  r^++ z b;  P(z) |] ==> P(y)"
  shows "P a"
  apply (rule trancl_induct' [OF trancl_converseI', OF conversepI, OF major])
   apply (rule cases)
   apply (erule conversepD)
  apply (blast intro: prems dest!: trancl_converseD' conversepD)
  done

lemmas converse_trancl_induct = converse_trancl_induct' [to_set]

lemma tranclD': "R^++ x y ==> EX z. R x z \<and> R^** z y"
  apply (erule converse_trancl_induct', auto)
  apply (blast intro: rtrancl_trans')
  done

lemmas tranclD = tranclD' [to_set]

lemma irrefl_tranclI: "r^-1 \<inter> r^* = {} ==> (x, x) \<notin> r^+"
  by (blast elim: tranclE dest: trancl_into_rtrancl)

lemma irrefl_trancl_rD: "!!X. ALL x. (x, x) \<notin> r^+ ==> (x, y) \<in> r ==> x \<noteq> y"
  by (blast dest: r_into_trancl)

lemma trancl_subset_Sigma_aux:
    "(a, b) \<in> r^* ==> r \<subseteq> A \<times> A ==> a = b \<or> a \<in> A"
  by (induct rule: rtrancl_induct) auto

lemma trancl_subset_Sigma: "r \<subseteq> A \<times> A ==> r^+ \<subseteq> A \<times> A"
  apply (rule subsetI)
  apply (simp only: split_tupled_all)
  apply (erule tranclE)
  apply (blast dest!: trancl_into_rtrancl trancl_subset_Sigma_aux)+
  done

lemma reflcl_trancl' [simp]: "(r^++)^== = r^**"
  apply (safe intro!: order_antisym)
   apply (erule trancl_into_rtrancl')
  apply (blast elim: rtrancl.cases dest: rtrancl_into_trancl1')
  done

lemmas reflcl_trancl [simp] = reflcl_trancl' [to_set]

lemma trancl_reflcl [simp]: "(r^=)^+ = r^*"
  apply safe
   apply (drule trancl_into_rtrancl, simp)
  apply (erule rtranclE, safe)
   apply (rule r_into_trancl, simp)
  apply (rule rtrancl_into_trancl1)
   apply (erule rtrancl_reflcl [THEN equalityD2, THEN subsetD], fast)
  done

lemma trancl_empty [simp]: "{}^+ = {}"
  by (auto elim: trancl_induct)

lemma rtrancl_empty [simp]: "{}^* = Id"
  by (rule subst [OF reflcl_trancl]) simp

lemma rtranclD': "R^** a b ==> a = b \<or> a \<noteq> b \<and> R^++ a b"
  by (force simp add: reflcl_trancl' [symmetric] simp del: reflcl_trancl')

lemmas rtranclD = rtranclD' [to_set]

lemma rtrancl_eq_or_trancl:
  "(x,y) \<in> R\<^sup>* = (x=y \<or> x\<noteq>y \<and> (x,y) \<in> R\<^sup>+)"
  by (fast elim: trancl_into_rtrancl dest: rtranclD)

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

lemma single_valued_confluent:
  "\<lbrakk> single_valued r; (x,y) \<in> r^*; (x,z) \<in> r^* \<rbrakk>
  \<Longrightarrow> (y,z) \<in> r^* \<or> (z,y) \<in> r^*"
apply(erule rtrancl_induct)
 apply simp
apply(erule disjE)
 apply(blast elim:converse_rtranclE dest:single_valuedD)
apply(blast intro:rtrancl_trans)
done

lemma r_r_into_trancl: "(a, b) \<in> R ==> (b, c) \<in> R ==> (a, c) \<in> R^+"
  by (fast intro: trancl_trans)

lemma trancl_into_trancl [rule_format]:
    "(a, b) \<in> r\<^sup>+ ==> (b, c) \<in> r --> (a,c) \<in> r\<^sup>+"
  apply (erule trancl_induct)
   apply (fast intro: r_r_into_trancl)
  apply (fast intro: r_r_into_trancl trancl_trans)
  done

lemma trancl_rtrancl_trancl':
    "r\<^sup>+\<^sup>+ a b ==> r\<^sup>*\<^sup>* b c ==> r\<^sup>+\<^sup>+ a c"
  apply (drule tranclD')
  apply (erule exE, erule conjE)
  apply (drule rtrancl_trans', assumption)
  apply (drule rtrancl_into_trancl2', assumption, assumption)
  done

lemmas trancl_rtrancl_trancl = trancl_rtrancl_trancl' [to_set]

lemmas transitive_closure_trans [trans] =
  r_r_into_trancl trancl_trans rtrancl_trans
  trancl_into_trancl trancl_into_trancl2
  rtrancl_into_rtrancl converse_rtrancl_into_rtrancl
  rtrancl_trancl_trancl trancl_rtrancl_trancl

lemmas transitive_closure_trans' [trans] =
  trancl_trans' rtrancl_trans'
  trancl.trancl_into_trancl trancl_into_trancl2'
  rtrancl.rtrancl_into_rtrancl converse_rtrancl_into_rtrancl'
  rtrancl_trancl_trancl' trancl_rtrancl_trancl'

declare trancl_into_rtrancl [elim]

declare rtranclE [cases set: rtrancl_set]
declare tranclE [cases set: trancl_set]





subsection {* Setup of transitivity reasoner *}

ML_setup {*

structure Trancl_Tac = Trancl_Tac_Fun (
  struct
    val r_into_trancl = thm "r_into_trancl";
    val trancl_trans  = thm "trancl_trans";
    val rtrancl_refl = thm "rtrancl_refl";
    val r_into_rtrancl = thm "r_into_rtrancl";
    val trancl_into_rtrancl = thm "trancl_into_rtrancl";
    val rtrancl_trancl_trancl = thm "rtrancl_trancl_trancl";
    val trancl_rtrancl_trancl = thm "trancl_rtrancl_trancl";
    val rtrancl_trans = thm "rtrancl_trans";

  fun decomp (Trueprop $ t) =
    let fun dec (Const ("op :", _) $ (Const ("Pair", _) $ a $ b) $ rel ) =
        let fun decr (Const ("Transitive_Closure.rtrancl_set", _ ) $ r) = (r,"r*")
              | decr (Const ("Transitive_Closure.trancl_set", _ ) $ r)  = (r,"r+")
              | decr r = (r,"r");
            val (rel,r) = decr rel;
        in SOME (a,b,rel,r) end
      | dec _ =  NONE
    in dec t end;

  end);

structure Tranclp_Tac = Trancl_Tac_Fun (
  struct
    val r_into_trancl = thm "trancl.r_into_trancl";
    val trancl_trans  = thm "trancl_trans'";
    val rtrancl_refl = thm "rtrancl.rtrancl_refl";
    val r_into_rtrancl = thm "r_into_rtrancl'";
    val trancl_into_rtrancl = thm "trancl_into_rtrancl'";
    val rtrancl_trancl_trancl = thm "rtrancl_trancl_trancl'";
    val trancl_rtrancl_trancl = thm "trancl_rtrancl_trancl'";
    val rtrancl_trans = thm "rtrancl_trans'";

  fun decomp (Trueprop $ t) =
    let fun dec (rel $ a $ b) =
        let fun decr (Const ("Transitive_Closure.rtrancl", _ ) $ r) = (r,"r*")
              | decr (Const ("Transitive_Closure.trancl", _ ) $ r)  = (r,"r+")
              | decr r = (r,"r");
            val (rel,r) = decr rel;
        in SOME (a, b, Envir.beta_eta_contract rel, r) end
      | dec _ =  NONE
    in dec t end;

  end);

change_simpset (fn ss => ss
  addSolver (mk_solver "Trancl" (fn _ => Trancl_Tac.trancl_tac))
  addSolver (mk_solver "Rtrancl" (fn _ => Trancl_Tac.rtrancl_tac))
  addSolver (mk_solver "Tranclp" (fn _ => Tranclp_Tac.trancl_tac))
  addSolver (mk_solver "Rtranclp" (fn _ => Tranclp_Tac.rtrancl_tac)));

*}

(* Optional methods *)

method_setup trancl =
  {* Method.no_args (Method.SIMPLE_METHOD' Trancl_Tac.trancl_tac) *}
  {* simple transitivity reasoner *}
method_setup rtrancl =
  {* Method.no_args (Method.SIMPLE_METHOD' Trancl_Tac.rtrancl_tac) *}
  {* simple transitivity reasoner *}
method_setup tranclp =
  {* Method.no_args (Method.SIMPLE_METHOD' Tranclp_Tac.trancl_tac) *}
  {* simple transitivity reasoner (predicate version) *}
method_setup rtranclp =
  {* Method.no_args (Method.SIMPLE_METHOD' Tranclp_Tac.rtrancl_tac) *}
  {* simple transitivity reasoner (predicate version) *}

end
