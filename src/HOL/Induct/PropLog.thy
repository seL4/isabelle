(*  Title:      HOL/Induct/PropLog.thy
    Author:     Tobias Nipkow
    Copyright   1994  TU Muenchen & University of Cambridge
*)

section \<open>Meta-theory of propositional logic\<close>

theory PropLog imports Main begin

text \<open>
  Datatype definition of propositional logic formulae and inductive
  definition of the propositional tautologies.

  Inductive definition of propositional logic.  Soundness and
  completeness w.r.t.\ truth-tables.

  Prove: If \<open>H \<Turnstile> p\<close> then \<open>G \<Turnstile> p\<close> where \<open>G \<in>
  Fin(H)\<close>
\<close>

subsection \<open>The datatype of propositions\<close>

datatype 'a pl =
    false 
  | var 'a (\<open>#_\<close> [1000]) 
  | imp "'a pl" "'a pl" (infixr \<open>\<rightharpoonup>\<close> 90)


subsection \<open>The proof system\<close>

inductive thms :: "['a pl set, 'a pl] \<Rightarrow> bool"  (infixl \<open>\<turnstile>\<close> 50)
  for H :: "'a pl set"
  where
    H: "p \<in> H \<Longrightarrow> H \<turnstile> p"
  | K: "H \<turnstile> p\<rightharpoonup>q\<rightharpoonup>p"
  | S: "H \<turnstile> (p\<rightharpoonup>q\<rightharpoonup>r) \<rightharpoonup> (p\<rightharpoonup>q) \<rightharpoonup> p\<rightharpoonup>r"
  | DN: "H \<turnstile> ((p\<rightharpoonup>false) \<rightharpoonup> false) \<rightharpoonup> p"
  | MP: "\<lbrakk>H \<turnstile> p\<rightharpoonup>q; H \<turnstile> p\<rbrakk> \<Longrightarrow> H \<turnstile> q"


subsection \<open>The semantics\<close>

subsubsection \<open>Semantics of propositional logic.\<close>

primrec eval :: "['a set, 'a pl] => bool"  (\<open>_[[_]]\<close> [100,0] 100)
  where
    "tt[[false]] = False"
  | "tt[[#v]] = (v \<in> tt)"
  | eval_imp: "tt[[p\<rightharpoonup>q]] = (tt[[p]] \<longrightarrow> tt[[q]])"

text \<open>
  A finite set of hypotheses from \<open>t\<close> and the \<open>Var\<close>s in
  \<open>p\<close>.
\<close>

primrec hyps :: "['a pl, 'a set] => 'a pl set"
  where
    "hyps false  tt = {}"
  | "hyps (#v)   tt = {if v \<in> tt then #v else #v\<rightharpoonup>false}"
  | "hyps (p\<rightharpoonup>q) tt = hyps p tt Un hyps q tt"


subsubsection \<open>Logical consequence\<close>

text \<open>
  For every valuation, if all elements of \<open>H\<close> are true then so
  is \<open>p\<close>.
\<close>

definition sat :: "['a pl set, 'a pl] => bool"  (infixl \<open>\<Turnstile>\<close> 50)
  where "H \<Turnstile> p = (\<forall>tt. (\<forall>q\<in>H. tt[[q]]) \<longrightarrow> tt[[p]])"


subsection \<open>Proof theory of propositional logic\<close>

lemma thms_mono: 
  assumes "G \<subseteq> H" shows "thms(G) \<le> thms(H)"
proof -
  have "G \<turnstile> p \<Longrightarrow> H \<turnstile> p" for p
    by (induction rule: thms.induct) (use assms in \<open>auto intro: thms.intros\<close>)
  then show ?thesis
    by blast
qed

lemma thms_I: "H \<turnstile> p\<rightharpoonup>p"
  \<comment> \<open>Called \<open>I\<close> for Identity Combinator, not for Introduction.\<close>
  by (best intro: thms.K thms.S thms.MP)


subsubsection \<open>Weakening, left and right\<close>

lemma weaken_left: "\<lbrakk>G \<subseteq> H;  G\<turnstile>p\<rbrakk> \<Longrightarrow> H\<turnstile>p"
  \<comment> \<open>Order of premises is convenient with \<open>THEN\<close>\<close>
  by (meson predicate1D thms_mono)

lemma weaken_left_insert: "G \<turnstile> p \<Longrightarrow> insert a G \<turnstile> p"
  by (meson subset_insertI weaken_left)

lemma weaken_left_Un1: "G \<turnstile> p \<Longrightarrow> G \<union> B \<turnstile> p"
  by (rule weaken_left) (rule Un_upper1)

lemma weaken_left_Un2: "G \<turnstile> p \<Longrightarrow> A \<union> G \<turnstile> p"
  by (metis Un_commute weaken_left_Un1)

lemma weaken_right: "H \<turnstile> q \<Longrightarrow> H \<turnstile> p\<rightharpoonup>q"
  using K MP by blast


subsubsection \<open>The deduction theorem\<close>

theorem deduction: "insert p H \<turnstile> q  \<Longrightarrow>  H \<turnstile> p\<rightharpoonup>q"
proof (induct set: thms)
  case (H p)
  then show ?case
    using thms.H thms_I weaken_right by fastforce 
qed (metis thms.simps)+


subsubsection \<open>The cut rule\<close>

lemma cut: "insert p H \<turnstile> q \<Longrightarrow> H \<turnstile> p \<Longrightarrow> H \<turnstile> q"
  using MP deduction by blast

lemma thms_falseE: "H \<turnstile> false \<Longrightarrow> H \<turnstile> q"
  by (metis thms.simps)

lemma thms_notE: "H \<turnstile> p \<rightharpoonup> false \<Longrightarrow> H \<turnstile> p \<Longrightarrow> H \<turnstile> q"
  using MP thms_falseE by blast


subsubsection \<open>Soundness of the rules wrt truth-table semantics\<close>

theorem soundness: "H \<turnstile> p \<Longrightarrow> H \<Turnstile> p"
  by (induct set: thms) (auto simp: sat_def)


subsection \<open>Completeness\<close>

subsubsection \<open>Towards the completeness proof\<close>

lemma false_imp: "H \<turnstile> p\<rightharpoonup>false \<Longrightarrow> H \<turnstile> p\<rightharpoonup>q"
  by (metis thms.simps)

lemma imp_false:
  "\<lbrakk>H \<turnstile> p;  H \<turnstile> q\<rightharpoonup>false\<rbrakk> \<Longrightarrow> H \<turnstile> (p\<rightharpoonup>q)\<rightharpoonup>false"
  by (meson MP S weaken_right)

lemma hyps_thms_if: "hyps p tt \<turnstile> (if tt[[p]] then p else p\<rightharpoonup>false)"
  \<comment> \<open>Typical example of strengthening the induction statement.\<close>
proof (induction p)
  case (imp p1 p2)
  then show ?case
    by (metis (full_types) eval_imp false_imp hyps.simps(3) imp_false weaken_left_Un1 weaken_left_Un2 weaken_right)

qed (simp_all add: thms_I thms.H)

lemma sat_thms_p: "{} \<Turnstile> p \<Longrightarrow> hyps p tt \<turnstile> p"
  \<comment> \<open>Key lemma for completeness; yields a set of assumptions
        satisfying \<open>p\<close>\<close>
  by (metis (full_types) empty_iff hyps_thms_if sat_def)

text \<open>
  For proving certain theorems in our new propositional logic.
\<close>

declare deduction [intro!]
declare thms.H [THEN thms.MP, intro]

text \<open>
  The excluded middle in the form of an elimination rule.
\<close>

lemma thms_excluded_middle: "H \<turnstile> (p\<rightharpoonup>q) \<rightharpoonup> ((p\<rightharpoonup>false)\<rightharpoonup>q) \<rightharpoonup> q"
proof -
  have "insert ((p \<rightharpoonup> false) \<rightharpoonup> q) (insert (p \<rightharpoonup> q) H) \<turnstile> (q \<rightharpoonup> false) \<rightharpoonup> false"
    by (best intro: H)
  then show ?thesis
    by (metis deduction thms.simps)
qed

lemma thms_excluded_middle_rule:
  "\<lbrakk>insert p H \<turnstile> q;  insert (p\<rightharpoonup>false) H \<turnstile> q\<rbrakk> \<Longrightarrow> H \<turnstile> q"
  \<comment> \<open>Hard to prove directly because it requires cuts\<close>
  by (rule thms_excluded_middle [THEN thms.MP, THEN thms.MP], auto)


subsection\<open>Completeness -- lemmas for reducing the set of assumptions\<close>

text \<open>
  For the case \<^prop>\<open>hyps p t - insert #v Y \<turnstile> p\<close> we also have \<^prop>\<open>hyps p t - {#v} \<subseteq> hyps p (t-{v})\<close>.
\<close>

lemma hyps_Diff: "hyps p (t-{v}) \<subseteq> insert (#v\<rightharpoonup>false) ((hyps p t)-{#v})"
  by (induct p) auto

text \<open>
  For the case \<^prop>\<open>hyps p t - insert (#v \<rightharpoonup> Fls) Y \<turnstile> p\<close> we also have
  \<^prop>\<open>hyps p t-{#v\<rightharpoonup>Fls} \<subseteq> hyps p (insert v t)\<close>.
\<close>

lemma hyps_insert: "hyps p (insert v t) \<subseteq> insert (#v) (hyps p t-{#v\<rightharpoonup>false})"
  by (induct p) auto

text \<open>Two lemmas for use with \<open>weaken_left\<close>\<close>

lemma insert_Diff_same: "B-C \<subseteq> insert a (B-insert a C)"
  by fast

lemma insert_Diff_subset2: "insert a (B-{c}) - D \<subseteq> insert a (B-insert c D)"
  by fast

text \<open>
  The set \<^term>\<open>hyps p t\<close> is finite, and elements have the form
  \<^term>\<open>#v\<close> or \<^term>\<open>#v\<rightharpoonup>Fls\<close>.
\<close>

lemma hyps_finite: "finite(hyps p t)"
  by (induct p) auto

lemma hyps_subset: "hyps p t \<subseteq> (UN v. {#v, #v\<rightharpoonup>false})"
  by (induct p) auto

lemma Diff_weaken_left: "A \<subseteq> C \<Longrightarrow> A - B \<turnstile> p \<Longrightarrow> C - B \<turnstile> p"
  by (rule Diff_mono [OF _ subset_refl, THEN weaken_left])


subsubsection \<open>Completeness theorem\<close>

text \<open>
  Induction on the finite set of assumptions \<^term>\<open>hyps p t0\<close>.  We
  may repeatedly subtract assumptions until none are left!
\<close>

lemma completeness_0: 
  assumes "{} \<Turnstile> p"
  shows "{} \<turnstile> p"
proof -
  { fix t t0
    have "hyps p t - hyps p t0 \<turnstile> p"
      using hyps_finite hyps_subset
    proof (induction arbitrary: t rule: finite_subset_induct)
      case empty
      then show ?case
        by (simp add: assms sat_thms_p)
    next
      case (insert q H)
      then consider v where "q = #v" | v where "q = #v \<rightharpoonup> false"
        by blast
      then show ?case
      proof cases
        case 1
        then show ?thesis
          by (metis (no_types, lifting) insert.IH thms_excluded_middle_rule insert_Diff_same 
              insert_Diff_subset2 weaken_left Diff_weaken_left hyps_Diff)
      next
        case 2
        then show ?thesis
          by (metis (no_types, lifting) insert.IH thms_excluded_middle_rule insert_Diff_same 
              insert_Diff_subset2 weaken_left Diff_weaken_left hyps_insert)
      qed
    qed
  }
  then show ?thesis
    by (metis Diff_cancel)
qed

text\<open>A semantic analogue of the Deduction Theorem\<close>
lemma sat_imp: "insert p H \<Turnstile> q \<Longrightarrow> H \<Turnstile> p\<rightharpoonup>q"
  by (auto simp: sat_def)

theorem completeness: "finite H \<Longrightarrow> H \<Turnstile> p \<Longrightarrow> H \<turnstile> p"
proof (induction arbitrary: p rule: finite_induct)
  case empty
  then show ?case
    by (simp add: completeness_0)
next
  case insert
  then show ?case
    by (meson H MP insertI1 sat_imp weaken_left_insert)
qed

theorem syntax_iff_semantics: "finite H \<Longrightarrow> (H \<turnstile> p) = (H \<Turnstile> p)"
  by (blast intro: soundness completeness)

end
