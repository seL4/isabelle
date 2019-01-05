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

  Prove: If \<open>H |= p\<close> then \<open>G |= p\<close> where \<open>G \<in>
  Fin(H)\<close>
\<close>

subsection \<open>The datatype of propositions\<close>

datatype 'a pl =
  false |
  var 'a ("#_" [1000]) |
  imp "'a pl" "'a pl" (infixr "->" 90)


subsection \<open>The proof system\<close>

inductive thms :: "['a pl set, 'a pl] => bool"  (infixl "|-" 50)
  for H :: "'a pl set"
where
  H: "p\<in>H ==> H |- p"
| K: "H |- p->q->p"
| S: "H |- (p->q->r) -> (p->q) -> p->r"
| DN: "H |- ((p->false) -> false) -> p"
| MP: "[| H |- p->q; H |- p |] ==> H |- q"


subsection \<open>The semantics\<close>

subsubsection \<open>Semantics of propositional logic.\<close>

primrec eval :: "['a set, 'a pl] => bool"  ("_[[_]]" [100,0] 100)
where
  "tt[[false]] = False"
| "tt[[#v]] = (v \<in> tt)"
| eval_imp: "tt[[p->q]] = (tt[[p]] --> tt[[q]])"

text \<open>
  A finite set of hypotheses from \<open>t\<close> and the \<open>Var\<close>s in
  \<open>p\<close>.
\<close>

primrec hyps :: "['a pl, 'a set] => 'a pl set"
where
  "hyps false  tt = {}"
| "hyps (#v)   tt = {if v \<in> tt then #v else #v->false}"
| "hyps (p->q) tt = hyps p tt Un hyps q tt"


subsubsection \<open>Logical consequence\<close>

text \<open>
  For every valuation, if all elements of \<open>H\<close> are true then so
  is \<open>p\<close>.
\<close>

definition sat :: "['a pl set, 'a pl] => bool"  (infixl "|=" 50)
  where "H |= p = (\<forall>tt. (\<forall>q\<in>H. tt[[q]]) --> tt[[p]])"


subsection \<open>Proof theory of propositional logic\<close>

lemma thms_mono: "G<=H ==> thms(G) <= thms(H)"
apply (rule predicate1I)
apply (erule thms.induct)
apply (auto intro: thms.intros)
done

lemma thms_I: "H |- p->p"
  \<comment> \<open>Called \<open>I\<close> for Identity Combinator, not for Introduction.\<close>
by (best intro: thms.K thms.S thms.MP)


subsubsection \<open>Weakening, left and right\<close>

lemma weaken_left: "[| G \<subseteq> H;  G|-p |] ==> H|-p"
  \<comment> \<open>Order of premises is convenient with \<open>THEN\<close>\<close>
  by (erule thms_mono [THEN predicate1D])

lemma weaken_left_insert: "G |- p \<Longrightarrow> insert a G |- p"
by (rule weaken_left) (rule subset_insertI)

lemma weaken_left_Un1: "G |- p \<Longrightarrow> G \<union> B |- p"
by (rule weaken_left) (rule Un_upper1)

lemma weaken_left_Un2: "G |- p \<Longrightarrow> A \<union> G |- p"
by (rule weaken_left) (rule Un_upper2)

lemma weaken_right: "H |- q ==> H |- p->q"
by (fast intro: thms.K thms.MP)


subsubsection \<open>The deduction theorem\<close>

theorem deduction: "insert p H |- q  ==>  H |- p->q"
apply (induct set: thms)
apply (fast intro: thms_I thms.H thms.K thms.S thms.DN
                   thms.S [THEN thms.MP, THEN thms.MP] weaken_right)+
done


subsubsection \<open>The cut rule\<close>

lemma cut: "insert p H |- q \<Longrightarrow> H |- p \<Longrightarrow> H |- q"
by (rule thms.MP) (rule deduction)

lemma thms_falseE: "H |- false \<Longrightarrow> H |- q"
by (rule thms.MP, rule thms.DN) (rule weaken_right)

lemma thms_notE: "H |- p -> false \<Longrightarrow> H |- p \<Longrightarrow> H |- q"
by (rule thms_falseE) (rule thms.MP)


subsubsection \<open>Soundness of the rules wrt truth-table semantics\<close>

theorem soundness: "H |- p ==> H |= p"
by (induct set: thms) (auto simp: sat_def)


subsection \<open>Completeness\<close>

subsubsection \<open>Towards the completeness proof\<close>

lemma false_imp: "H |- p->false ==> H |- p->q"
apply (rule deduction)
apply (metis H insert_iff weaken_left_insert thms_notE)
done

lemma imp_false:
    "[| H |- p;  H |- q->false |] ==> H |- (p->q)->false"
apply (rule deduction)
apply (metis H MP insert_iff weaken_left_insert)
done

lemma hyps_thms_if: "hyps p tt |- (if tt[[p]] then p else p->false)"
  \<comment> \<open>Typical example of strengthening the induction statement.\<close>
apply simp
apply (induct p)
apply (simp_all add: thms_I thms.H)
apply (blast intro: weaken_left_Un1 weaken_left_Un2 weaken_right
                    imp_false false_imp)
done

lemma sat_thms_p: "{} |= p ==> hyps p tt |- p"
  \<comment> \<open>Key lemma for completeness; yields a set of assumptions
        satisfying \<open>p\<close>\<close>
unfolding sat_def
by (metis (full_types) empty_iff hyps_thms_if)

text \<open>
  For proving certain theorems in our new propositional logic.
\<close>

declare deduction [intro!]
declare thms.H [THEN thms.MP, intro]

text \<open>
  The excluded middle in the form of an elimination rule.
\<close>

lemma thms_excluded_middle: "H |- (p->q) -> ((p->false)->q) -> q"
apply (rule deduction [THEN deduction])
apply (rule thms.DN [THEN thms.MP], best intro: H)
done

lemma thms_excluded_middle_rule:
    "[| insert p H |- q;  insert (p->false) H |- q |] ==> H |- q"
  \<comment> \<open>Hard to prove directly because it requires cuts\<close>
by (rule thms_excluded_middle [THEN thms.MP, THEN thms.MP], auto)


subsection\<open>Completeness -- lemmas for reducing the set of assumptions\<close>

text \<open>
  For the case \<^prop>\<open>hyps p t - insert #v Y |- p\<close> we also have \<^prop>\<open>hyps p t - {#v} \<subseteq> hyps p (t-{v})\<close>.
\<close>

lemma hyps_Diff: "hyps p (t-{v}) <= insert (#v->false) ((hyps p t)-{#v})"
by (induct p) auto

text \<open>
  For the case \<^prop>\<open>hyps p t - insert (#v -> Fls) Y |- p\<close> we also have
  \<^prop>\<open>hyps p t-{#v->Fls} \<subseteq> hyps p (insert v t)\<close>.
\<close>

lemma hyps_insert: "hyps p (insert v t) <= insert (#v) (hyps p t-{#v->false})"
by (induct p) auto

text \<open>Two lemmas for use with \<open>weaken_left\<close>\<close>

lemma insert_Diff_same: "B-C <= insert a (B-insert a C)"
by fast

lemma insert_Diff_subset2: "insert a (B-{c}) - D <= insert a (B-insert c D)"
by fast

text \<open>
  The set \<^term>\<open>hyps p t\<close> is finite, and elements have the form
  \<^term>\<open>#v\<close> or \<^term>\<open>#v->Fls\<close>.
\<close>

lemma hyps_finite: "finite(hyps p t)"
by (induct p) auto

lemma hyps_subset: "hyps p t <= (UN v. {#v, #v->false})"
by (induct p) auto

lemma Diff_weaken_left: "A \<subseteq> C \<Longrightarrow> A - B |- p \<Longrightarrow> C - B |- p"
  by (rule Diff_mono [OF _ subset_refl, THEN weaken_left])


subsubsection \<open>Completeness theorem\<close>

text \<open>
  Induction on the finite set of assumptions \<^term>\<open>hyps p t0\<close>.  We
  may repeatedly subtract assumptions until none are left!
\<close>

lemma completeness_0_lemma:
    "{} |= p ==> \<forall>t. hyps p t - hyps p t0 |- p"
apply (rule hyps_subset [THEN hyps_finite [THEN finite_subset_induct]])
 apply (simp add: sat_thms_p, safe)
 txt\<open>Case \<open>hyps p t-insert(#v,Y) |- p\<close>\<close>
 apply (iprover intro: thms_excluded_middle_rule
                     insert_Diff_same [THEN weaken_left]
                     insert_Diff_subset2 [THEN weaken_left]
                     hyps_Diff [THEN Diff_weaken_left])
txt\<open>Case \<open>hyps p t-insert(#v -> false,Y) |- p\<close>\<close>
 apply (iprover intro: thms_excluded_middle_rule
                     insert_Diff_same [THEN weaken_left]
                     insert_Diff_subset2 [THEN weaken_left]
                     hyps_insert [THEN Diff_weaken_left])
done

text\<open>The base case for completeness\<close>
lemma completeness_0:  "{} |= p ==> {} |- p"
  by (metis Diff_cancel completeness_0_lemma)

text\<open>A semantic analogue of the Deduction Theorem\<close>
lemma sat_imp: "insert p H |= q ==> H |= p->q"
by (auto simp: sat_def)

theorem completeness: "finite H ==> H |= p ==> H |- p"
apply (induct arbitrary: p rule: finite_induct)
 apply (blast intro: completeness_0)
apply (iprover intro: sat_imp thms.H insertI1 weaken_left_insert [THEN thms.MP])
done

theorem syntax_iff_semantics: "finite H ==> (H |- p) = (H |= p)"
by (blast intro: soundness completeness)

end
