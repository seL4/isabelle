(*  Title:      HOL/Induct/PropLog.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994  TU Muenchen & University of Cambridge
*)

header {* Meta-theory of propositional logic *}

theory PropLog = Main:

text {*
  Datatype definition of propositional logic formulae and inductive
  definition of the propositional tautologies.

  Inductive definition of propositional logic.  Soundness and
  completeness w.r.t.\ truth-tables.

  Prove: If @{text "H |= p"} then @{text "G |= p"} where @{text "G \<in>
  Fin(H)"}
*}

subsection {* The datatype of propositions *}

datatype
    'a pl = false | var 'a ("#_" [1000]) | "->" "'a pl" "'a pl" (infixr 90)

subsection {* The proof system *}

consts
  thms  :: "'a pl set => 'a pl set"
  "|-"  :: "['a pl set, 'a pl] => bool"   (infixl 50)

translations
  "H |- p" == "p \<in> thms(H)"

inductive "thms(H)"
  intros
  H [intro]:  "p\<in>H ==> H |- p"
  K:          "H |- p->q->p"
  S:          "H |- (p->q->r) -> (p->q) -> p->r"
  DN:         "H |- ((p->false) -> false) -> p"
  MP:         "[| H |- p->q; H |- p |] ==> H |- q"

subsection {* The semantics *}

subsubsection {* Semantics of propositional logic. *}

consts
  eval  :: "['a set, 'a pl] => bool"      ("_[[_]]" [100,0] 100)

primrec     "tt[[false]] = False"
	    "tt[[#v]]    = (v \<in> tt)"
  eval_imp: "tt[[p->q]]  = (tt[[p]] --> tt[[q]])"

text {*
  A finite set of hypotheses from @{text t} and the @{text Var}s in
  @{text p}.
*}

consts
  hyps  :: "['a pl, 'a set] => 'a pl set"

primrec
  "hyps false  tt = {}"
  "hyps (#v)   tt = {if v \<in> tt then #v else #v->false}"
  "hyps (p->q) tt = hyps p tt Un hyps q tt"

subsubsection {* Logical consequence *}

text {*
  For every valuation, if all elements of @{text H} are true then so
  is @{text p}.
*}

constdefs
  sat :: "['a pl set, 'a pl] => bool"   (infixl "|=" 50)
    "H |= p  ==  (\<forall>tt. (\<forall>q\<in>H. tt[[q]]) --> tt[[p]])"


subsection {* Proof theory of propositional logic *}

lemma thms_mono: "G<=H ==> thms(G) <= thms(H)"
apply (unfold thms.defs )
apply (rule lfp_mono)
apply (assumption | rule basic_monos)+
done

lemma thms_I: "H |- p->p"
  -- {*Called @{text I} for Identity Combinator, not for Introduction. *}
by (best intro: thms.K thms.S thms.MP)


subsubsection {* Weakening, left and right *}

lemma weaken_left: "[| G \<subseteq> H;  G|-p |] ==> H|-p"
  -- {* Order of premises is convenient with @{text THEN} *}
  by (erule thms_mono [THEN subsetD])

lemmas weaken_left_insert = subset_insertI [THEN weaken_left]

lemmas weaken_left_Un1  = Un_upper1 [THEN weaken_left]
lemmas weaken_left_Un2  = Un_upper2 [THEN weaken_left]

lemma weaken_right: "H |- q ==> H |- p->q"
by (fast intro: thms.K thms.MP)


subsubsection {* The deduction theorem *}

theorem deduction: "insert p H |- q  ==>  H |- p->q"
apply (erule thms.induct)
apply (fast intro: thms_I thms.H thms.K thms.S thms.DN 
                   thms.S [THEN thms.MP, THEN thms.MP] weaken_right)+
done


subsubsection {* The cut rule *}

lemmas cut = deduction [THEN thms.MP]

lemmas thms_falseE = weaken_right [THEN thms.DN [THEN thms.MP]]

lemmas thms_notE = thms.MP [THEN thms_falseE, standard]


subsubsection {* Soundness of the rules wrt truth-table semantics *}

theorem soundness: "H |- p ==> H |= p"
apply (unfold sat_def)
apply (erule thms.induct, auto) 
done

subsection {* Completeness *}

subsubsection {* Towards the completeness proof *}

lemma false_imp: "H |- p->false ==> H |- p->q"
apply (rule deduction)
apply (erule weaken_left_insert [THEN thms_notE])
apply blast
done

lemma imp_false:
    "[| H |- p;  H |- q->false |] ==> H |- (p->q)->false"
apply (rule deduction)
apply (blast intro: weaken_left_insert thms.MP thms.H) 
done

lemma hyps_thms_if: "hyps p tt |- (if tt[[p]] then p else p->false)"
  -- {* Typical example of strengthening the induction statement. *}
apply simp 
apply (induct_tac "p")
apply (simp_all add: thms_I thms.H)
apply (blast intro: weaken_left_Un1 weaken_left_Un2 weaken_right
                    imp_false false_imp)
done

lemma sat_thms_p: "{} |= p ==> hyps p tt |- p"
  -- {* Key lemma for completeness; yields a set of assumptions 
        satisfying @{text p} *}
apply (unfold sat_def) 
apply (drule spec, erule mp [THEN if_P, THEN subst], 
       rule_tac [2] hyps_thms_if, simp)
done

text {*
  For proving certain theorems in our new propositional logic.
*}

declare deduction [intro!]
declare thms.H [THEN thms.MP, intro]

text {*
  The excluded middle in the form of an elimination rule.
*}

lemma thms_excluded_middle: "H |- (p->q) -> ((p->false)->q) -> q"
apply (rule deduction [THEN deduction])
apply (rule thms.DN [THEN thms.MP], best) 
done

lemma thms_excluded_middle_rule:
    "[| insert p H |- q;  insert (p->false) H |- q |] ==> H |- q"
  -- {* Hard to prove directly because it requires cuts *}
by (rule thms_excluded_middle [THEN thms.MP, THEN thms.MP], auto) 


subsection{* Completeness -- lemmas for reducing the set of assumptions*}

text {*
  For the case @{prop "hyps p t - insert #v Y |- p"} we also have @{prop
  "hyps p t - {#v} \<subseteq> hyps p (t-{v})"}.
*}

lemma hyps_Diff: "hyps p (t-{v}) <= insert (#v->false) ((hyps p t)-{#v})"
by (induct_tac "p", auto) 

text {*
  For the case @{prop "hyps p t - insert (#v -> Fls) Y |- p"} we also have
  @{prop "hyps p t-{#v->Fls} \<subseteq> hyps p (insert v t)"}.
*}

lemma hyps_insert: "hyps p (insert v t) <= insert (#v) (hyps p t-{#v->false})"
by (induct_tac "p", auto)

text {* Two lemmas for use with @{text weaken_left} *}

lemma insert_Diff_same: "B-C <= insert a (B-insert a C)"
by fast

lemma insert_Diff_subset2: "insert a (B-{c}) - D <= insert a (B-insert c D)"
by fast

text {*
  The set @{term "hyps p t"} is finite, and elements have the form
  @{term "#v"} or @{term "#v->Fls"}.
*}

lemma hyps_finite: "finite(hyps p t)"
by (induct_tac "p", auto)

lemma hyps_subset: "hyps p t <= (UN v. {#v, #v->false})"
by (induct_tac "p", auto)

lemmas Diff_weaken_left = Diff_mono [OF _ subset_refl, THEN weaken_left]

subsubsection {* Completeness theorem *}

text {*
  Induction on the finite set of assumptions @{term "hyps p t0"}.  We
  may repeatedly subtract assumptions until none are left!
*}

lemma completeness_0_lemma:
    "{} |= p ==> \<forall>t. hyps p t - hyps p t0 |- p" 
apply (rule hyps_subset [THEN hyps_finite [THEN finite_subset_induct]])
 apply (simp add: sat_thms_p, safe)
(*Case hyps p t-insert(#v,Y) |- p *)
 apply (rule thms_excluded_middle_rule)
  apply (rule insert_Diff_same [THEN weaken_left])
  apply (erule spec)
 apply (rule insert_Diff_subset2 [THEN weaken_left])
 apply (rule hyps_Diff [THEN Diff_weaken_left])
 apply (erule spec)
(*Case hyps p t-insert(#v -> false,Y) |- p *)
apply (rule thms_excluded_middle_rule)
 apply (rule_tac [2] insert_Diff_same [THEN weaken_left])
 apply (erule_tac [2] spec)
apply (rule insert_Diff_subset2 [THEN weaken_left])
apply (rule hyps_insert [THEN Diff_weaken_left])
apply (erule spec)
done

text{*The base case for completeness*}
lemma completeness_0:  "{} |= p ==> {} |- p"
apply (rule Diff_cancel [THEN subst])
apply (erule completeness_0_lemma [THEN spec])
done

text{*A semantic analogue of the Deduction Theorem*}
lemma sat_imp: "insert p H |= q ==> H |= p->q"
by (unfold sat_def, auto)

theorem completeness [rule_format]: "finite H ==> \<forall>p. H |= p --> H |- p"
apply (erule finite_induct)
apply (safe intro!: completeness_0)
apply (drule sat_imp)
apply (drule spec) 
apply (blast intro: weaken_left_insert [THEN thms.MP])  
done

theorem syntax_iff_semantics: "finite H ==> (H |- p) = (H |= p)"
by (fast elim!: soundness completeness)

end

