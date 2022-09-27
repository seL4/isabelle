(*  Title:      ZF/Induct/PropLog.thy
    Author:     Tobias Nipkow \<and> Lawrence C Paulson
    Copyright   1993  University of Cambridge
*)

section \<open>Meta-theory of propositional logic\<close>

theory PropLog imports ZF begin

text \<open>
  Datatype definition of propositional logic formulae and inductive
  definition of the propositional tautologies.

  Inductive definition of propositional logic.  Soundness and
  completeness w.r.t.\ truth-tables.

  Prove: If \<open>H |= p\<close> then \<open>G |= p\<close> where \<open>G \<in>
  Fin(H)\<close>
\<close>


subsection \<open>The datatype of propositions\<close>

consts
  propn :: i

datatype propn =
    Fls
  | Var ("n \<in> nat")    (\<open>#_\<close> [100] 100)
  | Imp ("p \<in> propn", "q \<in> propn")    (infixr \<open>\<Rightarrow>\<close> 90)


subsection \<open>The proof system\<close>

consts thms     :: "i \<Rightarrow> i"

abbreviation
  thms_syntax :: "[i,i] \<Rightarrow> o"    (infixl \<open>|-\<close> 50)
  where "H |- p \<equiv> p \<in> thms(H)"

inductive
  domains "thms(H)" \<subseteq> "propn"
  intros
    H:  "\<lbrakk>p \<in> H;  p \<in> propn\<rbrakk> \<Longrightarrow> H |- p"
    K:  "\<lbrakk>p \<in> propn;  q \<in> propn\<rbrakk> \<Longrightarrow> H |- p\<Rightarrow>q\<Rightarrow>p"
    S:  "\<lbrakk>p \<in> propn;  q \<in> propn;  r \<in> propn\<rbrakk>
         \<Longrightarrow> H |- (p\<Rightarrow>q\<Rightarrow>r) \<Rightarrow> (p\<Rightarrow>q) \<Rightarrow> p\<Rightarrow>r"
    DN: "p \<in> propn \<Longrightarrow> H |- ((p\<Rightarrow>Fls) \<Rightarrow> Fls) \<Rightarrow> p"
    MP: "\<lbrakk>H |- p\<Rightarrow>q;  H |- p;  p \<in> propn;  q \<in> propn\<rbrakk> \<Longrightarrow> H |- q"
  type_intros "propn.intros"

declare propn.intros [simp]


subsection \<open>The semantics\<close>

subsubsection \<open>Semantics of propositional logic.\<close>

consts
  is_true_fun :: "[i,i] \<Rightarrow> i"
primrec
  "is_true_fun(Fls, t) = 0"
  "is_true_fun(Var(v), t) = (if v \<in> t then 1 else 0)"
  "is_true_fun(p\<Rightarrow>q, t) = (if is_true_fun(p,t) = 1 then is_true_fun(q,t) else 1)"

definition
  is_true :: "[i,i] \<Rightarrow> o"  where
  "is_true(p,t) \<equiv> is_true_fun(p,t) = 1"
  \<comment> \<open>this definition is required since predicates can't be recursive\<close>

lemma is_true_Fls [simp]: "is_true(Fls,t) \<longleftrightarrow> False"
  by (simp add: is_true_def)

lemma is_true_Var [simp]: "is_true(#v,t) \<longleftrightarrow> v \<in> t"
  by (simp add: is_true_def)

lemma is_true_Imp [simp]: "is_true(p\<Rightarrow>q,t) \<longleftrightarrow> (is_true(p,t)\<longrightarrow>is_true(q,t))"
  by (simp add: is_true_def)


subsubsection \<open>Logical consequence\<close>

text \<open>
  For every valuation, if all elements of \<open>H\<close> are true then so
  is \<open>p\<close>.
\<close>

definition
  logcon :: "[i,i] \<Rightarrow> o"    (infixl \<open>|=\<close> 50)  where
  "H |= p \<equiv> \<forall>t. (\<forall>q \<in> H. is_true(q,t)) \<longrightarrow> is_true(p,t)"


text \<open>
  A finite set of hypotheses from \<open>t\<close> and the \<open>Var\<close>s in
  \<open>p\<close>.
\<close>

consts
  hyps :: "[i,i] \<Rightarrow> i"
primrec
  "hyps(Fls, t) = 0"
  "hyps(Var(v), t) = (if v \<in> t then {#v} else {#v\<Rightarrow>Fls})"
  "hyps(p\<Rightarrow>q, t) = hyps(p,t) \<union> hyps(q,t)"



subsection \<open>Proof theory of propositional logic\<close>

lemma thms_mono: "G \<subseteq> H \<Longrightarrow> thms(G) \<subseteq> thms(H)"
  apply (unfold thms.defs)
  apply (rule lfp_mono)
    apply (rule thms.bnd_mono)+
  apply (assumption | rule univ_mono basic_monos)+
  done

lemmas thms_in_pl = thms.dom_subset [THEN subsetD]

inductive_cases ImpE: "p\<Rightarrow>q \<in> propn"

lemma thms_MP: "\<lbrakk>H |- p\<Rightarrow>q;  H |- p\<rbrakk> \<Longrightarrow> H |- q"
  \<comment> \<open>Stronger Modus Ponens rule: no typechecking!\<close>
  apply (rule thms.MP)
     apply (erule asm_rl thms_in_pl thms_in_pl [THEN ImpE])+
  done

lemma thms_I: "p \<in> propn \<Longrightarrow> H |- p\<Rightarrow>p"
  \<comment> \<open>Rule is called \<open>I\<close> for Identity Combinator, not for Introduction.\<close>
  apply (rule thms.S [THEN thms_MP, THEN thms_MP])
      apply (rule_tac [5] thms.K)
       apply (rule_tac [4] thms.K)
         apply simp_all
  done


subsubsection \<open>Weakening, left and right\<close>

lemma weaken_left: "\<lbrakk>G \<subseteq> H;  G|-p\<rbrakk> \<Longrightarrow> H|-p"
  \<comment> \<open>Order of premises is convenient with \<open>THEN\<close>\<close>
  by (erule thms_mono [THEN subsetD])

lemma weaken_left_cons: "H |- p \<Longrightarrow> cons(a,H) |- p"
  by (erule subset_consI [THEN weaken_left])

lemmas weaken_left_Un1  = Un_upper1 [THEN weaken_left]
lemmas weaken_left_Un2  = Un_upper2 [THEN weaken_left]

lemma weaken_right: "\<lbrakk>H |- q;  p \<in> propn\<rbrakk> \<Longrightarrow> H |- p\<Rightarrow>q"
  by (simp_all add: thms.K [THEN thms_MP] thms_in_pl)


subsubsection \<open>The deduction theorem\<close>

theorem deduction: "\<lbrakk>cons(p,H) |- q;  p \<in> propn\<rbrakk> \<Longrightarrow>  H |- p\<Rightarrow>q"
  apply (erule thms.induct)
      apply (blast intro: thms_I thms.H [THEN weaken_right])
     apply (blast intro: thms.K [THEN weaken_right])
    apply (blast intro: thms.S [THEN weaken_right])
   apply (blast intro: thms.DN [THEN weaken_right])
  apply (blast intro: thms.S [THEN thms_MP [THEN thms_MP]])
  done


subsubsection \<open>The cut rule\<close>

lemma cut: "\<lbrakk>H|-p;  cons(p,H) |- q\<rbrakk> \<Longrightarrow>  H |- q"
  apply (rule deduction [THEN thms_MP])
    apply (simp_all add: thms_in_pl)
  done

lemma thms_FlsE: "\<lbrakk>H |- Fls; p \<in> propn\<rbrakk> \<Longrightarrow> H |- p"
  apply (rule thms.DN [THEN thms_MP])
   apply (rule_tac [2] weaken_right)
    apply (simp_all add: propn.intros)
  done

lemma thms_notE: "\<lbrakk>H |- p\<Rightarrow>Fls;  H |- p;  q \<in> propn\<rbrakk> \<Longrightarrow> H |- q"
  by (erule thms_MP [THEN thms_FlsE])


subsubsection \<open>Soundness of the rules wrt truth-table semantics\<close>

theorem soundness: "H |- p \<Longrightarrow> H |= p"
  apply (unfold logcon_def)
  apply (induct set: thms)
      apply auto
  done


subsection \<open>Completeness\<close>

subsubsection \<open>Towards the completeness proof\<close>

lemma Fls_Imp: "\<lbrakk>H |- p\<Rightarrow>Fls; q \<in> propn\<rbrakk> \<Longrightarrow> H |- p\<Rightarrow>q"
  apply (frule thms_in_pl)
  apply (rule deduction)
   apply (rule weaken_left_cons [THEN thms_notE])
     apply (blast intro: thms.H elim: ImpE)+
  done

lemma Imp_Fls: "\<lbrakk>H |- p;  H |- q\<Rightarrow>Fls\<rbrakk> \<Longrightarrow> H |- (p\<Rightarrow>q)\<Rightarrow>Fls"
  apply (frule thms_in_pl)
  apply (frule thms_in_pl [of concl: "q\<Rightarrow>Fls"])
  apply (rule deduction)
   apply (erule weaken_left_cons [THEN thms_MP])
   apply (rule consI1 [THEN thms.H, THEN thms_MP])
    apply (blast intro: weaken_left_cons elim: ImpE)+
  done

lemma hyps_thms_if:
    "p \<in> propn \<Longrightarrow> hyps(p,t) |- (if is_true(p,t) then p else p\<Rightarrow>Fls)"
  \<comment> \<open>Typical example of strengthening the induction statement.\<close>
  apply simp
  apply (induct_tac p)
    apply (simp_all add: thms_I thms.H)
  apply (safe elim!: Fls_Imp [THEN weaken_left_Un1] Fls_Imp [THEN weaken_left_Un2])
  apply (blast intro: weaken_left_Un1 weaken_left_Un2 weaken_right Imp_Fls)+
  done

lemma logcon_thms_p: "\<lbrakk>p \<in> propn;  0 |= p\<rbrakk> \<Longrightarrow> hyps(p,t) |- p"
  \<comment> \<open>Key lemma for completeness; yields a set of assumptions satisfying \<open>p\<close>\<close>
  apply (drule hyps_thms_if)
  apply (simp add: logcon_def)
  done

text \<open>
  For proving certain theorems in our new propositional logic.
\<close>

lemmas propn_SIs = propn.intros deduction
  and propn_Is = thms_in_pl thms.H thms.H [THEN thms_MP]

text \<open>
  The excluded middle in the form of an elimination rule.
\<close>

lemma thms_excluded_middle:
    "\<lbrakk>p \<in> propn;  q \<in> propn\<rbrakk> \<Longrightarrow> H |- (p\<Rightarrow>q) \<Rightarrow> ((p\<Rightarrow>Fls)\<Rightarrow>q) \<Rightarrow> q"
  apply (rule deduction [THEN deduction])
    apply (rule thms.DN [THEN thms_MP])
     apply (best intro!: propn_SIs intro: propn_Is)+
  done

lemma thms_excluded_middle_rule:
  "\<lbrakk>cons(p,H) |- q;  cons(p\<Rightarrow>Fls,H) |- q;  p \<in> propn\<rbrakk> \<Longrightarrow> H |- q"
  \<comment> \<open>Hard to prove directly because it requires cuts\<close>
  apply (rule thms_excluded_middle [THEN thms_MP, THEN thms_MP])
     apply (blast intro!: propn_SIs intro: propn_Is)+
  done


subsubsection \<open>Completeness -- lemmas for reducing the set of assumptions\<close>

text \<open>
  For the case \<^prop>\<open>hyps(p,t)-cons(#v,Y) |- p\<close> we also have \<^prop>\<open>hyps(p,t)-{#v} \<subseteq> hyps(p, t-{v})\<close>.
\<close>

lemma hyps_Diff:
    "p \<in> propn \<Longrightarrow> hyps(p, t-{v}) \<subseteq> cons(#v\<Rightarrow>Fls, hyps(p,t)-{#v})"
  by (induct set: propn) auto

text \<open>
  For the case \<^prop>\<open>hyps(p,t)-cons(#v \<Rightarrow> Fls,Y) |- p\<close> we also have
  \<^prop>\<open>hyps(p,t)-{#v\<Rightarrow>Fls} \<subseteq> hyps(p, cons(v,t))\<close>.
\<close>

lemma hyps_cons:
    "p \<in> propn \<Longrightarrow> hyps(p, cons(v,t)) \<subseteq> cons(#v, hyps(p,t)-{#v\<Rightarrow>Fls})"
  by (induct set: propn) auto

text \<open>Two lemmas for use with \<open>weaken_left\<close>\<close>

lemma cons_Diff_same: "B-C \<subseteq> cons(a, B-cons(a,C))"
  by blast

lemma cons_Diff_subset2: "cons(a, B-{c}) - D \<subseteq> cons(a, B-cons(c,D))"
  by blast

text \<open>
  The set \<^term>\<open>hyps(p,t)\<close> is finite, and elements have the form
  \<^term>\<open>#v\<close> or \<^term>\<open>#v\<Rightarrow>Fls\<close>; could probably prove the stronger
  \<^prop>\<open>hyps(p,t) \<in> Fin(hyps(p,0) \<union> hyps(p,nat))\<close>.
\<close>

lemma hyps_finite: "p \<in> propn \<Longrightarrow> hyps(p,t) \<in> Fin(\<Union>v \<in> nat. {#v, #v\<Rightarrow>Fls})"
  by (induct set: propn) auto

lemmas Diff_weaken_left = Diff_mono [OF _ subset_refl, THEN weaken_left]

text \<open>
  Induction on the finite set of assumptions \<^term>\<open>hyps(p,t0)\<close>.  We
  may repeatedly subtract assumptions until none are left!
\<close>

lemma completeness_0_lemma [rule_format]:
    "\<lbrakk>p \<in> propn;  0 |= p\<rbrakk> \<Longrightarrow> \<forall>t. hyps(p,t) - hyps(p,t0) |- p"
  apply (frule hyps_finite)
  apply (erule Fin_induct)
   apply (simp add: logcon_thms_p Diff_0)
  txt \<open>inductive step\<close>
  apply safe
   txt \<open>Case \<^prop>\<open>hyps(p,t)-cons(#v,Y) |- p\<close>\<close>
   apply (rule thms_excluded_middle_rule)
     apply (erule_tac [3] propn.intros)
    apply (blast intro: cons_Diff_same [THEN weaken_left])
   apply (blast intro: cons_Diff_subset2 [THEN weaken_left]
     hyps_Diff [THEN Diff_weaken_left])
  txt \<open>Case \<^prop>\<open>hyps(p,t)-cons(#v \<Rightarrow> Fls,Y) |- p\<close>\<close>
  apply (rule thms_excluded_middle_rule)
    apply (erule_tac [3] propn.intros)
   apply (blast intro: cons_Diff_subset2 [THEN weaken_left]
     hyps_cons [THEN Diff_weaken_left])
  apply (blast intro: cons_Diff_same [THEN weaken_left])
  done


subsubsection \<open>Completeness theorem\<close>

lemma completeness_0: "\<lbrakk>p \<in> propn;  0 |= p\<rbrakk> \<Longrightarrow> 0 |- p"
  \<comment> \<open>The base case for completeness\<close>
  apply (rule Diff_cancel [THEN subst])
  apply (blast intro: completeness_0_lemma)
  done

lemma logcon_Imp: "\<lbrakk>cons(p,H) |= q\<rbrakk> \<Longrightarrow> H |= p\<Rightarrow>q"
  \<comment> \<open>A semantic analogue of the Deduction Theorem\<close>
  by (simp add: logcon_def)

lemma completeness:
     "H \<in> Fin(propn) \<Longrightarrow> p \<in> propn \<Longrightarrow> H |= p \<Longrightarrow> H |- p"
  apply (induct arbitrary: p set: Fin)
   apply (safe intro!: completeness_0)
  apply (rule weaken_left_cons [THEN thms_MP])
   apply (blast intro!: logcon_Imp propn.intros)
  apply (blast intro: propn_Is)
  done

theorem thms_iff: "H \<in> Fin(propn) \<Longrightarrow> H |- p \<longleftrightarrow> H |= p \<and> p \<in> propn"
  by (blast intro: soundness completeness thms_in_pl)

end
