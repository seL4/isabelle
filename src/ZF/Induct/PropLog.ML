(*  Title:      ZF/ex/prop-log.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Lawrence C Paulson
    Copyright   1992  University of Cambridge

Inductive definition of propositional logic.
Soundness and completeness w.r.t. truth-tables.

Prove: If H|=p then G|=p where G \\<in> Fin(H)
*)

Addsimps prop.intrs;

(*** Semantics of propositional logic ***)

(** The function is_true **)

Goalw [is_true_def] "is_true(Fls,t) <-> False";
by (Simp_tac 1);
qed "is_true_Fls";

Goalw [is_true_def] "is_true(#v,t) <-> v \\<in> t";
by (Simp_tac 1);
qed "is_true_Var";

Goalw [is_true_def] "is_true(p=>q,t) <-> (is_true(p,t)-->is_true(q,t))";
by (Simp_tac 1);
qed "is_true_Imp";

Addsimps [is_true_Fls, is_true_Var, is_true_Imp];


(*** Proof theory of propositional logic ***)

Goalw thms.defs "G \\<subseteq> H ==> thms(G) \\<subseteq> thms(H)";
by (rtac lfp_mono 1);
by (REPEAT (rtac thms.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::basic_monos) 1));
qed "thms_mono";

val thms_in_pl = thms.dom_subset RS subsetD;

val ImpE = prop.mk_cases "p=>q \\<in> prop";

(*Stronger Modus Ponens rule: no typechecking!*)
Goal "[| H |- p=>q;  H |- p |] ==> H |- q";
by (rtac thms.MP 1);
by (REPEAT (eresolve_tac [asm_rl, thms_in_pl, thms_in_pl RS ImpE] 1));
qed "thms_MP";

(*Rule is called I for Identity Combinator, not for Introduction*)
Goal "p \\<in> prop ==> H |- p=>p";
by (rtac (thms.S RS thms_MP RS thms_MP) 1);
by (rtac thms.K 5);
by (rtac thms.K 4);
by (REPEAT (ares_tac prop.intrs 1));
qed "thms_I";

(** Weakening, left and right **)

(* [| G \\<subseteq> H;  G|-p |] ==> H|-p   Order of premises is convenient with RS*)
bind_thm ("weaken_left", (thms_mono RS subsetD));

(* H |- p ==> cons(a,H) |- p *)
val weaken_left_cons = subset_consI RS weaken_left;

val weaken_left_Un1  = Un_upper1 RS weaken_left;
val weaken_left_Un2  = Un_upper2 RS weaken_left;

Goal "[| H |- q;  p \\<in> prop |] ==> H |- p=>q";
by (rtac (thms.K RS thms_MP) 1);
by (REPEAT (ares_tac [thms_in_pl] 1));
qed "weaken_right";

(*The deduction theorem*)
Goal "[| cons(p,H) |- q;  p \\<in> prop |] ==>  H |- p=>q";
by (etac thms.induct 1);
by (blast_tac (claset() addIs [thms_I, thms.H RS weaken_right]) 1);
by (blast_tac (claset() addIs [thms.K RS weaken_right]) 1);
by (blast_tac (claset() addIs [thms.S RS weaken_right]) 1);
by (blast_tac (claset() addIs [thms.DN RS weaken_right]) 1);
by (blast_tac (claset() addIs [thms.S RS thms_MP RS thms_MP]) 1);
qed "deduction";


(*The cut rule*)
Goal "[| H|-p;  cons(p,H) |- q |] ==>  H |- q";
by (rtac (deduction RS thms_MP) 1);
by (REPEAT (ares_tac [thms_in_pl] 1));
qed "cut";

Goal "[| H |- Fls; p \\<in> prop |] ==> H |- p";
by (rtac (thms.DN RS thms_MP) 1);
by (rtac weaken_right 2);
by (REPEAT (ares_tac (prop.intrs@[consI1]) 1));
qed "thms_FlsE";

(* [| H |- p=>Fls;  H |- p;  q \\<in> prop |] ==> H |- q *)
bind_thm ("thms_notE", (thms_MP RS thms_FlsE));

(*Soundness of the rules wrt truth-table semantics*)
Goalw [logcon_def] "H |- p ==> H |= p";
by (etac thms.induct 1);
by Auto_tac;
qed "soundness";

(*** Towards the completeness proof ***)

val [premf,premq] = goal PropLog.thy
    "[| H |- p=>Fls; q \\<in> prop |] ==> H |- p=>q";
by (rtac (premf RS thms_in_pl RS ImpE) 1);
by (rtac deduction 1);
by (rtac (premf RS weaken_left_cons RS thms_notE) 1);
by (REPEAT (ares_tac [premq, consI1, thms.H] 1));
qed "Fls_Imp";

val [premp,premq] = goal PropLog.thy
    "[| H |- p;  H |- q=>Fls |] ==> H |- (p=>q)=>Fls";
by (cut_facts_tac ([premp,premq] RL [thms_in_pl]) 1);
by (etac ImpE 1);
by (rtac deduction 1);
by (rtac (premq RS weaken_left_cons RS thms_MP) 1);
by (rtac (consI1 RS thms.H RS thms_MP) 1);
by (rtac (premp RS weaken_left_cons) 2);
by (REPEAT (ares_tac prop.intrs 1));
qed "Imp_Fls";

(*Typical example of strengthening the induction formula*)
Goal "p \\<in> prop ==> hyps(p,t) |- (if is_true(p,t) then p else p=>Fls)";
by (Simp_tac 1);
by (induct_tac "p" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [thms_I, thms.H])));
by (safe_tac (claset() addSEs [Fls_Imp RS weaken_left_Un1, 
			       Fls_Imp RS weaken_left_Un2]));
by (ALLGOALS (blast_tac (claset() addIs [weaken_left_Un1, weaken_left_Un2, 
					weaken_right, Imp_Fls])));
qed "hyps_thms_if";

(*Key lemma for completeness; yields a set of assumptions satisfying p*)
Goalw [logcon_def] "[| p \\<in> prop;  0 |= p |] ==> hyps(p,t) |- p";
by (dtac hyps_thms_if 1);
by (Asm_full_simp_tac 1);
qed "logcon_thms_p";

(*For proving certain theorems in our new propositional logic*)
val thms_cs = 
    ZF_cs addSIs (prop.intrs @ [deduction])
          addIs [thms_in_pl, thms.H, thms.H RS thms_MP];

(*The excluded middle in the form of an elimination rule*)
Goal "[| p \\<in> prop;  q \\<in> prop |] ==> H |- (p=>q) => ((p=>Fls)=>q) => q";
by (rtac (deduction RS deduction) 1);
by (rtac (thms.DN RS thms_MP) 1);
by (ALLGOALS (blast_tac thms_cs));
qed "thms_excluded_middle";

(*Hard to prove directly because it requires cuts*)
Goal "[| cons(p,H) |- q;  cons(p=>Fls,H) |- q;  p \\<in> prop |] ==> H |- q";
by (rtac (thms_excluded_middle RS thms_MP RS thms_MP) 1);
by (REPEAT (ares_tac (prop.intrs@[deduction,thms_in_pl]) 1));
qed "thms_excluded_middle_rule";

(*** Completeness -- lemmas for reducing the set of assumptions ***)

(*For the case hyps(p,t)-cons(#v,Y) |- p;
  we also have hyps(p,t)-{#v} \\<subseteq> hyps(p, t-{v}) *)
Goal "p \\<in> prop ==> hyps(p, t-{v}) \\<subseteq> cons(#v=>Fls, hyps(p,t)-{#v})";
by (induct_tac "p" 1);
by Auto_tac;
qed "hyps_Diff";

(*For the case hyps(p,t)-cons(#v => Fls,Y) |- p;
  we also have hyps(p,t)-{#v=>Fls} \\<subseteq> hyps(p, cons(v,t)) *)
Goal "p \\<in> prop ==> hyps(p, cons(v,t)) \\<subseteq> cons(#v, hyps(p,t)-{#v=>Fls})";
by (induct_tac "p" 1);
by Auto_tac;
qed "hyps_cons";

(** Two lemmas for use with weaken_left **)

Goal "B-C \\<subseteq> cons(a, B-cons(a,C))";
by (Fast_tac 1);
qed "cons_Diff_same";

Goal "cons(a, B-{c}) - D \\<subseteq> cons(a, B-cons(c,D))";
by (Fast_tac 1);
qed "cons_Diff_subset2";

(*The set hyps(p,t) is finite, and elements have the form #v or #v=>Fls;
 could probably prove the stronger hyps(p,t) \\<in> Fin(hyps(p,0) Un hyps(p,nat))*)
Goal "p \\<in> prop ==> hyps(p,t) \\<in> Fin(\\<Union>v \\<in> nat. {#v, #v=>Fls})";
by (induct_tac "p" 1);
by Auto_tac;  
qed "hyps_finite";

val Diff_weaken_left = subset_refl RSN (2, Diff_mono) RS weaken_left;

(*Induction on the finite set of assumptions hyps(p,t0).
  We may repeatedly subtract assumptions until none are left!*)
val [premp,sat] = goal PropLog.thy
    "[| p \\<in> prop;  0 |= p |] ==> \\<forall>t. hyps(p,t) - hyps(p,t0) |- p";
by (rtac (premp RS hyps_finite RS Fin_induct) 1);
by (simp_tac (simpset() addsimps [premp, sat, logcon_thms_p, Diff_0]) 1);
by Safe_tac;
(*Case hyps(p,t)-cons(#v,Y) |- p *)
by (rtac thms_excluded_middle_rule 1);
by (etac prop.Var_I 3);
by (rtac (cons_Diff_same RS weaken_left) 1);
by (etac spec 1);
by (rtac (cons_Diff_subset2 RS weaken_left) 1);
by (rtac (premp RS hyps_Diff RS Diff_weaken_left) 1);
by (etac spec 1);
(*Case hyps(p,t)-cons(#v => Fls,Y) |- p *)
by (rtac thms_excluded_middle_rule 1);
by (etac prop.Var_I 3);
by (rtac (cons_Diff_same RS weaken_left) 2);
by (etac spec 2);
by (rtac (cons_Diff_subset2 RS weaken_left) 1);
by (rtac (premp RS hyps_cons RS Diff_weaken_left) 1);
by (etac spec 1);
qed "completeness_0_lemma";

(*The base case for completeness*)
val [premp,sat] = goal PropLog.thy "[| p \\<in> prop;  0 |= p |] ==> 0 |- p";
by (rtac (Diff_cancel RS subst) 1);
by (rtac (sat RS (premp RS completeness_0_lemma RS spec)) 1);
qed "completeness_0";

(*A semantic analogue of the Deduction Theorem*)
Goalw [logcon_def] "[| cons(p,H) |= q |] ==> H |= p=>q";
by Auto_tac;
qed "logcon_Imp";

Goal "H \\<in> Fin(prop) ==> \\<forall>p \\<in> prop. H |= p --> H |- p";
by (etac Fin_induct 1);
by (safe_tac (claset() addSIs [completeness_0]));
by (rtac (weaken_left_cons RS thms_MP) 1);
by (blast_tac (claset() addSIs (logcon_Imp::prop.intrs)) 1);
by (blast_tac thms_cs 1);
qed "completeness_lemma";

val completeness = completeness_lemma RS bspec RS mp;

val [finite] = goal PropLog.thy "H \\<in> Fin(prop) ==> H |- p <-> H |= p & p \\<in> prop";
by (fast_tac (claset() addSEs [soundness, finite RS completeness, 
			       thms_in_pl]) 1);
qed "thms_iff";

writeln"Reached end of file.";
