(*  Title: 	ZF/ex/prop-log.ML
    ID:         $Id$
    Author: 	Tobias Nipkow & Lawrence C Paulson
    Copyright   1992  University of Cambridge

For ex/prop-log.thy.  Inductive definition of propositional logic.
Soundness and completeness w.r.t. truth-tables.

Prove: If H|=p then G|=p where G:Fin(H)
*)

open PropLog;

(*** prop_rec -- by Vset recursion ***)

(** conversion rules **)

goal PropLog.thy "prop_rec(Fls,b,c,d) = b";
by (rtac (prop_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac prop.con_defs);
by (simp_tac rank_ss 1);
qed "prop_rec_Fls";

goal PropLog.thy "prop_rec(#v,b,c,d) = c(v)";
by (rtac (prop_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac prop.con_defs);
by (simp_tac rank_ss 1);
qed "prop_rec_Var";

goal PropLog.thy "prop_rec(p=>q,b,c,d) = \
\      d(p, q, prop_rec(p,b,c,d), prop_rec(q,b,c,d))";
by (rtac (prop_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac prop.con_defs);
by (simp_tac rank_ss 1);
qed "prop_rec_Imp";

val prop_rec_ss = 
    arith_ss addsimps [prop_rec_Fls, prop_rec_Var, prop_rec_Imp];

(*** Semantics of propositional logic ***)

(** The function is_true **)

goalw PropLog.thy [is_true_def] "is_true(Fls,t) <-> False";
by (simp_tac (prop_rec_ss addsimps [one_not_0 RS not_sym]) 1);
qed "is_true_Fls";

goalw PropLog.thy [is_true_def] "is_true(#v,t) <-> v:t";
by (simp_tac (prop_rec_ss addsimps [one_not_0 RS not_sym] 
	      setloop (split_tac [expand_if])) 1);
qed "is_true_Var";

goalw PropLog.thy [is_true_def]
    "is_true(p=>q,t) <-> (is_true(p,t)-->is_true(q,t))";
by (simp_tac (prop_rec_ss setloop (split_tac [expand_if])) 1);
qed "is_true_Imp";

(** The function hyps **)

goalw PropLog.thy [hyps_def] "hyps(Fls,t) = 0";
by (simp_tac prop_rec_ss 1);
qed "hyps_Fls";

goalw PropLog.thy [hyps_def] "hyps(#v,t) = {if(v:t, #v, #v=>Fls)}";
by (simp_tac prop_rec_ss 1);
qed "hyps_Var";

goalw PropLog.thy [hyps_def] "hyps(p=>q,t) = hyps(p,t) Un hyps(q,t)";
by (simp_tac prop_rec_ss 1);
qed "hyps_Imp";

val prop_ss = prop_rec_ss 
    addsimps prop.intrs
    addsimps [is_true_Fls, is_true_Var, is_true_Imp,
	      hyps_Fls, hyps_Var, hyps_Imp];

(*** Proof theory of propositional logic ***)

goalw PropLog.thy thms.defs "!!G H. G<=H ==> thms(G) <= thms(H)";
by (rtac lfp_mono 1);
by (REPEAT (rtac thms.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::basic_monos) 1));
qed "thms_mono";

val thms_in_pl = thms.dom_subset RS subsetD;

val ImpE = prop.mk_cases prop.con_defs "p=>q : prop";

(*Stronger Modus Ponens rule: no typechecking!*)
goal PropLog.thy "!!p q H. [| H |- p=>q;  H |- p |] ==> H |- q";
by (rtac thms.MP 1);
by (REPEAT (eresolve_tac [asm_rl, thms_in_pl, thms_in_pl RS ImpE] 1));
qed "thms_MP";

(*Rule is called I for Identity Combinator, not for Introduction*)
goal PropLog.thy "!!p H. p:prop ==> H |- p=>p";
by (rtac (thms.S RS thms_MP RS thms_MP) 1);
by (rtac thms.K 5);
by (rtac thms.K 4);
by (REPEAT (ares_tac prop.intrs 1));
qed "thms_I";

(** Weakening, left and right **)

(* [| G<=H;  G|-p |] ==> H|-p   Order of premises is convenient with RS*)
bind_thm ("weaken_left", (thms_mono RS subsetD));

(* H |- p ==> cons(a,H) |- p *)
val weaken_left_cons = subset_consI RS weaken_left;

val weaken_left_Un1  = Un_upper1 RS weaken_left;
val weaken_left_Un2  = Un_upper2 RS weaken_left;

goal PropLog.thy "!!H p q. [| H |- q;  p:prop |] ==> H |- p=>q";
by (rtac (thms.K RS thms_MP) 1);
by (REPEAT (ares_tac [thms_in_pl] 1));
qed "weaken_right";

(*The deduction theorem*)
goal PropLog.thy "!!p q H. [| cons(p,H) |- q;  p:prop |] ==>  H |- p=>q";
by (etac thms.induct 1);
by (fast_tac (ZF_cs addIs [thms_I, thms.H RS weaken_right]) 1);
by (fast_tac (ZF_cs addIs [thms.K RS weaken_right]) 1);
by (fast_tac (ZF_cs addIs [thms.S RS weaken_right]) 1);
by (fast_tac (ZF_cs addIs [thms.DN RS weaken_right]) 1);
by (fast_tac (ZF_cs addIs [thms.S RS thms_MP RS thms_MP]) 1);
qed "deduction";


(*The cut rule*)
goal PropLog.thy "!!H p q. [| H|-p;  cons(p,H) |- q |] ==>  H |- q";
by (rtac (deduction RS thms_MP) 1);
by (REPEAT (ares_tac [thms_in_pl] 1));
qed "cut";

goal PropLog.thy "!!H p. [| H |- Fls; p:prop |] ==> H |- p";
by (rtac (thms.DN RS thms_MP) 1);
by (rtac weaken_right 2);
by (REPEAT (ares_tac (prop.intrs@[consI1]) 1));
qed "thms_FlsE";

(* [| H |- p=>Fls;  H |- p;  q: prop |] ==> H |- q *)
bind_thm ("thms_notE", (thms_MP RS thms_FlsE));

(*Soundness of the rules wrt truth-table semantics*)
goalw PropLog.thy [logcon_def] "!!H. H |- p ==> H |= p";
by (etac thms.induct 1);
by (fast_tac (ZF_cs addSDs [is_true_Imp RS iffD1 RS mp]) 5);
by (ALLGOALS (asm_simp_tac prop_ss));
qed "soundness";

(*** Towards the completeness proof ***)

val [premf,premq] = goal PropLog.thy
    "[| H |- p=>Fls; q: prop |] ==> H |- p=>q";
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
val [major] = goal PropLog.thy 
    "p: prop ==> hyps(p,t) |- if(is_true(p,t), p, p=>Fls)";
by (rtac (expand_if RS iffD2) 1);
by (rtac (major RS prop.induct) 1);
by (ALLGOALS (asm_simp_tac (prop_ss addsimps [thms_I, thms.H])));
by (safe_tac (ZF_cs addSEs [Fls_Imp RS weaken_left_Un1, 
			    Fls_Imp RS weaken_left_Un2]));
by (ALLGOALS (fast_tac (ZF_cs addIs [weaken_left_Un1, weaken_left_Un2, 
				     weaken_right, Imp_Fls])));
qed "hyps_thms_if";

(*Key lemma for completeness; yields a set of assumptions satisfying p*)
val [premp,sat] = goalw PropLog.thy [logcon_def]
    "[| p: prop;  0 |= p |] ==> hyps(p,t) |- p";
by (rtac (sat RS spec RS mp RS if_P RS subst) 1 THEN
    rtac (premp RS hyps_thms_if) 2);
by (fast_tac ZF_cs 1);
qed "logcon_thms_p";

(*For proving certain theorems in our new propositional logic*)
val thms_cs = 
    ZF_cs addSIs (prop.intrs @ [deduction])
          addIs [thms_in_pl, thms.H, thms.H RS thms_MP];

(*The excluded middle in the form of an elimination rule*)
val prems = goal PropLog.thy
    "[| p: prop;  q: prop |] ==> H |- (p=>q) => ((p=>Fls)=>q) => q";
by (rtac (deduction RS deduction) 1);
by (rtac (thms.DN RS thms_MP) 1);
by (ALLGOALS (best_tac (thms_cs addSIs prems)));
qed "thms_excluded_middle";

(*Hard to prove directly because it requires cuts*)
val prems = goal PropLog.thy
    "[| cons(p,H) |- q;  cons(p=>Fls,H) |- q;  p: prop |] ==> H |- q";
by (rtac (thms_excluded_middle RS thms_MP RS thms_MP) 1);
by (REPEAT (resolve_tac (prems@prop.intrs@[deduction,thms_in_pl]) 1));
qed "thms_excluded_middle_rule";

(*** Completeness -- lemmas for reducing the set of assumptions ***)

(*For the case hyps(p,t)-cons(#v,Y) |- p;
  we also have hyps(p,t)-{#v} <= hyps(p, t-{v}) *)
val [major] = goal PropLog.thy
    "p: prop ==> hyps(p, t-{v}) <= cons(#v=>Fls, hyps(p,t)-{#v})";
by (rtac (major RS prop.induct) 1);
by (simp_tac prop_ss 1);
by (asm_simp_tac (prop_ss setloop (split_tac [expand_if])) 1);
by (fast_tac (ZF_cs addSEs prop.free_SEs) 1);
by (asm_simp_tac prop_ss 1);
by (fast_tac ZF_cs 1);
qed "hyps_Diff";

(*For the case hyps(p,t)-cons(#v => Fls,Y) |- p;
  we also have hyps(p,t)-{#v=>Fls} <= hyps(p, cons(v,t)) *)
val [major] = goal PropLog.thy
    "p: prop ==> hyps(p, cons(v,t)) <= cons(#v, hyps(p,t)-{#v=>Fls})";
by (rtac (major RS prop.induct) 1);
by (simp_tac prop_ss 1);
by (asm_simp_tac (prop_ss setloop (split_tac [expand_if])) 1);
by (fast_tac (ZF_cs addSEs prop.free_SEs) 1);
by (asm_simp_tac prop_ss 1);
by (fast_tac ZF_cs 1);
qed "hyps_cons";

(** Two lemmas for use with weaken_left **)

goal ZF.thy "B-C <= cons(a, B-cons(a,C))";
by (fast_tac ZF_cs 1);
qed "cons_Diff_same";

goal ZF.thy "cons(a, B-{c}) - D <= cons(a, B-cons(c,D))";
by (fast_tac ZF_cs 1);
qed "cons_Diff_subset2";

(*The set hyps(p,t) is finite, and elements have the form #v or #v=>Fls;
 could probably prove the stronger hyps(p,t) : Fin(hyps(p,0) Un hyps(p,nat))*)
val [major] = goal PropLog.thy
    "p: prop ==> hyps(p,t) : Fin(UN v:nat. {#v, #v=>Fls})";
by (rtac (major RS prop.induct) 1);
by (asm_simp_tac (prop_ss addsimps (Fin.intrs @ [UN_I, cons_iff])
		  setloop (split_tac [expand_if])) 2);
by (ALLGOALS (asm_simp_tac (prop_ss addsimps [Un_0, Fin.emptyI, Fin_UnI])));
qed "hyps_finite";

val Diff_weaken_left = subset_refl RSN (2, Diff_mono) RS weaken_left;

(*Induction on the finite set of assumptions hyps(p,t0).
  We may repeatedly subtract assumptions until none are left!*)
val [premp,sat] = goal PropLog.thy
    "[| p: prop;  0 |= p |] ==> ALL t. hyps(p,t) - hyps(p,t0) |- p";
by (rtac (premp RS hyps_finite RS Fin_induct) 1);
by (simp_tac (prop_ss addsimps [premp, sat, logcon_thms_p, Diff_0]) 1);
by (safe_tac ZF_cs);
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
val [premp,sat] = goal PropLog.thy "[| p: prop;  0 |= p |] ==> 0 |- p";
by (rtac (Diff_cancel RS subst) 1);
by (rtac (sat RS (premp RS completeness_0_lemma RS spec)) 1);
qed "completeness_0";

(*A semantic analogue of the Deduction Theorem*)
goalw PropLog.thy [logcon_def] "!!H p q. [| cons(p,H) |= q |] ==> H |= p=>q";
by (simp_tac prop_ss 1);
by (fast_tac ZF_cs 1);
qed "logcon_Imp";

goal PropLog.thy "!!H. H: Fin(prop) ==> ALL p:prop. H |= p --> H |- p";
by (etac Fin_induct 1);
by (safe_tac (ZF_cs addSIs [completeness_0]));
by (rtac (weaken_left_cons RS thms_MP) 1);
by (fast_tac (ZF_cs addSIs (logcon_Imp::prop.intrs)) 1);
by (fast_tac thms_cs 1);
qed "completeness_lemma";

val completeness = completeness_lemma RS bspec RS mp;

val [finite] = goal PropLog.thy "H: Fin(prop) ==> H |- p <-> H |= p & p:prop";
by (fast_tac (ZF_cs addSEs [soundness, finite RS completeness, 
			    thms_in_pl]) 1);
qed "thms_iff";

writeln"Reached end of file.";
