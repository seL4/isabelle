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
by (rewrite_goals_tac Prop.con_defs);
by (simp_tac rank_ss 1);
val prop_rec_Fls = result();

goal PropLog.thy "prop_rec(#v,b,c,d) = c(v)";
by (rtac (prop_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac Prop.con_defs);
by (simp_tac rank_ss 1);
val prop_rec_Var = result();

goal PropLog.thy "prop_rec(p=>q,b,c,d) = \
\      d(p, q, prop_rec(p,b,c,d), prop_rec(q,b,c,d))";
by (rtac (prop_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac Prop.con_defs);
by (simp_tac rank_ss 1);
val prop_rec_Imp = result();

val prop_rec_ss = 
    arith_ss addsimps [prop_rec_Fls, prop_rec_Var, prop_rec_Imp];

(*** Semantics of propositional logic ***)

(** The function is_true **)

goalw PropLog.thy [is_true_def] "is_true(Fls,t) <-> False";
by (simp_tac (prop_rec_ss addsimps [one_not_0 RS not_sym]) 1);
val is_true_Fls = result();

goalw PropLog.thy [is_true_def] "is_true(#v,t) <-> v:t";
by (simp_tac (prop_rec_ss addsimps [one_not_0 RS not_sym] 
	      setloop (split_tac [expand_if])) 1);
val is_true_Var = result();

goalw PropLog.thy [is_true_def]
    "is_true(p=>q,t) <-> (is_true(p,t)-->is_true(q,t))";
by (simp_tac (prop_rec_ss setloop (split_tac [expand_if])) 1);
val is_true_Imp = result();

(** The function hyps **)

goalw PropLog.thy [hyps_def] "hyps(Fls,t) = 0";
by (simp_tac prop_rec_ss 1);
val hyps_Fls = result();

goalw PropLog.thy [hyps_def] "hyps(#v,t) = {if(v:t, #v, #v=>Fls)}";
by (simp_tac prop_rec_ss 1);
val hyps_Var = result();

goalw PropLog.thy [hyps_def] "hyps(p=>q,t) = hyps(p,t) Un hyps(q,t)";
by (simp_tac prop_rec_ss 1);
val hyps_Imp = result();

val prop_ss = prop_rec_ss 
    addsimps Prop.intrs
    addsimps [is_true_Fls, is_true_Var, is_true_Imp,
	      hyps_Fls, hyps_Var, hyps_Imp];

(*** Proof theory of propositional logic ***)

structure PropThms = Inductive_Fun
 (val thy = PropLog.thy;
  val rec_doms = [("thms","prop")];
  val sintrs = 
      ["[| p:H;  p:prop |] ==> H |- p",
       "[| p:prop;  q:prop |] ==> H |- p=>q=>p",
       "[| p:prop;  q:prop;  r:prop |] ==> H |- (p=>q=>r) => (p=>q) => p=>r",
       "p:prop ==> H |- ((p=>Fls) => Fls) => p",
       "[| H |- p=>q;  H |- p;  p:prop;  q:prop |] ==> H |- q"];
  val monos = [];
  val con_defs = [];
  val type_intrs = Prop.intrs;
  val type_elims = []);

goalw PropThms.thy PropThms.defs "!!G H. G<=H ==> thms(G) <= thms(H)";
by (rtac lfp_mono 1);
by (REPEAT (rtac PropThms.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::basic_monos) 1));
val thms_mono = result();

val thms_in_pl = PropThms.dom_subset RS subsetD;

val [thms_H, thms_K, thms_S, thms_DN, weak_thms_MP] = PropThms.intrs;

(*Modus Ponens rule -- this stronger version avoids typecheck*)
goal PropThms.thy "!!p q H. [| H |- p=>q;  H |- p |] ==> H |- q";
by (rtac weak_thms_MP 1);
by (REPEAT (eresolve_tac [asm_rl, thms_in_pl, thms_in_pl RS ImpE] 1));
val thms_MP = result();

(*Rule is called I for Identity Combinator, not for Introduction*)
goal PropThms.thy "!!p H. p:prop ==> H |- p=>p";
by (rtac (thms_S RS thms_MP RS thms_MP) 1);
by (rtac thms_K 5);
by (rtac thms_K 4);
by (REPEAT (ares_tac [ImpI] 1));
val thms_I = result();

(** Weakening, left and right **)

(* [| G<=H;  G|-p |] ==> H|-p   Order of premises is convenient with RS*)
val weaken_left = standard (thms_mono RS subsetD);

(* H |- p ==> cons(a,H) |- p *)
val weaken_left_cons = subset_consI RS weaken_left;

val weaken_left_Un1  = Un_upper1 RS weaken_left;
val weaken_left_Un2  = Un_upper2 RS weaken_left;

goal PropThms.thy "!!H p q. [| H |- q;  p:prop |] ==> H |- p=>q";
by (rtac (thms_K RS thms_MP) 1);
by (REPEAT (ares_tac [thms_in_pl] 1));
val weaken_right = result();

(*The deduction theorem*)
goal PropThms.thy "!!p q H. [| cons(p,H) |- q;  p:prop |] ==>  H |- p=>q";
by (etac PropThms.induct 1);
by (fast_tac (ZF_cs addIs [thms_I, thms_H RS weaken_right]) 1);
by (fast_tac (ZF_cs addIs [thms_K RS weaken_right]) 1);
by (fast_tac (ZF_cs addIs [thms_S RS weaken_right]) 1);
by (fast_tac (ZF_cs addIs [thms_DN RS weaken_right]) 1);
by (fast_tac (ZF_cs addIs [thms_S RS thms_MP RS thms_MP]) 1);
val deduction = result();


(*The cut rule*)
goal PropThms.thy "!!H p q. [| H|-p;  cons(p,H) |- q |] ==>  H |- q";
by (rtac (deduction RS thms_MP) 1);
by (REPEAT (ares_tac [thms_in_pl] 1));
val cut = result();

goal PropThms.thy "!!H p. [| H |- Fls; p:prop |] ==> H |- p";
by (rtac (thms_DN RS thms_MP) 1);
by (rtac weaken_right 2);
by (REPEAT (ares_tac (Prop.intrs@[consI1]) 1));
val thms_FlsE = result();

(* [| H |- p=>Fls;  H |- p;  q: prop |] ==> H |- q *)
val thms_notE = standard (thms_MP RS thms_FlsE);

(*Soundness of the rules wrt truth-table semantics*)
goalw PropThms.thy [sat_def] "!!H. H |- p ==> H |= p";
by (etac PropThms.induct 1);
by (fast_tac (ZF_cs addSDs [is_true_Imp RS iffD1 RS mp]) 5);
by (ALLGOALS (asm_simp_tac prop_ss));
val soundness = result();

(*** Towards the completeness proof ***)

val [premf,premq] = goal PropThms.thy
    "[| H |- p=>Fls; q: prop |] ==> H |- p=>q";
by (rtac (premf RS thms_in_pl RS ImpE) 1);
by (rtac deduction 1);
by (rtac (premf RS weaken_left_cons RS thms_notE) 1);
by (REPEAT (ares_tac [premq, consI1, thms_H] 1));
val Fls_Imp = result();

val [premp,premq] = goal PropThms.thy
    "[| H |- p;  H |- q=>Fls |] ==> H |- (p=>q)=>Fls";
by (cut_facts_tac ([premp,premq] RL [thms_in_pl]) 1);
by (etac ImpE 1);
by (rtac deduction 1);
by (rtac (premq RS weaken_left_cons RS thms_MP) 1);
by (rtac (consI1 RS thms_H RS thms_MP) 1);
by (rtac (premp RS weaken_left_cons) 2);
by (REPEAT (ares_tac Prop.intrs 1));
val Imp_Fls = result();

(*Typical example of strengthening the induction formula*)
val [major] = goal PropThms.thy 
    "p: prop ==> hyps(p,t) |- if(is_true(p,t), p, p=>Fls)";
by (rtac (expand_if RS iffD2) 1);
by (rtac (major RS Prop.induct) 1);
by (ALLGOALS (asm_simp_tac (prop_ss addsimps [thms_I, thms_H])));
by (safe_tac (ZF_cs addSEs [Fls_Imp RS weaken_left_Un1, 
			    Fls_Imp RS weaken_left_Un2]));
by (ALLGOALS (fast_tac (ZF_cs addIs [weaken_left_Un1, weaken_left_Un2, 
				     weaken_right, Imp_Fls])));
val hyps_thms_if = result();

(*Key lemma for completeness; yields a set of assumptions satisfying p*)
val [premp,sat] = goalw PropThms.thy [sat_def]
    "[| p: prop;  0 |= p |] ==> hyps(p,t) |- p";
by (rtac (sat RS spec RS mp RS if_P RS subst) 1 THEN
    rtac (premp RS hyps_thms_if) 2);
by (fast_tac ZF_cs 1);
val sat_thms_p = result();

(*For proving certain theorems in our new propositional logic*)
val thms_cs = 
    ZF_cs addSIs [FlsI, VarI, ImpI, deduction]
          addIs [thms_in_pl, thms_H, thms_H RS thms_MP];

(*The excluded middle in the form of an elimination rule*)
val prems = goal PropThms.thy
    "[| p: prop;  q: prop |] ==> H |- (p=>q) => ((p=>Fls)=>q) => q";
by (rtac (deduction RS deduction) 1);
by (rtac (thms_DN RS thms_MP) 1);
by (ALLGOALS (best_tac (thms_cs addSIs prems)));
val thms_excluded_middle = result();

(*Hard to prove directly because it requires cuts*)
val prems = goal PropThms.thy
    "[| cons(p,H) |- q;  cons(p=>Fls,H) |- q;  p: prop |] ==> H |- q";
by (rtac (thms_excluded_middle RS thms_MP RS thms_MP) 1);
by (REPEAT (resolve_tac (prems@Prop.intrs@[deduction,thms_in_pl]) 1));
val thms_excluded_middle_rule = result();

(*** Completeness -- lemmas for reducing the set of assumptions ***)

(*For the case hyps(p,t)-cons(#v,Y) |- p;
  we also have hyps(p,t)-{#v} <= hyps(p, t-{v}) *)
val [major] = goal PropThms.thy
    "p: prop ==> hyps(p, t-{v}) <= cons(#v=>Fls, hyps(p,t)-{#v})";
by (rtac (major RS Prop.induct) 1);
by (simp_tac prop_ss 1);
by (asm_simp_tac (prop_ss setloop (split_tac [expand_if])) 1);
by (fast_tac (ZF_cs addSEs Prop.free_SEs) 1);
by (asm_simp_tac prop_ss 1);
by (fast_tac ZF_cs 1);
val hyps_Diff = result();

(*For the case hyps(p,t)-cons(#v => Fls,Y) |- p;
  we also have hyps(p,t)-{#v=>Fls} <= hyps(p, cons(v,t)) *)
val [major] = goal PropThms.thy
    "p: prop ==> hyps(p, cons(v,t)) <= cons(#v, hyps(p,t)-{#v=>Fls})";
by (rtac (major RS Prop.induct) 1);
by (simp_tac prop_ss 1);
by (asm_simp_tac (prop_ss setloop (split_tac [expand_if])) 1);
by (fast_tac (ZF_cs addSEs Prop.free_SEs) 1);
by (asm_simp_tac prop_ss 1);
by (fast_tac ZF_cs 1);
val hyps_cons = result();

(** Two lemmas for use with weaken_left **)

goal ZF.thy "B-C <= cons(a, B-cons(a,C))";
by (fast_tac ZF_cs 1);
val cons_Diff_same = result();

goal ZF.thy "cons(a, B-{c}) - D <= cons(a, B-cons(c,D))";
by (fast_tac ZF_cs 1);
val cons_Diff_subset2 = result();

(*The set hyps(p,t) is finite, and elements have the form #v or #v=>Fls;
 could probably prove the stronger hyps(p,t) : Fin(hyps(p,0) Un hyps(p,nat))*)
val [major] = goal PropThms.thy
    "p: prop ==> hyps(p,t) : Fin(UN v:nat. {#v, #v=>Fls})";
by (rtac (major RS Prop.induct) 1);
by (asm_simp_tac (prop_ss addsimps [Fin_0I, Fin_consI, UN_I, cons_iff]
		  setloop (split_tac [expand_if])) 2);
by (ALLGOALS (asm_simp_tac (prop_ss addsimps [Un_0, Fin_0I, Fin_UnI])));
val hyps_finite = result();

val Diff_weaken_left = subset_refl RSN (2, Diff_mono) RS weaken_left;

(*Induction on the finite set of assumptions hyps(p,t0).
  We may repeatedly subtract assumptions until none are left!*)
val [premp,sat] = goal PropThms.thy
    "[| p: prop;  0 |= p |] ==> ALL t. hyps(p,t) - hyps(p,t0) |- p";
by (rtac (premp RS hyps_finite RS Fin_induct) 1);
by (simp_tac (prop_ss addsimps [premp, sat, sat_thms_p, Diff_0]) 1);
by (safe_tac ZF_cs);
(*Case hyps(p,t)-cons(#v,Y) |- p *)
by (rtac thms_excluded_middle_rule 1);
by (etac VarI 3);
by (rtac (cons_Diff_same RS weaken_left) 1);
by (etac spec 1);
by (rtac (cons_Diff_subset2 RS weaken_left) 1);
by (rtac (premp RS hyps_Diff RS Diff_weaken_left) 1);
by (etac spec 1);
(*Case hyps(p,t)-cons(#v => Fls,Y) |- p *)
by (rtac thms_excluded_middle_rule 1);
by (etac VarI 3);
by (rtac (cons_Diff_same RS weaken_left) 2);
by (etac spec 2);
by (rtac (cons_Diff_subset2 RS weaken_left) 1);
by (rtac (premp RS hyps_cons RS Diff_weaken_left) 1);
by (etac spec 1);
val completeness_0_lemma = result();

(*The base case for completeness*)
val [premp,sat] = goal PropThms.thy "[| p: prop;  0 |= p |] ==> 0 |- p";
by (rtac (Diff_cancel RS subst) 1);
by (rtac (sat RS (premp RS completeness_0_lemma RS spec)) 1);
val completeness_0 = result();

(*A semantic analogue of the Deduction Theorem*)
goalw PropThms.thy [sat_def] "!!H p q. [| cons(p,H) |= q |] ==> H |= p=>q";
by (simp_tac prop_ss 1);
by (fast_tac ZF_cs 1);
val sat_Imp = result();

goal PropThms.thy "!!H. H: Fin(prop) ==> ALL p:prop. H |= p --> H |- p";
by (etac Fin_induct 1);
by (safe_tac (ZF_cs addSIs [completeness_0]));
by (rtac (weaken_left_cons RS thms_MP) 1);
by (fast_tac (ZF_cs addSIs [sat_Imp,ImpI]) 1);
by (fast_tac thms_cs 1);
val completeness_lemma = result();

val completeness = completeness_lemma RS bspec RS mp;

val [finite] = goal PropThms.thy "H: Fin(prop) ==> H |- p <-> H |= p & p:prop";
by (fast_tac (ZF_cs addSEs [soundness, finite RS completeness, 
			    thms_in_pl]) 1);
val thms_iff = result();

writeln"Reached end of file.";
