(*  Title:      HOL/ex/pl.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Lawrence C Paulson
    Copyright   1994  TU Muenchen & University of Cambridge

Soundness and completeness of propositional logic w.r.t. truth-tables.

Prove: If H|=p then G|=p where G:Fin(H)
*)

open PropLog;

(** Monotonicity **)
goalw PropLog.thy thms.defs "!!G H. G<=H ==> thms(G) <= thms(H)";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "thms_mono";

(*Rule is called I for Identity Combinator, not for Introduction*)
goal PropLog.thy "H |- p->p";
by (best_tac (claset() addIs [thms.K,thms.S,thms.MP]) 1);
qed "thms_I";

(** Weakening, left and right **)

(* "[| G<=H;  G |- p |] ==> H |- p"
   This order of premises is convenient with RS
*)
bind_thm ("weaken_left", (thms_mono RS subsetD));

(* H |- p ==> insert(a,H) |- p *)
val weaken_left_insert = subset_insertI RS weaken_left;

val weaken_left_Un1  =    Un_upper1 RS weaken_left;
val weaken_left_Un2  =    Un_upper2 RS weaken_left;

goal PropLog.thy "!!H. H |- q ==> H |- p->q";
by (fast_tac (claset() addIs [thms.K,thms.MP]) 1);
qed "weaken_right";

(*The deduction theorem*)
goal PropLog.thy "!!H. insert p H |- q  ==>  H |- p->q";
by (etac thms.induct 1);
by (ALLGOALS 
    (fast_tac (claset() addIs [thms_I, thms.H, thms.K, thms.S, thms.DN, 
			       thms.S RS thms.MP RS thms.MP, weaken_right])));
qed "deduction";


(* "[| insert p H |- q; H |- p |] ==> H |- q"
    The cut rule - not used
*)
val cut = deduction RS thms.MP;

(* H |- false ==> H |- p *)
val thms_falseE = weaken_right RS (thms.DN RS thms.MP);

(* [| H |- p->false;  H |- p;  q: pl |] ==> H |- q *)
bind_thm ("thms_notE", (thms.MP RS thms_falseE));

(** The function eval **)

goalw PropLog.thy [eval_def] "tt[false] = False";
by (Simp_tac 1);
qed "eval_false";

goalw PropLog.thy [eval_def] "tt[#v] = (v:tt)";
by (Simp_tac 1);
qed "eval_var";

goalw PropLog.thy [eval_def] "tt[p->q] = (tt[p]-->tt[q])";
by (Simp_tac 1);
qed "eval_imp";

Addsimps [eval_false, eval_var, eval_imp];

(*Soundness of the rules wrt truth-table semantics*)
goalw PropLog.thy [sat_def] "!!H. H |- p ==> H |= p";
by (etac thms.induct 1);
by (fast_tac (claset() addSDs [eval_imp RS iffD1 RS mp]) 5);
by (ALLGOALS Asm_simp_tac);
qed "soundness";

(*** Towards the completeness proof ***)

goal PropLog.thy "!!H. H |- p->false ==> H |- p->q";
by (rtac deduction 1);
by (etac (weaken_left_insert RS thms_notE) 1);
by (rtac thms.H 1);
by (rtac insertI1 1);
qed "false_imp";

val [premp,premq] = goal PropLog.thy
    "[| H |- p;  H |- q->false |] ==> H |- (p->q)->false";
by (rtac deduction 1);
by (rtac (premq RS weaken_left_insert RS thms.MP) 1);
by (rtac (thms.H RS thms.MP) 1);
by (rtac insertI1 1);
by (rtac (premp RS weaken_left_insert) 1);
qed "imp_false";

(*This formulation is required for strong induction hypotheses*)
goal PropLog.thy "hyps p tt |- (if tt[p] then p else p->false)";
by (rtac (expand_if RS iffD2) 1);
by (PropLog.pl.induct_tac "p" 1);
by (ALLGOALS (simp_tac (simpset() addsimps [thms_I, thms.H])));
by (fast_tac (claset() addIs [weaken_left_Un1, weaken_left_Un2, 
			      weaken_right, imp_false]
                       addSEs [false_imp]) 1);
qed "hyps_thms_if";

(*Key lemma for completeness; yields a set of assumptions satisfying p*)
val [sat] = goalw PropLog.thy [sat_def] "{} |= p ==> hyps p tt |- p";
by (rtac (sat RS spec RS mp RS if_P RS subst) 1 THEN
    rtac hyps_thms_if 2);
by (Simp_tac 1);
qed "sat_thms_p";

(*For proving certain theorems in our new propositional logic*)

AddSIs [deduction];
AddIs [thms.H, thms.H RS thms.MP];

(*The excluded middle in the form of an elimination rule*)
goal PropLog.thy "H |- (p->q) -> ((p->false)->q) -> q";
by (rtac (deduction RS deduction) 1);
by (rtac (thms.DN RS thms.MP) 1);
by (ALLGOALS (best_tac (claset() addSIs prems)));
qed "thms_excluded_middle";

(*Hard to prove directly because it requires cuts*)
val prems = goal PropLog.thy
    "[| insert p H |- q;  insert (p->false) H |- q |] ==> H |- q";
by (rtac (thms_excluded_middle RS thms.MP RS thms.MP) 1);
by (REPEAT (resolve_tac (prems@[deduction]) 1));
qed "thms_excluded_middle_rule";

(*** Completeness -- lemmas for reducing the set of assumptions ***)

(*For the case hyps(p,t)-insert(#v,Y) |- p;
  we also have hyps(p,t)-{#v} <= hyps(p, t-{v}) *)
goal PropLog.thy "hyps p (t-{v}) <= insert (#v->false) ((hyps p t)-{#v})";
by (PropLog.pl.induct_tac "p" 1);
by (Simp_tac 1);
by (simp_tac (simpset() addsplits [expand_if]) 1);
by (Simp_tac 1);
by (Fast_tac 1);
qed "hyps_Diff";

(*For the case hyps(p,t)-insert(#v -> false,Y) |- p;
  we also have hyps(p,t)-{#v->false} <= hyps(p, insert(v,t)) *)
goal PropLog.thy "hyps p (insert v t) <= insert (#v) (hyps p t-{#v->false})";
by (PropLog.pl.induct_tac "p" 1);
by (Simp_tac 1);
by (simp_tac (simpset() addsplits [expand_if]) 1);
by (Simp_tac 1);
by (Fast_tac 1);
qed "hyps_insert";

(** Two lemmas for use with weaken_left **)

goal Set.thy "B-C <= insert a (B-insert a C)";
by (Fast_tac 1);
qed "insert_Diff_same";

goal Set.thy "insert a (B-{c}) - D <= insert a (B-insert c D)";
by (Fast_tac 1);
qed "insert_Diff_subset2";

goal PropLog.thy "finite(hyps p t)";
by (induct_tac "p" 1);
by (ALLGOALS Asm_simp_tac);
qed "hyps_finite";

goal PropLog.thy "hyps p t <= (UN v. {#v, #v->false})";
by (PropLog.pl.induct_tac "p" 1);
by (ALLGOALS (simp_tac (simpset() addsplits [expand_if])));
by (Blast_tac 1);
qed "hyps_subset";

val Diff_weaken_left = subset_refl RSN (2, Diff_mono) RS weaken_left;

(*Induction on the finite set of assumptions hyps(p,t0).
  We may repeatedly subtract assumptions until none are left!*)
val [sat] = goal PropLog.thy
    "{} |= p ==> !t. hyps p t - hyps p t0 |- p";
by (rtac (hyps_subset RS (hyps_finite RS finite_subset_induct)) 1);
by (simp_tac (simpset() addsimps [sat RS sat_thms_p]) 1);
by Safe_tac;
(*Case hyps(p,t)-insert(#v,Y) |- p *)
by (rtac thms_excluded_middle_rule 1);
by (rtac (insert_Diff_same RS weaken_left) 1);
by (etac spec 1);
by (rtac (insert_Diff_subset2 RS weaken_left) 1);
by (rtac (hyps_Diff RS Diff_weaken_left) 1);
by (etac spec 1);
(*Case hyps(p,t)-insert(#v -> false,Y) |- p *)
by (rtac thms_excluded_middle_rule 1);
by (rtac (insert_Diff_same RS weaken_left) 2);
by (etac spec 2);
by (rtac (insert_Diff_subset2 RS weaken_left) 1);
by (rtac (hyps_insert RS Diff_weaken_left) 1);
by (etac spec 1);
qed "completeness_0_lemma";

(*The base case for completeness*)
val [sat] = goal PropLog.thy "{} |= p ==> {} |- p";
by (rtac (Diff_cancel RS subst) 1);
by (rtac (sat RS (completeness_0_lemma RS spec)) 1);
qed "completeness_0";

(*A semantic analogue of the Deduction Theorem*)
goalw PropLog.thy [sat_def] "!!p H. insert p H |= q ==> H |= p->q";
by (Simp_tac 1);
by (Fast_tac 1);
qed "sat_imp";

goal PropLog.thy "!!H. finite H ==> !p. H |= p --> H |- p";
by (etac finite_induct 1);
by (safe_tac ((claset_of Fun.thy) addSIs [completeness_0]));
by (rtac (weaken_left_insert RS thms.MP) 1);
by (fast_tac ((claset_of Fun.thy) addSIs [sat_imp]) 1);
by (Fast_tac 1);
qed "completeness_lemma";

val completeness = completeness_lemma RS spec RS mp;

goal PropLog.thy "!!H. finite H ==> (H |- p) = (H |= p)";
by (fast_tac (claset() addSEs [soundness, completeness]) 1);
qed "syntax_iff_semantics";
