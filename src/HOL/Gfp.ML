(*  Title:      HOL/gfp
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For gfp.thy.  The Knaster-Tarski Theorem for greatest fixed points.
*)

open Gfp;

(*** Proof of Knaster-Tarski Theorem using gfp ***)

(* gfp(f) is the least upper bound of {u. u <= f(u)} *)

val prems = goalw Gfp.thy [gfp_def] "[| X <= f(X) |] ==> X <= gfp(f)";
by (rtac (CollectI RS Union_upper) 1);
by (resolve_tac prems 1);
qed "gfp_upperbound";

val prems = goalw Gfp.thy [gfp_def]
    "[| !!u. u <= f(u) ==> u<=X |] ==> gfp(f) <= X";
by (REPEAT (ares_tac ([Union_least]@prems) 1));
by (etac CollectD 1);
qed "gfp_least";

val [mono] = goal Gfp.thy "mono(f) ==> gfp(f) <= f(gfp(f))";
by (EVERY1 [rtac gfp_least, rtac subset_trans, atac,
            rtac (mono RS monoD), rtac gfp_upperbound, atac]);
qed "gfp_lemma2";

val [mono] = goal Gfp.thy "mono(f) ==> f(gfp(f)) <= gfp(f)";
by (EVERY1 [rtac gfp_upperbound, rtac (mono RS monoD), 
            rtac gfp_lemma2, rtac mono]);
qed "gfp_lemma3";

val [mono] = goal Gfp.thy "mono(f) ==> gfp(f) = f(gfp(f))";
by (REPEAT (resolve_tac [equalityI,gfp_lemma2,gfp_lemma3,mono] 1));
qed "gfp_Tarski";

(*** Coinduction rules for greatest fixed points ***)

(*weak version*)
val prems = goal Gfp.thy
    "[| a: X;  X <= f(X) |] ==> a : gfp(f)";
by (rtac (gfp_upperbound RS subsetD) 1);
by (REPEAT (ares_tac prems 1));
qed "weak_coinduct";

val [prem,mono] = goal Gfp.thy
    "[| X <= f(X Un gfp(f));  mono(f) |] ==>  \
\    X Un gfp(f) <= f(X Un gfp(f))";
by (rtac (prem RS Un_least) 1);
by (rtac (mono RS gfp_lemma2 RS subset_trans) 1);
by (rtac (Un_upper2 RS subset_trans) 1);
by (rtac (mono RS mono_Un) 1);
qed "coinduct_lemma";

(*strong version, thanks to Coen & Frost*)
goal Gfp.thy
    "!!X. [| mono(f);  a: X;  X <= f(X Un gfp(f)) |] ==> a : gfp(f)";
by (rtac (coinduct_lemma RSN (2, weak_coinduct)) 1);
by (REPEAT (ares_tac [UnI1, Un_least] 1));
qed "coinduct";

val [mono,prem] = goal Gfp.thy
    "[| mono(f);  a: gfp(f) |] ==> a: f(X Un gfp(f))";
by (rtac (mono RS mono_Un RS subsetD) 1);
by (rtac (mono RS gfp_lemma2 RS subsetD RS UnI2) 1);
by (rtac prem 1);
qed "gfp_fun_UnI2";

(***  Even Stronger version of coinduct  [by Martin Coen]
         - instead of the condition  X <= f(X)
                           consider  X <= (f(X) Un f(f(X)) ...) Un gfp(X) ***)

val [prem] = goal Gfp.thy "mono(f) ==> mono(%x. f(x) Un X Un B)";
by (REPEAT (ares_tac [subset_refl, monoI, Un_mono, prem RS monoD] 1));
qed "coinduct3_mono_lemma";

val [prem,mono] = goal Gfp.thy
    "[| X <= f(lfp(%x. f(x) Un X Un gfp(f)));  mono(f) |] ==> \
\    lfp(%x. f(x) Un X Un gfp(f)) <= f(lfp(%x. f(x) Un X Un gfp(f)))";
by (rtac subset_trans 1);
by (rtac (mono RS coinduct3_mono_lemma RS lfp_lemma3) 1);
by (rtac (Un_least RS Un_least) 1);
by (rtac subset_refl 1);
by (rtac prem 1);
by (rtac (mono RS gfp_Tarski RS equalityD1 RS subset_trans) 1);
by (rtac (mono RS monoD) 1);
by (stac (mono RS coinduct3_mono_lemma RS lfp_Tarski) 1);
by (rtac Un_upper2 1);
qed "coinduct3_lemma";

val prems = goal Gfp.thy
    "[| mono(f);  a:X;  X <= f(lfp(%x. f(x) Un X Un gfp(f))) |] ==> a : gfp(f)";
by (rtac (coinduct3_lemma RSN (2,weak_coinduct)) 1);
by (resolve_tac (prems RL [coinduct3_mono_lemma RS lfp_Tarski RS ssubst]) 1);
by (rtac (UnI2 RS UnI1) 1);
by (REPEAT (resolve_tac prems 1));
qed "coinduct3";


(** Definition forms of gfp_Tarski and coinduct, to control unfolding **)

val [rew,mono] = goal Gfp.thy "[| A==gfp(f);  mono(f) |] ==> A = f(A)";
by (rewtac rew);
by (rtac (mono RS gfp_Tarski) 1);
qed "def_gfp_Tarski";

val rew::prems = goal Gfp.thy
    "[| A==gfp(f);  mono(f);  a:X;  X <= f(X Un A) |] ==> a: A";
by (rewtac rew);
by (REPEAT (ares_tac (map (rewrite_rule [rew]) prems @ [coinduct]) 1));
qed "def_coinduct";

(*The version used in the induction/coinduction package*)
val prems = goal Gfp.thy
    "[| A == gfp(%w. Collect(P(w)));  mono(%w. Collect(P(w)));  \
\       a: X;  !!z. z: X ==> P (X Un A) z |] ==> \
\    a : A";
by (rtac def_coinduct 1);
by (REPEAT (ares_tac (prems @ [subsetI,CollectI]) 1));
qed "def_Collect_coinduct";

val rew::prems = goal Gfp.thy
    "[| A==gfp(f); mono(f);  a:X;  X <= f(lfp(%x. f(x) Un X Un A)) |] ==> a: A";
by (rewtac rew);
by (REPEAT (ares_tac (map (rewrite_rule [rew]) prems @ [coinduct3]) 1));
qed "def_coinduct3";

(*Monotonicity of gfp!*)
val prems = goal Gfp.thy
    "[| mono(f);  !!Z. f(Z)<=g(Z) |] ==> gfp(f) <= gfp(g)";
by (rtac gfp_upperbound 1);
by (rtac subset_trans 1);
by (rtac gfp_lemma2 1);
by (resolve_tac prems 1);
by (resolve_tac prems 1);
val gfp_mono = result();

(*Monotonicity of gfp!*)
val [prem] = goal Gfp.thy "[| !!Z. f(Z)<=g(Z) |] ==> gfp(f) <= gfp(g)";
by (rtac (gfp_upperbound RS gfp_least) 1);
by (etac (prem RSN (2,subset_trans)) 1);
qed "gfp_mono";
