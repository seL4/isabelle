(*  Title: 	CCL/gfp
    ID:         $Id$

Modified version of
    Title: 	HOL/gfp
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For gfp.thy.  The Knaster-Tarski Theorem for greatest fixed points.
*)

open Gfp;

(*** Proof of Knaster-Tarski Theorem using gfp ***)

(* gfp(f) is the least upper bound of {u. u <= f(u)} *)

val prems = goalw Gfp.thy [gfp_def] "[| A <= f(A) |] ==> A <= gfp(f)";
by (rtac (CollectI RS Union_upper) 1);
by (resolve_tac prems 1);
val gfp_upperbound = result();

val prems = goalw Gfp.thy [gfp_def]
    "[| !!u. u <= f(u) ==> u<=A |] ==> gfp(f) <= A";
by (REPEAT (ares_tac ([Union_least]@prems) 1));
by (etac CollectD 1);
val gfp_least = result();

val [mono] = goal Gfp.thy "mono(f) ==> gfp(f) <= f(gfp(f))";
by (EVERY1 [rtac gfp_least, rtac subset_trans, atac,
	    rtac (mono RS monoD), rtac gfp_upperbound, atac]);
val gfp_lemma2 = result();

val [mono] = goal Gfp.thy "mono(f) ==> f(gfp(f)) <= gfp(f)";
by (EVERY1 [rtac gfp_upperbound, rtac (mono RS monoD), 
	    rtac gfp_lemma2, rtac mono]);
val gfp_lemma3 = result();

val [mono] = goal Gfp.thy "mono(f) ==> gfp(f) = f(gfp(f))";
by (REPEAT (resolve_tac [equalityI,gfp_lemma2,gfp_lemma3,mono] 1));
val gfp_Tarski = result();

(*** Coinduction rules for greatest fixed points ***)

(*weak version*)
val prems = goal Gfp.thy
    "[| a: A;  A <= f(A) |] ==> a : gfp(f)";
by (rtac (gfp_upperbound RS subsetD) 1);
by (REPEAT (ares_tac prems 1));
val coinduct = result();

val [prem,mono] = goal Gfp.thy
    "[| A <= f(A) Un gfp(f);  mono(f) |] ==>  \
\    A Un gfp(f) <= f(A Un gfp(f))";
by (rtac subset_trans 1);
by (rtac (mono RS mono_Un) 2);
by (rtac (mono RS gfp_Tarski RS subst) 1);
by (rtac (prem RS Un_least) 1);
by (rtac Un_upper2 1);
val coinduct2_lemma = result();

(*strong version, thanks to Martin Coen*)
val ainA::prems = goal Gfp.thy
    "[| a: A;  A <= f(A) Un gfp(f);  mono(f) |] ==> a : gfp(f)";
by (rtac coinduct 1);
by (rtac (prems MRS coinduct2_lemma) 2);
by (resolve_tac [ainA RS UnI1] 1);
val coinduct2 = result();

(***  Even Stronger version of coinduct  [by Martin Coen]
         - instead of the condition  A <= f(A)
                           consider  A <= (f(A) Un f(f(A)) ...) Un gfp(A) ***)

val [prem] = goal Gfp.thy "mono(f) ==> mono(%x.f(x) Un A Un B)";
by (REPEAT (ares_tac [subset_refl, monoI, Un_mono, prem RS monoD] 1));
val coinduct3_mono_lemma= result();

val [prem,mono] = goal Gfp.thy
    "[| A <= f(lfp(%x.f(x) Un A Un gfp(f)));  mono(f) |] ==> \
\    lfp(%x.f(x) Un A Un gfp(f)) <= f(lfp(%x.f(x) Un A Un gfp(f)))";
by (rtac subset_trans 1);
by (rtac (mono RS coinduct3_mono_lemma RS lfp_lemma3) 1);
by (rtac (Un_least RS Un_least) 1);
by (rtac subset_refl 1);
by (rtac prem 1);
by (rtac (mono RS gfp_Tarski RS equalityD1 RS subset_trans) 1);
by (rtac (mono RS monoD) 1);
by (rtac (mono RS coinduct3_mono_lemma RS lfp_Tarski RS ssubst) 1);
by (rtac Un_upper2 1);
val coinduct3_lemma = result();

val ainA::prems = goal Gfp.thy
    "[| a:A;  A <= f(lfp(%x.f(x) Un A Un gfp(f))); mono(f) |] ==> a : gfp(f)";
by (rtac coinduct 1);
by (rtac (prems MRS coinduct3_lemma) 2);
by (resolve_tac (prems RL [coinduct3_mono_lemma RS lfp_Tarski RS ssubst]) 1);
by (rtac (ainA RS UnI2 RS UnI1) 1);
val coinduct3 = result();


(** Definition forms of gfp_Tarski, to control unfolding **)

val [rew,mono] = goal Gfp.thy "[| h==gfp(f);  mono(f) |] ==> h = f(h)";
by (rewtac rew);
by (rtac (mono RS gfp_Tarski) 1);
val def_gfp_Tarski = result();

val rew::prems = goal Gfp.thy
    "[| h==gfp(f);  a:A;  A <= f(A) |] ==> a: h";
by (rewtac rew);
by (REPEAT (ares_tac (prems @ [coinduct]) 1));
val def_coinduct = result();

val rew::prems = goal Gfp.thy
    "[| h==gfp(f);  a:A;  A <= f(A) Un h; mono(f) |] ==> a: h";
by (rewtac rew);
by (REPEAT (ares_tac (map (rewrite_rule [rew]) prems @ [coinduct2]) 1));
val def_coinduct2 = result();

val rew::prems = goal Gfp.thy
    "[| h==gfp(f);  a:A;  A <= f(lfp(%x.f(x) Un A Un h)); mono(f) |] ==> a: h";
by (rewtac rew);
by (REPEAT (ares_tac (map (rewrite_rule [rew]) prems @ [coinduct3]) 1));
val def_coinduct3 = result();

(*Monotonicity of gfp!*)
val prems = goal Gfp.thy
    "[| mono(f);  !!Z. f(Z)<=g(Z) |] ==> gfp(f) <= gfp(g)";
by (rtac gfp_upperbound 1);
by (rtac subset_trans 1);
by (rtac gfp_lemma2 1);
by (resolve_tac prems 1);
by (resolve_tac prems 1);
val gfp_mono = result();
