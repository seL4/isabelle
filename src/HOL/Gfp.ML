(*  Title:      HOL/Gfp.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

The Knaster-Tarski Theorem for greatest fixed points.
*)

(*** Proof of Knaster-Tarski Theorem using gfp ***)

(* gfp(f) is the least upper bound of {u. u <= f(u)} *)

Goalw [gfp_def] "[| X <= f(X) |] ==> X <= gfp(f)";
by (etac (CollectI RS Union_upper) 1);
qed "gfp_upperbound";

val prems = Goalw [gfp_def]
    "[| !!u. u <= f(u) ==> u<=X |] ==> gfp(f) <= X";
by (REPEAT (ares_tac ([Union_least]@prems) 1));
by (etac CollectD 1);
qed "gfp_least";

Goal "mono(f) ==> gfp(f) <= f(gfp(f))";
by (EVERY1 [rtac gfp_least, rtac subset_trans, atac,
            etac monoD, rtac gfp_upperbound, atac]);
qed "gfp_lemma2";

Goal "mono(f) ==> f(gfp(f)) <= gfp(f)";
by (EVERY1 [rtac gfp_upperbound, rtac monoD, assume_tac,
            etac gfp_lemma2]);
qed "gfp_lemma3";

Goal "mono(f) ==> gfp(f) = f(gfp(f))";
by (REPEAT (ares_tac [equalityI,gfp_lemma2,gfp_lemma3] 1));
qed "gfp_Tarski";

(*** Coinduction rules for greatest fixed points ***)

(*weak version*)
Goal "[| a: X;  X <= f(X) |] ==> a : gfp(f)";
by (rtac (gfp_upperbound RS subsetD) 1);
by Auto_tac;
qed "weak_coinduct";

Goal "[| X <= f(X Un gfp(f));  mono(f) |] ==>  \
\    X Un gfp(f) <= f(X Un gfp(f))";
by (blast_tac (claset() addDs [gfp_lemma2, mono_Un]) 1); 
qed "coinduct_lemma";

(*strong version, thanks to Coen & Frost*)
Goal "[| mono(f);  a: X;  X <= f(X Un gfp(f)) |] ==> a : gfp(f)";
by (rtac (coinduct_lemma RSN (2, weak_coinduct)) 1);
by (REPEAT (ares_tac [UnI1, Un_least] 1));
qed "coinduct";

Goal "[| mono(f);  a: gfp(f) |] ==> a: f(X Un gfp(f))";
by (blast_tac (claset() addDs [gfp_lemma2, mono_Un]) 1); 
qed "gfp_fun_UnI2";

(***  Even Stronger version of coinduct  [by Martin Coen]
         - instead of the condition  X <= f(X)
                           consider  X <= (f(X) Un f(f(X)) ...) Un gfp(X) ***)

Goal "mono(f) ==> mono(%x. f(x) Un X Un B)";
by (REPEAT (ares_tac [subset_refl, monoI, Un_mono] 1 ORELSE etac monoD 1));
qed "coinduct3_mono_lemma";

Goal "[| X <= f(lfp(%x. f(x) Un X Un gfp(f)));  mono(f) |] ==> \
\    lfp(%x. f(x) Un X Un gfp(f)) <= f(lfp(%x. f(x) Un X Un gfp(f)))";
by (rtac subset_trans 1);
by (etac (coinduct3_mono_lemma RS lfp_lemma3) 1);
by (rtac (Un_least RS Un_least) 1);
by (rtac subset_refl 1);
by (assume_tac 1); 
by (rtac (gfp_Tarski RS equalityD1 RS subset_trans) 1);
by (assume_tac 1);
by (rtac monoD 1 THEN assume_tac 1);
by (stac (coinduct3_mono_lemma RS lfp_Tarski) 1);
by Auto_tac;  
qed "coinduct3_lemma";

Goal
  "[| mono(f);  a:X;  X <= f(lfp(%x. f(x) Un X Un gfp(f))) |] ==> a : gfp(f)";
by (rtac (coinduct3_lemma RSN (2,weak_coinduct)) 1);
by (resolve_tac [coinduct3_mono_lemma RS lfp_Tarski RS ssubst] 1);
by Auto_tac;
qed "coinduct3";


(** Definition forms of gfp_Tarski and coinduct, to control unfolding **)

Goal "[| A==gfp(f);  mono(f) |] ==> A = f(A)";
by (auto_tac (claset() addSIs [gfp_Tarski], simpset()));  
qed "def_gfp_Tarski";

Goal "[| A==gfp(f);  mono(f);  a:X;  X <= f(X Un A) |] ==> a: A";
by (auto_tac (claset() addSIs [coinduct], simpset()));  
qed "def_coinduct";

(*The version used in the induction/coinduction package*)
val prems = Goal
    "[| A == gfp(%w. Collect(P(w)));  mono(%w. Collect(P(w)));  \
\       a: X;  !!z. z: X ==> P (X Un A) z |] ==> \
\    a : A";
by (rtac def_coinduct 1);
by (REPEAT (ares_tac (prems @ [subsetI,CollectI]) 1));
qed "def_Collect_coinduct";

Goal "[| A==gfp(f); mono(f);  a:X;  X <= f(lfp(%x. f(x) Un X Un A)) |] \
\     ==> a: A";
by (auto_tac (claset() addSIs [coinduct3], simpset()));  
qed "def_coinduct3";

(*Monotonicity of gfp!*)
val [prem] = Goal "[| !!Z. f(Z)<=g(Z) |] ==> gfp(f) <= gfp(g)";
by (rtac (gfp_upperbound RS gfp_least) 1);
by (etac (prem RSN (2,subset_trans)) 1);
qed "gfp_mono";
