(*  Title:      CCL/hered
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For hered.thy.
*)

open Hered;

fun type_of_terms (Const("Trueprop",_) $ (Const("op =",(Type ("fun", [t,_])))$_$_)) = t;

(*** Hereditary Termination ***)

goalw Hered.thy [HTTgen_def]  "mono(%X. HTTgen(X))";
by (rtac monoI 1);
by (fast_tac set_cs 1);
qed "HTTgen_mono";

goalw Hered.thy [HTTgen_def]
  "t : HTTgen(A) <-> t=true | t=false | (EX a b. t=<a,b> & a : A & b : A) | \
\                                       (EX f. t=lam x. f(x) & (ALL x. f(x) : A))";
by (fast_tac set_cs 1);
qed "HTTgenXH";

goal Hered.thy
  "t : HTT <-> t=true | t=false | (EX a b. t=<a,b> & a : HTT & b : HTT) | \
\                                  (EX f. t=lam x. f(x) & (ALL x. f(x) : HTT))";
by (rtac (rewrite_rule [HTTgen_def] 
                 (HTTgen_mono RS (HTT_def RS def_gfp_Tarski) RS XHlemma1)) 1);
by (fast_tac set_cs 1);
qed "HTTXH";

(*** Introduction Rules for HTT ***)

goal Hered.thy "~ bot : HTT";
by (fast_tac (term_cs addDs [XH_to_D HTTXH]) 1);
qed "HTT_bot";

goal Hered.thy "true : HTT";
by (fast_tac (term_cs addIs [XH_to_I HTTXH]) 1);
qed "HTT_true";

goal Hered.thy "false : HTT";
by (fast_tac (term_cs addIs [XH_to_I HTTXH]) 1);
qed "HTT_false";

goal Hered.thy "<a,b> : HTT <->  a : HTT  & b : HTT";
by (rtac (HTTXH RS iff_trans) 1);
by (fast_tac term_cs 1);
qed "HTT_pair";

goal Hered.thy "lam x. f(x) : HTT <-> (ALL x. f(x) : HTT)";
by (rtac (HTTXH RS iff_trans) 1);
by (simp_tac term_ss 1);
by (safe_tac term_cs);
by (asm_simp_tac term_ss 1);
by (fast_tac term_cs 1);
qed "HTT_lam";

local
  val raw_HTTrews = [HTT_bot,HTT_true,HTT_false,HTT_pair,HTT_lam];
  fun mk_thm s = prove_goalw Hered.thy data_defs s (fn _ => 
                  [simp_tac (term_ss addsimps raw_HTTrews) 1]);
in
  val HTT_rews = raw_HTTrews @
               map mk_thm ["one : HTT",
                           "inl(a) : HTT <-> a : HTT",
                           "inr(b) : HTT <-> b : HTT",
                           "zero : HTT",
                           "succ(n) : HTT <-> n : HTT",
                           "[] : HTT",
                           "x$xs : HTT <-> x : HTT & xs : HTT"];
end;

val HTT_Is = HTT_rews @ (HTT_rews RL [iffD2]);

(*** Coinduction for HTT ***)

val prems = goal Hered.thy "[|  t : R;  R <= HTTgen(R) |] ==> t : HTT";
by (rtac (HTT_def RS def_coinduct) 1);
by (REPEAT (ares_tac prems 1));
qed "HTT_coinduct";

fun HTT_coinduct_tac s i = res_inst_tac [("R",s)] HTT_coinduct i;

val prems = goal Hered.thy 
    "[|  t : R;   R <= HTTgen(lfp(%x. HTTgen(x) Un R Un HTT)) |] ==> t : HTT";
by (rtac (HTTgen_mono RSN(3,HTT_def RS def_coinduct3)) 1);
by (REPEAT (ares_tac prems 1));
qed "HTT_coinduct3";
val HTT_coinduct3_raw = rewrite_rule [HTTgen_def] HTT_coinduct3;

fun HTT_coinduct3_tac s i = res_inst_tac [("R",s)] HTT_coinduct3 i;

val HTTgenIs = map (mk_genIs Hered.thy data_defs HTTgenXH HTTgen_mono)
       ["true : HTTgen(R)",
        "false : HTTgen(R)",
        "[| a : R;  b : R |] ==> <a,b> : HTTgen(R)",
        "[| !!x. b(x) : R |] ==> lam x. b(x) : HTTgen(R)",
        "one : HTTgen(R)",
        "a : lfp(%x. HTTgen(x) Un R Un HTT) ==> \
\                         inl(a) : HTTgen(lfp(%x. HTTgen(x) Un R Un HTT))",
        "b : lfp(%x. HTTgen(x) Un R Un HTT) ==> \
\                         inr(b) : HTTgen(lfp(%x. HTTgen(x) Un R Un HTT))",
        "zero : HTTgen(lfp(%x. HTTgen(x) Un R Un HTT))",
        "n : lfp(%x. HTTgen(x) Un R Un HTT) ==> \
\                         succ(n) : HTTgen(lfp(%x. HTTgen(x) Un R Un HTT))",
        "[] : HTTgen(lfp(%x. HTTgen(x) Un R Un HTT))",
        "[| h : lfp(%x. HTTgen(x) Un R Un HTT); t : lfp(%x. HTTgen(x) Un R Un HTT) |] ==>\
\                         h$t : HTTgen(lfp(%x. HTTgen(x) Un R Un HTT))"];

(*** Formation Rules for Types ***)

goal Hered.thy "Unit <= HTT";
by (simp_tac (CCL_ss addsimps ([subsetXH,UnitXH] @ HTT_rews)) 1);
qed "UnitF";

goal Hered.thy "Bool <= HTT";
by (simp_tac (CCL_ss addsimps ([subsetXH,BoolXH] @ HTT_rews)) 1);
by (fast_tac (set_cs addIs HTT_Is @ (prems RL [subsetD])) 1);
qed "BoolF";

val prems = goal Hered.thy "[| A <= HTT;  B <= HTT |] ==> A + B  <= HTT";
by (simp_tac (CCL_ss addsimps ([subsetXH,PlusXH] @ HTT_rews)) 1);
by (fast_tac (set_cs addIs HTT_Is @ (prems RL [subsetD])) 1);
qed "PlusF";

val prems = goal Hered.thy 
     "[| A <= HTT;  !!x. x:A ==> B(x) <= HTT |] ==> SUM x:A. B(x) <= HTT";
by (simp_tac (CCL_ss addsimps ([subsetXH,SgXH] @ HTT_rews)) 1);
by (fast_tac (set_cs addIs HTT_Is @ (prems RL [subsetD])) 1);
qed "SigmaF";

(*** Formation Rules for Recursive types - using coinduction these only need ***)
(***                                          exhaution rule for type-former ***)

(*Proof by induction - needs induction rule for type*)
goal Hered.thy "Nat <= HTT";
by (simp_tac (term_ss addsimps [subsetXH]) 1);
by (safe_tac set_cs);
by (etac Nat_ind 1);
by (ALLGOALS (fast_tac (set_cs addIs HTT_Is @ (prems RL [subsetD]))));
val NatF = result();

goal Hered.thy "Nat <= HTT";
by (safe_tac set_cs);
by (etac HTT_coinduct3 1);
by (fast_tac (set_cs addIs HTTgenIs 
                 addSEs [HTTgen_mono RS ci3_RI] addEs [XH_to_E NatXH]) 1);
qed "NatF";

val [prem] = goal Hered.thy "A <= HTT ==> List(A) <= HTT";
by (safe_tac set_cs);
by (etac HTT_coinduct3 1);
by (fast_tac (set_cs addSIs HTTgenIs 
                 addSEs [HTTgen_mono RS ci3_RI,prem RS subsetD RS (HTTgen_mono RS ci3_AI)] 
                 addEs [XH_to_E ListXH]) 1);
qed "ListF";

val [prem] = goal Hered.thy "A <= HTT ==> Lists(A) <= HTT";
by (safe_tac set_cs);
by (etac HTT_coinduct3 1);
by (fast_tac (set_cs addSIs HTTgenIs 
                 addSEs [HTTgen_mono RS ci3_RI,prem RS subsetD RS (HTTgen_mono RS ci3_AI)] 
                 addEs [XH_to_E ListsXH]) 1);
qed "ListsF";

val [prem] = goal Hered.thy "A <= HTT ==> ILists(A) <= HTT";
by (safe_tac set_cs);
by (etac HTT_coinduct3 1);
by (fast_tac (set_cs addSIs HTTgenIs 
                 addSEs [HTTgen_mono RS ci3_RI,prem RS subsetD RS (HTTgen_mono RS ci3_AI)] 
                 addEs [XH_to_E IListsXH]) 1);
qed "IListsF";

(*** A possible use for this predicate is proving equality from pre-order       ***)
(*** but it seems as easy (and more general) to do this directly by coinduction ***)
(*
val prems = goal Hered.thy "[| t : HTT;  t [= u |] ==> u [= t";
by (po_coinduct_tac "{p. EX a b. p=<a,b> & b : HTT & b [= a}" 1);
by (fast_tac (ccl_cs addIs prems) 1);
by (safe_tac ccl_cs);
by (dtac (poXH RS iffD1) 1);
by (safe_tac (set_cs addSEs [HTT_bot RS notE]));
by (REPEAT_SOME (rtac (POgenXH RS iffD2) ORELSE' etac rev_mp));
by (ALLGOALS (simp_tac (term_ss addsimps HTT_rews)));
by (ALLGOALS (fast_tac ccl_cs));
qed "HTT_po_op";

val prems = goal Hered.thy "[| t : HTT;  t [= u |] ==> t = u";
by (REPEAT (ares_tac (prems @ [conjI RS (eq_iff RS iffD2),HTT_po_op]) 1));
qed "HTT_po_eq";
*)
