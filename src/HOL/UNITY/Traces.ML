open Traces;

goal thy "reachable Init Acts <= {s. EX evs. s#evs: traces Init Acts}";
by (rtac subsetI 1);
be reachable.induct 1;
by (REPEAT (blast_tac (claset() addIs traces.intrs) 1));
val lemma1 = result();

goal thy "!!evs. evs : traces Init Acts \
\                ==> ALL s evs'. evs = s#evs' --> s: reachable Init Acts";
be traces.induct 1;
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
val lemma2 = normalize_thm [RSmp, RSspec] (result());

goal thy "{s. EX evs. s#evs: traces Init Acts} <= reachable Init Acts";
by (blast_tac (claset() addIs [lemma2]) 1);
val lemma3 = result();

goal thy "reachable Init Acts = {s. EX evs. s#evs: traces Init Acts}";
by (rtac ([lemma1,lemma3] MRS equalityI) 1);
qed "reachable_eq_traces";


(*Could/should this be proved?*)
goal thy "reachable Init Acts = (UN evs: traces Init Acts. set evs)";


(*The strongest invariant is the set of all reachable states!*)
goalw thy [stable_def, constrains_def]
    "!!A. [| Init<=A;  stable Acts A |] ==> reachable Init Acts <= A";
by (rtac subsetI 1);
be reachable.induct 1;
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "strongest_invariant";

goal thy "stable Acts (reachable Init Acts)";
by (REPEAT (blast_tac (claset() addIs [stableI, constrainsI]
				addIs reachable.intrs) 1));
qed "stable_reachable";
