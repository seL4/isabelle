(*  Title:      HOL/UNITY/Traces
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Definitions of
  * traces: the possible execution traces
  * reachable: the set of reachable states

*)

(****
Now simulate the inductive definition (illegal due to paired arguments)

inductive "reachable(Init,Acts)"
  intrs 
    Init  "s: Init ==> s : reachable(Init,Acts)"

    Acts  "[| act: Acts;  s : reachable(Init,Acts);  (s,s'): act |]
	   ==> s' : reachable(Init,Acts)"

This amounts to an equivalence proof for the definition actually used, 
****)


(** reachable: Deriving the Introduction rules **)

Goal "s: Init ==> s : reachable(Init,Acts)";
by (simp_tac (simpset() addsimps [reachable_def]) 1);
by (blast_tac (claset() addIs traces.intrs) 1);
qed "reachable_Init";


Goal "[| act: Acts;  s : reachable(Init,Acts) |] \
\     ==> (s,s'): act --> s' : reachable(Init,Acts)";
by (asm_full_simp_tac (simpset() addsimps [reachable_def]) 1);
by (etac exE 1);
by (etac traces.induct 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (blast_tac (claset() addIs traces.intrs)));
qed_spec_mp "reachable_Acts";


val major::prems = 
Goalw [reachable_def] 
  "[| za : reachable(Init,Acts);  \
\     !!s. s : Init ==> P s;      \
\     !!act s s'.  \
\        [| act : Acts; s : reachable(Init,Acts); P s; (s, s') : act |]  \
\        ==> P s' |] \
\  ==> P za";
by (cut_facts_tac [major] 1);
by Auto_tac;
by (etac traces.induct 1);
by (ALLGOALS (blast_tac (claset() addIs prems)));
qed "reachable_induct";

structure reachable = 
  struct 
  val Init = reachable_Init
  val Acts = reachable_Acts
  val intrs = [reachable_Init, reachable_Acts]
  val induct = reachable_induct
  end;


(*The strongest invariant is the set of all reachable states!*)
Goalw [stable_def, constrains_def]
    "[| Init<=A;  stable Acts A |] ==> reachable(Init,Acts) <= A";
by (rtac subsetI 1);
by (etac reachable.induct 1);
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "strongest_invariant";

Goal "stable Acts (reachable(Init,Acts))";
by (REPEAT (blast_tac (claset() addIs [stableI, constrainsI]
				addIs reachable.intrs) 1));
qed "stable_reachable";
