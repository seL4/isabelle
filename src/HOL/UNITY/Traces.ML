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



Goal "stable Acts (reachable(Init,Acts))";
by (blast_tac (claset() addIs ([stableI, constrainsI] @ reachable.intrs)) 1);
qed "stable_reachable";

(*The set of all reachable states is an invariant...*)
Goal "invariant (Init,Acts) (reachable(Init,Acts))";
by (simp_tac (simpset() addsimps [invariant_def]) 1);
by (blast_tac (claset() addIs (stable_reachable::reachable.intrs)) 1);
qed "invariant_reachable";

(*...in fact the strongest invariant!*)
Goal "invariant (Init,Acts) A ==> reachable(Init,Acts) <= A";
by (full_simp_tac 
    (simpset() addsimps [stable_def, constrains_def, invariant_def]) 1);
by (rtac subsetI 1);
by (etac reachable.induct 1);
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "invariant_includes_reachable";

(*If "A" includes the initial states and is stable then "A" is invariant.
  Result is trivial from the definition, but it is handy.*)
Goal "[| Init<=A;  stable Acts A |] ==> invariant (Init,Acts) A";
by (asm_simp_tac (simpset() addsimps [invariant_def]) 1);
qed "invariantI";


(** Conjoining invariants **)

Goal "[| invariant (Init,Acts) A;  invariant (Init,Acts) B |] \
\     ==> invariant (Init,Acts) (A Int B)";
by (asm_full_simp_tac (simpset() addsimps [invariant_def, stable_Int]) 1);
by Auto_tac;
qed "invariant_Int";

(*Delete the nearest invariance assumption (which will be the second one
  used by invariant_Int) *)
val invariant_thin =
    read_instantiate_sg (sign_of thy)
                [("V", "invariant ?Prg ?A")] thin_rl;

(*Combines two invariance ASSUMPTIONS into one.  USEFUL??*)
val invariant_Int_tac = dtac invariant_Int THEN' 
                        assume_tac THEN'
			etac invariant_thin;

(*Combines two invariance THEOREMS into one.*)
val invariant_Int_rule = foldr1 (fn (th1,th2) => [th1,th2] MRS invariant_Int);


