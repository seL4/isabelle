(*  Title:      HOL/UNITY/Traces
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Definitions of
  * traces: the possible execution traces
  * reachable: the set of reachable states

*)

Goal "reachable prg = {s. EX evs. (s,evs): traces (Init prg) (Acts prg)}";
by Safe_tac;
by (etac traces.induct 2);
be reachable.induct 1;
by (ALLGOALS (blast_tac (claset() addIs (reachable.intrs @ traces.intrs))));
qed "reachable_equiv_traces";

Goal "stable (Acts prg) (reachable prg)";
by (blast_tac (claset() addIs ([stableI, constrainsI] @ reachable.intrs)) 1);
qed "stable_reachable";

(*The set of all reachable states is an invariant...*)
Goal "invariant prg (reachable prg)";
by (simp_tac (simpset() addsimps [invariant_def]) 1);
by (blast_tac (claset() addIs (stable_reachable::reachable.intrs)) 1);
qed "invariant_reachable";

(*...in fact the strongest invariant!*)
Goal "invariant prg A ==> reachable prg <= A";
by (full_simp_tac 
    (simpset() addsimps [stable_def, constrains_def, invariant_def]) 1);
by (rtac subsetI 1);
by (etac reachable.induct 1);
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "invariant_includes_reachable";

(*If "A" includes the initial states and is stable then "A" is invariant.
  Result is trivial from the definition, but it is handy.*)
Goal "[| (Init prg)<=A;  stable (Acts prg) A |] ==> invariant prg A";
by (asm_simp_tac (simpset() addsimps [invariant_def]) 1);
qed "invariantI";


(** Conjoining invariants **)

Goal "[| invariant prg A;  invariant prg B |] \
\     ==> invariant prg (A Int B)";
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


