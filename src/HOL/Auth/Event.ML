(*  Title:      HOL/Auth/Event
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of events for security protocols

Datatype of events; function "sees"; freshness
*)

open Event;

AddIffs [Spy_in_bad, Server_not_bad];

(**** Function "spies" ****)

(** Simplifying   parts (insert X (spies evs))
      = parts {X} Un parts (spies evs) -- since general case loops*)

bind_thm ("parts_insert_spies",
	  parts_insert |> 
	  read_instantiate_sg (sign_of thy) [("H", "spies evs")]);


goal thy
    "P(event_case sf nf ev) = \
\      ((ALL A B X. ev = Says A B X --> P(sf A B X)) & \
\       (ALL A X. ev = Notes A X --> P(nf A X)))";
by (induct_tac "ev" 1);
by (Auto_tac());
qed "expand_event_case";

goal thy "spies (Says A B X # evs) = insert X (spies evs)";
by (Simp_tac 1);
qed "spies_Says";

(*The point of letting the Spy see "bad" agents' notes is to prevent
  redundant case-splits on whether A=Spy and whether A:bad*)
goal thy "spies (Notes A X # evs) = \
\         (if A:bad then insert X (spies evs) else spies evs)";
by (Simp_tac 1);
qed "spies_Notes";

goal thy "spies evs <= spies (Says A B X # evs)";
by (simp_tac (simpset() addsimps [subset_insertI]) 1);
qed "spies_subset_spies_Says";

goal thy "spies evs <= spies (Notes A X # evs)";
by (simp_tac (simpset() addsplits [expand_if]) 1);
by (Fast_tac 1);
qed "spies_subset_spies_Notes";

(*Spy sees all traffic*)
goal thy "Says A B X : set evs --> X : spies evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac
	      (simpset() addsplits [expand_event_case, expand_if])));
qed_spec_mp "Says_imp_spies";

(*Spy sees Notes of bad agents*)
goal thy "Notes A X : set evs --> A: bad --> X : spies evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac
	      (simpset() addsplits [expand_event_case, expand_if])));
qed_spec_mp "Notes_imp_spies";

(*Use with addSEs to derive contradictions from old Says events containing
  items known to be fresh*)
val spies_partsEs = make_elim (Says_imp_spies RS parts.Inj) :: partsEs;

Addsimps [spies_Says, spies_Notes];

(**** NOTE REMOVAL--laws above are cleaner, as they don't involve "case" ****)
Delsimps [spies_Cons];   


(*** Fresh nonces ***)

goal thy "parts (spies evs) <= used evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac
	      (simpset() addsimps [parts_insert_spies]
	                addsplits [expand_event_case, expand_if])));
by (ALLGOALS Blast_tac);
qed "parts_spies_subset_used";

bind_thm ("usedI", impOfSubs parts_spies_subset_used);
AddIs [usedI];

goal thy "parts (initState B) <= used evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac
	      (simpset() addsimps [parts_insert_spies]
	                addsplits [expand_event_case, expand_if])));
by (ALLGOALS Blast_tac);
bind_thm ("initState_into_used", impOfSubs (result()));

goal thy "used (Says A B X # evs) = parts{X} Un used evs";
by (Simp_tac 1);
qed "used_Says";
Addsimps [used_Says];

goal thy "used (Notes A X # evs) = parts{X} Un used evs";
by (Simp_tac 1);
qed "used_Notes";
Addsimps [used_Notes];

goal thy "used [] <= used evs";
by (Simp_tac 1);
by (blast_tac (claset() addIs [initState_into_used]) 1);
qed "used_nil_subset";

(**** NOTE REMOVAL--laws above are cleaner, as they don't involve "case" ****)
Delsimps [used_Nil, used_Cons];   


(*currently unused*)
goal thy "used evs <= used (evs@evs')";
by (induct_tac "evs" 1);
by (simp_tac (simpset() addsimps [used_nil_subset]) 1);
by (induct_tac "a" 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS Blast_tac);
qed "used_subset_append";


(*For proving theorems of the form X ~: analz (spies evs) --> P
  New events added by induction to "evs" are discarded.  Provided 
  this information isn't needed, the proof will be much shorter, since
  it will omit complicated reasoning about analz.*)
val analz_mono_contra_tac = 
  let val analz_impI = read_instantiate_sg (sign_of thy)
                [("P", "?Y ~: analz (spies ?evs)")] impI;
  in
    rtac analz_impI THEN' 
    REPEAT1 o 
      (dresolve_tac 
       [spies_subset_spies_Says  RS analz_mono RS contra_subsetD,
	spies_subset_spies_Notes RS analz_mono RS contra_subsetD])
    THEN'
    mp_tac
  end;
