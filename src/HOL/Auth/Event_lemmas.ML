(*  Title:      HOL/Auth/Event
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)


val knows_Cons     = thm "knows_Cons";
val used_Nil       = thm "used_Nil";
val used_Cons      = thm "used_Cons";


(*Inserted by default but later removed.  This declaration lets the file
  be re-loaded.*)
Addsimps [knows_Cons, used_Nil, used_Cons];

(**** Function "knows" ****)

(** Simplifying   parts (insert X (knows Spy evs))
      = parts {X} Un parts (knows Spy evs) -- since general case loops*)

bind_thm ("parts_insert_knows_Spy",
	  parts_insert |> 
	  read_instantiate_sg (sign_of thy) [("H", "knows Spy evs")]);


val expand_event_case = thm "event.split";

Goal "knows Spy (Says A B X # evs) = insert X (knows Spy evs)";
by (Simp_tac 1);
qed "knows_Spy_Says";

(*The point of letting the Spy see "bad" agents' notes is to prevent
  redundant case-splits on whether A=Spy and whether A:bad*)
Goal "knows Spy (Notes A X # evs) = \
\         (if A:bad then insert X (knows Spy evs) else knows Spy evs)";
by (Simp_tac 1);
qed "knows_Spy_Notes";

Goal "knows Spy (Gets A X # evs) = knows Spy evs";
by (Simp_tac 1);
qed "knows_Spy_Gets";

Goal "knows Spy evs <= knows Spy (Says A B X # evs)";
by (simp_tac (simpset() addsimps [subset_insertI]) 1);
qed "knows_Spy_subset_knows_Spy_Says";

Goal "knows Spy evs <= knows Spy (Notes A X # evs)";
by (Simp_tac 1);
by (Fast_tac 1);
qed "knows_Spy_subset_knows_Spy_Notes";

Goal "knows Spy evs <= knows Spy (Gets A X # evs)";
by (simp_tac (simpset() addsimps [subset_insertI]) 1);
qed "knows_Spy_subset_knows_Spy_Gets";

(*Spy sees what is sent on the traffic*)
Goal "Says A B X : set evs --> X : knows Spy evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_event_case])));
qed_spec_mp "Says_imp_knows_Spy";

Goal "Notes A X : set evs --> A: bad --> X : knows Spy evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_event_case])));
qed_spec_mp "Notes_imp_knows_Spy";


(*Use with addSEs to derive contradictions from old Says events containing
  items known to be fresh*)
bind_thms ("knows_Spy_partsEs", 
           map make_elim [Says_imp_knows_Spy RS parts.Inj, parts.Body]);

Addsimps [knows_Spy_Says, knows_Spy_Notes, knows_Spy_Gets];


(*Begin lemmas about agents' knowledge*)

Goal "knows A (Says A B X # evs) = insert X (knows A evs)";
by (Simp_tac 1);
qed "knows_Says";

Goal "knows A (Notes A X # evs) = insert X (knows A evs)";
by (Simp_tac 1);
qed "knows_Notes";

Goal "A ~= Spy --> knows A (Gets A X # evs) = insert X (knows A evs)";
by (Simp_tac 1);
qed "knows_Gets";


Goal "knows A evs <= knows A (Says A B X # evs)";
by (simp_tac (simpset() addsimps [subset_insertI]) 1);
qed "knows_subset_knows_Says";

Goal "knows A evs <= knows A (Notes A X # evs)";
by (simp_tac (simpset() addsimps [subset_insertI]) 1);
qed "knows_subset_knows_Notes";

Goal "knows A evs <= knows A (Gets A X # evs)";
by (simp_tac (simpset() addsimps [subset_insertI]) 1);
qed "knows_subset_knows_Gets";

(*Agents know what they say*)
Goal "Says A B X : set evs --> X : knows A evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_event_case])));
by (Blast_tac 1);
qed_spec_mp "Says_imp_knows";

(*Agents know what they note*)
Goal "Notes A X : set evs --> X : knows A evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_event_case])));
by (Blast_tac 1);
qed_spec_mp "Notes_imp_knows";

(*Agents know what they receive*)
Goal "A ~= Spy --> Gets A X : set evs --> X : knows A evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_event_case])));
qed_spec_mp "Gets_imp_knows_agents";


(*What agents DIFFERENT FROM Spy know 
  was either said, or noted, or got, or known initially*)
Goal "[| X : knows A evs; A ~= Spy |] ==> EX B. \
\ Says A B X : set evs | Gets A X : set evs | Notes A X : set evs | X : initState A";
by (etac rev_mp 1);
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_event_case])));
by (Blast_tac 1);
qed_spec_mp "knows_imp_Says_Gets_Notes_initState";

(*What the Spy knows -- for the time being --
  was either said or noted, or known initially*)
Goal "[| X : knows Spy evs |] ==> EX A B. \
\ Says A B X : set evs | Notes A X : set evs | X : initState Spy";
by (etac rev_mp 1);
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_event_case])));
by (Blast_tac 1);
qed_spec_mp "knows_Spy_imp_Says_Notes_initState";

(*END lemmas about agents' knowledge*)



(**** NOTE REMOVAL--laws above are cleaner, as they don't involve "case" ****)
Delsimps [knows_Cons];   


(*** Fresh nonces ***)

Goal "parts (knows Spy evs) <= used evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac
	      (simpset() addsimps [parts_insert_knows_Spy]
	                addsplits [expand_event_case])));
by (ALLGOALS Blast_tac);
qed "parts_knows_Spy_subset_used";

bind_thm ("usedI", impOfSubs parts_knows_Spy_subset_used);
AddIs [usedI];

Goal "parts (initState B) <= used evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac
	      (simpset() addsimps [parts_insert_knows_Spy]
	                addsplits [expand_event_case])));
by (ALLGOALS Blast_tac);
bind_thm ("initState_into_used", impOfSubs (result()));

Goal "used (Says A B X # evs) = parts{X} Un used evs";
by (Simp_tac 1);
qed "used_Says";
Addsimps [used_Says];

Goal "used (Notes A X # evs) = parts{X} Un used evs";
by (Simp_tac 1);
qed "used_Notes";
Addsimps [used_Notes];

Goal "used (Gets A X # evs) = used evs";
by (Simp_tac 1);
qed "used_Gets";
Addsimps [used_Gets];

Goal "used [] <= used evs";
by (Simp_tac 1);
by (blast_tac (claset() addIs [initState_into_used]) 1);
qed "used_nil_subset";

(**** NOTE REMOVAL--laws above are cleaner, as they don't involve "case" ****)
Delsimps [used_Nil, used_Cons];   


(*For proving theorems of the form X ~: analz (knows Spy evs) --> P
  New events added by induction to "evs" are discarded.  Provided 
  this information isn't needed, the proof will be much shorter, since
  it will omit complicated reasoning about analz.*)

bind_thms ("analz_mono_contra",
       [knows_Spy_subset_knows_Spy_Says RS analz_mono RS contra_subsetD,
        knows_Spy_subset_knows_Spy_Notes RS analz_mono RS contra_subsetD,
	knows_Spy_subset_knows_Spy_Gets RS analz_mono RS contra_subsetD]);

val analz_mono_contra_tac = 
  let val analz_impI = inst "P" "?Y ~: analz (knows Spy ?evs)" impI
  in
    rtac analz_impI THEN' 
    REPEAT1 o 
      (dresolve_tac 
       [knows_Spy_subset_knows_Spy_Says RS analz_mono RS contra_subsetD,
        knows_Spy_subset_knows_Spy_Notes RS analz_mono RS contra_subsetD,
	knows_Spy_subset_knows_Spy_Gets RS analz_mono RS contra_subsetD])
    THEN'
    mp_tac
  end;

fun Reception_tac i =
    blast_tac (claset() addDs [Says_imp_knows_Spy RS parts.Inj, 
                               impOfSubs (parts_insert RS equalityD1), 
			       parts_trans,
                               Says_imp_knows_Spy RS analz.Inj,
                               impOfSubs analz_mono, analz_cut] 
                        addIs [less_SucI]) i;


(*Compatibility for the old "spies" function*)
bind_thms ("spies_partsEs", knows_Spy_partsEs);
bind_thm ("Says_imp_spies", Says_imp_knows_Spy);
bind_thm ("parts_insert_spies", parts_insert_knows_Spy);
