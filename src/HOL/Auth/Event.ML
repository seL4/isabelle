(*  Title:      HOL/Auth/Event
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of events for security protocols

Datatype of events; function "sees"; freshness
*)

open Event;

AddIffs [Spy_in_lost, Server_not_lost];

(**** Function "sees" ****)

(** Specialized rewrite rules for (sees A' (Says A B X #evs)) **)

goal thy "sees B (Says A B X # evs) = insert X (sees B evs)";
by (Simp_tac 1);
qed "sees_own_Says";

(** Three special-case rules for rewriting of sees A **)

goal thy "!!A. Server ~= B ==> \
\              sees Server (Says A B X # evs) = sees Server evs";
by (Asm_simp_tac 1);
qed "sees_Server_Says";

goal thy "!!A. Friend i ~= B ==> \
\              sees (Friend i) (Says A B X # evs) = sees (Friend i) evs";
by (Asm_simp_tac 1);
qed "sees_Friend_Says";

goal thy "sees Spy (Says A B X # evs) = insert X (sees Spy evs)";
by (Simp_tac 1);
qed "sees_Spy_Says";


(** Specialized rewrite rules for (sees A' (Notes A X evs)) **)

goal thy "sees A (Notes A X # evs) = insert X (sees A evs)";
by (Simp_tac 1);
qed "sees_own_Notes";

(** Three special-case rules for rewriting of sees A **)

goal thy "!!A. Server ~= A ==> \
\              sees Server (Notes A X # evs) = sees Server evs";
by (Asm_simp_tac 1);
qed "sees_Server_Notes";

goal thy "!!A. Friend i ~= A ==> \
\              sees (Friend i) (Notes A X # evs) = sees (Friend i) evs";
by (Asm_simp_tac 1);
qed "sees_Friend_Notes";

(*The point of letting the Spy see "lost" agents' notes is to prevent
  redundant case-splits on whether A=Spy and whether A:lost*)
goal thy "sees Spy (Notes A X # evs) = \
\         (if A:lost then insert X (sees Spy evs) else sees Spy evs)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Blast_tac 1);
qed "sees_Spy_Notes";


(** Other "sees" lemmas **)

goal thy "sees A (Says A' B X # evs) <= insert X (sees A evs)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Fast_tac 1);
qed "sees_Says_subset_insert";

goal thy "sees A evs <= sees A (Says A' B X # evs)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Fast_tac 1);
qed "sees_subset_sees_Says";

goal thy "sees A evs <= sees A (Notes A' X # evs)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Fast_tac 1);
qed "sees_subset_sees_Notes";

(*Pushing Unions into parts.  One of the agents A is B, and thus sees Y.*)
goal thy "(UN A. parts (sees A (Says B C Y # evs))) = \
\         parts {Y} Un (UN A. parts (sees A evs))";
by (Step_tac 1);
by (etac rev_mp 1);     (*split_tac does not work on assumptions*)
by (ALLGOALS
    (fast_tac (!claset addss (!simpset addsimps [parts_Un] 
				       setloop split_tac [expand_if]))));
qed "UN_parts_sees_Says";

goal thy "(UN A. parts (sees A (Notes B Y # evs))) = \
\         parts {Y} Un (UN A. parts (sees A evs))";
by (Step_tac 1);
by (etac rev_mp 1);     (*split_tac does not work on assumptions*)
by (ALLGOALS
    (fast_tac (!claset addss (!simpset addsimps [parts_Un] 
				       setloop split_tac [expand_if]))));
qed "UN_parts_sees_Notes";

(*Spy sees all traffic*)
goal thy "Says A B X : set evs --> X : sees Spy evs";
by (induct_tac "evs" 1);
by (Auto_tac ());
qed_spec_mp "Says_imp_sees_Spy";

(*Spy sees Notes of lost agents*)
goal thy "Notes A X : set evs --> A: lost --> X : sees Spy evs";
by (induct_tac "evs" 1);
by (Auto_tac ());
qed_spec_mp "Notes_imp_sees_Spy";

(*Use with addSEs to derive contradictions from old Says events containing
  items known to be fresh*)
val sees_Spy_partsEs = make_elim (Says_imp_sees_Spy RS parts.Inj) :: partsEs;

Addsimps [sees_own_Says, sees_Server_Says, sees_Friend_Says, sees_Spy_Says,
      sees_own_Notes, sees_Server_Notes, sees_Friend_Notes, sees_Spy_Notes];

(**** NOTE REMOVAL--laws above are cleaner--def of sees1 is messy ****)
Delsimps [sees_Cons];   


(*** Fresh nonces ***)

goalw thy [used_def] "!!X. X: parts (sees B evs) ==> X: used evs";
by (etac (impOfSubs parts_mono) 1);
by (Fast_tac 1);
qed "usedI";
AddIs [usedI];

goal thy "used (Says A B X # evs) = parts{X} Un used evs";
by (simp_tac (!simpset addsimps [used_def, UN_parts_sees_Says]) 1);
qed "used_Says";
Addsimps [used_Says];

goal thy "used (Notes A X # evs) = parts{X} Un used evs";
by (simp_tac (!simpset addsimps [used_def, UN_parts_sees_Notes]) 1);
qed "used_Notes";
Addsimps [used_Notes];

(*These two facts about "used" are unused.*)
goal thy "used [] <= used l";
by (induct_tac "l" 1);
by (induct_tac "a" 2);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS Blast_tac);
qed "used_nil_subset";

goal thy "used l <= used (l@l')";
by (induct_tac "l" 1);
by (simp_tac (!simpset addsimps [used_nil_subset]) 1);
by (induct_tac "a" 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS Blast_tac);
qed "used_subset_append";


(** Simplifying   parts (insert X (sees A evs))
      = parts {X} Un parts (sees A evs) -- since general case loops*)

val parts_insert_sees = 
    parts_insert |> read_instantiate_sg (sign_of thy)
                                        [("H", "sees A evs")]
                 |> standard;



(*For proving theorems of the form X ~: analz (sees Spy evs) --> P
  New events added by induction to "evs" are discarded.  Provided 
  this information isn't needed, the proof will be much shorter, since
  it will omit complicated reasoning about analz.*)
val analz_mono_contra_tac = 
  let val impI' = read_instantiate_sg (sign_of thy)
                [("P", "?Y ~: analz (sees ?A ?evs)")] impI;
  in
    rtac impI THEN' 
    REPEAT1 o 
      (dresolve_tac 
       [sees_subset_sees_Says  RS analz_mono RS contra_subsetD,
	sees_subset_sees_Notes RS analz_mono RS contra_subsetD])
    THEN'
    mp_tac
  end;
