(*  Title:      HOL/Auth/Event
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of events for security protocols

Datatype of events; function "sees"; freshness
*)

open Event;

(*** Function "sees" ***)

(** Specialized rewrite rules for (sees lost A (Says...#evs)) **)

goal thy "sees lost B (Says A B X # evs) = insert X (sees lost B evs)";
by (Simp_tac 1);
qed "sees_own";

goal thy "sees lost B (Notes A X # evs) = \
\         (if A=B then insert X (sees lost B evs) else sees lost B evs)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
qed "sees_Notes";

(** Three special-case rules for rewriting of sees lost A **)

goal thy "!!A. Server ~= B ==> \
\          sees lost Server (Says A B X # evs) = sees lost Server evs";
by (Asm_simp_tac 1);
qed "sees_Server";

goal thy "!!A. Friend i ~= B ==> \
\          sees lost (Friend i) (Says A B X # evs) = sees lost (Friend i) evs";
by (Asm_simp_tac 1);
qed "sees_Friend";

goal thy "sees lost Spy (Says A B X # evs) = insert X (sees lost Spy evs)";
by (Simp_tac 1);
qed "sees_Spy";

goal thy "sees lost A (Says A' B X # evs) <= insert X (sees lost A evs)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Fast_tac 1);
qed "sees_Says_subset_insert";

goal thy "sees lost A evs <= sees lost A (Says A' B X # evs)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Fast_tac 1);
qed "sees_subset_sees_Says";

goal thy "sees lost A evs <= sees lost A (Notes A' X # evs)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Fast_tac 1);
qed "sees_subset_sees_Notes";

(*Pushing Unions into parts.  One of the agents A is B, and thus sees Y.*)
goal thy "(UN A. parts (sees lost A (Says B C Y # evs))) = \
\         parts {Y} Un (UN A. parts (sees lost A evs))";
by (Step_tac 1);
by (etac rev_mp 1);     (*split_tac does not work on assumptions*)
by (ALLGOALS
    (fast_tac (!claset addss (!simpset addsimps [parts_Un] 
				       setloop split_tac [expand_if]))));
qed "UN_parts_sees_Says";

goal thy "(UN A. parts (sees lost A (Notes B Y # evs))) = \
\         parts {Y} Un (UN A. parts (sees lost A evs))";
by (Step_tac 1);
by (etac rev_mp 1);     (*split_tac does not work on assumptions*)
by (ALLGOALS
    (fast_tac (!claset addss (!simpset addsimps [parts_Un] 
				       setloop split_tac [expand_if]))));
qed "UN_parts_sees_Notes";

goal thy "Says A B X : set evs --> X : sees lost Spy evs";
by (list.induct_tac "evs" 1);
by (Auto_tac ());
qed_spec_mp "Says_imp_sees_Spy";

(*Use with addSEs to derive contradictions from old Says events containing
  items known to be fresh*)
val sees_Spy_partsEs = make_elim (Says_imp_sees_Spy RS parts.Inj):: partsEs;

Addsimps [sees_own, sees_Notes, sees_Server, sees_Friend, sees_Spy];

(**** NOTE REMOVAL--laws above are cleaner--def of sees1 is messy ****)
Delsimps [sees_Cons];   


(*** Fresh nonces ***)

goalw thy [used_def] "!!X. X: parts (sees lost B evs) ==> X: used evs";
by (etac (impOfSubs parts_mono) 1);
by (Fast_tac 1);
qed "usedI";
AddIs [usedI];

goal thy "used (Says A B X # evs) = parts{X} Un used evs";
by (simp_tac (!simpset addsimps [used_def, UN_parts_sees_Says]) 1);
qed "used_Says";
Addsimps [used_Says];

goal thy "used (Notes A X # evs) = parts{X} Un used evs";
by (simp_tac (!simpset delsimps [sees_Notes]
		       addsimps [used_def, UN_parts_sees_Notes]) 1);
qed "used_Notes";
Addsimps [used_Notes];

(*These two facts about "used" are unused.*)
goal thy "used [] <= used l";
by (list.induct_tac "l" 1);
by (event.induct_tac "a" 2);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS Blast_tac);
qed "used_nil_subset";

goal thy "used l <= used (l@l')";
by (list.induct_tac "l" 1);
by (simp_tac (!simpset addsimps [used_nil_subset]) 1);
by (event.induct_tac "a" 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS Blast_tac);
qed "used_subset_append";


(** Simplifying   parts (insert X (sees lost A evs))
      = parts {X} Un parts (sees lost A evs) -- since general case loops*)

val parts_insert_sees = 
    parts_insert |> read_instantiate_sg (sign_of thy)
                                        [("H", "sees lost A evs")]
                 |> standard;



(*For proving theorems of the form X ~: analz (sees Spy evs) --> P
  New events added by induction to "evs" are discarded.  Provided 
  this information isn't needed, the proof will be much shorter, since
  it will omit complicated reasoning about analz.*)
val analz_mono_contra_tac = 
  let val impI' = read_instantiate_sg (sign_of thy)
                [("P", "?Y ~: analz (sees lost ?A ?evs)")] impI;
  in
    rtac impI THEN' 
    REPEAT1 o 
      (dresolve_tac 
       [sees_subset_sees_Says  RS analz_mono RS contra_subsetD,
	sees_subset_sees_Notes RS analz_mono RS contra_subsetD])
    THEN'
    mp_tac
  end;
