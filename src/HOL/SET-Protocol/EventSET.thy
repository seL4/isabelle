(*  Title:      HOL/Auth/SET/EventSET
    ID:         $Id$
    Authors:     Giampaolo Bella, Fabio Massacci, Lawrence C Paulson
*)

header{*Theory of Events for SET*}

theory EventSET = MessageSET:

text{*The Root Certification Authority*}
syntax        RCA :: agent
translations "RCA" == "CA 0"


text{*Message events*}
datatype
  event = Says  agent agent msg
	| Gets  agent	    msg
        | Notes agent       msg


text{*compromised agents: keys known, Notes visible*}
consts bad :: "agent set"

text{*Spy has access to his own key for spoof messages, but RCA is secure*}
specification (bad)
  Spy_in_bad     [iff]: "Spy \<in> bad"
  RCA_not_bad [iff]: "RCA \<notin> bad"
    by (rule exI [of _ "{Spy}"], simp)


subsection{*Agents' Knowledge*}

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: "agent => msg set"
  knows  :: "[agent, event list] => msg set"

(* Message reception does not extend spy's knowledge because of
   reception invariant enforced by Reception rule in protocol definition*)
primrec

knows_Nil:
  "knows A []       = initState A"
knows_Cons:
    "knows A (ev # evs) =
       (if A = Spy then
	(case ev of
	   Says A' B X => insert X (knows Spy evs)
	 | Gets A' X => knows Spy evs
	 | Notes A' X  =>
	     if A' \<in> bad then insert X (knows Spy evs) else knows Spy evs)
	else
	(case ev of
	   Says A' B X =>
	     if A'=A then insert X (knows A evs) else knows A evs
	 | Gets A' X    =>
	     if A'=A then insert X (knows A evs) else knows A evs
	 | Notes A' X    =>
	     if A'=A then insert X (knows A evs) else knows A evs))"


subsection{*Used Messages*}

consts
  (*Set of items that might be visible to somebody:
    complement of the set of fresh items*)
  used :: "event list => msg set"

(* As above, message reception does extend used items *)
primrec
  used_Nil:  "used []         = (UN B. parts (initState B))"
  used_Cons: "used (ev # evs) =
	         (case ev of
		    Says A B X => parts {X} Un (used evs)
         	  | Gets A X   => used evs
		  | Notes A X  => parts {X} Un (used evs))"



(* Inserted by default but later removed.  This declaration lets the file
be re-loaded. Addsimps [knows_Cons, used_Nil, *)

(** Simplifying   parts (insert X (knows Spy evs))
      = parts {X} Un parts (knows Spy evs) -- since general case loops*)

lemmas parts_insert_knows_A = parts_insert [of _ "knows A evs", standard]

lemma knows_Spy_Says [simp]:
     "knows Spy (Says A B X # evs) = insert X (knows Spy evs)"
by auto

text{*Letting the Spy see "bad" agents' notes avoids redundant case-splits
      on whether @{term "A=Spy"} and whether @{term "A\<in>bad"}*}
lemma knows_Spy_Notes [simp]:
     "knows Spy (Notes A X # evs) =
          (if A:bad then insert X (knows Spy evs) else knows Spy evs)"
apply auto
done

lemma knows_Spy_Gets [simp]: "knows Spy (Gets A X # evs) = knows Spy evs"
by auto

lemma initState_subset_knows: "initState A <= knows A evs"
apply (induct_tac "evs")
apply (auto split: event.split) 
done

lemma knows_Spy_subset_knows_Spy_Says:
     "knows Spy evs <= knows Spy (Says A B X # evs)"
by auto

lemma knows_Spy_subset_knows_Spy_Notes:
     "knows Spy evs <= knows Spy (Notes A X # evs)"
by auto

lemma knows_Spy_subset_knows_Spy_Gets:
     "knows Spy evs <= knows Spy (Gets A X # evs)"
by auto

(*Spy sees what is sent on the traffic*)
lemma Says_imp_knows_Spy [rule_format]:
     "Says A B X \<in> set evs --> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (auto split: event.split) 
done

(*Use with addSEs to derive contradictions from old Says events containing
  items known to be fresh*)
lemmas knows_Spy_partsEs =
     Says_imp_knows_Spy [THEN parts.Inj, THEN revcut_rl, standard] 
     parts.Body [THEN revcut_rl, standard]


subsection{*Lemmas About Agents' Knowledge*}

lemma knows_Says: "knows A (Says A B X # evs) = insert X (knows A evs)"
by auto

lemma knows_Notes: "knows A (Notes A X # evs) = insert X (knows A evs)"
by auto

lemma knows_Gets:
     "A \<noteq> Spy --> knows A (Gets A X # evs) = insert X (knows A evs)"
by auto

lemma knows_subset_knows_Says: "knows A evs <= knows A (Says A B X # evs)"
by auto

lemma knows_subset_knows_Notes: "knows A evs <= knows A (Notes A X # evs)"
by auto

lemma knows_subset_knows_Gets: "knows A evs <= knows A (Gets A X # evs)"
by auto

(*Agents know what they say*)
lemma Says_imp_knows [rule_format]:
     "Says A B X \<in> set evs --> X \<in> knows A evs"
apply (induct_tac "evs")
apply (auto split: event.split) 
done

(*Agents know what they note*)
lemma Notes_imp_knows [rule_format]:
     "Notes A X \<in> set evs --> X \<in> knows A evs"
apply (induct_tac "evs")
apply (auto split: event.split) 
done

(*Agents know what they receive*)
lemma Gets_imp_knows_agents [rule_format]:
     "A \<noteq> Spy --> Gets A X \<in> set evs --> X \<in> knows A evs"
apply (induct_tac "evs")
apply (auto split: event.split) 
done


(*What agents DIFFERENT FROM Spy know
  was either said, or noted, or got, or known initially*)
lemma knows_imp_Says_Gets_Notes_initState [rule_format]:
     "[| X \<in> knows A evs; A \<noteq> Spy |] ==>
  \<exists>B. Says A B X \<in> set evs |
               Gets A X \<in> set evs |
               Notes A X \<in> set evs |
               X \<in> initState A"
apply (erule rev_mp) 
apply (induct_tac "evs")
apply (auto split: event.split) 
done

(*What the Spy knows -- for the time being --
  was either said or noted, or known initially*)
lemma knows_Spy_imp_Says_Notes_initState [rule_format]:
     "[| X \<in> knows Spy evs |] ==>
   \<exists>A B. Says A B X \<in> set evs |
                  Notes A X \<in> set evs |
                  X \<in> initState Spy"
apply (erule rev_mp) 
apply (induct_tac "evs")
apply (auto split: event.split) 
done


subsection{*The Function @{term used}*}

lemma parts_knows_Spy_subset_used: "parts (knows Spy evs) <= used evs"
apply (induct_tac "evs")
apply (auto simp add: parts_insert_knows_A split: event.split) 
done

lemmas usedI = parts_knows_Spy_subset_used [THEN subsetD, intro]

lemma initState_subset_used: "parts (initState B) <= used evs"
apply (induct_tac "evs")
apply (auto split: event.split) 
done

lemmas initState_into_used = initState_subset_used [THEN subsetD]

lemma used_Says [simp]: "used (Says A B X # evs) = parts{X} Un used evs"
by auto

lemma used_Notes [simp]: "used (Notes A X # evs) = parts{X} Un used evs"
by auto

lemma used_Gets [simp]: "used (Gets A X # evs) = used evs"
by auto

lemma used_nil_subset: "used [] <= used evs"
apply auto
apply (rule initState_into_used, auto)
done


lemma Notes_imp_parts_subset_used [rule_format]:
     "Notes A X \<in> set evs --> parts {X} <= used evs"
apply (induct_tac "evs")
apply (induct_tac [2] "a", auto)
done

text{*NOTE REMOVAL--laws above are cleaner, as they don't involve "case"*}
declare knows_Cons [simp del]
        used_Nil [simp del] used_Cons [simp del]


text{*For proving theorems of the form @{term "X \<notin> analz (knows Spy evs) --> P"}
  New events added by induction to "evs" are discarded.  Provided 
  this information isn't needed, the proof will be much shorter, since
  it will omit complicated reasoning about @{term analz}.*}

lemmas analz_mono_contra =
       knows_Spy_subset_knows_Spy_Says [THEN analz_mono, THEN contra_subsetD]
       knows_Spy_subset_knows_Spy_Notes [THEN analz_mono, THEN contra_subsetD]
       knows_Spy_subset_knows_Spy_Gets [THEN analz_mono, THEN contra_subsetD]
ML
{*
val analz_mono_contra_tac = 
  let val analz_impI = inst "P" "?Y \<notin> analz (knows Spy ?evs)" impI
  in
    rtac analz_impI THEN' 
    REPEAT1 o 
      (dresolve_tac (thms"analz_mono_contra"))
    THEN' mp_tac
  end
*}

method_setup analz_mono_contra = {*
    Method.no_args
      (Method.METHOD (fn facts => REPEAT_FIRST analz_mono_contra_tac)) *}
    "for proving theorems of the form X \<notin> analz (knows Spy evs) --> P"

end
