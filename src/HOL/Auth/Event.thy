(*  Title:      HOL/Auth/Event
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatype of events; function "spies"; freshness

"bad" agents have been broken by the Spy; their private keys and internal
    stores are visible to him
*)

header{*Theory of Events for Security Protocols*}

theory Event = Message:

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: "agent => msg set"

datatype
  event = Says  agent agent msg
        | Gets  agent       msg
        | Notes agent       msg
       
consts 
  bad    :: "agent set"				(*compromised agents*)
  knows  :: "agent => event list => msg set"


text{*The constant "spies" is retained for compatibility's sake*}
syntax
  spies  :: "event list => msg set"

translations
  "spies"   => "knows Spy"

text{*Spy has access to his own key for spoof messages, but Server is secure*}
specification (bad)
  Spy_in_bad     [iff]: "Spy \<in> bad"
  Server_not_bad [iff]: "Server \<notin> bad"
    by (rule exI [of _ "{Spy}"], simp)

primrec
  knows_Nil:   "knows A [] = initState A"
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

(*
  Case A=Spy on the Gets event
  enforces the fact that if a message is received then it must have been sent,
  therefore the oops case must use Notes
*)

consts
  (*Set of items that might be visible to somebody:
    complement of the set of fresh items*)
  used :: "event list => msg set"

primrec
  used_Nil:   "used []         = (UN B. parts (initState B))"
  used_Cons:  "used (ev # evs) =
		     (case ev of
			Says A B X => parts {X} \<union> used evs
		      | Gets A X   => used evs
		      | Notes A X  => parts {X} \<union> used evs)"
    --{*The case for @{term Gets} seems anomalous, but @{term Gets} always
        follows @{term Says} in real protocols.  Seems difficult to change.
        See @{text Gets_correct} in theory @{text "Guard/Extensions.thy"}. *}

lemma Notes_imp_used [rule_format]: "Notes A X \<in> set evs --> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done

lemma Says_imp_used [rule_format]: "Says A B X \<in> set evs --> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done

lemma MPair_used [rule_format]:
     "MPair X Y \<in> used evs --> X \<in> used evs & Y \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done


subsection{*Function @{term knows}*}

(*Simplifying   
 parts(insert X (knows Spy evs)) = parts{X} \<union> parts(knows Spy evs).
  This version won't loop with the simplifier.*)
lemmas parts_insert_knows_A = parts_insert [of _ "knows A evs", standard]

lemma knows_Spy_Says [simp]:
     "knows Spy (Says A B X # evs) = insert X (knows Spy evs)"
by simp

text{*Letting the Spy see "bad" agents' notes avoids redundant case-splits
      on whether @{term "A=Spy"} and whether @{term "A\<in>bad"}*}
lemma knows_Spy_Notes [simp]:
     "knows Spy (Notes A X # evs) =  
          (if A:bad then insert X (knows Spy evs) else knows Spy evs)"
by simp

lemma knows_Spy_Gets [simp]: "knows Spy (Gets A X # evs) = knows Spy evs"
by simp

lemma knows_Spy_subset_knows_Spy_Says:
     "knows Spy evs \<subseteq> knows Spy (Says A B X # evs)"
by (simp add: subset_insertI)

lemma knows_Spy_subset_knows_Spy_Notes:
     "knows Spy evs \<subseteq> knows Spy (Notes A X # evs)"
by force

lemma knows_Spy_subset_knows_Spy_Gets:
     "knows Spy evs \<subseteq> knows Spy (Gets A X # evs)"
by (simp add: subset_insertI)

text{*Spy sees what is sent on the traffic*}
lemma Says_imp_knows_Spy [rule_format]:
     "Says A B X \<in> set evs --> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
done

lemma Notes_imp_knows_Spy [rule_format]:
     "Notes A X \<in> set evs --> A: bad --> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
done


text{*Elimination rules: derive contradictions from old Says events containing
  items known to be fresh*}
lemmas knows_Spy_partsEs =
     Says_imp_knows_Spy [THEN parts.Inj, THEN revcut_rl, standard] 
     parts.Body [THEN revcut_rl, standard]

text{*Compatibility for the old "spies" function*}
lemmas spies_partsEs = knows_Spy_partsEs
lemmas Says_imp_spies = Says_imp_knows_Spy
lemmas parts_insert_spies = parts_insert_knows_A [of _ Spy]


subsection{*Knowledge of Agents*}

lemma knows_Says: "knows A (Says A B X # evs) = insert X (knows A evs)"
by simp

lemma knows_Notes: "knows A (Notes A X # evs) = insert X (knows A evs)"
by simp

lemma knows_Gets:
     "A \<noteq> Spy --> knows A (Gets A X # evs) = insert X (knows A evs)"
by simp


lemma knows_subset_knows_Says: "knows A evs \<subseteq> knows A (Says A' B X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Notes: "knows A evs \<subseteq> knows A (Notes A' X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Gets: "knows A evs \<subseteq> knows A (Gets A' X # evs)"
by (simp add: subset_insertI)

text{*Agents know what they say*}
lemma Says_imp_knows [rule_format]: "Says A B X \<in> set evs --> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
apply blast
done

text{*Agents know what they note*}
lemma Notes_imp_knows [rule_format]: "Notes A X \<in> set evs --> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
apply blast
done

text{*Agents know what they receive*}
lemma Gets_imp_knows_agents [rule_format]:
     "A \<noteq> Spy --> Gets A X \<in> set evs --> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
done


text{*What agents DIFFERENT FROM Spy know 
  was either said, or noted, or got, or known initially*}
lemma knows_imp_Says_Gets_Notes_initState [rule_format]:
     "[| X \<in> knows A evs; A \<noteq> Spy |] ==> EX B.  
  Says A B X \<in> set evs | Gets A X \<in> set evs | Notes A X \<in> set evs | X \<in> initState A"
apply (erule rev_mp)
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
apply blast
done

text{*What the Spy knows -- for the time being --
  was either said or noted, or known initially*}
lemma knows_Spy_imp_Says_Notes_initState [rule_format]:
     "[| X \<in> knows Spy evs |] ==> EX A B.  
  Says A B X \<in> set evs | Notes A X \<in> set evs | X \<in> initState Spy"
apply (erule rev_mp)
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
apply blast
done

lemma parts_knows_Spy_subset_used: "parts (knows Spy evs) \<subseteq> used evs"
apply (induct_tac "evs", force)  
apply (simp add: parts_insert_knows_A knows_Cons add: event.split, blast) 
done

lemmas usedI = parts_knows_Spy_subset_used [THEN subsetD, intro]

lemma initState_into_used: "X \<in> parts (initState B) ==> X \<in> used evs"
apply (induct_tac "evs")
apply (simp_all add: parts_insert_knows_A split add: event.split, blast)
done

lemma used_Says [simp]: "used (Says A B X # evs) = parts{X} \<union> used evs"
by simp

lemma used_Notes [simp]: "used (Notes A X # evs) = parts{X} \<union> used evs"
by simp

lemma used_Gets [simp]: "used (Gets A X # evs) = used evs"
by simp

lemma used_nil_subset: "used [] \<subseteq> used evs"
apply simp
apply (blast intro: initState_into_used)
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


lemma knows_subset_knows_Cons: "knows A evs \<subseteq> knows A (e # evs)"
by (induct e, auto simp: knows_Cons)

lemma initState_subset_knows: "initState A \<subseteq> knows A evs"
apply (induct_tac evs, simp) 
apply (blast intro: knows_subset_knows_Cons [THEN subsetD])
done


text{*For proving @{text new_keys_not_used}*}
lemma keysFor_parts_insert:
     "[| K \<in> keysFor (parts (insert X G));  X \<in> synth (analz H) |] 
      ==> K \<in> keysFor (parts (G \<union> H)) | Key (invKey K) \<in> parts H"; 
by (force 
    dest!: parts_insert_subset_Un [THEN keysFor_mono, THEN [2] rev_subsetD]
           analz_subset_parts [THEN keysFor_mono, THEN [2] rev_subsetD]
    intro: analz_subset_parts [THEN subsetD] parts_mono [THEN [2] rev_subsetD])

method_setup analz_mono_contra = {*
    Method.no_args
      (Method.METHOD (fn facts => REPEAT_FIRST analz_mono_contra_tac)) *}
    "for proving theorems of the form X \<notin> analz (knows Spy evs) --> P"

subsubsection{*Useful for case analysis on whether a hash is a spoof or not*}

ML
{*
val knows_Cons     = thm "knows_Cons"
val used_Nil       = thm "used_Nil"
val used_Cons      = thm "used_Cons"

val Notes_imp_used = thm "Notes_imp_used";
val Says_imp_used = thm "Says_imp_used";
val MPair_used = thm "MPair_used";
val Says_imp_knows_Spy = thm "Says_imp_knows_Spy";
val Notes_imp_knows_Spy = thm "Notes_imp_knows_Spy";
val knows_Spy_partsEs = thms "knows_Spy_partsEs";
val spies_partsEs = thms "spies_partsEs";
val Says_imp_spies = thm "Says_imp_spies";
val parts_insert_spies = thm "parts_insert_spies";
val Says_imp_knows = thm "Says_imp_knows";
val Notes_imp_knows = thm "Notes_imp_knows";
val Gets_imp_knows_agents = thm "Gets_imp_knows_agents";
val knows_imp_Says_Gets_Notes_initState = thm "knows_imp_Says_Gets_Notes_initState";
val knows_Spy_imp_Says_Notes_initState = thm "knows_Spy_imp_Says_Notes_initState";
val usedI = thm "usedI";
val initState_into_used = thm "initState_into_used";
val used_Says = thm "used_Says";
val used_Notes = thm "used_Notes";
val used_Gets = thm "used_Gets";
val used_nil_subset = thm "used_nil_subset";
val analz_mono_contra = thms "analz_mono_contra";
val knows_subset_knows_Cons = thm "knows_subset_knows_Cons";
val initState_subset_knows = thm "initState_subset_knows";
val keysFor_parts_insert = thm "keysFor_parts_insert";


val synth_analz_mono = thm "synth_analz_mono";

val knows_Spy_subset_knows_Spy_Says = thm "knows_Spy_subset_knows_Spy_Says";
val knows_Spy_subset_knows_Spy_Notes = thm "knows_Spy_subset_knows_Spy_Notes";
val knows_Spy_subset_knows_Spy_Gets = thm "knows_Spy_subset_knows_Spy_Gets";


val synth_analz_mono_contra_tac = 
  let val syan_impI = inst "P" "?Y \<notin> synth (analz (knows Spy ?evs))" impI
  in
    rtac syan_impI THEN' 
    REPEAT1 o 
      (dresolve_tac 
       [knows_Spy_subset_knows_Spy_Says RS synth_analz_mono RS contra_subsetD,
        knows_Spy_subset_knows_Spy_Notes RS synth_analz_mono RS contra_subsetD,
	knows_Spy_subset_knows_Spy_Gets RS synth_analz_mono RS contra_subsetD])
    THEN'
    mp_tac
  end;
*}

method_setup synth_analz_mono_contra = {*
    Method.no_args
      (Method.METHOD (fn facts => REPEAT_FIRST synth_analz_mono_contra_tac)) *}
    "for proving theorems of the form X \<notin> synth (analz (knows Spy evs)) --> P"

end
