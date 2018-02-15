(*  Title:      HOL/SET_Protocol/Event_SET.thy
    Author:     Giampaolo Bella
    Author:     Fabio Massacci
    Author:     Lawrence C Paulson
*)

section\<open>Theory of Events for SET\<close>

theory Event_SET
imports Message_SET
begin

text\<open>The Root Certification Authority\<close>
abbreviation "RCA == CA 0"


text\<open>Message events\<close>
datatype
  event = Says  agent agent msg
        | Gets  agent       msg
        | Notes agent       msg


text\<open>compromised agents: keys known, Notes visible\<close>
consts bad :: "agent set"

text\<open>Spy has access to his own key for spoof messages, but RCA is secure\<close>
specification (bad)
  Spy_in_bad     [iff]: "Spy \<in> bad"
  RCA_not_bad [iff]: "RCA \<notin> bad"
    by (rule exI [of _ "{Spy}"], simp)


subsection\<open>Agents' Knowledge\<close>

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: "agent \<Rightarrow> msg set"

(* Message reception does not extend spy's knowledge because of
   reception invariant enforced by Reception rule in protocol definition*)
primrec knows :: "[agent, event list] \<Rightarrow> msg set"
where
  knows_Nil:
    "knows A [] = initState A"
| knows_Cons:
    "knows A (ev # evs) =
       (if A = Spy then
        (case ev of
           Says A' B X \<Rightarrow> insert X (knows Spy evs)
         | Gets A' X \<Rightarrow> knows Spy evs
         | Notes A' X  \<Rightarrow>
             if A' \<in> bad then insert X (knows Spy evs) else knows Spy evs)
        else
        (case ev of
           Says A' B X \<Rightarrow>
             if A'=A then insert X (knows A evs) else knows A evs
         | Gets A' X    \<Rightarrow>
             if A'=A then insert X (knows A evs) else knows A evs
         | Notes A' X    \<Rightarrow>
             if A'=A then insert X (knows A evs) else knows A evs))"


subsection\<open>Used Messages\<close>

primrec used :: "event list \<Rightarrow> msg set"
where
  (*Set of items that might be visible to somebody:
    complement of the set of fresh items.
    As above, message reception does extend used items *)
  used_Nil:  "used []         = (UN B. parts (initState B))"
| used_Cons: "used (ev # evs) =
                 (case ev of
                    Says A B X \<Rightarrow> parts {X} \<union> (used evs)
                  | Gets A X   \<Rightarrow> used evs
                  | Notes A X  \<Rightarrow> parts {X} \<union> (used evs))"



(* Inserted by default but later removed.  This declaration lets the file
be re-loaded. Addsimps [knows_Cons, used_Nil, *)

(** Simplifying   parts (insert X (knows Spy evs))
      = parts {X} \<union> parts (knows Spy evs) -- since general case loops*)

lemmas parts_insert_knows_A = parts_insert [of _ "knows A evs"] for A evs

lemma knows_Spy_Says [simp]:
     "knows Spy (Says A B X # evs) = insert X (knows Spy evs)"
by auto

text\<open>Letting the Spy see "bad" agents' notes avoids redundant case-splits
      on whether @{term "A=Spy"} and whether @{term "A\<in>bad"}\<close>
lemma knows_Spy_Notes [simp]:
     "knows Spy (Notes A X # evs) =
          (if A\<in>bad then insert X (knows Spy evs) else knows Spy evs)"
apply auto
done

lemma knows_Spy_Gets [simp]: "knows Spy (Gets A X # evs) = knows Spy evs"
by auto

lemma initState_subset_knows: "initState A \<subseteq> knows A evs"
apply (induct_tac "evs")
apply (auto split: event.split) 
done

lemma knows_Spy_subset_knows_Spy_Says:
     "knows Spy evs \<subseteq> knows Spy (Says A B X # evs)"
by auto

lemma knows_Spy_subset_knows_Spy_Notes:
     "knows Spy evs \<subseteq> knows Spy (Notes A X # evs)"
by auto

lemma knows_Spy_subset_knows_Spy_Gets:
     "knows Spy evs \<subseteq> knows Spy (Gets A X # evs)"
by auto

(*Spy sees what is sent on the traffic*)
lemma Says_imp_knows_Spy [rule_format]:
     "Says A B X \<in> set evs \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (auto split: event.split) 
done

(*Use with addSEs to derive contradictions from old Says events containing
  items known to be fresh*)
lemmas knows_Spy_partsEs =
     Says_imp_knows_Spy [THEN parts.Inj, elim_format] 
     parts.Body [elim_format]


subsection\<open>The Function @{term used}\<close>

lemma parts_knows_Spy_subset_used: "parts (knows Spy evs) \<subseteq> used evs"
apply (induct_tac "evs")
apply (auto simp add: parts_insert_knows_A split: event.split) 
done

lemmas usedI = parts_knows_Spy_subset_used [THEN subsetD, intro]

lemma initState_subset_used: "parts (initState B) \<subseteq> used evs"
apply (induct_tac "evs")
apply (auto split: event.split) 
done

lemmas initState_into_used = initState_subset_used [THEN subsetD]

lemma used_Says [simp]: "used (Says A B X # evs) = parts{X} \<union> used evs"
by auto

lemma used_Notes [simp]: "used (Notes A X # evs) = parts{X} \<union> used evs"
by auto

lemma used_Gets [simp]: "used (Gets A X # evs) = used evs"
by auto


lemma Notes_imp_parts_subset_used [rule_format]:
     "Notes A X \<in> set evs \<longrightarrow> parts {X} \<subseteq> used evs"
apply (induct_tac "evs")
apply (rename_tac [2] a evs')
apply (induct_tac [2] "a", auto)
done

text\<open>NOTE REMOVAL--laws above are cleaner, as they don't involve "case"\<close>
declare knows_Cons [simp del]
        used_Nil [simp del] used_Cons [simp del]


text\<open>For proving theorems of the form @{term "X \<notin> analz (knows Spy evs) \<longrightarrow> P"}
  New events added by induction to "evs" are discarded.  Provided 
  this information isn't needed, the proof will be much shorter, since
  it will omit complicated reasoning about @{term analz}.\<close>

lemmas analz_mono_contra =
       knows_Spy_subset_knows_Spy_Says [THEN analz_mono, THEN contra_subsetD]
       knows_Spy_subset_knows_Spy_Notes [THEN analz_mono, THEN contra_subsetD]
       knows_Spy_subset_knows_Spy_Gets [THEN analz_mono, THEN contra_subsetD]

lemmas analz_impI = impI [where P = "Y \<notin> analz (knows Spy evs)"] for Y evs

ML
\<open>
fun analz_mono_contra_tac ctxt = 
  resolve_tac ctxt @{thms analz_impI} THEN' 
  REPEAT1 o (dresolve_tac ctxt @{thms analz_mono_contra})
  THEN' mp_tac ctxt
\<close>

method_setup analz_mono_contra = \<open>
    Scan.succeed (fn ctxt => SIMPLE_METHOD (REPEAT_FIRST (analz_mono_contra_tac ctxt)))\<close>
    "for proving theorems of the form X \<notin> analz (knows Spy evs) \<longrightarrow> P"

end
