(*  Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatype of events; function "spies"; freshness

"bad" agents have been broken by the Spy; their private keys and internal
    stores are visible to him
*)(*<*)

section\<open>Theory of Events for Security Protocols\<close>

theory Event imports Message begin

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: "agent \<Rightarrow> msg set"

datatype
  event = Says  agent agent msg
        | Gets  agent       msg
        | Notes agent       msg
       
consts 
  bad    :: "agent set"                         \<comment> \<open>compromised agents\<close>


text\<open>The constant "spies" is retained for compatibility's sake\<close>

primrec
  knows :: "agent \<Rightarrow> event list \<Rightarrow> msg set"
where
  knows_Nil:   "knows A [] = initState A"
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

abbreviation (input)
  spies  :: "event list \<Rightarrow> msg set" where
  "spies == knows Spy"

text\<open>Spy has access to his own key for spoof messages, but Server is secure\<close>
specification (bad)
  Spy_in_bad     [iff]: "Spy \<in> bad"
  Server_not_bad [iff]: "Server \<notin> bad"
    by (rule exI [of _ "{Spy}"], simp)

(*
  Case A=Spy on the Gets event
  enforces the fact that if a message is received then it must have been sent,
  therefore the oops case must use Notes
*)

primrec
  (*Set of items that might be visible to somebody:
    complement of the set of fresh items*)
  used :: "event list \<Rightarrow> msg set"
where
  used_Nil:   "used []         = (UN B. parts (initState B))"
| used_Cons:  "used (ev # evs) =
                     (case ev of
                        Says A B X \<Rightarrow> parts {X} \<union> used evs
                      | Gets A X   \<Rightarrow> used evs
                      | Notes A X  \<Rightarrow> parts {X} \<union> used evs)"
    \<comment> \<open>The case for \<^term>\<open>Gets\<close> seems anomalous, but \<^term>\<open>Gets\<close> always
        follows \<^term>\<open>Says\<close> in real protocols.  Seems difficult to change.
        See \<^text>\<open>Gets_correct\<close> in theory \<^text>\<open>Guard/Extensions.thy\<close>.\<close>

lemma Notes_imp_used [rule_format]: "Notes A X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done

lemma Says_imp_used [rule_format]: "Says A B X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done


subsection\<open>Function \<^term>\<open>knows\<close>\<close>

(*Simplifying   
 parts(insert X (knows Spy evs)) = parts{X} \<union> parts(knows Spy evs).
  This version won't loop with the simplifier.*)
lemmas parts_insert_knows_A = parts_insert [of _ "knows A evs"] for A evs

lemma knows_Spy_Says [simp]:
     "knows Spy (Says A B X # evs) = insert X (knows Spy evs)"
by simp

text\<open>Letting the Spy see "bad" agents' notes avoids redundant case-splits
      on whether \<^term>\<open>A=Spy\<close> and whether \<^term>\<open>A\<in>bad\<close>\<close>
lemma knows_Spy_Notes [simp]:
     "knows Spy (Notes A X # evs) =  
          (if A\<in>bad then insert X (knows Spy evs) else knows Spy evs)"
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

text\<open>Spy sees what is sent on the traffic\<close>
lemma Says_imp_knows_Spy [rule_format]:
     "Says A B X \<in> set evs \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
done

lemma Notes_imp_knows_Spy [rule_format]:
     "Notes A X \<in> set evs \<longrightarrow> A \<in> bad \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
done


text\<open>Elimination rules: derive contradictions from old Says events containing
  items known to be fresh\<close>
lemmas knows_Spy_partsEs =
     Says_imp_knows_Spy [THEN parts.Inj, elim_format] 
     parts.Body [elim_format]

lemmas Says_imp_analz_Spy = Says_imp_knows_Spy [THEN analz.Inj]

text\<open>Compatibility for the old "spies" function\<close>
lemmas spies_partsEs = knows_Spy_partsEs
lemmas Says_imp_spies = Says_imp_knows_Spy
lemmas parts_insert_spies = parts_insert_knows_A [of _ Spy]


subsection\<open>Knowledge of Agents\<close>

lemma knows_Says: "knows A (Says A B X # evs) = insert X (knows A evs)"
by simp

lemma knows_Notes: "knows A (Notes A X # evs) = insert X (knows A evs)"
by simp

lemma knows_Gets:
     "A \<noteq> Spy \<longrightarrow> knows A (Gets A X # evs) = insert X (knows A evs)"
by simp


lemma knows_subset_knows_Says: "knows A evs \<subseteq> knows A (Says A' B X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Notes: "knows A evs \<subseteq> knows A (Notes A' X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Gets: "knows A evs \<subseteq> knows A (Gets A' X # evs)"
by (simp add: subset_insertI)

text\<open>Agents know what they say\<close>
lemma Says_imp_knows [rule_format]: "Says A B X \<in> set evs \<longrightarrow> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply blast
done

text\<open>Agents know what they note\<close>
lemma Notes_imp_knows [rule_format]: "Notes A X \<in> set evs \<longrightarrow> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply blast
done

text\<open>Agents know what they receive\<close>
lemma Gets_imp_knows_agents [rule_format]:
     "A \<noteq> Spy \<longrightarrow> Gets A X \<in> set evs \<longrightarrow> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
done


text\<open>What agents DIFFERENT FROM Spy know 
  was either said, or noted, or got, or known initially\<close>
lemma knows_imp_Says_Gets_Notes_initState [rule_format]:
     "[| X \<in> knows A evs; A \<noteq> Spy |] ==> \<exists>B.
  Says A B X \<in> set evs \<or> Gets A X \<in> set evs \<or> Notes A X \<in> set evs \<or> X \<in> initState A"
apply (erule rev_mp)
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply blast
done

text\<open>What the Spy knows -- for the time being --
  was either said or noted, or known initially\<close>
lemma knows_Spy_imp_Says_Notes_initState [rule_format]:
     "[| X \<in> knows Spy evs |] ==> \<exists>A B.
  Says A B X \<in> set evs \<or> Notes A X \<in> set evs \<or> X \<in> initState Spy"
apply (erule rev_mp)
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply blast
done

lemma parts_knows_Spy_subset_used: "parts (knows Spy evs) \<subseteq> used evs"
apply (induct_tac "evs", force)  
apply (simp add: parts_insert_knows_A knows_Cons add: event.split, blast) 
done

lemmas usedI = parts_knows_Spy_subset_used [THEN subsetD, intro]

lemma initState_into_used: "X \<in> parts (initState B) \<Longrightarrow> X \<in> used evs"
apply (induct_tac "evs")
apply (simp_all add: parts_insert_knows_A split: event.split, blast)
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

text\<open>NOTE REMOVAL--laws above are cleaner, as they don't involve "case"\<close>
declare knows_Cons [simp del]
        used_Nil [simp del] used_Cons [simp del]


text\<open>For proving theorems of the form \<^term>\<open>X \<notin> analz (knows Spy evs) \<longrightarrow> P\<close>
  New events added by induction to "evs" are discarded.  Provided 
  this information isn't needed, the proof will be much shorter, since
  it will omit complicated reasoning about \<^term>\<open>analz\<close>.\<close>

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

lemma knows_subset_knows_Cons: "knows A evs \<subseteq> knows A (e # evs)"
by (induct e, auto simp: knows_Cons)

lemma initState_subset_knows: "initState A \<subseteq> knows A evs"
apply (induct_tac evs, simp) 
apply (blast intro: knows_subset_knows_Cons [THEN subsetD])
done


text\<open>For proving \<open>new_keys_not_used\<close>\<close>
lemma keysFor_parts_insert:
     "[| K \<in> keysFor (parts (insert X G));  X \<in> synth (analz H) |] 
      ==> K \<in> keysFor (parts (G \<union> H)) | Key (invKey K) \<in> parts H" 
by (force 
    dest!: parts_insert_subset_Un [THEN keysFor_mono, THEN [2] rev_subsetD]
           analz_subset_parts [THEN keysFor_mono, THEN [2] rev_subsetD]
    intro: analz_subset_parts [THEN subsetD] parts_mono [THEN [2] rev_subsetD])

method_setup analz_mono_contra = \<open>
    Scan.succeed (fn ctxt => SIMPLE_METHOD (REPEAT_FIRST (analz_mono_contra_tac ctxt)))\<close>
    "for proving theorems of the form X \<notin> analz (knows Spy evs) \<longrightarrow> P"

subsubsection\<open>Useful for case analysis on whether a hash is a spoof or not\<close>

lemmas syan_impI = impI [where P = "Y \<notin> synth (analz (knows Spy evs))"] for Y evs

ML
\<open>
val knows_Cons = @{thm knows_Cons};
val used_Nil = @{thm used_Nil};
val used_Cons = @{thm used_Cons};

val Notes_imp_used = @{thm Notes_imp_used};
val Says_imp_used = @{thm Says_imp_used};
val Says_imp_knows_Spy = @{thm Says_imp_knows_Spy};
val Notes_imp_knows_Spy = @{thm Notes_imp_knows_Spy};
val knows_Spy_partsEs = @{thms knows_Spy_partsEs};
val spies_partsEs = @{thms spies_partsEs};
val Says_imp_spies = @{thm Says_imp_spies};
val parts_insert_spies = @{thm parts_insert_spies};
val Says_imp_knows = @{thm Says_imp_knows};
val Notes_imp_knows = @{thm Notes_imp_knows};
val Gets_imp_knows_agents = @{thm Gets_imp_knows_agents};
val knows_imp_Says_Gets_Notes_initState = @{thm knows_imp_Says_Gets_Notes_initState};
val knows_Spy_imp_Says_Notes_initState = @{thm knows_Spy_imp_Says_Notes_initState};
val usedI = @{thm usedI};
val initState_into_used = @{thm initState_into_used};
val used_Says = @{thm used_Says};
val used_Notes = @{thm used_Notes};
val used_Gets = @{thm used_Gets};
val used_nil_subset = @{thm used_nil_subset};
val analz_mono_contra = @{thms analz_mono_contra};
val knows_subset_knows_Cons = @{thm knows_subset_knows_Cons};
val initState_subset_knows = @{thm initState_subset_knows};
val keysFor_parts_insert = @{thm keysFor_parts_insert};


val synth_analz_mono = @{thm synth_analz_mono};

val knows_Spy_subset_knows_Spy_Says = @{thm knows_Spy_subset_knows_Spy_Says};
val knows_Spy_subset_knows_Spy_Notes = @{thm knows_Spy_subset_knows_Spy_Notes};
val knows_Spy_subset_knows_Spy_Gets = @{thm knows_Spy_subset_knows_Spy_Gets};


fun synth_analz_mono_contra_tac ctxt = 
  resolve_tac ctxt @{thms syan_impI} THEN'
  REPEAT1 o 
    (dresolve_tac ctxt
     [@{thm knows_Spy_subset_knows_Spy_Says} RS @{thm synth_analz_mono} RS @{thm contra_subsetD},
      @{thm knows_Spy_subset_knows_Spy_Notes} RS @{thm synth_analz_mono} RS @{thm contra_subsetD},
      @{thm knows_Spy_subset_knows_Spy_Gets} RS @{thm synth_analz_mono} RS @{thm contra_subsetD}])
  THEN'
  mp_tac ctxt
\<close>

method_setup synth_analz_mono_contra = \<open>
    Scan.succeed (fn ctxt => SIMPLE_METHOD (REPEAT_FIRST (synth_analz_mono_contra_tac ctxt)))\<close>
    "for proving theorems of the form X \<notin> synth (analz (knows Spy evs)) \<longrightarrow> P"
(*>*)

section\<open>Event Traces \label{sec:events}\<close>

text \<open>
The system's behaviour is formalized as a set of traces of
\emph{events}.  The most important event, \<open>Says A B X\<close>, expresses
$A\to B : X$, which is the attempt by~$A$ to send~$B$ the message~$X$.
A trace is simply a list, constructed in reverse
using~\<open>#\<close>.  Other event types include reception of messages (when
we want to make it explicit) and an agent's storing a fact.

Sometimes the protocol requires an agent to generate a new nonce. The
probability that a 20-byte random number has appeared before is effectively
zero.  To formalize this important property, the set \<^term>\<open>used evs\<close>
denotes the set of all items mentioned in the trace~\<open>evs\<close>.
The function \<open>used\<close> has a straightforward
recursive definition.  Here is the case for \<open>Says\<close> event:
@{thm [display,indent=5] used_Says [no_vars]}

The function \<open>knows\<close> formalizes an agent's knowledge.  Mostly we only
care about the spy's knowledge, and \<^term>\<open>knows Spy evs\<close> is the set of items
available to the spy in the trace~\<open>evs\<close>.  Already in the empty trace,
the spy starts with some secrets at his disposal, such as the private keys
of compromised users.  After each \<open>Says\<close> event, the spy learns the
message that was sent:
@{thm [display,indent=5] knows_Spy_Says [no_vars]}
Combinations of functions express other important
sets of messages derived from~\<open>evs\<close>:
\begin{itemize}
\item \<^term>\<open>analz (knows Spy evs)\<close> is everything that the spy could
learn by decryption
\item \<^term>\<open>synth (analz (knows Spy evs))\<close> is everything that the spy
could generate
\end{itemize}
\<close>

(*<*)
end
(*>*)
