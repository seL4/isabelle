header{*Theory of Events for Security Protocols that use smartcards*}

theory EventSC imports "../Message" begin

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: "agent => msg set"

datatype card = Card agent

text{*Four new events express the traffic between an agent and his card*}
datatype  
  event = Says  agent agent msg
        | Notes agent       msg
        | Gets  agent       msg
        | Inputs agent card msg (*Agent sends to card and\<dots>*)
        | C_Gets card       msg (*\<dots> card receives it*) 
        | Outpts card agent msg (*Card sends to agent and\<dots>*)
        | A_Gets agent      msg (*agent receives it*)
    
consts 
 bad     :: "agent set"  (*compromised agents*)
 stolen    :: "card set" (* stolen smart cards *)
 cloned  :: "card set"   (* cloned smart cards*)
 secureM :: "bool"(*assumption of secure means between agents and their cards*)

abbreviation
  insecureM :: bool where (*certain protocols make no assumption of secure means*)
  "insecureM == \<not>secureM"


text{*Spy has access to his own key for spoof messages, but Server is secure*}
specification (bad)
  Spy_in_bad     [iff]: "Spy \<in> bad"
  Server_not_bad [iff]: "Server \<notin> bad"
  apply (rule exI [of _ "{Spy}"], simp) done

specification (stolen)
  (*The server's card is secure by assumption\<dots>*)
  Card_Server_not_stolen [iff]: "Card Server \<notin> stolen"
  Card_Spy_not_stolen    [iff]: "Card Spy \<notin> stolen"
  apply blast done

specification (cloned)
  (*\<dots> the spy's card is secure because she already can use it freely*)
  Card_Server_not_cloned [iff]: "Card Server \<notin> cloned"
  Card_Spy_not_cloned    [iff]: "Card Spy \<notin> cloned"
  apply blast done


primrec (*This definition is extended over the new events, subject to the 
          assumption of secure means*)
  knows   :: "agent => event list => msg set" (*agents' knowledge*) where
  knows_Nil:   "knows A [] = initState A" |
  knows_Cons:  "knows A (ev # evs) =
         (case ev of
            Says A' B X => 
                if (A=A' | A=Spy) then insert X (knows A evs) else knows A evs
          | Notes A' X  => 
                if (A=A' | (A=Spy & A'\<in>bad)) then insert X (knows A evs) 
                                             else knows A evs 
          | Gets A' X   =>
                if (A=A' & A \<noteq> Spy) then insert X (knows A evs) 
                                     else knows A evs
          | Inputs A' C X =>
              if secureM then
                if A=A' then insert X (knows A evs) else knows A evs
              else
                if (A=A' | A=Spy) then insert X (knows A evs) else knows A evs
          | C_Gets C X   => knows A evs
          | Outpts C A' X =>
              if secureM then
                if A=A' then insert X (knows A evs) else knows A evs
              else
                if A=Spy then insert X (knows A evs) else knows A evs
          | A_Gets A' X   =>
                if (A=A' & A \<noteq> Spy) then insert X (knows A evs) 
                                     else knows A evs)"



primrec
  (*The set of items that might be visible to someone is easily extended 
    over the new events*)
  used :: "event list => msg set" where
  used_Nil:   "used []         = (UN B. parts (initState B))" |
  used_Cons:  "used (ev # evs) =
                 (case ev of
                    Says A B X => parts {X} \<union> (used evs)
                  | Notes A X  => parts {X} \<union> (used evs)
                  | Gets A X   => used evs
                  | Inputs A C X  => parts{X} \<union> (used evs) 
                  | C_Gets C X   => used evs
                  | Outpts C A X  => parts{X} \<union> (used evs)
                  | A_Gets A X   => used evs)"
    --{*@{term Gets} always follows @{term Says} in real protocols. 
       Likewise, @{term C_Gets} will always have to follow @{term Inputs}
       and @{term A_Gets} will always have to follow @{term Outpts}*}

lemma Notes_imp_used [rule_format]: "Notes A X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done

lemma Says_imp_used [rule_format]: "Says A B X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done

lemma MPair_used [rule_format]:
     "MPair X Y \<in> used evs \<longrightarrow> X \<in> used evs & Y \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done


subsection{*Function @{term knows}*}

(*Simplifying   
 parts(insert X (knows Spy evs)) = parts{X} \<union> parts(knows Spy evs).
  This version won't loop with the simplifier.*)
lemmas parts_insert_knows_A = parts_insert [of _ "knows A evs"] for A evs

lemma knows_Spy_Says [simp]:
     "knows Spy (Says A B X # evs) = insert X (knows Spy evs)"
by simp

text{*Letting the Spy see "bad" agents' notes avoids redundant case-splits
      on whether @{term "A=Spy"} and whether @{term "A\<in>bad"}*}
lemma knows_Spy_Notes [simp]:
     "knows Spy (Notes A X # evs) =  
          (if A\<in>bad then insert X (knows Spy evs) else knows Spy evs)"
by simp

lemma knows_Spy_Gets [simp]: "knows Spy (Gets A X # evs) = knows Spy evs"
by simp

lemma knows_Spy_Inputs_secureM [simp]: 
     "secureM \<Longrightarrow> knows Spy (Inputs A C X # evs) =  
        (if A=Spy then insert X (knows Spy evs) else knows Spy evs)"
by simp

lemma knows_Spy_Inputs_insecureM [simp]: 
     "insecureM \<Longrightarrow> knows Spy (Inputs A C X # evs) = insert X (knows Spy evs)"
by simp

lemma knows_Spy_C_Gets [simp]: "knows Spy (C_Gets C X # evs) = knows Spy evs"
by simp

lemma knows_Spy_Outpts_secureM [simp]: 
      "secureM \<Longrightarrow> knows Spy (Outpts C A X # evs) = 
         (if A=Spy then insert X (knows Spy evs) else knows Spy evs)"
by simp

lemma knows_Spy_Outpts_insecureM [simp]: 
      "insecureM \<Longrightarrow> knows Spy (Outpts C A X # evs) = insert X (knows Spy evs)"
by simp

lemma knows_Spy_A_Gets [simp]: "knows Spy (A_Gets A X # evs) = knows Spy evs"
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

lemma knows_Spy_subset_knows_Spy_Inputs: 
     "knows Spy evs \<subseteq> knows Spy (Inputs A C X # evs)"
by auto

lemma knows_Spy_equals_knows_Spy_Gets: 
     "knows Spy evs = knows Spy (C_Gets C X # evs)"
by (simp add: subset_insertI)

lemma knows_Spy_subset_knows_Spy_Outpts: "knows Spy evs \<subseteq> knows Spy (Outpts C A X # evs)"
by auto

lemma knows_Spy_subset_knows_Spy_A_Gets: "knows Spy evs \<subseteq> knows Spy (A_Gets A X # evs)"
by (simp add: subset_insertI)



text{*Spy sees what is sent on the traffic*}
lemma Says_imp_knows_Spy [rule_format]:
     "Says A B X \<in> set evs \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
done

lemma Notes_imp_knows_Spy [rule_format]:
     "Notes A X \<in> set evs \<longrightarrow> A\<in> bad \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
done

(*Nothing can be stated on a Gets event*)

lemma Inputs_imp_knows_Spy_secureM [rule_format (no_asm)]: 
     "Inputs Spy C X \<in> set evs \<longrightarrow> secureM \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
done

lemma Inputs_imp_knows_Spy_insecureM [rule_format (no_asm)]:
     "Inputs A C X \<in> set evs \<longrightarrow> insecureM \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
done

(*Nothing can be stated on a C_Gets event*)

lemma Outpts_imp_knows_Spy_secureM [rule_format (no_asm)]: 
     "Outpts C Spy X \<in> set evs \<longrightarrow> secureM \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
done

lemma Outpts_imp_knows_Spy_insecureM [rule_format (no_asm)]:
     "Outpts C A X \<in> set evs \<longrightarrow> insecureM \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
done

(*Nothing can be stated on an A_Gets event*)



text{*Elimination rules: derive contradictions from old Says events containing
  items known to be fresh*}
lemmas knows_Spy_partsEs =
     Says_imp_knows_Spy [THEN parts.Inj, THEN revcut_rl]
     parts.Body [THEN revcut_rl]



subsection{*Knowledge of Agents*}

lemma knows_Says: "knows A (Says A B X # evs) = insert X (knows A evs)"
by simp

lemma knows_Notes: "knows A (Notes A X # evs) = insert X (knows A evs)"
by simp

lemma knows_Gets:
      "A \<noteq> Spy \<longrightarrow> knows A (Gets A X # evs) = insert X (knows A evs)"
by simp

lemma knows_Inputs: "knows A (Inputs A C X # evs) = insert X (knows A evs)"
by simp

lemma knows_C_Gets: "knows A (C_Gets C X # evs) = knows A evs"
by simp

lemma knows_Outpts_secureM: 
      "secureM \<longrightarrow> knows A (Outpts C A X # evs) = insert X (knows A evs)"
by simp

lemma knows_Outpts_insecureM: 
      "insecureM \<longrightarrow> knows Spy (Outpts C A X # evs) = insert X (knows Spy evs)"
by simp
(*somewhat equivalent to knows_Spy_Outpts_insecureM*)




lemma knows_subset_knows_Says: "knows A evs \<subseteq> knows A (Says A' B X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Notes: "knows A evs \<subseteq> knows A (Notes A' X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Gets: "knows A evs \<subseteq> knows A (Gets A' X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Inputs: "knows A evs \<subseteq> knows A (Inputs A' C X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_C_Gets: "knows A evs \<subseteq> knows A (C_Gets C X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Outpts: "knows A evs \<subseteq> knows A (Outpts C A' X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_A_Gets: "knows A evs \<subseteq> knows A (A_Gets A' X # evs)"
by (simp add: subset_insertI)


text{*Agents know what they say*}
lemma Says_imp_knows [rule_format]: "Says A B X \<in> set evs \<longrightarrow> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
apply blast
done

text{*Agents know what they note*}
lemma Notes_imp_knows [rule_format]: "Notes A X \<in> set evs \<longrightarrow> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
apply blast
done

text{*Agents know what they receive*}
lemma Gets_imp_knows_agents [rule_format]:
     "A \<noteq> Spy \<longrightarrow> Gets A X \<in> set evs \<longrightarrow> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
done

(*Agents know what they input to their smart card*)
lemma Inputs_imp_knows_agents [rule_format (no_asm)]: 
     "Inputs A (Card A) X \<in> set evs \<longrightarrow> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
apply blast
done

(*Nothing to prove about C_Gets*)

(*Agents know what they obtain as output of their smart card,
  if the means is secure...*)
lemma Outpts_imp_knows_agents_secureM [rule_format (no_asm)]: 
     "secureM \<longrightarrow> Outpts (Card A) A X \<in> set evs \<longrightarrow> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
done

(*otherwise only the spy knows the outputs*)
lemma Outpts_imp_knows_agents_insecureM [rule_format (no_asm)]: 
      "insecureM \<longrightarrow> Outpts (Card A) A X \<in> set evs \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
done

(*end lemmas about agents' knowledge*)



lemma parts_knows_Spy_subset_used: "parts (knows Spy evs) \<subseteq> used evs"
apply (induct_tac "evs", force)  
apply (simp add: parts_insert_knows_A knows_Cons add: event.split, blast) 
done

lemmas usedI = parts_knows_Spy_subset_used [THEN subsetD, intro]

lemma initState_into_used: "X \<in> parts (initState B) \<Longrightarrow> X \<in> used evs"
apply (induct_tac "evs")
apply (simp_all add: parts_insert_knows_A split add: event.split, blast)
done

lemma used_Says [simp]: "used (Says A B X # evs) = parts{X} \<union> used evs"
by simp

lemma used_Notes [simp]: "used (Notes A X # evs) = parts{X} \<union> used evs"
by simp

lemma used_Gets [simp]: "used (Gets A X # evs) = used evs"
by simp

lemma used_Inputs [simp]: "used (Inputs A C X # evs) = parts{X} \<union> used evs"
by simp

lemma used_C_Gets [simp]: "used (C_Gets C X # evs) = used evs"
by simp

lemma used_Outpts [simp]: "used (Outpts C A X # evs) = parts{X} \<union> used evs"
by simp

lemma used_A_Gets [simp]: "used (A_Gets A X # evs) = used evs"
by simp

lemma used_nil_subset: "used [] \<subseteq> used evs"
apply simp
apply (blast intro: initState_into_used)
done



(*Novel lemmas*)
lemma Says_parts_used [rule_format (no_asm)]: 
     "Says A B X \<in> set evs \<longrightarrow> (parts  {X}) \<subseteq> used evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
apply blast
done

lemma Notes_parts_used [rule_format (no_asm)]: 
     "Notes A X \<in> set evs \<longrightarrow> (parts  {X}) \<subseteq> used evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
apply blast
done

lemma Outpts_parts_used [rule_format (no_asm)]: 
     "Outpts C A X \<in> set evs \<longrightarrow> (parts  {X}) \<subseteq> used evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
apply blast
done

lemma Inputs_parts_used [rule_format (no_asm)]: 
     "Inputs A C X \<in> set evs \<longrightarrow> (parts  {X}) \<subseteq> used evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split add: event.split)
apply blast
done




text{*NOTE REMOVAL--laws above are cleaner, as they don't involve "case"*}
declare knows_Cons [simp del]
        used_Nil [simp del] used_Cons [simp del]


lemma knows_subset_knows_Cons: "knows A evs \<subseteq> knows A (e # evs)"
by (induct e, auto simp: knows_Cons)

lemma initState_subset_knows: "initState A \<subseteq> knows A evs"
apply (induct_tac evs, simp) 
apply (blast intro: knows_subset_knows_Cons [THEN subsetD])
done


text{*For proving @{text new_keys_not_used}*}
lemma keysFor_parts_insert:
     "\<lbrakk> K \<in> keysFor (parts (insert X G));  X \<in> synth (analz H) \<rbrakk>   
      \<Longrightarrow> K \<in> keysFor (parts (G \<union> H)) \<or> Key (invKey K) \<in> parts H"; 
by (force 
    dest!: parts_insert_subset_Un [THEN keysFor_mono, THEN [2] rev_subsetD]
           analz_subset_parts [THEN keysFor_mono, THEN [2] rev_subsetD]
    intro: analz_subset_parts [THEN subsetD] parts_mono [THEN [2] rev_subsetD])

end
