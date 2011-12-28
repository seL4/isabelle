(*  Title:      HOL/Auth/Guard/Extensions.thy
    Author:     Frederic Blanqui, University of Cambridge Computer Laboratory
    Copyright   2001  University of Cambridge
*)

header {*Extensions to Standard Theories*}

theory Extensions
imports "../Event"
begin

subsection{*Extensions to Theory @{text Set}*}

lemma eq: "[| !!x. x:A ==> x:B; !!x. x:B ==> x:A |] ==> A=B"
by auto

lemma insert_Un: "P ({x} Un A) ==> P (insert x A)"
by simp

lemma in_sub: "x:A ==> {x}<=A"
by auto


subsection{*Extensions to Theory @{text List}*}

subsubsection{*"remove l x" erase the first element of "l" equal to "x"*}

primrec remove :: "'a list => 'a => 'a list" where
"remove [] y = []" |
"remove (x#xs) y = (if x=y then xs else x # remove xs y)"

lemma set_remove: "set (remove l x) <= set l"
by (induct l, auto)

subsection{*Extensions to Theory @{text Message}*}

subsubsection{*declarations for tactics*}

declare analz_subset_parts [THEN subsetD, dest]
declare image_eq_UN [simp]
declare parts_insert2 [simp]
declare analz_cut [dest]
declare split_if_asm [split]
declare analz_insertI [intro]
declare Un_Diff [simp]

subsubsection{*extract the agent number of an Agent message*}

primrec agt_nb :: "msg => agent" where
"agt_nb (Agent A) = A"

subsubsection{*messages that are pairs*}

definition is_MPair :: "msg => bool" where
"is_MPair X == EX Y Z. X = {|Y,Z|}"

declare is_MPair_def [simp]

lemma MPair_is_MPair [iff]: "is_MPair {|X,Y|}"
by simp

lemma Agent_isnt_MPair [iff]: "~ is_MPair (Agent A)"
by simp

lemma Number_isnt_MPair [iff]: "~ is_MPair (Number n)"
by simp

lemma Key_isnt_MPair [iff]: "~ is_MPair (Key K)"
by simp

lemma Nonce_isnt_MPair [iff]: "~ is_MPair (Nonce n)"
by simp

lemma Hash_isnt_MPair [iff]: "~ is_MPair (Hash X)"
by simp

lemma Crypt_isnt_MPair [iff]: "~ is_MPair (Crypt K X)"
by simp

abbreviation
  not_MPair :: "msg => bool" where
  "not_MPair X == ~ is_MPair X"

lemma is_MPairE: "[| is_MPair X ==> P; not_MPair X ==> P |] ==> P"
by auto

declare is_MPair_def [simp del]

definition has_no_pair :: "msg set => bool" where
"has_no_pair H == ALL X Y. {|X,Y|} ~:H"

declare has_no_pair_def [simp]

subsubsection{*well-foundedness of messages*}

lemma wf_Crypt1 [iff]: "Crypt K X ~= X"
by (induct X, auto)

lemma wf_Crypt2 [iff]: "X ~= Crypt K X"
by (induct X, auto)

lemma parts_size: "X:parts {Y} ==> X=Y | size X < size Y"
by (erule parts.induct, auto)

lemma wf_Crypt_parts [iff]: "Crypt K X ~:parts {X}"
by (auto dest: parts_size)

subsubsection{*lemmas on keysFor*}

definition usekeys :: "msg set => key set" where
"usekeys G == {K. EX Y. Crypt K Y:G}"

lemma finite_keysFor [intro]: "finite G ==> finite (keysFor G)"
apply (simp add: keysFor_def)
apply (rule finite_UN_I, auto)
apply (erule finite_induct, auto)
apply (case_tac "EX K X. x = Crypt K X", clarsimp)
apply (subgoal_tac "{Ka. EX Xa. (Ka=K & Xa=X) | Crypt Ka Xa:F}
= insert K (usekeys F)", auto simp: usekeys_def)
by (subgoal_tac "{K. EX X. Crypt K X = x | Crypt K X:F} = usekeys F",
auto simp: usekeys_def)

subsubsection{*lemmas on parts*}

lemma parts_sub: "[| X:parts G; G<=H |] ==> X:parts H"
by (auto dest: parts_mono)

lemma parts_Diff [dest]: "X:parts (G - H) ==> X:parts G"
by (erule parts_sub, auto)

lemma parts_Diff_notin: "[| Y ~:H; Nonce n ~:parts (H - {Y}) |]
==> Nonce n ~:parts H"
by simp

lemmas parts_insert_substI = parts_insert [THEN ssubst]
lemmas parts_insert_substD = parts_insert [THEN sym, THEN ssubst]

lemma finite_parts_msg [iff]: "finite (parts {X})"
by (induct X, auto)

lemma finite_parts [intro]: "finite H ==> finite (parts H)"
apply (erule finite_induct, simp)
by (rule parts_insert_substI, simp)

lemma parts_parts: "[| X:parts {Y}; Y:parts G |] ==> X:parts G"
by (frule parts_cut, auto) 


lemma parts_parts_parts: "[| X:parts {Y}; Y:parts {Z}; Z:parts G |] ==> X:parts G"
by (auto dest: parts_parts)

lemma parts_parts_Crypt: "[| Crypt K X:parts G; Nonce n:parts {X} |]
==> Nonce n:parts G"
by (blast intro: parts.Body dest: parts_parts)

subsubsection{*lemmas on synth*}

lemma synth_sub: "[| X:synth G; G<=H |] ==> X:synth H"
by (auto dest: synth_mono)

lemma Crypt_synth [rule_format]: "[| X:synth G; Key K ~:G |] ==>
Crypt K Y:parts {X} --> Crypt K Y:parts G"
by (erule synth.induct, auto dest: parts_sub)

subsubsection{*lemmas on analz*}

lemma analz_UnI1 [intro]: "X:analz G ==> X:analz (G Un H)"
  by (subgoal_tac "G <= G Un H") (blast dest: analz_mono)+

lemma analz_sub: "[| X:analz G; G <= H |] ==> X:analz H"
by (auto dest: analz_mono)

lemma analz_Diff [dest]: "X:analz (G - H) ==> X:analz G"
by (erule analz.induct, auto)

lemmas in_analz_subset_cong = analz_subset_cong [THEN subsetD]

lemma analz_eq: "A=A' ==> analz A = analz A'"
by auto

lemmas insert_commute_substI = insert_commute [THEN ssubst]

lemma analz_insertD:
     "[| Crypt K Y:H; Key (invKey K):H |] ==> analz (insert Y H) = analz H"
by (blast intro: analz.Decrypt analz_insert_eq)  

lemma must_decrypt [rule_format,dest]: "[| X:analz H; has_no_pair H |] ==>
X ~:H --> (EX K Y. Crypt K Y:H & Key (invKey K):H)"
by (erule analz.induct, auto)

lemma analz_needs_only_finite: "X:analz H ==> EX G. G <= H & finite G"
by (erule analz.induct, auto)

lemma notin_analz_insert: "X ~:analz (insert Y G) ==> X ~:analz G"
by auto

subsubsection{*lemmas on parts, synth and analz*}

lemma parts_invKey [rule_format,dest]:"X:parts {Y} ==>
X:analz (insert (Crypt K Y) H) --> X ~:analz H --> Key (invKey K):analz H"
by (erule parts.induct, auto dest: parts.Fst parts.Snd parts.Body)

lemma in_analz: "Y:analz H ==> EX X. X:H & Y:parts {X}"
by (erule analz.induct, auto intro: parts.Fst parts.Snd parts.Body)

lemmas in_analz_subset_parts = analz_subset_parts [THEN subsetD]

lemma Crypt_synth_insert: "[| Crypt K X:parts (insert Y H);
Y:synth (analz H); Key K ~:analz H |] ==> Crypt K X:parts H"
apply (drule parts_insert_substD, clarify)
apply (frule in_sub)
apply (frule parts_mono)
apply auto
done

subsubsection{*greatest nonce used in a message*}

fun greatest_msg :: "msg => nat"
where
  "greatest_msg (Nonce n) = n"
| "greatest_msg {|X,Y|} = max (greatest_msg X) (greatest_msg Y)"
| "greatest_msg (Crypt K X) = greatest_msg X"
| "greatest_msg other = 0"

lemma greatest_msg_is_greatest: "Nonce n:parts {X} ==> n <= greatest_msg X"
by (induct X, auto)

subsubsection{*sets of keys*}

definition keyset :: "msg set => bool" where
"keyset G == ALL X. X:G --> (EX K. X = Key K)"

lemma keyset_in [dest]: "[| keyset G; X:G |] ==> EX K. X = Key K"
by (auto simp: keyset_def)

lemma MPair_notin_keyset [simp]: "keyset G ==> {|X,Y|} ~:G"
by auto

lemma Crypt_notin_keyset [simp]: "keyset G ==> Crypt K X ~:G"
by auto

lemma Nonce_notin_keyset [simp]: "keyset G ==> Nonce n ~:G"
by auto

lemma parts_keyset [simp]: "keyset G ==> parts G = G"
by (auto, erule parts.induct, auto)

subsubsection{*keys a priori necessary for decrypting the messages of G*}

definition keysfor :: "msg set => msg set" where
"keysfor G == Key ` keysFor (parts G)"

lemma keyset_keysfor [iff]: "keyset (keysfor G)"
by (simp add: keyset_def keysfor_def, blast)

lemma keyset_Diff_keysfor [simp]: "keyset H ==> keyset (H - keysfor G)"
by (auto simp: keyset_def)

lemma keysfor_Crypt: "Crypt K X:parts G ==> Key (invKey K):keysfor G"
by (auto simp: keysfor_def Crypt_imp_invKey_keysFor)

lemma no_key_no_Crypt: "Key K ~:keysfor G ==> Crypt (invKey K) X ~:parts G"
by (auto dest: keysfor_Crypt)

lemma finite_keysfor [intro]: "finite G ==> finite (keysfor G)"
by (auto simp: keysfor_def intro: finite_UN_I)

subsubsection{*only the keys necessary for G are useful in analz*}

lemma analz_keyset: "keyset H ==>
analz (G Un H) = H - keysfor G Un (analz (G Un (H Int keysfor G)))"
apply (rule eq)
apply (erule analz.induct, blast)
apply (simp, blast)
apply (simp, blast)
apply (case_tac "Key (invKey K):H - keysfor G", clarsimp)
apply (drule_tac X=X in no_key_no_Crypt)
by (auto intro: analz_sub)

lemmas analz_keyset_substD = analz_keyset [THEN sym, THEN ssubst]


subsection{*Extensions to Theory @{text Event}*}


subsubsection{*general protocol properties*}

definition is_Says :: "event => bool" where
"is_Says ev == (EX A B X. ev = Says A B X)"

lemma is_Says_Says [iff]: "is_Says (Says A B X)"
by (simp add: is_Says_def)

(* one could also require that Gets occurs after Says
but this is sufficient for our purpose *)
definition Gets_correct :: "event list set => bool" where
"Gets_correct p == ALL evs B X. evs:p --> Gets B X:set evs
--> (EX A. Says A B X:set evs)"

lemma Gets_correct_Says: "[| Gets_correct p; Gets B X # evs:p |]
==> EX A. Says A B X:set evs"
apply (simp add: Gets_correct_def)
by (drule_tac x="Gets B X # evs" in spec, auto)

definition one_step :: "event list set => bool" where
"one_step p == ALL evs ev. ev#evs:p --> evs:p"

lemma one_step_Cons [dest]: "[| one_step p; ev#evs:p |] ==> evs:p"
by (unfold one_step_def, blast)

lemma one_step_app: "[| evs@evs':p; one_step p; []:p |] ==> evs':p"
by (induct evs, auto)

lemma trunc: "[| evs @ evs':p; one_step p |] ==> evs':p"
by (induct evs, auto)

definition has_only_Says :: "event list set => bool" where
"has_only_Says p == ALL evs ev. evs:p --> ev:set evs
--> (EX A B X. ev = Says A B X)"

lemma has_only_SaysD: "[| ev:set evs; evs:p; has_only_Says p |]
==> EX A B X. ev = Says A B X"
by (unfold has_only_Says_def, blast)

lemma in_has_only_Says [dest]: "[| has_only_Says p; evs:p; ev:set evs |]
==> EX A B X. ev = Says A B X"
by (auto simp: has_only_Says_def)

lemma has_only_Says_imp_Gets_correct [simp]: "has_only_Says p
==> Gets_correct p"
by (auto simp: has_only_Says_def Gets_correct_def)

subsubsection{*lemma on knows*}

lemma Says_imp_spies2: "Says A B {|X,Y|}:set evs ==> Y:parts (spies evs)"
by (drule Says_imp_spies, drule parts.Inj, drule parts.Snd, simp)

lemma Says_not_parts: "[| Says A B X:set evs; Y ~:parts (spies evs) |]
==> Y ~:parts {X}"
by (auto dest: Says_imp_spies parts_parts)

subsubsection{*knows without initState*}

primrec knows' :: "agent => event list => msg set" where
  knows'_Nil: "knows' A [] = {}" |
  knows'_Cons0:
 "knows' A (ev # evs) = (
   if A = Spy then (
     case ev of
       Says A' B X => insert X (knows' A evs)
     | Gets A' X => knows' A evs
     | Notes A' X => if A':bad then insert X (knows' A evs) else knows' A evs
   ) else (
     case ev of
       Says A' B X => if A=A' then insert X (knows' A evs) else knows' A evs
     | Gets A' X => if A=A' then insert X (knows' A evs) else knows' A evs
     | Notes A' X => if A=A' then insert X (knows' A evs) else knows' A evs
   ))"

abbreviation
  spies' :: "event list => msg set" where
  "spies' == knows' Spy"

subsubsection{*decomposition of knows into knows' and initState*}

lemma knows_decomp: "knows A evs = knows' A evs Un (initState A)"
by (induct evs, auto split: event.split simp: knows.simps)

lemmas knows_decomp_substI = knows_decomp [THEN ssubst]
lemmas knows_decomp_substD = knows_decomp [THEN sym, THEN ssubst]

lemma knows'_sub_knows: "knows' A evs <= knows A evs"
by (auto simp: knows_decomp)

lemma knows'_Cons: "knows' A (ev#evs) = knows' A [ev] Un knows' A evs"
by (induct ev, auto)

lemmas knows'_Cons_substI = knows'_Cons [THEN ssubst]
lemmas knows'_Cons_substD = knows'_Cons [THEN sym, THEN ssubst]

lemma knows_Cons: "knows A (ev#evs) = initState A Un knows' A [ev]
Un knows A evs"
apply (simp only: knows_decomp)
apply (rule_tac s="(knows' A [ev] Un knows' A evs) Un initState A" in trans)
apply (simp only: knows'_Cons [of A ev evs] Un_ac)
apply blast
done


lemmas knows_Cons_substI = knows_Cons [THEN ssubst]
lemmas knows_Cons_substD = knows_Cons [THEN sym, THEN ssubst]

lemma knows'_sub_spies': "[| evs:p; has_only_Says p; one_step p |]
==> knows' A evs <= spies' evs"
by (induct evs, auto split: event.splits)

subsubsection{*knows' is finite*}

lemma finite_knows' [iff]: "finite (knows' A evs)"
by (induct evs, auto split: event.split simp: knows.simps)

subsubsection{*monotonicity of knows*}

lemma knows_sub_Cons: "knows A evs <= knows A (ev#evs)"
by(cases A, induct evs, auto simp: knows.simps split:event.split)

lemma knows_ConsI: "X:knows A evs ==> X:knows A (ev#evs)"
by (auto dest: knows_sub_Cons [THEN subsetD])

lemma knows_sub_app: "knows A evs <= knows A (evs @ evs')"
apply (induct evs, auto)
apply (simp add: knows_decomp)
by (case_tac a, auto simp: knows.simps)

subsubsection{*maximum knowledge an agent can have
includes messages sent to the agent*}

primrec knows_max' :: "agent => event list => msg set" where
knows_max'_def_Nil: "knows_max' A [] = {}" |
knows_max'_def_Cons: "knows_max' A (ev # evs) = (
  if A=Spy then (
    case ev of
      Says A' B X => insert X (knows_max' A evs)
    | Gets A' X => knows_max' A evs
    | Notes A' X =>
      if A':bad then insert X (knows_max' A evs) else knows_max' A evs
  ) else (
    case ev of
      Says A' B X =>
      if A=A' | A=B then insert X (knows_max' A evs) else knows_max' A evs
    | Gets A' X =>
      if A=A' then insert X (knows_max' A evs) else knows_max' A evs
    | Notes A' X =>
      if A=A' then insert X (knows_max' A evs) else knows_max' A evs
  ))"

definition knows_max :: "agent => event list => msg set" where
"knows_max A evs == knows_max' A evs Un initState A"

abbreviation
  spies_max :: "event list => msg set" where
  "spies_max evs == knows_max Spy evs"

subsubsection{*basic facts about @{term knows_max}*}

lemma spies_max_spies [iff]: "spies_max evs = spies evs"
by (induct evs, auto simp: knows_max_def split: event.splits)

lemma knows_max'_Cons: "knows_max' A (ev#evs)
= knows_max' A [ev] Un knows_max' A evs"
by (auto split: event.splits)

lemmas knows_max'_Cons_substI = knows_max'_Cons [THEN ssubst]
lemmas knows_max'_Cons_substD = knows_max'_Cons [THEN sym, THEN ssubst]

lemma knows_max_Cons: "knows_max A (ev#evs)
= knows_max' A [ev] Un knows_max A evs"
apply (simp add: knows_max_def del: knows_max'_def_Cons)
apply (rule_tac evs=evs in knows_max'_Cons_substI)
by blast

lemmas knows_max_Cons_substI = knows_max_Cons [THEN ssubst]
lemmas knows_max_Cons_substD = knows_max_Cons [THEN sym, THEN ssubst]

lemma finite_knows_max' [iff]: "finite (knows_max' A evs)"
by (induct evs, auto split: event.split)

lemma knows_max'_sub_spies': "[| evs:p; has_only_Says p; one_step p |]
==> knows_max' A evs <= spies' evs"
by (induct evs, auto split: event.splits)

lemma knows_max'_in_spies' [dest]: "[| evs:p; X:knows_max' A evs;
has_only_Says p; one_step p |] ==> X:spies' evs"
by (rule knows_max'_sub_spies' [THEN subsetD], auto)

lemma knows_max'_app: "knows_max' A (evs @ evs')
= knows_max' A evs Un knows_max' A evs'"
by (induct evs, auto split: event.splits)

lemma Says_to_knows_max': "Says A B X:set evs ==> X:knows_max' B evs"
by (simp add: in_set_conv_decomp, clarify, simp add: knows_max'_app)

lemma Says_from_knows_max': "Says A B X:set evs ==> X:knows_max' A evs"
by (simp add: in_set_conv_decomp, clarify, simp add: knows_max'_app)

subsubsection{*used without initState*}

primrec used' :: "event list => msg set" where
"used' [] = {}" |
"used' (ev # evs) = (
  case ev of
    Says A B X => parts {X} Un used' evs
    | Gets A X => used' evs
    | Notes A X => parts {X} Un used' evs
  )"

definition init :: "msg set" where
"init == used []"

lemma used_decomp: "used evs = init Un used' evs"
by (induct evs, auto simp: init_def split: event.split)

lemma used'_sub_app: "used' evs <= used' (evs@evs')"
by (induct evs, auto split: event.split)

lemma used'_parts [rule_format]: "X:used' evs ==> Y:parts {X} --> Y:used' evs"
apply (induct evs, simp) 
apply (case_tac a, simp_all) 
apply (blast dest: parts_trans)+; 
done

subsubsection{*monotonicity of used*}

lemma used_sub_Cons: "used evs <= used (ev#evs)"
by (induct evs, (induct ev, auto)+)

lemma used_ConsI: "X:used evs ==> X:used (ev#evs)"
by (auto dest: used_sub_Cons [THEN subsetD])

lemma notin_used_ConsD: "X ~:used (ev#evs) ==> X ~:used evs"
by (auto dest: used_sub_Cons [THEN subsetD])

lemma used_appD [dest]: "X:used (evs @ evs') ==> X:used evs | X:used evs'"
by (induct evs, auto, case_tac a, auto)

lemma used_ConsD: "X:used (ev#evs) ==> X:used [ev] | X:used evs"
by (case_tac ev, auto)

lemma used_sub_app: "used evs <= used (evs@evs')"
by (auto simp: used_decomp dest: used'_sub_app [THEN subsetD])

lemma used_appIL: "X:used evs ==> X:used (evs' @ evs)"
by (induct evs', auto intro: used_ConsI)

lemma used_appIR: "X:used evs ==> X:used (evs @ evs')"
by (erule used_sub_app [THEN subsetD])

lemma used_parts: "[| X:parts {Y}; Y:used evs |] ==> X:used evs"
apply (auto simp: used_decomp dest: used'_parts)
by (auto simp: init_def used_Nil dest: parts_trans)

lemma parts_Says_used: "[| Says A B X:set evs; Y:parts {X} |] ==> Y:used evs"
by (induct evs, simp_all, safe, auto intro: used_ConsI)

lemma parts_used_app: "X:parts {Y} ==> X:used (evs @ Says A B Y # evs')"
apply (drule_tac evs="[Says A B Y]" in used_parts, simp, blast)
apply (drule_tac evs'=evs' in used_appIR)
apply (drule_tac evs'=evs in used_appIL)
by simp

subsubsection{*lemmas on used and knows*}

lemma initState_used: "X:parts (initState A) ==> X:used evs"
by (induct evs, auto simp: used.simps split: event.split)

lemma Says_imp_used: "Says A B X:set evs ==> parts {X} <= used evs"
by (induct evs, auto intro: used_ConsI)

lemma not_used_not_spied: "X ~:used evs ==> X ~:parts (spies evs)"
by (induct evs, auto simp: used_Nil)

lemma not_used_not_parts: "[| Y ~:used evs; Says A B X:set evs |]
==> Y ~:parts {X}"
by (induct evs, auto intro: used_ConsI)

lemma not_used_parts_false: "[| X ~:used evs; Y:parts (spies evs) |]
==> X ~:parts {Y}"
by (auto dest: parts_parts)

lemma known_used [rule_format]: "[| evs:p; Gets_correct p; one_step p |]
==> X:parts (knows A evs) --> X:used evs"
apply (case_tac "A=Spy", blast)
apply (induct evs)
apply (simp add: used.simps, blast)
apply (frule_tac ev=a and evs=evs in one_step_Cons, simp, clarify)
apply (drule_tac P="%G. X:parts G" in knows_Cons_substD, safe)
apply (erule initState_used)
apply (case_tac a, auto)
apply (drule_tac B=A and X=msg and evs=evs in Gets_correct_Says)
by (auto dest: Says_imp_used intro: used_ConsI)

lemma known_max_used [rule_format]: "[| evs:p; Gets_correct p; one_step p |]
==> X:parts (knows_max A evs) --> X:used evs"
apply (case_tac "A=Spy")
apply force
apply (induct evs)
apply (simp add: knows_max_def used.simps, blast)
apply (frule_tac ev=a and evs=evs in one_step_Cons, simp, clarify)
apply (drule_tac P="%G. X:parts G" in knows_max_Cons_substD, safe)
apply (case_tac a, auto)
apply (drule_tac B=A and X=msg and evs=evs in Gets_correct_Says)
by (auto simp: knows_max'_Cons dest: Says_imp_used intro: used_ConsI)

lemma not_used_not_known: "[| evs:p; X ~:used evs;
Gets_correct p; one_step p |] ==> X ~:parts (knows A evs)"
by (case_tac "A=Spy", auto dest: not_used_not_spied known_used)

lemma not_used_not_known_max: "[| evs:p; X ~:used evs;
Gets_correct p; one_step p |] ==> X ~:parts (knows_max A evs)"
by (case_tac "A=Spy", auto dest: not_used_not_spied known_max_used)

subsubsection{*a nonce or key in a message cannot equal a fresh nonce or key*}

lemma Nonce_neq [dest]: "[| Nonce n' ~:used evs;
Says A B X:set evs; Nonce n:parts {X} |] ==> n ~= n'"
by (drule not_used_not_spied, auto dest: Says_imp_knows_Spy parts_sub)

lemma Key_neq [dest]: "[| Key n' ~:used evs;
Says A B X:set evs; Key n:parts {X} |] ==> n ~= n'"
by (drule not_used_not_spied, auto dest: Says_imp_knows_Spy parts_sub)

subsubsection{*message of an event*}

primrec msg :: "event => msg"
where
  "msg (Says A B X) = X"
| "msg (Gets A X) = X"
| "msg (Notes A X) = X"

lemma used_sub_parts_used: "X:used (ev # evs) ==> X:parts {msg ev} Un used evs"
by (induct ev, auto)

end
