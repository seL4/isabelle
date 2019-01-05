(*  Title:      HOL/Auth/Guard/Extensions.thy
    Author:     Frederic Blanqui, University of Cambridge Computer Laboratory
    Copyright   2001  University of Cambridge
*)

section \<open>Extensions to Standard Theories\<close>

theory Extensions
imports "../Event"
begin

subsection\<open>Extensions to Theory \<open>Set\<close>\<close>

lemma eq: "[| \<And>x. x\<in>A \<Longrightarrow> x\<in>B; \<And>x. x\<in>B \<Longrightarrow> x\<in>A |] ==> A=B"
by auto

lemma insert_Un: "P ({x} \<union> A) \<Longrightarrow> P (insert x A)"
by simp

lemma in_sub: "x\<in>A \<Longrightarrow> {x}\<subseteq>A"
by auto


subsection\<open>Extensions to Theory \<open>List\<close>\<close>

subsubsection\<open>"remove l x" erase the first element of "l" equal to "x"\<close>

primrec remove :: "'a list => 'a => 'a list" where
"remove [] y = []" |
"remove (x#xs) y = (if x=y then xs else x # remove xs y)"

lemma set_remove: "set (remove l x) <= set l"
by (induct l, auto)

subsection\<open>Extensions to Theory \<open>Message\<close>\<close>

subsubsection\<open>declarations for tactics\<close>

declare analz_subset_parts [THEN subsetD, dest]
declare parts_insert2 [simp]
declare analz_cut [dest]
declare if_split_asm [split]
declare analz_insertI [intro]
declare Un_Diff [simp]

subsubsection\<open>extract the agent number of an Agent message\<close>

primrec agt_nb :: "msg => agent" where
"agt_nb (Agent A) = A"

subsubsection\<open>messages that are pairs\<close>

definition is_MPair :: "msg => bool" where
"is_MPair X == \<exists>Y Z. X = \<lbrace>Y,Z\<rbrace>"

declare is_MPair_def [simp]

lemma MPair_is_MPair [iff]: "is_MPair \<lbrace>X,Y\<rbrace>"
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
"has_no_pair H == \<forall>X Y. \<lbrace>X,Y\<rbrace> \<notin> H"

declare has_no_pair_def [simp]

subsubsection\<open>well-foundedness of messages\<close>

lemma wf_Crypt1 [iff]: "Crypt K X ~= X"
by (induct X, auto)

lemma wf_Crypt2 [iff]: "X ~= Crypt K X"
by (induct X, auto)

lemma parts_size: "X \<in> parts {Y} \<Longrightarrow> X=Y \<or> size X < size Y"
by (erule parts.induct, auto)

lemma wf_Crypt_parts [iff]: "Crypt K X \<notin> parts {X}"
by (auto dest: parts_size)

subsubsection\<open>lemmas on keysFor\<close>

definition usekeys :: "msg set => key set" where
"usekeys G \<equiv> {K. \<exists>Y. Crypt K Y \<in> G}"

lemma finite_keysFor [intro]: "finite G ==> finite (keysFor G)"
apply (simp add: keysFor_def)
apply (rule finite_imageI)
apply (induct G rule: finite_induct)
apply auto
apply (case_tac "\<exists>K X. x = Crypt K X", clarsimp)
apply (subgoal_tac "{Ka. \<exists>Xa. (Ka=K \<and> Xa=X) \<or> Crypt Ka Xa \<in> F} 
= insert K (usekeys F)", auto simp: usekeys_def)
by (subgoal_tac "{K. \<exists>X. Crypt K X = x \<or> Crypt K X \<in> F} = usekeys F",
auto simp: usekeys_def)

subsubsection\<open>lemmas on parts\<close>

lemma parts_sub: "[| X \<in> parts G; G \<subseteq> H |] ==> X \<in> parts H"
by (auto dest: parts_mono)

lemma parts_Diff [dest]: "X \<in> parts (G - H) \<Longrightarrow> X \<in> parts G"
by (erule parts_sub, auto)

lemma parts_Diff_notin: "[| Y \<notin> H; Nonce n \<notin> parts (H - {Y}) |]
==> Nonce n \<notin> parts H"
by simp

lemmas parts_insert_substI = parts_insert [THEN ssubst]
lemmas parts_insert_substD = parts_insert [THEN sym, THEN ssubst]

lemma finite_parts_msg [iff]: "finite (parts {X})"
by (induct X, auto)

lemma finite_parts [intro]: "finite H \<Longrightarrow> finite (parts H)"
apply (erule finite_induct, simp)
by (rule parts_insert_substI, simp)

lemma parts_parts: "[| X \<in> parts {Y}; Y \<in> parts G |] ==> X \<in> parts G"
by (frule parts_cut, auto) 


lemma parts_parts_parts: "[| X \<in> parts {Y}; Y \<in> parts {Z}; Z \<in> parts G |] ==> X \<in> parts G"
by (auto dest: parts_parts)

lemma parts_parts_Crypt: "[| Crypt K X \<in> parts G; Nonce n \<in> parts {X} |]
==> Nonce n \<in> parts G"
by (blast intro: parts.Body dest: parts_parts)

subsubsection\<open>lemmas on synth\<close>

lemma synth_sub: "[| X \<in> synth G; G \<subseteq> H |] ==> X \<in> synth H"
by (auto dest: synth_mono)

lemma Crypt_synth [rule_format]: "[| X \<in> synth G; Key K \<notin> G |] ==>
Crypt K Y \<in> parts {X} \<longrightarrow> Crypt K Y \<in> parts G"
by (erule synth.induct, auto dest: parts_sub)

subsubsection\<open>lemmas on analz\<close>

lemma analz_UnI1 [intro]: "X \<in> analz G ==> X \<in> analz (G \<union> H)"
  by (subgoal_tac "G <= G Un H") (blast dest: analz_mono)+

lemma analz_sub: "[| X \<in> analz G; G \<subseteq> H |] ==> X \<in> analz H"
by (auto dest: analz_mono)

lemma analz_Diff [dest]: "X \<in> analz (G - H) \<Longrightarrow> X \<in> analz G"
by (erule analz.induct, auto)

lemmas in_analz_subset_cong = analz_subset_cong [THEN subsetD]

lemma analz_eq: "A=A' ==> analz A = analz A'"
by auto

lemmas insert_commute_substI = insert_commute [THEN ssubst]

lemma analz_insertD:
     "[| Crypt K Y \<in> H; Key (invKey K) \<in> H |] ==> analz (insert Y H) = analz H"
by (blast intro: analz.Decrypt analz_insert_eq)  

lemma must_decrypt [rule_format,dest]: "[| X \<in> analz H; has_no_pair H |] ==>
X \<notin> H \<longrightarrow> (\<exists>K Y. Crypt K Y \<in> H \<and> Key (invKey K) \<in> H)"
by (erule analz.induct, auto)

lemma analz_needs_only_finite: "X \<in> analz H \<Longrightarrow> \<exists>G. G \<subseteq> H \<and> finite G"
by (erule analz.induct, auto)

lemma notin_analz_insert: "X \<notin> analz (insert Y G) \<Longrightarrow> X \<notin> analz G"
by auto

subsubsection\<open>lemmas on parts, synth and analz\<close>

lemma parts_invKey [rule_format,dest]:"X \<in> parts {Y} \<Longrightarrow>
X \<in> analz (insert (Crypt K Y) H) \<longrightarrow> X \<notin> analz H \<longrightarrow> Key (invKey K) \<in> analz H"
by (erule parts.induct, auto dest: parts.Fst parts.Snd parts.Body)

lemma in_analz: "Y \<in> analz H \<Longrightarrow> \<exists>X. X \<in> H \<and> Y \<in> parts {X}"
by (erule analz.induct, auto intro: parts.Fst parts.Snd parts.Body)

lemmas in_analz_subset_parts = analz_subset_parts [THEN subsetD]

lemma Crypt_synth_insert: "[| Crypt K X \<in> parts (insert Y H);
Y \<in> synth (analz H); Key K \<notin> analz H |] ==> Crypt K X \<in> parts H"
apply (drule parts_insert_substD, clarify)
apply (frule in_sub)
apply (frule parts_mono)
apply auto
done

subsubsection\<open>greatest nonce used in a message\<close>

fun greatest_msg :: "msg => nat"
where
  "greatest_msg (Nonce n) = n"
| "greatest_msg \<lbrace>X,Y\<rbrace> = max (greatest_msg X) (greatest_msg Y)"
| "greatest_msg (Crypt K X) = greatest_msg X"
| "greatest_msg other = 0"

lemma greatest_msg_is_greatest: "Nonce n \<in> parts {X} \<Longrightarrow> n \<le> greatest_msg X"
by (induct X, auto)

subsubsection\<open>sets of keys\<close>

definition keyset :: "msg set => bool" where
"keyset G \<equiv> \<forall>X. X \<in> G \<longrightarrow> (\<exists>K. X = Key K)"

lemma keyset_in [dest]: "[| keyset G; X \<in> G |] ==> \<exists>K. X = Key K"
by (auto simp: keyset_def)

lemma MPair_notin_keyset [simp]: "keyset G ==> \<lbrace>X,Y\<rbrace> \<notin> G"
by auto

lemma Crypt_notin_keyset [simp]: "keyset G \<Longrightarrow> Crypt K X \<notin> G"
by auto

lemma Nonce_notin_keyset [simp]: "keyset G \<Longrightarrow> Nonce n \<notin> G"
by auto

lemma parts_keyset [simp]: "keyset G ==> parts G = G"
by (auto, erule parts.induct, auto)

subsubsection\<open>keys a priori necessary for decrypting the messages of G\<close>

definition keysfor :: "msg set => msg set" where
"keysfor G == Key ` keysFor (parts G)"

lemma keyset_keysfor [iff]: "keyset (keysfor G)"
by (simp add: keyset_def keysfor_def, blast)

lemma keyset_Diff_keysfor [simp]: "keyset H ==> keyset (H - keysfor G)"
by (auto simp: keyset_def)

lemma keysfor_Crypt: "Crypt K X \<in> parts G \<Longrightarrow> Key (invKey K) \<in> keysfor G"
by (auto simp: keysfor_def Crypt_imp_invKey_keysFor)

lemma no_key_no_Crypt: "Key K \<notin> keysfor G \<Longrightarrow> Crypt (invKey K) X \<notin> parts G"
by (auto dest: keysfor_Crypt)

lemma finite_keysfor [intro]: "finite G ==> finite (keysfor G)"
by (auto simp: keysfor_def intro: finite_UN_I)

subsubsection\<open>only the keys necessary for G are useful in analz\<close>

lemma analz_keyset: "keyset H ==>
analz (G Un H) = H - keysfor G Un (analz (G Un (H Int keysfor G)))"
apply (rule eq)
apply (erule analz.induct, blast)
apply (simp, blast)
apply (simp, blast)
apply (case_tac "Key (invKey K) \<in> H - keysfor G", clarsimp)
apply (drule_tac X=X in no_key_no_Crypt)
by (auto intro: analz_sub)

lemmas analz_keyset_substD = analz_keyset [THEN sym, THEN ssubst]


subsection\<open>Extensions to Theory \<open>Event\<close>\<close>


subsubsection\<open>general protocol properties\<close>

definition is_Says :: "event => bool" where
"is_Says ev == (\<exists>A B X. ev = Says A B X)"

lemma is_Says_Says [iff]: "is_Says (Says A B X)"
by (simp add: is_Says_def)

(* one could also require that Gets occurs after Says
but this is sufficient for our purpose *)
definition Gets_correct :: "event list set => bool" where
"Gets_correct p == \<forall>evs B X. evs \<in> p \<longrightarrow> Gets B X \<in> set evs
\<longrightarrow> (\<exists>A. Says A B X \<in> set evs)"

lemma Gets_correct_Says: "[| Gets_correct p; Gets B X # evs \<in> p |]
==> \<exists>A. Says A B X \<in> set evs"
apply (simp add: Gets_correct_def)
by (drule_tac x="Gets B X # evs" in spec, auto)

definition one_step :: "event list set => bool" where
"one_step p == \<forall>evs ev. ev#evs \<in> p \<longrightarrow> evs \<in> p"

lemma one_step_Cons [dest]: "[| one_step p; ev#evs \<in> p |] ==> evs \<in> p"
by (unfold one_step_def, blast)

lemma one_step_app: "[| evs@evs' \<in> p; one_step p; [] \<in> p |] ==> evs' \<in> p"
by (induct evs, auto)

lemma trunc: "[| evs @ evs' \<in> p; one_step p |] ==> evs' \<in> p"
by (induct evs, auto)

definition has_only_Says :: "event list set => bool" where
"has_only_Says p \<equiv> \<forall>evs ev. evs \<in> p \<longrightarrow> ev \<in> set evs
\<longrightarrow> (\<exists>A B X. ev = Says A B X)"

lemma has_only_SaysD: "[| ev \<in> set evs; evs \<in> p; has_only_Says p |]
==> \<exists>A B X. ev = Says A B X"
by (unfold has_only_Says_def, blast)

lemma in_has_only_Says [dest]: "[| has_only_Says p; evs \<in> p; ev \<in> set evs |]
==> \<exists>A B X. ev = Says A B X"
by (auto simp: has_only_Says_def)

lemma has_only_Says_imp_Gets_correct [simp]: "has_only_Says p
==> Gets_correct p"
by (auto simp: has_only_Says_def Gets_correct_def)

subsubsection\<open>lemma on knows\<close>

lemma Says_imp_spies2: "Says A B \<lbrace>X,Y\<rbrace> \<in> set evs \<Longrightarrow> Y \<in> parts (spies evs)"
by (drule Says_imp_spies, drule parts.Inj, drule parts.Snd, simp)

lemma Says_not_parts: "[| Says A B X \<in> set evs; Y \<notin> parts (spies evs) |]
==> Y \<notin> parts {X}"
by (auto dest: Says_imp_spies parts_parts)

subsubsection\<open>knows without initState\<close>

primrec knows' :: "agent => event list => msg set" where
  knows'_Nil: "knows' A [] = {}" |
  knows'_Cons0:
 "knows' A (ev # evs) = (
   if A = Spy then (
     case ev of
       Says A' B X => insert X (knows' A evs)
     | Gets A' X => knows' A evs
     | Notes A' X => if A' \<in> bad then insert X (knows' A evs) else knows' A evs
   ) else (
     case ev of
       Says A' B X => if A=A' then insert X (knows' A evs) else knows' A evs
     | Gets A' X => if A=A' then insert X (knows' A evs) else knows' A evs
     | Notes A' X => if A=A' then insert X (knows' A evs) else knows' A evs
   ))"

abbreviation
  spies' :: "event list => msg set" where
  "spies' == knows' Spy"

subsubsection\<open>decomposition of knows into knows' and initState\<close>

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

lemma knows'_sub_spies': "[| evs \<in> p; has_only_Says p; one_step p |]
==> knows' A evs \<subseteq> spies' evs"
by (induct evs, auto split: event.splits)

subsubsection\<open>knows' is finite\<close>

lemma finite_knows' [iff]: "finite (knows' A evs)"
by (induct evs, auto split: event.split simp: knows.simps)

subsubsection\<open>monotonicity of knows\<close>

lemma knows_sub_Cons: "knows A evs <= knows A (ev#evs)"
by(cases A, induct evs, auto simp: knows.simps split:event.split)

lemma knows_ConsI: "X \<in> knows A evs \<Longrightarrow> X \<in> knows A (ev#evs)"
by (auto dest: knows_sub_Cons [THEN subsetD])

lemma knows_sub_app: "knows A evs <= knows A (evs @ evs')"
apply (induct evs, auto)
apply (simp add: knows_decomp)
apply (rename_tac a b c)
by (case_tac a, auto simp: knows.simps)

subsubsection\<open>maximum knowledge an agent can have
includes messages sent to the agent\<close>

primrec knows_max' :: "agent => event list => msg set" where
knows_max'_def_Nil: "knows_max' A [] = {}" |
knows_max'_def_Cons: "knows_max' A (ev # evs) = (
  if A=Spy then (
    case ev of
      Says A' B X => insert X (knows_max' A evs)
    | Gets A' X => knows_max' A evs
    | Notes A' X =>
      if A' \<in> bad then insert X (knows_max' A evs) else knows_max' A evs
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

subsubsection\<open>basic facts about \<^term>\<open>knows_max\<close>\<close>

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

lemma knows_max'_sub_spies': "[| evs \<in> p; has_only_Says p; one_step p |]
==> knows_max' A evs \<subseteq> spies' evs"
by (induct evs, auto split: event.splits)

lemma knows_max'_in_spies' [dest]: "[| evs \<in> p; X \<in> knows_max' A evs;
has_only_Says p; one_step p |] ==> X \<in> spies' evs"
by (rule knows_max'_sub_spies' [THEN subsetD], auto)

lemma knows_max'_app: "knows_max' A (evs @ evs')
= knows_max' A evs Un knows_max' A evs'"
by (induct evs, auto split: event.splits)

lemma Says_to_knows_max': "Says A B X \<in> set evs \<Longrightarrow> X \<in> knows_max' B evs"
by (simp add: in_set_conv_decomp, clarify, simp add: knows_max'_app)

lemma Says_from_knows_max': "Says A B X \<in> set evs \<Longrightarrow> X \<in> knows_max' A evs"
by (simp add: in_set_conv_decomp, clarify, simp add: knows_max'_app)

subsubsection\<open>used without initState\<close>

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

lemma used'_sub_app: "used' evs \<subseteq> used' (evs@evs')"
by (induct evs, auto split: event.split)

lemma used'_parts [rule_format]: "X \<in> used' evs \<Longrightarrow> Y \<in> parts {X} \<longrightarrow> Y \<in> used' evs"
apply (induct evs, simp)
apply (rename_tac a b)
apply (case_tac a, simp_all) 
apply (blast dest: parts_trans)+ 
done

subsubsection\<open>monotonicity of used\<close>

lemma used_sub_Cons: "used evs <= used (ev#evs)"
by (induct evs, (induct ev, auto)+)

lemma used_ConsI: "X \<in> used evs \<Longrightarrow> X \<in> used (ev#evs)"
by (auto dest: used_sub_Cons [THEN subsetD])

lemma notin_used_ConsD: "X \<notin> used (ev#evs) \<Longrightarrow> X \<notin> used evs"
by (auto dest: used_sub_Cons [THEN subsetD])

lemma used_appD [dest]: "X \<in> used (evs @ evs') \<Longrightarrow> X \<in> used evs \<or> X \<in> used evs'"
by (induct evs, auto, rename_tac a b, case_tac a, auto)

lemma used_ConsD: "X \<in> used (ev#evs) \<Longrightarrow> X \<in> used [ev] \<or> X \<in> used evs"
by (case_tac ev, auto)

lemma used_sub_app: "used evs <= used (evs@evs')"
by (auto simp: used_decomp dest: used'_sub_app [THEN subsetD])

lemma used_appIL: "X \<in> used evs \<Longrightarrow> X \<in> used (evs' @ evs)"
by (induct evs', auto intro: used_ConsI)

lemma used_appIR: "X \<in> used evs \<Longrightarrow> X \<in> used (evs @ evs')"
by (erule used_sub_app [THEN subsetD])

lemma used_parts: "[| X \<in> parts {Y}; Y \<in> used evs |] ==> X \<in> used evs"
apply (auto simp: used_decomp dest: used'_parts)
by (auto simp: init_def used_Nil dest: parts_trans)

lemma parts_Says_used: "[| Says A B X \<in> set evs; Y \<in> parts {X} |] ==> Y \<in> used evs"
by (induct evs, simp_all, safe, auto intro: used_ConsI)

lemma parts_used_app: "X \<in> parts {Y} \<Longrightarrow> X \<in> used (evs @ Says A B Y # evs')"
apply (drule_tac evs="[Says A B Y]" in used_parts, simp, blast)
apply (drule_tac evs'=evs' in used_appIR)
apply (drule_tac evs'=evs in used_appIL)
by simp

subsubsection\<open>lemmas on used and knows\<close>

lemma initState_used: "X \<in> parts (initState A) \<Longrightarrow> X \<in> used evs"
by (induct evs, auto simp: used.simps split: event.split)

lemma Says_imp_used: "Says A B X \<in> set evs \<Longrightarrow> parts {X} \<subseteq> used evs"
by (induct evs, auto intro: used_ConsI)

lemma not_used_not_spied: "X \<notin> used evs \<Longrightarrow> X \<notin> parts (spies evs)"
by (induct evs, auto simp: used_Nil)

lemma not_used_not_parts: "[| Y \<notin> used evs; Says A B X \<in> set evs |]
==> Y \<notin> parts {X}"
by (induct evs, auto intro: used_ConsI)

lemma not_used_parts_false: "[| X \<notin> used evs; Y \<in> parts (spies evs) |]
==> X \<notin> parts {Y}"
by (auto dest: parts_parts)

lemma known_used [rule_format]: "[| evs \<in> p; Gets_correct p; one_step p |]
==> X \<in> parts (knows A evs) \<longrightarrow> X \<in> used evs"
apply (case_tac "A=Spy", blast)
apply (induct evs)
apply (simp add: used.simps, blast)
apply (rename_tac a evs)
apply (frule_tac ev=a and evs=evs in one_step_Cons, simp, clarify)
apply (drule_tac P="\<lambda>G. X \<in> parts G" in knows_Cons_substD, safe)
apply (erule initState_used)
apply (case_tac a, auto)
apply (rename_tac msg)
apply (drule_tac B=A and X=msg and evs=evs in Gets_correct_Says)
by (auto dest: Says_imp_used intro: used_ConsI)

lemma known_max_used [rule_format]: "[| evs \<in> p; Gets_correct p; one_step p |]
==> X \<in> parts (knows_max A evs) \<longrightarrow> X \<in> used evs"
apply (case_tac "A=Spy")
apply force
apply (induct evs)
apply (simp add: knows_max_def used.simps, blast)
apply (rename_tac a evs)
apply (frule_tac ev=a and evs=evs in one_step_Cons, simp, clarify)
apply (drule_tac P="\<lambda>G. X \<in> parts G" in knows_max_Cons_substD, safe)
apply (case_tac a, auto)
apply (rename_tac msg)
apply (drule_tac B=A and X=msg and evs=evs in Gets_correct_Says)
by (auto simp: knows_max'_Cons dest: Says_imp_used intro: used_ConsI)

lemma not_used_not_known: "[| evs \<in> p; X \<notin> used evs;
Gets_correct p; one_step p |] ==> X \<notin> parts (knows A evs)"
by (case_tac "A=Spy", auto dest: not_used_not_spied known_used)

lemma not_used_not_known_max: "[| evs \<in> p; X \<notin> used evs;
Gets_correct p; one_step p |] ==> X \<notin> parts (knows_max A evs)"
by (case_tac "A=Spy", auto dest: not_used_not_spied known_max_used)

subsubsection\<open>a nonce or key in a message cannot equal a fresh nonce or key\<close>

lemma Nonce_neq [dest]: "[| Nonce n' \<notin> used evs;
Says A B X \<in> set evs; Nonce n \<in> parts {X} |] ==> n \<noteq> n'"
by (drule not_used_not_spied, auto dest: Says_imp_knows_Spy parts_sub)

lemma Key_neq [dest]: "[| Key n' \<notin> used evs;
Says A B X \<in> set evs; Key n \<in> parts {X} |] ==> n ~= n'"
by (drule not_used_not_spied, auto dest: Says_imp_knows_Spy parts_sub)

subsubsection\<open>message of an event\<close>

primrec msg :: "event => msg"
where
  "msg (Says A B X) = X"
| "msg (Gets A X) = X"
| "msg (Notes A X) = X"

lemma used_sub_parts_used: "X \<in> used (ev # evs) ==> X \<in> parts {msg ev} \<union> used evs"
by (induct ev, auto)

end
