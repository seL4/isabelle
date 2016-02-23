(*  Title:      HOL/Auth/Guard/Guard_Shared.thy
    Author:     Frederic Blanqui, University of Cambridge Computer Laboratory
    Copyright   2002  University of Cambridge
*)

section\<open>lemmas on guarded messages for protocols with symmetric keys\<close>

theory Guard_Shared imports Guard GuardK "../Shared" begin

subsection\<open>Extensions to Theory \<open>Shared\<close>\<close>

declare initState.simps [simp del]

subsubsection\<open>a little abbreviation\<close>

abbreviation
  Ciph :: "agent => msg => msg" where
  "Ciph A X == Crypt (shrK A) X"

subsubsection\<open>agent associated to a key\<close>

definition agt :: "key => agent" where
"agt K == @A. K = shrK A"

lemma agt_shrK [simp]: "agt (shrK A) = A"
by (simp add: agt_def)

subsubsection\<open>basic facts about @{term initState}\<close>

lemma no_Crypt_in_parts_init [simp]: "Crypt K X ~:parts (initState A)"
by (cases A, auto simp: initState.simps)

lemma no_Crypt_in_analz_init [simp]: "Crypt K X ~:analz (initState A)"
by auto

lemma no_shrK_in_analz_init [simp]: "A ~:bad
==> Key (shrK A) ~:analz (initState Spy)"
by (auto simp: initState.simps)

lemma shrK_notin_initState_Friend [simp]: "A ~= Friend C
==> Key (shrK A) ~: parts (initState (Friend C))"
by (auto simp: initState.simps)

lemma keyset_init [iff]: "keyset (initState A)"
by (cases A, auto simp: keyset_def initState.simps)

subsubsection\<open>sets of symmetric keys\<close>

definition shrK_set :: "key set => bool" where
"shrK_set Ks == ALL K. K:Ks --> (EX A. K = shrK A)"

lemma in_shrK_set: "[| shrK_set Ks; K:Ks |] ==> EX A. K = shrK A"
by (simp add: shrK_set_def)

lemma shrK_set1 [iff]: "shrK_set {shrK A}"
by (simp add: shrK_set_def)

lemma shrK_set2 [iff]: "shrK_set {shrK A, shrK B}"
by (simp add: shrK_set_def)

subsubsection\<open>sets of good keys\<close>

definition good :: "key set => bool" where
"good Ks == ALL K. K:Ks --> agt K ~:bad"

lemma in_good: "[| good Ks; K:Ks |] ==> agt K ~:bad"
by (simp add: good_def)

lemma good1 [simp]: "A ~:bad ==> good {shrK A}"
by (simp add: good_def)

lemma good2 [simp]: "[| A ~:bad; B ~:bad |] ==> good {shrK A, shrK B}"
by (simp add: good_def)


subsection\<open>Proofs About Guarded Messages\<close>

subsubsection\<open>small hack\<close>

lemma shrK_is_invKey_shrK: "shrK A = invKey (shrK A)"
by simp

lemmas shrK_is_invKey_shrK_substI = shrK_is_invKey_shrK [THEN ssubst]

lemmas invKey_invKey_substI = invKey [THEN ssubst]

lemma "Nonce n:parts {X} ==> Crypt (shrK A) X:guard n {shrK A}"
apply (rule shrK_is_invKey_shrK_substI, rule invKey_invKey_substI)
by (rule Guard_Nonce, simp+)

subsubsection\<open>guardedness results on nonces\<close>

lemma guard_ciph [simp]: "shrK A:Ks ==> Ciph A X:guard n Ks"
by (rule Guard_Nonce, simp)

lemma guardK_ciph [simp]: "shrK A:Ks ==> Ciph A X:guardK n Ks"
by (rule Guard_Key, simp)

lemma Guard_init [iff]: "Guard n Ks (initState B)"
by (induct B, auto simp: Guard_def initState.simps)

lemma Guard_knows_max': "Guard n Ks (knows_max' C evs)
==> Guard n Ks (knows_max C evs)"
by (simp add: knows_max_def)

lemma Nonce_not_used_Guard_spies [dest]: "Nonce n ~:used evs
==> Guard n Ks (spies evs)"
by (auto simp: Guard_def dest: not_used_not_known parts_sub)

lemma Nonce_not_used_Guard [dest]: "[| evs:p; Nonce n ~:used evs;
Gets_correct p; one_step p |] ==> Guard n Ks (knows (Friend C) evs)"
by (auto simp: Guard_def dest: known_used parts_trans)

lemma Nonce_not_used_Guard_max [dest]: "[| evs:p; Nonce n ~:used evs;
Gets_correct p; one_step p |] ==> Guard n Ks (knows_max (Friend C) evs)"
by (auto simp: Guard_def dest: known_max_used parts_trans)

lemma Nonce_not_used_Guard_max' [dest]: "[| evs:p; Nonce n ~:used evs;
Gets_correct p; one_step p |] ==> Guard n Ks (knows_max' (Friend C) evs)"
apply (rule_tac H="knows_max (Friend C) evs" in Guard_mono)
by (auto simp: knows_max_def)

subsubsection\<open>guardedness results on keys\<close>

lemma GuardK_init [simp]: "n ~:range shrK ==> GuardK n Ks (initState B)"
by (induct B, auto simp: GuardK_def initState.simps)

lemma GuardK_knows_max': "[| GuardK n A (knows_max' C evs); n ~:range shrK |]
==> GuardK n A (knows_max C evs)"
by (simp add: knows_max_def)

lemma Key_not_used_GuardK_spies [dest]: "Key n ~:used evs
==> GuardK n A (spies evs)"
by (auto simp: GuardK_def dest: not_used_not_known parts_sub)

lemma Key_not_used_GuardK [dest]: "[| evs:p; Key n ~:used evs;
Gets_correct p; one_step p |] ==> GuardK n A (knows (Friend C) evs)"
by (auto simp: GuardK_def dest: known_used parts_trans)

lemma Key_not_used_GuardK_max [dest]: "[| evs:p; Key n ~:used evs;
Gets_correct p; one_step p |] ==> GuardK n A (knows_max (Friend C) evs)"
by (auto simp: GuardK_def dest: known_max_used parts_trans)

lemma Key_not_used_GuardK_max' [dest]: "[| evs:p; Key n ~:used evs;
Gets_correct p; one_step p |] ==> GuardK n A (knows_max' (Friend C) evs)"
apply (rule_tac H="knows_max (Friend C) evs" in GuardK_mono)
by (auto simp: knows_max_def)

subsubsection\<open>regular protocols\<close>

definition regular :: "event list set => bool" where
"regular p == ALL evs A. evs:p --> (Key (shrK A):parts (spies evs)) = (A:bad)"

lemma shrK_parts_iff_bad [simp]: "[| evs:p; regular p |] ==>
(Key (shrK A):parts (spies evs)) = (A:bad)"
by (auto simp: regular_def)

lemma shrK_analz_iff_bad [simp]: "[| evs:p; regular p |] ==>
(Key (shrK A):analz (spies evs)) = (A:bad)"
by auto

lemma Guard_Nonce_analz: "[| Guard n Ks (spies evs); evs:p;
shrK_set Ks; good Ks; regular p |] ==> Nonce n ~:analz (spies evs)"
apply (clarify, simp only: knows_decomp)
apply (drule Guard_invKey_keyset, simp+, safe)
apply (drule in_good, simp)
apply (drule in_shrK_set, simp+, clarify)
apply (frule_tac A=A in shrK_analz_iff_bad)
by (simp add: knows_decomp)+

lemma GuardK_Key_analz:
  assumes "GuardK n Ks (spies evs)" "evs \<in> p" "shrK_set Ks"
    "good Ks" "regular p" "n \<notin> range shrK"
  shows "Key n \<notin> analz (spies evs)"
proof (rule ccontr)
  assume "\<not> Key n \<notin> analz (knows Spy evs)"
  then have *: "Key n \<in> analz (spies' evs \<union> initState Spy)"
    by (simp add: knows_decomp)
  from \<open>GuardK n Ks (spies evs)\<close>
  have "GuardK n Ks (spies' evs \<union> initState Spy)"
    by (simp add: knows_decomp)  
  then have "GuardK n Ks (spies' evs)"
    and "finite (spies' evs)" "keyset (initState Spy)"
    by simp_all
  moreover have "Key n \<notin> initState Spy"
    using \<open>n \<notin> range shrK\<close> by (simp add: image_iff initState_Spy)
  ultimately obtain K
    where "K \<in> Ks" and **: "Key K \<in> analz (spies' evs \<union> initState Spy)"
    using * by (auto dest: GuardK_invKey_keyset)
  from \<open>K \<in> Ks\<close> and \<open>good Ks\<close> have "agt K \<notin> bad"
    by (auto dest: in_good)
  from \<open>K \<in> Ks\<close> \<open>shrK_set Ks\<close> obtain A
    where "K = shrK A"
    by (auto dest: in_shrK_set)
  then have "agt K \<in> bad"
    using ** \<open>evs \<in> p\<close> \<open>regular p\<close> shrK_analz_iff_bad [of evs p "agt K"]
    by (simp add: knows_decomp)
  with \<open>agt K \<notin> bad\<close> show False by simp
qed

end
