(*  Title:      HOL/Metis_Examples/Message.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Metis example featuring message authentication.
*)

header {* Metis Example Featuring Message Authentication *}

theory Message
imports Main
begin

declare [[metis_new_skolemizer]]

lemma strange_Un_eq [simp]: "A \<union> (B \<union> A) = B \<union> A"
by (metis Un_commute Un_left_absorb)

type_synonym key = nat

consts
  all_symmetric :: bool        --{*true if all keys are symmetric*}
  invKey        :: "key=>key"  --{*inverse of a symmetric key*}

specification (invKey)
  invKey [simp]: "invKey (invKey K) = K"
  invKey_symmetric: "all_symmetric --> invKey = id"
by (metis id_apply)


text{*The inverse of a symmetric key is itself; that of a public key
      is the private key and vice versa*}

definition symKeys :: "key set" where
  "symKeys == {K. invKey K = K}"

datatype  --{*We allow any number of friendly agents*}
  agent = Server | Friend nat | Spy

datatype
     msg = Agent  agent     --{*Agent names*}
         | Number nat       --{*Ordinary integers, timestamps, ...*}
         | Nonce  nat       --{*Unguessable nonces*}
         | Key    key       --{*Crypto keys*}
         | Hash   msg       --{*Hashing*}
         | MPair  msg msg   --{*Compound messages*}
         | Crypt  key msg   --{*Encryption, public- or shared-key*}


text{*Concrete syntax: messages appear as {|A,B,NA|}, etc...*}
syntax
  "_MTuple"      :: "['a, args] => 'a * 'b"       ("(2{|_,/ _|})")

syntax (xsymbols)
  "_MTuple"      :: "['a, args] => 'a * 'b"       ("(2\<lbrace>_,/ _\<rbrace>)")

translations
  "{|x, y, z|}"   == "{|x, {|y, z|}|}"
  "{|x, y|}"      == "CONST MPair x y"


definition HPair :: "[msg,msg] => msg" ("(4Hash[_] /_)" [0, 1000]) where
    --{*Message Y paired with a MAC computed with the help of X*}
    "Hash[X] Y == {| Hash{|X,Y|}, Y|}"

definition keysFor :: "msg set => key set" where
    --{*Keys useful to decrypt elements of a message set*}
  "keysFor H == invKey ` {K. \<exists>X. Crypt K X \<in> H}"


subsubsection{*Inductive Definition of All Parts" of a Message*}

inductive_set
  parts :: "msg set => msg set"
  for H :: "msg set"
  where
    Inj [intro]:               "X \<in> H ==> X \<in> parts H"
  | Fst:         "{|X,Y|}   \<in> parts H ==> X \<in> parts H"
  | Snd:         "{|X,Y|}   \<in> parts H ==> Y \<in> parts H"
  | Body:        "Crypt K X \<in> parts H ==> X \<in> parts H"

lemma parts_mono: "G \<subseteq> H ==> parts(G) \<subseteq> parts(H)"
apply auto
apply (erule parts.induct)
   apply (metis parts.Inj set_rev_mp)
  apply (metis parts.Fst)
 apply (metis parts.Snd)
by (metis parts.Body)

text{*Equations hold because constructors are injective.*}
lemma Friend_image_eq [simp]: "(Friend x \<in> Friend`A) = (x:A)"
by (metis agent.inject image_iff)

lemma Key_image_eq [simp]: "(Key x \<in> Key`A) = (x \<in> A)"
by (metis image_iff msg.inject(4))

lemma Nonce_Key_image_eq [simp]: "Nonce x \<notin> Key`A"
by (metis image_iff msg.distinct(23))


subsubsection{*Inverse of keys *}

lemma invKey_eq [simp]: "(invKey K = invKey K') = (K = K')"
by (metis invKey)


subsection{*keysFor operator*}

lemma keysFor_empty [simp]: "keysFor {} = {}"
by (unfold keysFor_def, blast)

lemma keysFor_Un [simp]: "keysFor (H \<union> H') = keysFor H \<union> keysFor H'"
by (unfold keysFor_def, blast)

lemma keysFor_UN [simp]: "keysFor (\<Union>i\<in>A. H i) = (\<Union>i\<in>A. keysFor (H i))"
by (unfold keysFor_def, blast)

text{*Monotonicity*}
lemma keysFor_mono: "G \<subseteq> H ==> keysFor(G) \<subseteq> keysFor(H)"
by (unfold keysFor_def, blast)

lemma keysFor_insert_Agent [simp]: "keysFor (insert (Agent A) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Nonce [simp]: "keysFor (insert (Nonce N) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Number [simp]: "keysFor (insert (Number N) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Key [simp]: "keysFor (insert (Key K) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Hash [simp]: "keysFor (insert (Hash X) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_MPair [simp]: "keysFor (insert {|X,Y|} H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Crypt [simp]:
    "keysFor (insert (Crypt K X) H) = insert (invKey K) (keysFor H)"
by (unfold keysFor_def, auto)

lemma keysFor_image_Key [simp]: "keysFor (Key`E) = {}"
by (unfold keysFor_def, auto)

lemma Crypt_imp_invKey_keysFor: "Crypt K X \<in> H ==> invKey K \<in> keysFor H"
by (unfold keysFor_def, blast)


subsection{*Inductive relation "parts"*}

lemma MPair_parts:
     "[| {|X,Y|} \<in> parts H;
         [| X \<in> parts H; Y \<in> parts H |] ==> P |] ==> P"
by (blast dest: parts.Fst parts.Snd)

declare MPair_parts [elim!] parts.Body [dest!]
text{*NB These two rules are UNSAFE in the formal sense, as they discard the
     compound message.  They work well on THIS FILE.
  @{text MPair_parts} is left as SAFE because it speeds up proofs.
  The Crypt rule is normally kept UNSAFE to avoid breaking up certificates.*}

lemma parts_increasing: "H \<subseteq> parts(H)"
by blast

lemmas parts_insertI = subset_insertI [THEN parts_mono, THEN subsetD]

lemma parts_empty [simp]: "parts{} = {}"
apply safe
apply (erule parts.induct)
apply blast+
done

lemma parts_emptyE [elim!]: "X\<in> parts{} ==> P"
by simp

text{*WARNING: loops if H = {Y}, therefore must not be repeated!*}
lemma parts_singleton: "X\<in> parts H ==> \<exists>Y\<in>H. X\<in> parts {Y}"
apply (erule parts.induct)
apply fast+
done


subsubsection{*Unions *}

lemma parts_Un_subset1: "parts(G) \<union> parts(H) \<subseteq> parts(G \<union> H)"
by (intro Un_least parts_mono Un_upper1 Un_upper2)

lemma parts_Un_subset2: "parts(G \<union> H) \<subseteq> parts(G) \<union> parts(H)"
apply (rule subsetI)
apply (erule parts.induct, blast+)
done

lemma parts_Un [simp]: "parts(G \<union> H) = parts(G) \<union> parts(H)"
by (intro equalityI parts_Un_subset1 parts_Un_subset2)

lemma parts_insert: "parts (insert X H) = parts {X} \<union> parts H"
apply (subst insert_is_Un [of _ H])
apply (simp only: parts_Un)
done

lemma parts_insert2:
     "parts (insert X (insert Y H)) = parts {X} \<union> parts {Y} \<union> parts H"
by (metis Un_commute Un_empty_left Un_empty_right Un_insert_left Un_insert_right parts_Un)


lemma parts_UN_subset1: "(\<Union>x\<in>A. parts(H x)) \<subseteq> parts(\<Union>x\<in>A. H x)"
by (intro UN_least parts_mono UN_upper)

lemma parts_UN_subset2: "parts(\<Union>x\<in>A. H x) \<subseteq> (\<Union>x\<in>A. parts(H x))"
apply (rule subsetI)
apply (erule parts.induct, blast+)
done

lemma parts_UN [simp]: "parts(\<Union>x\<in>A. H x) = (\<Union>x\<in>A. parts(H x))"
by (intro equalityI parts_UN_subset1 parts_UN_subset2)

text{*Added to simplify arguments to parts, analz and synth.
  NOTE: the UN versions are no longer used!*}


text{*This allows @{text blast} to simplify occurrences of
  @{term "parts(G\<union>H)"} in the assumption.*}
lemmas in_parts_UnE = parts_Un [THEN equalityD1, THEN subsetD, THEN UnE]
declare in_parts_UnE [elim!]

lemma parts_insert_subset: "insert X (parts H) \<subseteq> parts(insert X H)"
by (blast intro: parts_mono [THEN [2] rev_subsetD])

subsubsection{*Idempotence and transitivity *}

lemma parts_partsD [dest!]: "X\<in> parts (parts H) ==> X\<in> parts H"
by (erule parts.induct, blast+)

lemma parts_idem [simp]: "parts (parts H) = parts H"
by blast

lemma parts_subset_iff [simp]: "(parts G \<subseteq> parts H) = (G \<subseteq> parts H)"
apply (rule iffI)
apply (metis Un_absorb1 Un_subset_iff parts_Un parts_increasing)
apply (metis parts_idem parts_mono)
done

lemma parts_trans: "[| X\<in> parts G;  G \<subseteq> parts H |] ==> X\<in> parts H"
by (blast dest: parts_mono)

lemma parts_cut: "[|Y\<in> parts (insert X G);  X\<in> parts H|] ==> Y\<in> parts(G \<union> H)"
by (metis Un_insert_left Un_insert_right insert_absorb mem_def parts_Un parts_idem sup1CI)


subsubsection{*Rewrite rules for pulling out atomic messages *}

lemmas parts_insert_eq_I = equalityI [OF subsetI parts_insert_subset]


lemma parts_insert_Agent [simp]:
     "parts (insert (Agent agt) H) = insert (Agent agt) (parts H)"
apply (rule parts_insert_eq_I)
apply (erule parts.induct, auto)
done

lemma parts_insert_Nonce [simp]:
     "parts (insert (Nonce N) H) = insert (Nonce N) (parts H)"
apply (rule parts_insert_eq_I)
apply (erule parts.induct, auto)
done

lemma parts_insert_Number [simp]:
     "parts (insert (Number N) H) = insert (Number N) (parts H)"
apply (rule parts_insert_eq_I)
apply (erule parts.induct, auto)
done

lemma parts_insert_Key [simp]:
     "parts (insert (Key K) H) = insert (Key K) (parts H)"
apply (rule parts_insert_eq_I)
apply (erule parts.induct, auto)
done

lemma parts_insert_Hash [simp]:
     "parts (insert (Hash X) H) = insert (Hash X) (parts H)"
apply (rule parts_insert_eq_I)
apply (erule parts.induct, auto)
done

lemma parts_insert_Crypt [simp]:
     "parts (insert (Crypt K X) H) =
          insert (Crypt K X) (parts (insert X H))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct, auto)
apply (blast intro: parts.Body)
done

lemma parts_insert_MPair [simp]:
     "parts (insert {|X,Y|} H) =
          insert {|X,Y|} (parts (insert X (insert Y H)))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct, auto)
apply (blast intro: parts.Fst parts.Snd)+
done

lemma parts_image_Key [simp]: "parts (Key`N) = Key`N"
apply auto
apply (erule parts.induct, auto)
done

lemma msg_Nonce_supply: "\<exists>N. \<forall>n. N\<le>n --> Nonce n \<notin> parts {msg}"
apply (induct_tac "msg")
apply (simp_all add: parts_insert2)
apply (metis Suc_n_not_le_n)
apply (metis le_trans linorder_linear)
done

subsection{*Inductive relation "analz"*}

text{*Inductive definition of "analz" -- what can be broken down from a set of
    messages, including keys.  A form of downward closure.  Pairs can
    be taken apart; messages decrypted with known keys.  *}

inductive_set
  analz :: "msg set => msg set"
  for H :: "msg set"
  where
    Inj [intro,simp] :    "X \<in> H ==> X \<in> analz H"
  | Fst:     "{|X,Y|} \<in> analz H ==> X \<in> analz H"
  | Snd:     "{|X,Y|} \<in> analz H ==> Y \<in> analz H"
  | Decrypt [dest]:
             "[|Crypt K X \<in> analz H; Key(invKey K): analz H|] ==> X \<in> analz H"


text{*Monotonicity; Lemma 1 of Lowe's paper*}
lemma analz_mono: "G\<subseteq>H ==> analz(G) \<subseteq> analz(H)"
apply auto
apply (erule analz.induct)
apply (auto dest: analz.Fst analz.Snd)
done

text{*Making it safe speeds up proofs*}
lemma MPair_analz [elim!]:
     "[| {|X,Y|} \<in> analz H;
             [| X \<in> analz H; Y \<in> analz H |] ==> P
          |] ==> P"
by (blast dest: analz.Fst analz.Snd)

lemma analz_increasing: "H \<subseteq> analz(H)"
by blast

lemma analz_subset_parts: "analz H \<subseteq> parts H"
apply (rule subsetI)
apply (erule analz.induct, blast+)
done

lemmas analz_into_parts = analz_subset_parts [THEN subsetD]

lemmas not_parts_not_analz = analz_subset_parts [THEN contra_subsetD]

lemma parts_analz [simp]: "parts (analz H) = parts H"
apply (rule equalityI)
apply (metis analz_subset_parts parts_subset_iff)
apply (metis analz_increasing parts_mono)
done


lemma analz_parts [simp]: "analz (parts H) = parts H"
apply auto
apply (erule analz.induct, auto)
done

lemmas analz_insertI = subset_insertI [THEN analz_mono, THEN [2] rev_subsetD]

subsubsection{*General equational properties *}

lemma analz_empty [simp]: "analz{} = {}"
apply safe
apply (erule analz.induct, blast+)
done

text{*Converse fails: we can analz more from the union than from the
  separate parts, as a key in one might decrypt a message in the other*}
lemma analz_Un: "analz(G) \<union> analz(H) \<subseteq> analz(G \<union> H)"
by (intro Un_least analz_mono Un_upper1 Un_upper2)

lemma analz_insert: "insert X (analz H) \<subseteq> analz(insert X H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])

subsubsection{*Rewrite rules for pulling out atomic messages *}

lemmas analz_insert_eq_I = equalityI [OF subsetI analz_insert]

lemma analz_insert_Agent [simp]:
     "analz (insert (Agent agt) H) = insert (Agent agt) (analz H)"
apply (rule analz_insert_eq_I)
apply (erule analz.induct, auto)
done

lemma analz_insert_Nonce [simp]:
     "analz (insert (Nonce N) H) = insert (Nonce N) (analz H)"
apply (rule analz_insert_eq_I)
apply (erule analz.induct, auto)
done

lemma analz_insert_Number [simp]:
     "analz (insert (Number N) H) = insert (Number N) (analz H)"
apply (rule analz_insert_eq_I)
apply (erule analz.induct, auto)
done

lemma analz_insert_Hash [simp]:
     "analz (insert (Hash X) H) = insert (Hash X) (analz H)"
apply (rule analz_insert_eq_I)
apply (erule analz.induct, auto)
done

text{*Can only pull out Keys if they are not needed to decrypt the rest*}
lemma analz_insert_Key [simp]:
    "K \<notin> keysFor (analz H) ==>
          analz (insert (Key K) H) = insert (Key K) (analz H)"
apply (unfold keysFor_def)
apply (rule analz_insert_eq_I)
apply (erule analz.induct, auto)
done

lemma analz_insert_MPair [simp]:
     "analz (insert {|X,Y|} H) =
          insert {|X,Y|} (analz (insert X (insert Y H)))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule analz.induct, auto)
apply (erule analz.induct)
apply (blast intro: analz.Fst analz.Snd)+
done

text{*Can pull out enCrypted message if the Key is not known*}
lemma analz_insert_Crypt:
     "Key (invKey K) \<notin> analz H
      ==> analz (insert (Crypt K X) H) = insert (Crypt K X) (analz H)"
apply (rule analz_insert_eq_I)
apply (erule analz.induct, auto)

done

lemma lemma1: "Key (invKey K) \<in> analz H ==>
               analz (insert (Crypt K X) H) \<subseteq>
               insert (Crypt K X) (analz (insert X H))"
apply (rule subsetI)
apply (erule_tac x = x in analz.induct, auto)
done

lemma lemma2: "Key (invKey K) \<in> analz H ==>
               insert (Crypt K X) (analz (insert X H)) \<subseteq>
               analz (insert (Crypt K X) H)"
apply auto
apply (erule_tac x = x in analz.induct, auto)
apply (blast intro: analz_insertI analz.Decrypt)
done

lemma analz_insert_Decrypt:
     "Key (invKey K) \<in> analz H ==>
               analz (insert (Crypt K X) H) =
               insert (Crypt K X) (analz (insert X H))"
by (intro equalityI lemma1 lemma2)

text{*Case analysis: either the message is secure, or it is not! Effective,
but can cause subgoals to blow up! Use with @{text "split_if"}; apparently
@{text "split_tac"} does not cope with patterns such as @{term"analz (insert
(Crypt K X) H)"} *}
lemma analz_Crypt_if [simp]:
     "analz (insert (Crypt K X) H) =
          (if (Key (invKey K) \<in> analz H)
           then insert (Crypt K X) (analz (insert X H))
           else insert (Crypt K X) (analz H))"
by (simp add: analz_insert_Crypt analz_insert_Decrypt)


text{*This rule supposes "for the sake of argument" that we have the key.*}
lemma analz_insert_Crypt_subset:
     "analz (insert (Crypt K X) H) \<subseteq>
           insert (Crypt K X) (analz (insert X H))"
apply (rule subsetI)
apply (erule analz.induct, auto)
done


lemma analz_image_Key [simp]: "analz (Key`N) = Key`N"
apply auto
apply (erule analz.induct, auto)
done


subsubsection{*Idempotence and transitivity *}

lemma analz_analzD [dest!]: "X\<in> analz (analz H) ==> X\<in> analz H"
by (erule analz.induct, blast+)

lemma analz_idem [simp]: "analz (analz H) = analz H"
by blast

lemma analz_subset_iff [simp]: "(analz G \<subseteq> analz H) = (G \<subseteq> analz H)"
apply (rule iffI)
apply (iprover intro: subset_trans analz_increasing)
apply (frule analz_mono, simp)
done

lemma analz_trans: "[| X\<in> analz G;  G \<subseteq> analz H |] ==> X\<in> analz H"
by (drule analz_mono, blast)


declare analz_trans[intro]

lemma analz_cut: "[| Y\<in> analz (insert X H);  X\<in> analz H |] ==> Y\<in> analz H"
(*TOO SLOW
by (metis analz_idem analz_increasing analz_mono insert_absorb insert_mono insert_subset) --{*317s*}
??*)
by (erule analz_trans, blast)


text{*This rewrite rule helps in the simplification of messages that involve
  the forwarding of unknown components (X).  Without it, removing occurrences
  of X can be very complicated. *}
lemma analz_insert_eq: "X\<in> analz H ==> analz (insert X H) = analz H"
by (blast intro: analz_cut analz_insertI)


text{*A congruence rule for "analz" *}

lemma analz_subset_cong:
     "[| analz G \<subseteq> analz G'; analz H \<subseteq> analz H' |]
      ==> analz (G \<union> H) \<subseteq> analz (G' \<union> H')"
apply simp
apply (metis Un_absorb2 Un_commute Un_subset_iff Un_upper1 Un_upper2 analz_mono)
done


lemma analz_cong:
     "[| analz G = analz G'; analz H = analz H'
               |] ==> analz (G \<union> H) = analz (G' \<union> H')"
by (intro equalityI analz_subset_cong, simp_all)

lemma analz_insert_cong:
     "analz H = analz H' ==> analz(insert X H) = analz(insert X H')"
by (force simp only: insert_def intro!: analz_cong)

text{*If there are no pairs or encryptions then analz does nothing*}
lemma analz_trivial:
     "[| \<forall>X Y. {|X,Y|} \<notin> H;  \<forall>X K. Crypt K X \<notin> H |] ==> analz H = H"
apply safe
apply (erule analz.induct, blast+)
done

text{*These two are obsolete (with a single Spy) but cost little to prove...*}
lemma analz_UN_analz_lemma:
     "X\<in> analz (\<Union>i\<in>A. analz (H i)) ==> X\<in> analz (\<Union>i\<in>A. H i)"
apply (erule analz.induct)
apply (blast intro: analz_mono [THEN [2] rev_subsetD])+
done

lemma analz_UN_analz [simp]: "analz (\<Union>i\<in>A. analz (H i)) = analz (\<Union>i\<in>A. H i)"
by (blast intro: analz_UN_analz_lemma analz_mono [THEN [2] rev_subsetD])


subsection{*Inductive relation "synth"*}

text{*Inductive definition of "synth" -- what can be built up from a set of
    messages.  A form of upward closure.  Pairs can be built, messages
    encrypted with known keys.  Agent names are public domain.
    Numbers can be guessed, but Nonces cannot be.  *}

inductive_set
  synth :: "msg set => msg set"
  for H :: "msg set"
  where
    Inj    [intro]:   "X \<in> H ==> X \<in> synth H"
  | Agent  [intro]:   "Agent agt \<in> synth H"
  | Number [intro]:   "Number n  \<in> synth H"
  | Hash   [intro]:   "X \<in> synth H ==> Hash X \<in> synth H"
  | MPair  [intro]:   "[|X \<in> synth H;  Y \<in> synth H|] ==> {|X,Y|} \<in> synth H"
  | Crypt  [intro]:   "[|X \<in> synth H;  Key(K) \<in> H|] ==> Crypt K X \<in> synth H"

text{*Monotonicity*}
lemma synth_mono: "G\<subseteq>H ==> synth(G) \<subseteq> synth(H)"
  by (auto, erule synth.induct, auto)

text{*NO @{text Agent_synth}, as any Agent name can be synthesized.
  The same holds for @{term Number}*}
inductive_cases Nonce_synth [elim!]: "Nonce n \<in> synth H"
inductive_cases Key_synth   [elim!]: "Key K \<in> synth H"
inductive_cases Hash_synth  [elim!]: "Hash X \<in> synth H"
inductive_cases MPair_synth [elim!]: "{|X,Y|} \<in> synth H"
inductive_cases Crypt_synth [elim!]: "Crypt K X \<in> synth H"


lemma synth_increasing: "H \<subseteq> synth(H)"
by blast

subsubsection{*Unions *}

text{*Converse fails: we can synth more from the union than from the
  separate parts, building a compound message using elements of each.*}
lemma synth_Un: "synth(G) \<union> synth(H) \<subseteq> synth(G \<union> H)"
by (intro Un_least synth_mono Un_upper1 Un_upper2)

lemma synth_insert: "insert X (synth H) \<subseteq> synth(insert X H)"
by (metis insert_iff insert_subset subset_insertI synth.Inj synth_mono)

subsubsection{*Idempotence and transitivity *}

lemma synth_synthD [dest!]: "X\<in> synth (synth H) ==> X\<in> synth H"
by (erule synth.induct, blast+)

lemma synth_idem: "synth (synth H) = synth H"
by blast

lemma synth_subset_iff [simp]: "(synth G \<subseteq> synth H) = (G \<subseteq> synth H)"
apply (rule iffI)
apply (iprover intro: subset_trans synth_increasing)
apply (frule synth_mono, simp add: synth_idem)
done

lemma synth_trans: "[| X\<in> synth G;  G \<subseteq> synth H |] ==> X\<in> synth H"
by (drule synth_mono, blast)

lemma synth_cut: "[| Y\<in> synth (insert X H);  X\<in> synth H |] ==> Y\<in> synth H"
(*TOO SLOW
by (metis insert_absorb insert_mono insert_subset synth_idem synth_increasing synth_mono)
*)
by (erule synth_trans, blast)


lemma Agent_synth [simp]: "Agent A \<in> synth H"
by blast

lemma Number_synth [simp]: "Number n \<in> synth H"
by blast

lemma Nonce_synth_eq [simp]: "(Nonce N \<in> synth H) = (Nonce N \<in> H)"
by blast

lemma Key_synth_eq [simp]: "(Key K \<in> synth H) = (Key K \<in> H)"
by blast

lemma Crypt_synth_eq [simp]:
     "Key K \<notin> H ==> (Crypt K X \<in> synth H) = (Crypt K X \<in> H)"
by blast


lemma keysFor_synth [simp]:
    "keysFor (synth H) = keysFor H \<union> invKey`{K. Key K \<in> H}"
by (unfold keysFor_def, blast)


subsubsection{*Combinations of parts, analz and synth *}

lemma parts_synth [simp]: "parts (synth H) = parts H \<union> synth H"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct)
apply (metis UnCI)
apply (metis MPair_synth UnCI UnE insert_absorb insert_subset parts.Fst parts_increasing)
apply (metis MPair_synth UnCI UnE insert_absorb insert_subset parts.Snd parts_increasing)
apply (metis Body Crypt_synth UnCI UnE insert_absorb insert_subset parts_increasing)
apply (metis Un_subset_iff parts_increasing parts_mono synth_increasing)
done

lemma analz_analz_Un [simp]: "analz (analz G \<union> H) = analz (G \<union> H)"
apply (rule equalityI)
apply (metis analz_idem analz_subset_cong order_eq_refl)
apply (metis analz_increasing analz_subset_cong order_eq_refl)
done

declare analz_mono [intro] analz.Fst [intro] analz.Snd [intro] Un_least [intro]

lemma analz_synth_Un [simp]: "analz (synth G \<union> H) = analz (G \<union> H) \<union> synth G"
apply (rule equalityI)
apply (rule subsetI)
apply (erule analz.induct)
apply (metis UnCI UnE Un_commute analz.Inj)
apply (metis MPair_synth UnCI UnE Un_commute analz.Fst analz.Inj mem_def)
apply (metis MPair_synth UnCI UnE Un_commute analz.Inj analz.Snd mem_def)
apply (blast intro: analz.Decrypt)
apply blast
done

lemma analz_synth [simp]: "analz (synth H) = analz H \<union> synth H"
proof -
  have "\<forall>x\<^isub>2 x\<^isub>1. synth x\<^isub>1 \<union> analz (x\<^isub>1 \<union> x\<^isub>2) = analz (synth x\<^isub>1 \<union> x\<^isub>2)" by (metis Un_commute analz_synth_Un)
  hence "\<forall>x\<^isub>1. synth x\<^isub>1 \<union> analz x\<^isub>1 = analz (synth x\<^isub>1 \<union> {})" by (metis Un_empty_right)
  hence "\<forall>x\<^isub>1. synth x\<^isub>1 \<union> analz x\<^isub>1 = analz (synth x\<^isub>1)" by (metis Un_empty_right)
  hence "\<forall>x\<^isub>1. analz x\<^isub>1 \<union> synth x\<^isub>1 = analz (synth x\<^isub>1)" by (metis Un_commute)
  thus "analz (synth H) = analz H \<union> synth H" by metis
qed


subsubsection{*For reasoning about the Fake rule in traces *}

lemma parts_insert_subset_Un: "X\<in> G ==> parts(insert X H) \<subseteq> parts G \<union> parts H"
proof -
  assume "X \<in> G"
  hence "G X" by (metis mem_def)
  hence "\<forall>x\<^isub>1. G \<subseteq> x\<^isub>1 \<longrightarrow> x\<^isub>1 X" by (metis predicate1D)
  hence "\<forall>x\<^isub>1. (G \<union> x\<^isub>1) X" by (metis Un_upper1)
  hence "\<forall>x\<^isub>1. X \<in> G \<union> x\<^isub>1" by (metis mem_def)
  hence "insert X H \<subseteq> G \<union> H" by (metis Un_upper2 insert_subset)
  hence "parts (insert X H) \<subseteq> parts (G \<union> H)" by (metis parts_mono)
  thus "parts (insert X H) \<subseteq> parts G \<union> parts H" by (metis parts_Un)
qed

lemma Fake_parts_insert:
     "X \<in> synth (analz H) ==>
      parts (insert X H) \<subseteq> synth (analz H) \<union> parts H"
proof -
  assume A1: "X \<in> synth (analz H)"
  have F1: "\<forall>x\<^isub>1. analz x\<^isub>1 \<union> synth (analz x\<^isub>1) = analz (synth (analz x\<^isub>1))"
    by (metis analz_idem analz_synth)
  have F2: "\<forall>x\<^isub>1. parts x\<^isub>1 \<union> synth (analz x\<^isub>1) = parts (synth (analz x\<^isub>1))"
    by (metis parts_analz parts_synth)
  have F3: "synth (analz H) X" using A1 by (metis mem_def)
  have "\<forall>x\<^isub>2 x\<^isub>1\<Colon>msg set. x\<^isub>1 \<le> sup x\<^isub>1 x\<^isub>2" by (metis inf_sup_ord(3))
  hence F4: "\<forall>x\<^isub>1. analz x\<^isub>1 \<subseteq> analz (synth x\<^isub>1)" by (metis analz_synth)
  have F5: "X \<in> synth (analz H)" using F3 by (metis mem_def)
  have "\<forall>x\<^isub>1. analz x\<^isub>1 \<subseteq> synth (analz x\<^isub>1)
         \<longrightarrow> analz (synth (analz x\<^isub>1)) = synth (analz x\<^isub>1)"
    using F1 by (metis subset_Un_eq)
  hence F6: "\<forall>x\<^isub>1. analz (synth (analz x\<^isub>1)) = synth (analz x\<^isub>1)"
    by (metis synth_increasing)
  have "\<forall>x\<^isub>1. x\<^isub>1 \<subseteq> analz (synth x\<^isub>1)" using F4 by (metis analz_subset_iff)
  hence "\<forall>x\<^isub>1. x\<^isub>1 \<subseteq> analz (synth (analz x\<^isub>1))" by (metis analz_subset_iff)
  hence "\<forall>x\<^isub>1. x\<^isub>1 \<subseteq> synth (analz x\<^isub>1)" using F6 by metis
  hence "H \<subseteq> synth (analz H)" by metis
  hence "H \<subseteq> synth (analz H) \<and> X \<in> synth (analz H)" using F5 by metis
  hence "insert X H \<subseteq> synth (analz H)" by (metis insert_subset)
  hence "parts (insert X H) \<subseteq> parts (synth (analz H))" by (metis parts_mono)
  hence "parts (insert X H) \<subseteq> parts H \<union> synth (analz H)" using F2 by metis
  thus "parts (insert X H) \<subseteq> synth (analz H) \<union> parts H" by (metis Un_commute)
qed

lemma Fake_parts_insert_in_Un:
     "[|Z \<in> parts (insert X H);  X: synth (analz H)|]
      ==> Z \<in>  synth (analz H) \<union> parts H"
by (blast dest: Fake_parts_insert [THEN subsetD, dest])

declare analz_mono [intro] synth_mono [intro]

lemma Fake_analz_insert:
     "X \<in> synth (analz G) ==>
      analz (insert X H) \<subseteq> synth (analz G) \<union> analz (G \<union> H)"
by (metis Un_commute Un_insert_left Un_insert_right Un_upper1 analz_analz_Un
          analz_mono analz_synth_Un insert_absorb)

lemma Fake_analz_insert_simpler:
     "X \<in> synth (analz G) ==>
      analz (insert X H) \<subseteq> synth (analz G) \<union> analz (G \<union> H)"
apply (rule subsetI)
apply (subgoal_tac "x \<in> analz (synth (analz G) \<union> H) ")
apply (metis Un_commute analz_analz_Un analz_synth_Un)
by (metis Un_upper1 Un_upper2 analz_mono insert_absorb insert_subset)

end
