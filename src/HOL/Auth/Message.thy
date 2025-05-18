(*  Title:      HOL/Auth/Message.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatypes of agents and messages;
Inductive relations "parts", "analz" and "synth"
*)

section\<open>Theory of Agents and Messages for Security Protocols\<close>

theory Message
imports Main
begin

(*Needed occasionally with spy_analz_tac, e.g. in analz_insert_Key_newK*)
lemma [simp] : "A \<union> (B \<union> A) = B \<union> A"
  by blast

type_synonym
  key = nat

consts
  all_symmetric :: bool        \<comment> \<open>true if all keys are symmetric\<close>
  invKey        :: "key\<Rightarrow>key"  \<comment> \<open>inverse of a symmetric key\<close>

specification (invKey)
  invKey [simp]: "invKey (invKey K) = K"
  invKey_symmetric: "all_symmetric \<longrightarrow> invKey = id"
    by (rule exI [of _ id], auto)


text\<open>The inverse of a symmetric key is itself; that of a public key
      is the private key and vice versa\<close>

definition symKeys :: "key set" where
  "symKeys == {K. invKey K = K}"

datatype  \<comment> \<open>We allow any number of friendly agents\<close>
  agent = Server | Friend nat | Spy

datatype
     msg = Agent  agent     \<comment> \<open>Agent names\<close>
         | Number nat       \<comment> \<open>Ordinary integers, timestamps, ...\<close>
         | Nonce  nat       \<comment> \<open>Unguessable nonces\<close>
         | Key    key       \<comment> \<open>Crypto keys\<close>
         | Hash   msg       \<comment> \<open>Hashing\<close>
         | MPair  msg msg   \<comment> \<open>Compound messages\<close>
         | Crypt  key msg   \<comment> \<open>Encryption, public- or shared-key\<close>


text\<open>Concrete syntax: messages appear as \<open>\<lbrace>A,B,NA\<rbrace>\<close>, etc...\<close>
syntax
  "_MTuple" :: "['a, args] \<Rightarrow> 'a * 'b"  (\<open>(\<open>indent=2 notation=\<open>mixfix message tuple\<close>\<close>\<lbrace>_,/ _\<rbrace>)\<close>)
syntax_consts
  "_MTuple" \<rightleftharpoons> MPair
translations
  "\<lbrace>x, y, z\<rbrace>" \<rightleftharpoons> "\<lbrace>x, \<lbrace>y, z\<rbrace>\<rbrace>"
  "\<lbrace>x, y\<rbrace>" \<rightleftharpoons> "CONST MPair x y"


definition HPair :: "[msg,msg] \<Rightarrow> msg" (\<open>(4Hash[_] /_)\<close> [0, 1000]) where
    \<comment> \<open>Message Y paired with a MAC computed with the help of X\<close>
    "Hash[X] Y == \<lbrace>Hash\<lbrace>X,Y\<rbrace>, Y\<rbrace>"

definition keysFor :: "msg set \<Rightarrow> key set" where
    \<comment> \<open>Keys useful to decrypt elements of a message set\<close>
  "keysFor H == invKey ` {K. \<exists>X. Crypt K X \<in> H}"


subsection\<open>Inductive Definition of All Parts of a Message\<close>

inductive_set
  parts :: "msg set \<Rightarrow> msg set"
  for H :: "msg set"
  where
    Inj [intro]: "X \<in> H \<Longrightarrow> X \<in> parts H"
  | Fst:         "\<lbrace>X,Y\<rbrace> \<in> parts H \<Longrightarrow> X \<in> parts H"
  | Snd:         "\<lbrace>X,Y\<rbrace> \<in> parts H \<Longrightarrow> Y \<in> parts H"
  | Body:        "Crypt K X \<in> parts H \<Longrightarrow> X \<in> parts H"


text\<open>Monotonicity\<close>
lemma parts_mono_aux: "\<lbrakk>G \<subseteq> H; X \<in> parts G\<rbrakk> \<Longrightarrow> X \<in> parts H"
  by (erule parts.induct) (auto dest: parts.Fst parts.Snd parts.Body)

lemma parts_mono: "G \<subseteq> H \<Longrightarrow> parts(G) \<subseteq> parts(H)"
  using parts_mono_aux by blast


text\<open>Equations hold because constructors are injective.\<close>
lemma Friend_image_eq [simp]: "(Friend x \<in> Friend`A) = (x \<in>A)"
  by auto

lemma Key_image_eq [simp]: "(Key x \<in> Key`A) = (x \<in>A)"
  by auto

lemma Nonce_Key_image_eq [simp]: "(Nonce x \<notin> Key`A)"
  by auto


subsection\<open>Inverse of keys\<close>

lemma invKey_eq [simp]: "(invKey K = invKey K') = (K=K')"
  by (metis invKey)


subsection\<open>The @{term keysFor} operator\<close>

lemma keysFor_empty [simp]: "keysFor {} = {}"
    unfolding keysFor_def by blast

lemma keysFor_Un [simp]: "keysFor (H \<union> H') = keysFor H \<union> keysFor H'"
    unfolding keysFor_def by blast

lemma keysFor_UN [simp]: "keysFor (\<Union>i \<in>A. H i) = (\<Union>i \<in>A. keysFor (H i))"
    unfolding keysFor_def by blast

text\<open>Monotonicity\<close>
lemma keysFor_mono: "G \<subseteq> H \<Longrightarrow> keysFor(G) \<subseteq> keysFor(H)"
  unfolding keysFor_def by blast

lemma keysFor_insert_Agent [simp]: "keysFor (insert (Agent A) H) = keysFor H"
  unfolding keysFor_def by auto

lemma keysFor_insert_Nonce [simp]: "keysFor (insert (Nonce N) H) = keysFor H"
  unfolding keysFor_def by auto

lemma keysFor_insert_Number [simp]: "keysFor (insert (Number N) H) = keysFor H"
  unfolding keysFor_def by auto

lemma keysFor_insert_Key [simp]: "keysFor (insert (Key K) H) = keysFor H"
  unfolding keysFor_def by auto

lemma keysFor_insert_Hash [simp]: "keysFor (insert (Hash X) H) = keysFor H"
  unfolding keysFor_def by auto

lemma keysFor_insert_MPair [simp]: "keysFor (insert \<lbrace>X,Y\<rbrace> H) = keysFor H"
  unfolding keysFor_def by auto

lemma keysFor_insert_Crypt [simp]: 
    "keysFor (insert (Crypt K X) H) = insert (invKey K) (keysFor H)"
  unfolding keysFor_def by auto

lemma keysFor_image_Key [simp]: "keysFor (Key`E) = {}"
  unfolding keysFor_def by auto

lemma Crypt_imp_invKey_keysFor: "Crypt K X \<in> H \<Longrightarrow> invKey K \<in> keysFor H"
  unfolding keysFor_def by blast


subsection\<open>Inductive relation "parts"\<close>

lemma MPair_parts:
  "\<lbrakk>\<lbrace>X,Y\<rbrace> \<in> parts H;        
         \<lbrakk>X \<in> parts H; Y \<in> parts H\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (blast dest: parts.Fst parts.Snd) 

declare MPair_parts [elim!]  parts.Body [dest!]
text\<open>NB These two rules are UNSAFE in the formal sense, as they discard the
     compound message.  They work well on THIS FILE.  
  \<open>MPair_parts\<close> is left as SAFE because it speeds up proofs.
  The Crypt rule is normally kept UNSAFE to avoid breaking up certificates.\<close>

lemma parts_increasing: "H \<subseteq> parts(H)"
  by blast

lemmas parts_insertI = subset_insertI [THEN parts_mono, THEN subsetD]

lemma parts_empty_aux: "X \<in> parts{} \<Longrightarrow> False"
  by (induction rule: parts.induct) (blast+)

lemma parts_empty [simp]: "parts{} = {}"
  using parts_empty_aux by blast

lemma parts_emptyE [elim!]: "X \<in> parts{} \<Longrightarrow> P"
  by simp

text\<open>WARNING: loops if H = {Y}, therefore must not be repeated!\<close>
lemma parts_singleton: "X \<in> parts H \<Longrightarrow> \<exists>Y \<in>H. X \<in> parts {Y}"
  by (erule parts.induct, fast+)


subsubsection\<open>Unions\<close>

lemma parts_Un [simp]: "parts(G \<union> H) = parts(G) \<union> parts(H)"
proof -
  have "X \<in> parts (G \<union> H) \<Longrightarrow> X \<in> parts G \<union> parts H" for X
    by (induction rule: parts.induct) auto
  then show ?thesis
    by (simp add: order_antisym parts_mono subsetI)
qed

lemma parts_insert: "parts (insert X H) = parts {X} \<union> parts H"
  by (metis insert_is_Un parts_Un)

text\<open>TWO inserts to avoid looping.  This rewrite is better than nothing.
  But its behaviour can be strange.\<close>
lemma parts_insert2:
  "parts (insert X (insert Y H)) = parts {X} \<union> parts {Y} \<union> parts H"
  by (metis Un_commute Un_empty_right Un_insert_right insert_is_Un parts_Un)

lemma parts_image [simp]:
  "parts (f ` A) = (\<Union>x \<in>A. parts {f x})"
  apply auto
   apply (metis (mono_tags, opaque_lifting) image_iff parts_singleton)
  apply (metis empty_subsetI image_eqI insert_absorb insert_subset parts_mono)
  done

text\<open>Added to simplify arguments to parts, analz and synth.\<close>

text\<open>This allows \<open>blast\<close> to simplify occurrences of 
  \<^term>\<open>parts(G\<union>H)\<close> in the assumption.\<close>
lemmas in_parts_UnE = parts_Un [THEN equalityD1, THEN subsetD, THEN UnE] 
declare in_parts_UnE [elim!]


lemma parts_insert_subset: "insert X (parts H) \<subseteq> parts(insert X H)"
  by (blast intro: parts_mono [THEN [2] rev_subsetD])

subsubsection\<open>Idempotence and transitivity\<close>

lemma parts_partsD [dest!]: "X \<in> parts (parts H) \<Longrightarrow> X \<in> parts H"
  by (erule parts.induct, blast+)

lemma parts_idem [simp]: "parts (parts H) = parts H"
  by blast

lemma parts_subset_iff [simp]: "(parts G \<subseteq> parts H) = (G \<subseteq> parts H)"
  by (metis parts_idem parts_increasing parts_mono subset_trans)

lemma parts_trans: "\<lbrakk>X \<in> parts G;  G \<subseteq> parts H\<rbrakk> \<Longrightarrow> X \<in> parts H"
  by (metis parts_subset_iff subsetD)

text\<open>Cut\<close>
lemma parts_cut:
  "\<lbrakk>Y \<in> parts (insert X G);  X \<in> parts H\<rbrakk> \<Longrightarrow> Y \<in> parts (G \<union> H)" 
  by (blast intro: parts_trans) 

lemma parts_cut_eq [simp]: "X \<in> parts H \<Longrightarrow> parts (insert X H) = parts H"
  by (metis insert_absorb parts_idem parts_insert)


subsubsection\<open>Rewrite rules for pulling out atomic messages\<close>

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
  "parts (insert (Crypt K X) H) = insert (Crypt K X) (parts (insert X H))"
proof -
  have "Y \<in> parts (insert (Crypt K X) H) \<Longrightarrow> Y \<in> insert (Crypt K X) (parts (insert X H))" for Y
    by (induction rule: parts.induct) auto
  then show ?thesis
    by (smt (verit) insertI1 insert_commute parts.simps parts_cut_eq parts_insert_eq_I)
qed

lemma parts_insert_MPair [simp]:
  "parts (insert \<lbrace>X,Y\<rbrace> H) = insert \<lbrace>X,Y\<rbrace> (parts (insert X (insert Y H)))"
proof -
  have "Z \<in> parts (insert \<lbrace>X, Y\<rbrace> H) \<Longrightarrow> Z \<in> insert \<lbrace>X, Y\<rbrace> (parts (insert X (insert Y H)))" for Z
    by (induction rule: parts.induct) auto
  then show ?thesis
    by (smt (verit) insertI1 insert_commute parts.simps parts_cut_eq parts_insert_eq_I)
qed

lemma parts_image_Key [simp]: "parts (Key`N) = Key`N"
  by auto

text\<open>In any message, there is an upper bound N on its greatest nonce.\<close>
lemma msg_Nonce_supply: "\<exists>N. \<forall>n. N\<le>n \<longrightarrow> Nonce n \<notin> parts {msg}"
proof (induct msg)
  case (Nonce n)
  show ?case
    by simp (metis Suc_n_not_le_n)
next
  case (MPair X Y)
  then show ?case \<comment> \<open>metis works out the necessary sum itself!\<close>
    by (simp add: parts_insert2) (metis le_trans nat_le_linear)
qed auto

subsection\<open>Inductive relation "analz"\<close>

text\<open>Inductive definition of "analz" -- what can be broken down from a set of
    messages, including keys.  A form of downward closure.  Pairs can
    be taken apart; messages decrypted with known keys.\<close>

inductive_set
  analz :: "msg set \<Rightarrow> msg set"
  for H :: "msg set"
  where
    Inj [intro,simp]: "X \<in> H \<Longrightarrow> X \<in> analz H"
  | Fst:     "\<lbrace>X,Y\<rbrace> \<in> analz H \<Longrightarrow> X \<in> analz H"
  | Snd:     "\<lbrace>X,Y\<rbrace> \<in> analz H \<Longrightarrow> Y \<in> analz H"
  | Decrypt [dest]: 
    "\<lbrakk>Crypt K X \<in> analz H; Key(invKey K) \<in> analz H\<rbrakk> \<Longrightarrow> X \<in> analz H"


text\<open>Monotonicity; Lemma 1 of Lowe's paper\<close>
lemma analz_mono_aux: "\<lbrakk>G \<subseteq> H; X \<in> analz G\<rbrakk> \<Longrightarrow> X \<in> analz H"
  by (erule analz.induct) (auto dest: analz.Fst analz.Snd) 

lemma analz_mono: "G\<subseteq>H \<Longrightarrow> analz(G) \<subseteq> analz(H)"
  using analz_mono_aux by blast

text\<open>Making it safe speeds up proofs\<close>
lemma MPair_analz [elim!]:
  "\<lbrakk>\<lbrace>X,Y\<rbrace> \<in> analz H;        
    \<lbrakk>X \<in> analz H; Y \<in> analz H\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (blast dest: analz.Fst analz.Snd)

lemma analz_increasing: "H \<subseteq> analz(H)"
  by blast

lemma analz_into_parts: "X \<in> analz H \<Longrightarrow> X \<in> parts H"
  by (erule analz.induct) auto

lemma analz_subset_parts: "analz H \<subseteq> parts H"
  using analz_into_parts by blast

lemma analz_parts [simp]: "analz (parts H) = parts H"
  using analz_subset_parts by blast

lemmas not_parts_not_analz = analz_subset_parts [THEN contra_subsetD]


lemma parts_analz [simp]: "parts (analz H) = parts H"
  by (metis analz_increasing analz_subset_parts parts_idem parts_mono subset_antisym)

lemmas analz_insertI = subset_insertI [THEN analz_mono, THEN [2] rev_subsetD]

subsubsection\<open>General equational properties\<close>

lemma analz_empty [simp]: "analz{} = {}"
  using analz_parts by fastforce

text\<open>Converse fails: we can analz more from the union than from the 
  separate parts, as a key in one might decrypt a message in the other\<close>
lemma analz_Un: "analz(G) \<union> analz(H) \<subseteq> analz(G \<union> H)"
  by (intro Un_least analz_mono Un_upper1 Un_upper2)

lemma analz_insert: "insert X (analz H) \<subseteq> analz(insert X H)"
  by (blast intro: analz_mono [THEN [2] rev_subsetD])

subsubsection\<open>Rewrite rules for pulling out atomic messages\<close>

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

text\<open>Can only pull out Keys if they are not needed to decrypt the rest\<close>
lemma analz_insert_Key [simp]: 
  "K \<notin> keysFor (analz H) \<Longrightarrow>   
          analz (insert (Key K) H) = insert (Key K) (analz H)"
  unfolding keysFor_def
  apply (rule analz_insert_eq_I) 
  apply (erule analz.induct, auto) 
  done

lemma analz_insert_MPair [simp]:
  "analz (insert \<lbrace>X,Y\<rbrace> H) = insert \<lbrace>X,Y\<rbrace> (analz (insert X (insert Y H)))"
proof -
  have "Z \<in> analz (insert \<lbrace>X, Y\<rbrace> H) \<Longrightarrow> Z \<in> insert \<lbrace>X, Y\<rbrace> (analz (insert X (insert Y H)))" for Z
    by (induction rule: analz.induct) auto
  moreover have "Z \<in> analz (insert X (insert Y H)) \<Longrightarrow> Z \<in> analz (insert \<lbrace>X, Y\<rbrace> H)" for Z
    by (induction rule: analz.induct) (use analz.Inj in blast)+
  ultimately show ?thesis
    by auto
qed

text\<open>Can pull out encrypted message if the Key is not known\<close>
lemma analz_insert_Crypt:
  "Key (invKey K) \<notin> analz H 
      \<Longrightarrow> analz (insert (Crypt K X) H) = insert (Crypt K X) (analz H)"
  apply (rule analz_insert_eq_I) 
  apply (erule analz.induct, auto) 
  done

lemma analz_insert_Decrypt:
  assumes "Key (invKey K) \<in> analz H"
  shows "analz (insert (Crypt K X) H) = insert (Crypt K X) (analz (insert X H))"
proof -
  have "Y \<in> analz (insert (Crypt K X) H) \<Longrightarrow> Y \<in> insert (Crypt K X) (analz (insert X H))" for Y
    by (induction rule: analz.induct) auto
  moreover
  have "Y \<in> analz (insert X H) \<Longrightarrow> Y \<in> analz (insert (Crypt K X) H)" for Y
  proof (induction rule: analz.induct)
    case (Inj X)
    then show ?case
      by (metis analz.Decrypt analz.Inj analz_insertI assms insert_iff)
  qed auto
  ultimately show ?thesis
    by auto
qed

text\<open>Case analysis: either the message is secure, or it is not! Effective,
but can cause subgoals to blow up! Use with \<open>if_split\<close>; apparently
\<open>split_tac\<close> does not cope with patterns such as \<^term>\<open>analz (insert
(Crypt K X) H)\<close>\<close> 
lemma analz_Crypt_if [simp]:
  "analz (insert (Crypt K X) H) =                 
          (if (Key (invKey K) \<in> analz H)                 
           then insert (Crypt K X) (analz (insert X H))  
           else insert (Crypt K X) (analz H))"
  by (simp add: analz_insert_Crypt analz_insert_Decrypt)


text\<open>This rule supposes "for the sake of argument" that we have the key.\<close>
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


subsubsection\<open>Idempotence and transitivity\<close>

lemma analz_analzD [dest!]: "X \<in> analz (analz H) \<Longrightarrow> X \<in> analz H"
  by (erule analz.induct, blast+)

lemma analz_idem [simp]: "analz (analz H) = analz H"
  by blast

lemma analz_subset_iff [simp]: "(analz G \<subseteq> analz H) = (G \<subseteq> analz H)"
  by (metis analz_idem analz_increasing analz_mono subset_trans)

lemma analz_trans: "\<lbrakk>X \<in> analz G;  G \<subseteq> analz H\<rbrakk> \<Longrightarrow> X \<in> analz H"
  by (drule analz_mono, blast)

text\<open>Cut; Lemma 2 of Lowe\<close>
lemma analz_cut: "\<lbrakk>Y \<in> analz (insert X H);  X \<in> analz H\<rbrakk> \<Longrightarrow> Y \<in> analz H"
  by (erule analz_trans, blast)

(*Cut can be proved easily by induction on
   "Y: analz (insert X H) \<Longrightarrow> X: analz H \<longrightarrow> Y: analz H"
*)

text\<open>This rewrite rule helps in the simplification of messages that involve
  the forwarding of unknown components (X).  Without it, removing occurrences
  of X can be very complicated.\<close>
lemma analz_insert_eq: "X \<in> analz H \<Longrightarrow> analz (insert X H) = analz H"
  by (metis analz_cut analz_insert_eq_I insert_absorb)


text\<open>A congruence rule for "analz"\<close>

lemma analz_subset_cong:
  "\<lbrakk>analz G \<subseteq> analz G'; analz H \<subseteq> analz H'\<rbrakk> 
      \<Longrightarrow> analz (G \<union> H) \<subseteq> analz (G' \<union> H')"
  by (metis Un_mono analz_Un analz_subset_iff subset_trans)

lemma analz_cong:
  "\<lbrakk>analz G = analz G'; analz H = analz H'\<rbrakk> 
      \<Longrightarrow> analz (G \<union> H) = analz (G' \<union> H')"
  by (intro equalityI analz_subset_cong, simp_all) 

lemma analz_insert_cong:
  "analz H = analz H' \<Longrightarrow> analz(insert X H) = analz(insert X H')"
  by (force simp only: insert_def intro!: analz_cong)

text\<open>If there are no pairs or encryptions then analz does nothing\<close>
lemma analz_trivial:
  "\<lbrakk>\<forall>X Y. \<lbrace>X,Y\<rbrace> \<notin> H;  \<forall>X K. Crypt K X \<notin> H\<rbrakk> \<Longrightarrow> analz H = H"
  apply safe
   apply (erule analz.induct, blast+)
  done


subsection\<open>Inductive relation "synth"\<close>

text\<open>Inductive definition of "synth" -- what can be built up from a set of
    messages.  A form of upward closure.  Pairs can be built, messages
    encrypted with known keys.  Agent names are public domain.
    Numbers can be guessed, but Nonces cannot be.\<close>

inductive_set
  synth :: "msg set => msg set"
  for H :: "msg set"
  where
    Inj    [intro]:   "X \<in> H \<Longrightarrow> X \<in> synth H"
  | Agent  [intro]:   "Agent agt \<in> synth H"
  | Number [intro]:   "Number n  \<in> synth H"
  | Hash   [intro]:   "X \<in> synth H \<Longrightarrow> Hash X \<in> synth H"
  | MPair  [intro]:   "\<lbrakk>X \<in> synth H;  Y \<in> synth H\<rbrakk> \<Longrightarrow> \<lbrace>X,Y\<rbrace> \<in> synth H"
  | Crypt  [intro]:   "\<lbrakk>X \<in> synth H;  Key(K) \<in> H\<rbrakk> \<Longrightarrow> Crypt K X \<in> synth H"

text\<open>Monotonicity\<close>
lemma synth_mono: "G\<subseteq>H \<Longrightarrow> synth(G) \<subseteq> synth(H)"
  by (auto, erule synth.induct, auto)  

text\<open>NO \<open>Agent_synth\<close>, as any Agent name can be synthesized.  
  The same holds for \<^term>\<open>Number\<close>\<close>

inductive_simps synth_simps [iff]:
  "Nonce n \<in> synth H"
  "Key K \<in> synth H"
  "Hash X \<in> synth H"
  "\<lbrace>X,Y\<rbrace> \<in> synth H"
  "Crypt K X \<in> synth H"

lemma synth_increasing: "H \<subseteq> synth(H)"
  by blast

subsubsection\<open>Unions\<close>

text\<open>Converse fails: we can synth more from the union than from the 
  separate parts, building a compound message using elements of each.\<close>
lemma synth_Un: "synth(G) \<union> synth(H) \<subseteq> synth(G \<union> H)"
  by (intro Un_least synth_mono Un_upper1 Un_upper2)

lemma synth_insert: "insert X (synth H) \<subseteq> synth(insert X H)"
  by (blast intro: synth_mono [THEN [2] rev_subsetD])

subsubsection\<open>Idempotence and transitivity\<close>

lemma synth_synthD [dest!]: "X \<in> synth (synth H) \<Longrightarrow> X \<in> synth H"
  by (erule synth.induct, auto)

lemma synth_idem: "synth (synth H) = synth H"
  by blast

lemma synth_subset_iff [simp]: "(synth G \<subseteq> synth H) = (G \<subseteq> synth H)"
  by (metis subset_trans synth_idem synth_increasing synth_mono)

lemma synth_trans: "\<lbrakk>X \<in> synth G;  G \<subseteq> synth H\<rbrakk> \<Longrightarrow> X \<in> synth H"
  by (drule synth_mono, blast)

text\<open>Cut; Lemma 2 of Lowe\<close>
lemma synth_cut: "\<lbrakk>Y \<in> synth (insert X H);  X \<in> synth H\<rbrakk> \<Longrightarrow> Y \<in> synth H"
  by (erule synth_trans, blast)

lemma Crypt_synth_eq [simp]:
  "Key K \<notin> H \<Longrightarrow> (Crypt K X \<in> synth H) = (Crypt K X \<in> H)"
  by blast


lemma keysFor_synth [simp]: 
  "keysFor (synth H) = keysFor H \<union> invKey`{K. Key K \<in> H}"
  unfolding keysFor_def by blast


subsubsection\<open>Combinations of parts, analz and synth\<close>

lemma parts_synth [simp]: "parts (synth H) = parts H \<union> synth H"
proof -
  have "X \<in> parts (synth H) \<Longrightarrow> X \<in> parts H \<union> synth H" for X
    by (induction X rule: parts.induct) (auto intro: parts.intros)
  then show ?thesis
    by (meson parts_increasing parts_mono subsetI antisym sup_least synth_increasing)
qed

lemma analz_analz_Un [simp]: "analz (analz G \<union> H) = analz (G \<union> H)"
  using analz_cong by blast

lemma analz_synth_Un [simp]: "analz (synth G \<union> H) = analz (G \<union> H) \<union> synth G"
proof -
  have "X \<in> analz (synth G \<union> H) \<Longrightarrow> X \<in> analz (G \<union> H) \<union> synth G" for X
    by (induction X rule: analz.induct) (auto intro: analz.intros)
  then show ?thesis
    by (metis analz_subset_iff le_sup_iff subsetI subset_antisym synth_subset_iff)
qed

lemma analz_synth [simp]: "analz (synth H) = analz H \<union> synth H"
  by (metis Un_empty_right analz_synth_Un)


subsubsection\<open>For reasoning about the Fake rule in traces\<close>

lemma parts_insert_subset_Un: "X \<in> G \<Longrightarrow> parts(insert X H) \<subseteq> parts G \<union> parts H"
  by (metis UnCI Un_upper2 insert_subset parts_Un parts_mono)

text\<open>More specifically for Fake. See also \<open>Fake_parts_sing\<close> below\<close>
lemma Fake_parts_insert:
  "X \<in> synth (analz H) \<Longrightarrow>  
      parts (insert X H) \<subseteq> synth (analz H) \<union> parts H"
  by (metis Un_commute analz_increasing insert_subset parts_analz parts_mono 
      parts_synth synth_mono synth_subset_iff)

lemma Fake_parts_insert_in_Un:
  "\<lbrakk>Z \<in> parts (insert X H);  X \<in> synth (analz H)\<rbrakk> 
      \<Longrightarrow> Z \<in> synth (analz H) \<union> parts H"
  by (metis Fake_parts_insert subsetD)

text\<open>\<^term>\<open>H\<close> is sometimes \<^term>\<open>Key ` KK \<union> spies evs\<close>, so can't put 
  \<^term>\<open>G=H\<close>.\<close>
lemma Fake_analz_insert:
  "X \<in> synth (analz G) \<Longrightarrow>  
      analz (insert X H) \<subseteq> synth (analz G) \<union> analz (G \<union> H)"
  by (metis UnCI Un_commute Un_upper1 analz_analz_Un analz_mono analz_synth_Un insert_subset)

lemma analz_conj_parts [simp]:
  "(X \<in> analz H \<and> X \<in> parts H) = (X \<in> analz H)"
  by (blast intro: analz_subset_parts [THEN subsetD])

lemma analz_disj_parts [simp]:
  "(X \<in> analz H | X \<in> parts H) = (X \<in> parts H)"
  by (blast intro: analz_subset_parts [THEN subsetD])

text\<open>Without this equation, other rules for synth and analz would yield
  redundant cases\<close>
lemma MPair_synth_analz [iff]:
  "\<lbrace>X,Y\<rbrace> \<in> synth (analz H) \<longleftrightarrow> X \<in> synth (analz H) \<and> Y \<in> synth (analz H)"
  by blast

lemma Crypt_synth_analz:
  "\<lbrakk>Key K \<in> analz H;  Key (invKey K) \<in> analz H\<rbrakk>  
       \<Longrightarrow> (Crypt K X \<in> synth (analz H)) = (X \<in> synth (analz H))"
  by blast

lemma Hash_synth_analz [simp]:
  "X \<notin> synth (analz H)  
      \<Longrightarrow> (Hash\<lbrace>X,Y\<rbrace> \<in> synth (analz H)) = (Hash\<lbrace>X,Y\<rbrace> \<in> analz H)"
  by blast


subsection\<open>HPair: a combination of Hash and MPair\<close>

subsubsection\<open>Freeness\<close>

lemma Agent_neq_HPair: "Agent A \<noteq> Hash[X] Y"
  unfolding HPair_def by simp

lemma Nonce_neq_HPair: "Nonce N \<noteq> Hash[X] Y"
  unfolding HPair_def by simp

lemma Number_neq_HPair: "Number N \<noteq> Hash[X] Y"
  unfolding HPair_def by simp

lemma Key_neq_HPair: "Key K \<noteq> Hash[X] Y"
  unfolding HPair_def by simp

lemma Hash_neq_HPair: "Hash Z \<noteq> Hash[X] Y"
  unfolding HPair_def by simp

lemma Crypt_neq_HPair: "Crypt K X' \<noteq> Hash[X] Y"
  unfolding HPair_def by simp

lemmas HPair_neqs = Agent_neq_HPair Nonce_neq_HPair Number_neq_HPair 
  Key_neq_HPair Hash_neq_HPair Crypt_neq_HPair

declare HPair_neqs [iff]
declare HPair_neqs [symmetric, iff]

lemma HPair_eq [iff]: "(Hash[X'] Y' = Hash[X] Y) = (X' = X \<and> Y'=Y)"
  by (simp add: HPair_def)

lemma MPair_eq_HPair [iff]:
  "(\<lbrace>X',Y'\<rbrace> = Hash[X] Y) = (X' = Hash\<lbrace>X,Y\<rbrace> \<and> Y'=Y)"
  by (simp add: HPair_def)

lemma HPair_eq_MPair [iff]:
  "(Hash[X] Y = \<lbrace>X',Y'\<rbrace>) = (X' = Hash\<lbrace>X,Y\<rbrace> \<and> Y'=Y)"
  by (auto simp add: HPair_def)


subsubsection\<open>Specialized laws, proved in terms of those for Hash and MPair\<close>

lemma keysFor_insert_HPair [simp]: "keysFor (insert (Hash[X] Y) H) = keysFor H"
  by (simp add: HPair_def)

lemma parts_insert_HPair [simp]: 
  "parts (insert (Hash[X] Y) H) =  
     insert (Hash[X] Y) (insert (Hash\<lbrace>X,Y\<rbrace>) (parts (insert Y H)))"
  by (simp add: HPair_def)

lemma analz_insert_HPair [simp]: 
  "analz (insert (Hash[X] Y) H) =  
     insert (Hash[X] Y) (insert (Hash\<lbrace>X,Y\<rbrace>) (analz (insert Y H)))"
  by (simp add: HPair_def)

lemma HPair_synth_analz [simp]:
  "X \<notin> synth (analz H)  
    \<Longrightarrow> (Hash[X] Y \<in> synth (analz H)) =  
        (Hash \<lbrace>X, Y\<rbrace> \<in> analz H \<and> Y \<in> synth (analz H))"
  by (auto simp add: HPair_def)


text\<open>We do NOT want Crypt... messages broken up in protocols!!\<close>
declare parts.Body [rule del]


text\<open>Rewrites to push in Key and Crypt messages, so that other messages can
    be pulled out using the \<open>analz_insert\<close> rules\<close>

lemmas pushKeys =
  insert_commute [of "Key K" "Agent C"]
  insert_commute [of "Key K" "Nonce N"]
  insert_commute [of "Key K" "Number N"]
  insert_commute [of "Key K" "Hash X"]
  insert_commute [of "Key K" "MPair X Y"]
  insert_commute [of "Key K" "Crypt X K'"]
  for K C N X Y K'

lemmas pushCrypts =
  insert_commute [of "Crypt X K" "Agent C"]
  insert_commute [of "Crypt X K" "Agent C"]
  insert_commute [of "Crypt X K" "Nonce N"]
  insert_commute [of "Crypt X K" "Number N"]
  insert_commute [of "Crypt X K" "Hash X'"]
  insert_commute [of "Crypt X K" "MPair X' Y"]
  for X K C N X' Y

text\<open>Cannot be added with \<open>[simp]\<close> -- messages should not always be
  re-ordered.\<close>
lemmas pushes = pushKeys pushCrypts


subsection\<open>The set of key-free messages\<close>

(*Note that even the encryption of a key-free message remains key-free.
  This concept is valuable because of the theorem analz_keyfree_into_Un, proved below. *)

inductive_set
  keyfree :: "msg set"
  where
    Agent:  "Agent A \<in> keyfree"
  | Number: "Number N \<in> keyfree"
  | Nonce:  "Nonce N \<in> keyfree"
  | Hash:   "Hash X \<in> keyfree"
  | MPair:  "\<lbrakk>X \<in> keyfree;  Y \<in> keyfree\<rbrakk> \<Longrightarrow> \<lbrace>X,Y\<rbrace> \<in> keyfree"
  | Crypt:  "\<lbrakk>X \<in> keyfree\<rbrakk> \<Longrightarrow> Crypt K X \<in> keyfree"


declare keyfree.intros [intro] 

inductive_cases keyfree_KeyE: "Key K \<in> keyfree"
inductive_cases keyfree_MPairE: "\<lbrace>X,Y\<rbrace> \<in> keyfree"
inductive_cases keyfree_CryptE: "Crypt K X \<in> keyfree"

lemma parts_keyfree: "parts (keyfree) \<subseteq> keyfree"
  by (clarify, erule parts.induct, auto elim!: keyfree_KeyE keyfree_MPairE keyfree_CryptE)

(*The key-free part of a set of messages can be removed from the scope of the analz operator.*)
lemma analz_keyfree_into_Un: "\<lbrakk>X \<in> analz (G \<union> H); G \<subseteq> keyfree\<rbrakk> \<Longrightarrow> X \<in> parts G \<union> analz H"
proof (induction rule: analz.induct)
  case (Decrypt K X)
  then show ?case
    by (metis Un_iff analz.Decrypt in_mono keyfree_KeyE parts.Body parts_keyfree parts_mono)
qed (auto dest: parts.Body)

subsection\<open>Tactics useful for many protocol proofs\<close>
ML
  \<open>
(*Analysis of Fake cases.  Also works for messages that forward unknown parts,
  but this application is no longer necessary if analz_insert_eq is used.
  DEPENDS UPON "X" REFERRING TO THE FRADULENT MESSAGE *)

fun impOfSubs th = th RSN (2, @{thm rev_subsetD})

(*Apply rules to break down assumptions of the form
  Y \<in> parts(insert X H)  and  Y \<in> analz(insert X H)
*)
fun Fake_insert_tac ctxt = 
    dresolve_tac ctxt [impOfSubs @{thm Fake_analz_insert},
                  impOfSubs @{thm Fake_parts_insert}] THEN'
    eresolve_tac ctxt [asm_rl, @{thm synth.Inj}];

fun Fake_insert_simp_tac ctxt i = 
  REPEAT (Fake_insert_tac ctxt i) THEN asm_full_simp_tac ctxt i;

fun atomic_spy_analz_tac ctxt =
  SELECT_GOAL
   (Fake_insert_simp_tac ctxt 1 THEN
    IF_UNSOLVED
      (Blast.depth_tac
        (ctxt addIs [@{thm analz_insertI}, impOfSubs @{thm analz_subset_parts}]) 4 1));

fun spy_analz_tac ctxt i =
  DETERM
   (SELECT_GOAL
     (EVERY 
      [  (*push in occurrences of X...*)
       (REPEAT o CHANGED)
         (Rule_Insts.res_inst_tac ctxt [((("x", 1), Position.none), "X")] []
           (@{thm insert_commute} RS ssubst) 1),
       (*...allowing further simplifications*)
       simp_tac ctxt 1,
       REPEAT (FIRSTGOAL (resolve_tac ctxt [allI,impI,notI,conjI,iffI])),
       DEPTH_SOLVE (atomic_spy_analz_tac ctxt 1)]) i);
\<close>

text\<open>By default only \<open>o_apply\<close> is built-in.  But in the presence of
eta-expansion this means that some terms displayed as \<^term>\<open>f o g\<close> will be
rewritten, and others will not!\<close>
declare o_def [simp]


lemma Crypt_notin_image_Key [simp]: "Crypt K X \<notin> Key ` A"
  by auto

lemma Hash_notin_image_Key [simp] :"Hash X \<notin> Key ` A"
  by auto

lemma synth_analz_mono: "G\<subseteq>H \<Longrightarrow> synth (analz(G)) \<subseteq> synth (analz(H))"
  by (iprover intro: synth_mono analz_mono) 

lemma Fake_analz_eq [simp]:
  "X \<in> synth(analz H) \<Longrightarrow> synth (analz (insert X H)) = synth (analz H)"
  by (metis Fake_analz_insert Un_absorb Un_absorb1 Un_commute 
      subset_insertI synth_analz_mono synth_increasing synth_subset_iff)

text\<open>Two generalizations of \<open>analz_insert_eq\<close>\<close>
lemma gen_analz_insert_eq [rule_format]:
  "X \<in> analz H \<Longrightarrow> \<forall>G. H \<subseteq> G \<longrightarrow> analz (insert X G) = analz G"
  by (blast intro: analz_cut analz_insertI analz_mono [THEN [2] rev_subsetD])

lemma synth_analz_insert_eq:
  "\<lbrakk>X \<in> synth (analz H); H \<subseteq> G\<rbrakk>
      \<Longrightarrow> (Key K \<in> analz (insert X G)) \<longleftrightarrow> (Key K \<in> analz G)"
proof (induction arbitrary: G rule: synth.induct)
  case (Inj X)
  then show ?case
    using gen_analz_insert_eq by presburger 
qed (simp_all add: subset_eq)

lemma Fake_parts_sing:
  "X \<in> synth (analz H) \<Longrightarrow> parts{X} \<subseteq> synth (analz H) \<union> parts H"
  by (metis Fake_parts_insert empty_subsetI insert_mono parts_mono subset_trans)

lemmas Fake_parts_sing_imp_Un = Fake_parts_sing [THEN [2] rev_subsetD]

method_setup spy_analz = \<open>
    Scan.succeed (SIMPLE_METHOD' o spy_analz_tac)\<close>
  "for proving the Fake case when analz is involved"

method_setup atomic_spy_analz = \<open>
    Scan.succeed (SIMPLE_METHOD' o atomic_spy_analz_tac)\<close>
  "for debugging spy_analz"

method_setup Fake_insert_simp = \<open>
    Scan.succeed (SIMPLE_METHOD' o Fake_insert_simp_tac)\<close>
  "for debugging spy_analz"

end
