(*  Title:      HOL/Auth/SET/MessageSET
    ID:         $Id$
    Authors:     Giampaolo Bella, Fabio Massacci, Lawrence C Paulson
*)

header{*The Message Theory, Modified for SET*}

theory MessageSET = NatPair:

subsection{*General Lemmas*}

text{*Needed occasionally with @{text spy_analz_tac}, e.g. in
     @{text analz_insert_Key_newK}*}

lemma Un_absorb3 [simp] : "A \<union> (B \<union> A) = B \<union> A"
by blast

text{*Collapses redundant cases in the huge protocol proofs*}
lemmas disj_simps = disj_comms disj_left_absorb disj_assoc 

text{*Effective with assumptions like @{term "K \<notin> range pubK"} and 
   @{term "K \<notin> invKey`range pubK"}*}
lemma notin_image_iff: "(y \<notin> f`I) = (\<forall>i\<in>I. f i \<noteq> y)"
by blast

text{*Effective with the assumption @{term "KK \<subseteq> - (range(invKey o pubK))"} *}
lemma disjoint_image_iff: "(A <= - (f`I)) = (\<forall>i\<in>I. f i \<notin> A)"
by blast



types
  key = nat

consts
  all_symmetric :: bool        --{*true if all keys are symmetric*}
  invKey        :: "key=>key"  --{*inverse of a symmetric key*}

specification (invKey)
  invKey [simp]: "invKey (invKey K) = K"
  invKey_symmetric: "all_symmetric --> invKey = id"
    by (rule exI [of _ id], auto)


text{*The inverse of a symmetric key is itself; that of a public key
      is the private key and vice versa*}

constdefs
  symKeys :: "key set"
  "symKeys == {K. invKey K = K}"

text{*Agents. We allow any number of certification authorities, cardholders
            merchants, and payment gateways.*}
datatype
  agent = CA nat | Cardholder nat | Merchant nat | PG nat | Spy

text{*Messages*}
datatype
     msg = Agent  agent	    --{*Agent names*}
         | Number nat       --{*Ordinary integers, timestamps, ...*}
         | Nonce  nat       --{*Unguessable nonces*}
         | Pan    nat       --{*Unguessable Primary Account Numbers (??)*}
         | Key    key       --{*Crypto keys*}
	 | Hash   msg       --{*Hashing*}
	 | MPair  msg msg   --{*Compound messages*}
	 | Crypt  key msg   --{*Encryption, public- or shared-key*}


(*Concrete syntax: messages appear as {|A,B,NA|}, etc...*)
syntax
  "@MTuple"      :: "['a, args] => 'a * 'b"       ("(2{|_,/ _|})")

syntax (xsymbols)
  "@MTuple"      :: "['a, args] => 'a * 'b"       ("(2\<lbrace>_,/ _\<rbrace>)")

translations
  "{|x, y, z|}"   == "{|x, {|y, z|}|}"
  "{|x, y|}"      == "MPair x y"


constdefs
  nat_of_agent :: "agent => nat"
   "nat_of_agent == agent_case (curry nat2_to_nat 0)
			       (curry nat2_to_nat 1)
			       (curry nat2_to_nat 2)
			       (curry nat2_to_nat 3)
			       (nat2_to_nat (4,0))"
    --{*maps each agent to a unique natural number, for specifications*}

text{*The function is indeed injective*}
lemma inj_nat_of_agent: "inj nat_of_agent"
by (simp add: nat_of_agent_def inj_on_def curry_def
              nat2_to_nat_inj [THEN inj_eq]  split: agent.split) 


constdefs
  (*Keys useful to decrypt elements of a message set*)
  keysFor :: "msg set => key set"
  "keysFor H == invKey ` {K. \<exists>X. Crypt K X \<in> H}"

subsubsection{*Inductive definition of all "parts" of a message.*}

consts  parts   :: "msg set => msg set"
inductive "parts H"
  intros
    Inj [intro]:               "X \<in> H ==> X \<in> parts H"
    Fst:         "{|X,Y|}   \<in> parts H ==> X \<in> parts H"
    Snd:         "{|X,Y|}   \<in> parts H ==> Y \<in> parts H"
    Body:        "Crypt K X \<in> parts H ==> X \<in> parts H"


(*Monotonicity*)
lemma parts_mono: "G<=H ==> parts(G) <= parts(H)"
apply auto
apply (erule parts.induct)
apply (auto dest: Fst Snd Body)
done


subsubsection{*Inverse of keys*}

(*Equations hold because constructors are injective; cannot prove for all f*)
lemma Key_image_eq [simp]: "(Key x \<in> Key`A) = (x\<in>A)"
by auto

lemma Nonce_Key_image_eq [simp]: "(Nonce x \<notin> Key`A)"
by auto

lemma Cardholder_image_eq [simp]: "(Cardholder x \<in> Cardholder`A) = (x \<in> A)"
by auto

lemma CA_image_eq [simp]: "(CA x \<in> CA`A) = (x \<in> A)"
by auto

lemma Pan_image_eq [simp]: "(Pan x \<in> Pan`A) = (x \<in> A)"
by auto

lemma Pan_Key_image_eq [simp]: "(Pan x \<notin> Key`A)"
by auto

lemma Nonce_Pan_image_eq [simp]: "(Nonce x \<notin> Pan`A)"
by auto

lemma invKey_eq [simp]: "(invKey K = invKey K') = (K=K')"
apply safe
apply (drule_tac f = invKey in arg_cong, simp)
done


subsection{*keysFor operator*}

lemma keysFor_empty [simp]: "keysFor {} = {}"
by (unfold keysFor_def, blast)

lemma keysFor_Un [simp]: "keysFor (H \<union> H') = keysFor H \<union> keysFor H'"
by (unfold keysFor_def, blast)

lemma keysFor_UN [simp]: "keysFor (\<Union>i\<in>A. H i) = (\<Union>i\<in>A. keysFor (H i))"
by (unfold keysFor_def, blast)

(*Monotonicity*)
lemma keysFor_mono: "G\<subseteq>H ==> keysFor(G) \<subseteq> keysFor(H)"
by (unfold keysFor_def, blast)

lemma keysFor_insert_Agent [simp]: "keysFor (insert (Agent A) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Nonce [simp]: "keysFor (insert (Nonce N) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Number [simp]: "keysFor (insert (Number N) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Key [simp]: "keysFor (insert (Key K) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Pan [simp]: "keysFor (insert (Pan A) H) = keysFor H"
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

declare MPair_parts [elim!]  parts.Body [dest!]
text{*NB These two rules are UNSAFE in the formal sense, as they discard the
     compound message.  They work well on THIS FILE.
  @{text MPair_parts} is left as SAFE because it speeds up proofs.
  The Crypt rule is normally kept UNSAFE to avoid breaking up certificates.*}

lemma parts_increasing: "H \<subseteq> parts(H)"
by blast

lemmas parts_insertI = subset_insertI [THEN parts_mono, THEN subsetD, standard]

lemma parts_empty [simp]: "parts{} = {}"
apply safe
apply (erule parts.induct, blast+)
done

lemma parts_emptyE [elim!]: "X\<in> parts{} ==> P"
by simp

(*WARNING: loops if H = {Y}, therefore must not be repeated!*)
lemma parts_singleton: "X\<in> parts H ==> \<exists>Y\<in>H. X\<in> parts {Y}"
by (erule parts.induct, blast+)


subsubsection{*Unions*}

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

(*TWO inserts to avoid looping.  This rewrite is better than nothing.
  Not suitable for Addsimps: its behaviour can be strange.*)
lemma parts_insert2:
     "parts (insert X (insert Y H)) = parts {X} \<union> parts {Y} \<union> parts H"
apply (simp add: Un_assoc)
apply (simp add: parts_insert [symmetric])
done

lemma parts_UN_subset1: "(\<Union>x\<in>A. parts(H x)) \<subseteq> parts(\<Union>x\<in>A. H x)"
by (intro UN_least parts_mono UN_upper)

lemma parts_UN_subset2: "parts(\<Union>x\<in>A. H x) \<subseteq> (\<Union>x\<in>A. parts(H x))"
apply (rule subsetI)
apply (erule parts.induct, blast+)
done

lemma parts_UN [simp]: "parts(\<Union>x\<in>A. H x) = (\<Union>x\<in>A. parts(H x))"
by (intro equalityI parts_UN_subset1 parts_UN_subset2)

(*Added to simplify arguments to parts, analz and synth.
  NOTE: the UN versions are no longer used!*)


text{*This allows @{text blast} to simplify occurrences of
  @{term "parts(G\<union>H)"} in the assumption.*}
declare parts_Un [THEN equalityD1, THEN subsetD, THEN UnE, elim!]


lemma parts_insert_subset: "insert X (parts H) \<subseteq> parts(insert X H)"
by (blast intro: parts_mono [THEN [2] rev_subsetD])

subsubsection{*Idempotence and transitivity*}

lemma parts_partsD [dest!]: "X\<in> parts (parts H) ==> X\<in> parts H"
by (erule parts.induct, blast+)

lemma parts_idem [simp]: "parts (parts H) = parts H"
by blast

lemma parts_trans: "[| X\<in> parts G;  G \<subseteq> parts H |] ==> X\<in> parts H"
by (drule parts_mono, blast)

(*Cut*)
lemma parts_cut:
     "[| Y\<in> parts (insert X G);  X\<in> parts H |] ==> Y\<in> parts (G \<union> H)"
by (erule parts_trans, auto)

lemma parts_cut_eq [simp]: "X\<in> parts H ==> parts (insert X H) = parts H"
by (force dest!: parts_cut intro: parts_insertI)


subsubsection{*Rewrite rules for pulling out atomic messages*}

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

lemma parts_insert_Pan [simp]:
     "parts (insert (Pan A) H) = insert (Pan A) (parts H)"
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
apply (erule parts.induct)
apply (blast intro: parts.Body)+
done

lemma parts_insert_MPair [simp]:
     "parts (insert {|X,Y|} H) =
          insert {|X,Y|} (parts (insert X (insert Y H)))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct, auto)
apply (erule parts.induct)
apply (blast intro: parts.Fst parts.Snd)+
done

lemma parts_image_Key [simp]: "parts (Key`N) = Key`N"
apply auto
apply (erule parts.induct, auto)
done

lemma parts_image_Pan [simp]: "parts (Pan`A) = Pan`A"
apply auto
apply (erule parts.induct, auto)
done


(*In any message, there is an upper bound N on its greatest nonce.*)
lemma msg_Nonce_supply: "\<exists>N. \<forall>n. N\<le>n --> Nonce n \<notin> parts {msg}"
apply (induct_tac "msg")
apply (simp_all (no_asm_simp) add: exI parts_insert2)
(*MPair case: blast_tac works out the necessary sum itself!*)
prefer 2 apply (blast elim!: add_leE)
(*Nonce case*)
apply (rule_tac x = "N + Suc nat" in exI)
apply (auto elim!: add_leE)
done

(* Ditto, for numbers.*)
lemma msg_Number_supply: "\<exists>N. \<forall>n. N<=n --> Number n \<notin> parts {msg}"
apply (induct_tac "msg")
apply (simp_all (no_asm_simp) add: exI parts_insert2)
prefer 2 apply (blast elim!: add_leE)
apply (rule_tac x = "N + Suc nat" in exI, auto)
done

subsection{*Inductive relation "analz"*}

text{*Inductive definition of "analz" -- what can be broken down from a set of
    messages, including keys.  A form of downward closure.  Pairs can
    be taken apart; messages decrypted with known keys.*}

consts  analz   :: "msg set => msg set"
inductive "analz H"
  intros
    Inj [intro,simp] :    "X \<in> H ==> X \<in> analz H"
    Fst:     "{|X,Y|} \<in> analz H ==> X \<in> analz H"
    Snd:     "{|X,Y|} \<in> analz H ==> Y \<in> analz H"
    Decrypt [dest]:
             "[|Crypt K X \<in> analz H; Key(invKey K): analz H|] ==> X \<in> analz H"


(*Monotonicity; Lemma 1 of Lowe's paper*)
lemma analz_mono: "G<=H ==> analz(G) <= analz(H)"
apply auto
apply (erule analz.induct)
apply (auto dest: Fst Snd)
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

lemmas analz_into_parts = analz_subset_parts [THEN subsetD, standard]

lemmas not_parts_not_analz = analz_subset_parts [THEN contra_subsetD, standard]


lemma parts_analz [simp]: "parts (analz H) = parts H"
apply (rule equalityI)
apply (rule analz_subset_parts [THEN parts_mono, THEN subset_trans], simp)
apply (blast intro: analz_increasing [THEN parts_mono, THEN subsetD])
done

lemma analz_parts [simp]: "analz (parts H) = parts H"
apply auto
apply (erule analz.induct, auto)
done

lemmas analz_insertI = subset_insertI [THEN analz_mono, THEN [2] rev_subsetD, standard]

subsubsection{*General equational properties*}

lemma analz_empty [simp]: "analz{} = {}"
apply safe
apply (erule analz.induct, blast+)
done

(*Converse fails: we can analz more from the union than from the
  separate parts, as a key in one might decrypt a message in the other*)
lemma analz_Un: "analz(G) \<union> analz(H) \<subseteq> analz(G \<union> H)"
by (intro Un_least analz_mono Un_upper1 Un_upper2)

lemma analz_insert: "insert X (analz H) \<subseteq> analz(insert X H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])

subsubsection{*Rewrite rules for pulling out atomic messages*}

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

(*Can only pull out Keys if they are not needed to decrypt the rest*)
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

(*Can pull out enCrypted message if the Key is not known*)
lemma analz_insert_Crypt:
     "Key (invKey K) \<notin> analz H
      ==> analz (insert (Crypt K X) H) = insert (Crypt K X) (analz H)"
apply (rule analz_insert_eq_I)
apply (erule analz.induct, auto)
done

lemma analz_insert_Pan [simp]:
     "analz (insert (Pan A) H) = insert (Pan A) (analz H)"
apply (rule analz_insert_eq_I)
apply (erule analz.induct, auto)
done

lemma lemma1: "Key (invKey K) \<in> analz H ==>
               analz (insert (Crypt K X) H) \<subseteq>
               insert (Crypt K X) (analz (insert X H))"
apply (rule subsetI)
apply (erule_tac xa = x in analz.induct, auto)
done

lemma lemma2: "Key (invKey K) \<in> analz H ==>
               insert (Crypt K X) (analz (insert X H)) \<subseteq>
               analz (insert (Crypt K X) H)"
apply auto
apply (erule_tac xa = x in analz.induct, auto)
apply (blast intro: analz_insertI analz.Decrypt)
done

lemma analz_insert_Decrypt:
     "Key (invKey K) \<in> analz H ==>
               analz (insert (Crypt K X) H) =
               insert (Crypt K X) (analz (insert X H))"
by (intro equalityI lemma1 lemma2)

(*Case analysis: either the message is secure, or it is not!
  Effective, but can cause subgoals to blow up!
  Use with split_if;  apparently split_tac does not cope with patterns
  such as "analz (insert (Crypt K X) H)" *)
lemma analz_Crypt_if [simp]:
     "analz (insert (Crypt K X) H) =
          (if (Key (invKey K) \<in> analz H)
           then insert (Crypt K X) (analz (insert X H))
           else insert (Crypt K X) (analz H))"
by (simp add: analz_insert_Crypt analz_insert_Decrypt)


(*This rule supposes "for the sake of argument" that we have the key.*)
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

lemma analz_image_Pan [simp]: "analz (Pan`A) = Pan`A"
apply auto
apply (erule analz.induct, auto)
done


subsubsection{*Idempotence and transitivity*}

lemma analz_analzD [dest!]: "X\<in> analz (analz H) ==> X\<in> analz H"
by (erule analz.induct, blast+)

lemma analz_idem [simp]: "analz (analz H) = analz H"
by blast

lemma analz_trans: "[| X\<in> analz G;  G \<subseteq> analz H |] ==> X\<in> analz H"
by (drule analz_mono, blast)

(*Cut; Lemma 2 of Lowe*)
lemma analz_cut: "[| Y\<in> analz (insert X H);  X\<in> analz H |] ==> Y\<in> analz H"
by (erule analz_trans, blast)

(*Cut can be proved easily by induction on
   "Y: analz (insert X H) ==> X: analz H --> Y: analz H"
*)

(*This rewrite rule helps in the simplification of messages that involve
  the forwarding of unknown components (X).  Without it, removing occurrences
  of X can be very complicated. *)
lemma analz_insert_eq: "X\<in> analz H ==> analz (insert X H) = analz H"
by (blast intro: analz_cut analz_insertI)


text{*A congruence rule for "analz"*}

lemma analz_subset_cong:
     "[| analz G \<subseteq> analz G'; analz H \<subseteq> analz H'
               |] ==> analz (G \<union> H) \<subseteq> analz (G' \<union> H')"
apply clarify
apply (erule analz.induct)
apply (best intro: analz_mono [THEN subsetD])+
done

lemma analz_cong:
     "[| analz G = analz G'; analz H = analz H'
               |] ==> analz (G \<union> H) = analz (G' \<union> H')"
by (intro equalityI analz_subset_cong, simp_all)

lemma analz_insert_cong:
     "analz H = analz H' ==> analz(insert X H) = analz(insert X H')"
by (force simp only: insert_def intro!: analz_cong)

(*If there are no pairs or encryptions then analz does nothing*)
lemma analz_trivial:
     "[| \<forall>X Y. {|X,Y|} \<notin> H;  \<forall>X K. Crypt K X \<notin> H |] ==> analz H = H"
apply safe
apply (erule analz.induct, blast+)
done

(*These two are obsolete (with a single Spy) but cost little to prove...*)
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
    Numbers can be guessed, but Nonces cannot be.*}

consts  synth   :: "msg set => msg set"
inductive "synth H"
  intros
    Inj    [intro]:   "X \<in> H ==> X \<in> synth H"
    Agent  [intro]:   "Agent agt \<in> synth H"
    Number [intro]:   "Number n  \<in> synth H"
    Hash   [intro]:   "X \<in> synth H ==> Hash X \<in> synth H"
    MPair  [intro]:   "[|X \<in> synth H;  Y \<in> synth H|] ==> {|X,Y|} \<in> synth H"
    Crypt  [intro]:   "[|X \<in> synth H;  Key(K) \<in> H|] ==> Crypt K X \<in> synth H"

(*Monotonicity*)
lemma synth_mono: "G<=H ==> synth(G) <= synth(H)"
apply auto
apply (erule synth.induct)
apply (auto dest: Fst Snd Body)
done

(*NO Agent_synth, as any Agent name can be synthesized.  Ditto for Number*)
inductive_cases Nonce_synth [elim!]: "Nonce n \<in> synth H"
inductive_cases Key_synth   [elim!]: "Key K \<in> synth H"
inductive_cases Hash_synth  [elim!]: "Hash X \<in> synth H"
inductive_cases MPair_synth [elim!]: "{|X,Y|} \<in> synth H"
inductive_cases Crypt_synth [elim!]: "Crypt K X \<in> synth H"
inductive_cases Pan_synth   [elim!]: "Pan A \<in> synth H"


lemma synth_increasing: "H \<subseteq> synth(H)"
by blast

subsubsection{*Unions*}

(*Converse fails: we can synth more from the union than from the
  separate parts, building a compound message using elements of each.*)
lemma synth_Un: "synth(G) \<union> synth(H) \<subseteq> synth(G \<union> H)"
by (intro Un_least synth_mono Un_upper1 Un_upper2)

lemma synth_insert: "insert X (synth H) \<subseteq> synth(insert X H)"
by (blast intro: synth_mono [THEN [2] rev_subsetD])

subsubsection{*Idempotence and transitivity*}

lemma synth_synthD [dest!]: "X\<in> synth (synth H) ==> X\<in> synth H"
by (erule synth.induct, blast+)

lemma synth_idem: "synth (synth H) = synth H"
by blast

lemma synth_trans: "[| X\<in> synth G;  G \<subseteq> synth H |] ==> X\<in> synth H"
by (drule synth_mono, blast)

(*Cut; Lemma 2 of Lowe*)
lemma synth_cut: "[| Y\<in> synth (insert X H);  X\<in> synth H |] ==> Y\<in> synth H"
by (erule synth_trans, blast)

lemma Agent_synth [simp]: "Agent A \<in> synth H"
by blast

lemma Number_synth [simp]: "Number n \<in> synth H"
by blast

lemma Nonce_synth_eq [simp]: "(Nonce N \<in> synth H) = (Nonce N \<in> H)"
by blast

lemma Key_synth_eq [simp]: "(Key K \<in> synth H) = (Key K \<in> H)"
by blast

lemma Crypt_synth_eq [simp]: "Key K \<notin> H ==> (Crypt K X \<in> synth H) = (Crypt K X \<in> H)"
by blast

lemma Pan_synth_eq [simp]: "(Pan A \<in> synth H) = (Pan A \<in> H)"
by blast

lemma keysFor_synth [simp]:
    "keysFor (synth H) = keysFor H \<union> invKey`{K. Key K \<in> H}"
by (unfold keysFor_def, blast)


subsubsection{*Combinations of parts, analz and synth*}

lemma parts_synth [simp]: "parts (synth H) = parts H \<union> synth H"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct)
apply (blast intro: synth_increasing [THEN parts_mono, THEN subsetD]
                    parts.Fst parts.Snd parts.Body)+
done

lemma analz_analz_Un [simp]: "analz (analz G \<union> H) = analz (G \<union> H)"
apply (intro equalityI analz_subset_cong)+
apply simp_all
done

lemma analz_synth_Un [simp]: "analz (synth G \<union> H) = analz (G \<union> H) \<union> synth G"
apply (rule equalityI)
apply (rule subsetI)
apply (erule analz.induct)
prefer 5 apply (blast intro: analz_mono [THEN [2] rev_subsetD])
apply (blast intro: analz.Fst analz.Snd analz.Decrypt)+
done

lemma analz_synth [simp]: "analz (synth H) = analz H \<union> synth H"
apply (cut_tac H = "{}" in analz_synth_Un)
apply (simp (no_asm_use))
done


subsubsection{*For reasoning about the Fake rule in traces*}

lemma parts_insert_subset_Un: "X\<in> G ==> parts(insert X H) \<subseteq> parts G \<union> parts H"
by (rule subset_trans [OF parts_mono parts_Un_subset2], blast)

(*More specifically for Fake.  Very occasionally we could do with a version
  of the form  parts{X} \<subseteq> synth (analz H) \<union> parts H *)
lemma Fake_parts_insert: "X \<in> synth (analz H) ==>
      parts (insert X H) \<subseteq> synth (analz H) \<union> parts H"
apply (drule parts_insert_subset_Un)
apply (simp (no_asm_use))
apply blast
done

lemma Fake_parts_insert_in_Un:
     "[|Z \<in> parts (insert X H);  X: synth (analz H)|] 
      ==> Z \<in>  synth (analz H) \<union> parts H";
by (blast dest: Fake_parts_insert [THEN subsetD, dest])

(*H is sometimes (Key ` KK \<union> spies evs), so can't put G=H*)
lemma Fake_analz_insert:
     "X\<in> synth (analz G) ==>
      analz (insert X H) \<subseteq> synth (analz G) \<union> analz (G \<union> H)"
apply (rule subsetI)
apply (subgoal_tac "x \<in> analz (synth (analz G) \<union> H) ")
prefer 2 apply (blast intro: analz_mono [THEN [2] rev_subsetD] analz_mono [THEN synth_mono, THEN [2] rev_subsetD])
apply (simp (no_asm_use))
apply blast
done

lemma analz_conj_parts [simp]:
     "(X \<in> analz H & X \<in> parts H) = (X \<in> analz H)"
by (blast intro: analz_subset_parts [THEN subsetD])

lemma analz_disj_parts [simp]:
     "(X \<in> analz H | X \<in> parts H) = (X \<in> parts H)"
by (blast intro: analz_subset_parts [THEN subsetD])

(*Without this equation, other rules for synth and analz would yield
  redundant cases*)
lemma MPair_synth_analz [iff]:
     "({|X,Y|} \<in> synth (analz H)) =
      (X \<in> synth (analz H) & Y \<in> synth (analz H))"
by blast

lemma Crypt_synth_analz:
     "[| Key K \<in> analz H;  Key (invKey K) \<in> analz H |]
       ==> (Crypt K X \<in> synth (analz H)) = (X \<in> synth (analz H))"
by blast


lemma Hash_synth_analz [simp]:
     "X \<notin> synth (analz H)
      ==> (Hash{|X,Y|} \<in> synth (analz H)) = (Hash{|X,Y|} \<in> analz H)"
by blast


(*We do NOT want Crypt... messages broken up in protocols!!*)
declare parts.Body [rule del]


text{*Rewrites to push in Key and Crypt messages, so that other messages can
    be pulled out using the @{text analz_insert} rules*}
ML
{*
fun insComm x y = inst "x" x (inst "y" y insert_commute);

bind_thms ("pushKeys",
           map (insComm "Key ?K")
                   ["Agent ?C", "Nonce ?N", "Number ?N", "Pan ?PAN",
		    "Hash ?X", "MPair ?X ?Y", "Crypt ?X ?K'"]);

bind_thms ("pushCrypts",
           map (insComm "Crypt ?X ?K")
                     ["Agent ?C", "Nonce ?N", "Number ?N", "Pan ?PAN",
		      "Hash ?X'", "MPair ?X' ?Y"]);
*}

text{*Cannot be added with @{text "[simp]"} -- messages should not always be
  re-ordered.*}
lemmas pushes = pushKeys pushCrypts


subsection{*Tactics useful for many protocol proofs*}
ML
{*
val invKey = thm "invKey"
val keysFor_def = thm "keysFor_def"
val symKeys_def = thm "symKeys_def"
val parts_mono = thm "parts_mono";
val analz_mono = thm "analz_mono";
val Key_image_eq = thm "Key_image_eq";
val Nonce_Key_image_eq = thm "Nonce_Key_image_eq";
val keysFor_Un = thm "keysFor_Un";
val keysFor_mono = thm "keysFor_mono";
val keysFor_image_Key = thm "keysFor_image_Key";
val Crypt_imp_invKey_keysFor = thm "Crypt_imp_invKey_keysFor";
val MPair_parts = thm "MPair_parts";
val parts_increasing = thm "parts_increasing";
val parts_insertI = thm "parts_insertI";
val parts_empty = thm "parts_empty";
val parts_emptyE = thm "parts_emptyE";
val parts_singleton = thm "parts_singleton";
val parts_Un_subset1 = thm "parts_Un_subset1";
val parts_Un_subset2 = thm "parts_Un_subset2";
val parts_insert = thm "parts_insert";
val parts_insert2 = thm "parts_insert2";
val parts_UN_subset1 = thm "parts_UN_subset1";
val parts_UN_subset2 = thm "parts_UN_subset2";
val parts_UN = thm "parts_UN";
val parts_insert_subset = thm "parts_insert_subset";
val parts_partsD = thm "parts_partsD";
val parts_trans = thm "parts_trans";
val parts_cut = thm "parts_cut";
val parts_cut_eq = thm "parts_cut_eq";
val parts_insert_eq_I = thm "parts_insert_eq_I";
val parts_image_Key = thm "parts_image_Key";
val MPair_analz = thm "MPair_analz";
val analz_increasing = thm "analz_increasing";
val analz_subset_parts = thm "analz_subset_parts";
val not_parts_not_analz = thm "not_parts_not_analz";
val parts_analz = thm "parts_analz";
val analz_parts = thm "analz_parts";
val analz_insertI = thm "analz_insertI";
val analz_empty = thm "analz_empty";
val analz_Un = thm "analz_Un";
val analz_insert_Crypt_subset = thm "analz_insert_Crypt_subset";
val analz_image_Key = thm "analz_image_Key";
val analz_analzD = thm "analz_analzD";
val analz_trans = thm "analz_trans";
val analz_cut = thm "analz_cut";
val analz_insert_eq = thm "analz_insert_eq";
val analz_subset_cong = thm "analz_subset_cong";
val analz_cong = thm "analz_cong";
val analz_insert_cong = thm "analz_insert_cong";
val analz_trivial = thm "analz_trivial";
val analz_UN_analz = thm "analz_UN_analz";
val synth_mono = thm "synth_mono";
val synth_increasing = thm "synth_increasing";
val synth_Un = thm "synth_Un";
val synth_insert = thm "synth_insert";
val synth_synthD = thm "synth_synthD";
val synth_trans = thm "synth_trans";
val synth_cut = thm "synth_cut";
val Agent_synth = thm "Agent_synth";
val Number_synth = thm "Number_synth";
val Nonce_synth_eq = thm "Nonce_synth_eq";
val Key_synth_eq = thm "Key_synth_eq";
val Crypt_synth_eq = thm "Crypt_synth_eq";
val keysFor_synth = thm "keysFor_synth";
val parts_synth = thm "parts_synth";
val analz_analz_Un = thm "analz_analz_Un";
val analz_synth_Un = thm "analz_synth_Un";
val analz_synth = thm "analz_synth";
val parts_insert_subset_Un = thm "parts_insert_subset_Un";
val Fake_parts_insert = thm "Fake_parts_insert";
val Fake_analz_insert = thm "Fake_analz_insert";
val analz_conj_parts = thm "analz_conj_parts";
val analz_disj_parts = thm "analz_disj_parts";
val MPair_synth_analz = thm "MPair_synth_analz";
val Crypt_synth_analz = thm "Crypt_synth_analz";
val Hash_synth_analz = thm "Hash_synth_analz";
val pushes = thms "pushes";


(*Prove base case (subgoal i) and simplify others.  A typical base case
  concerns  Crypt K X \<notin> Key`shrK`bad  and cannot be proved by rewriting
  alone.*)
fun prove_simple_subgoals_tac i =
    force_tac (claset(), simpset() addsimps [image_eq_UN]) i THEN
    ALLGOALS Asm_simp_tac

(*Analysis of Fake cases.  Also works for messages that forward unknown parts,
  but this application is no longer necessary if analz_insert_eq is used.
  Abstraction over i is ESSENTIAL: it delays the dereferencing of claset
  DEPENDS UPON "X" REFERRING TO THE FRADULENT MESSAGE *)

(*Apply rules to break down assumptions of the form
  Y \<in> parts(insert X H)  and  Y \<in> analz(insert X H)
*)
val Fake_insert_tac =
    dresolve_tac [impOfSubs Fake_analz_insert,
                  impOfSubs Fake_parts_insert] THEN'
    eresolve_tac [asm_rl, thm"synth.Inj"];

fun Fake_insert_simp_tac ss i =
    REPEAT (Fake_insert_tac i) THEN asm_full_simp_tac ss i;

fun atomic_spy_analz_tac (cs,ss) = SELECT_GOAL
    (Fake_insert_simp_tac ss 1
     THEN
     IF_UNSOLVED (Blast.depth_tac
		  (cs addIs [analz_insertI,
				   impOfSubs analz_subset_parts]) 4 1))

(*The explicit claset and simpset arguments help it work with Isar*)
fun gen_spy_analz_tac (cs,ss) i =
  DETERM
   (SELECT_GOAL
     (EVERY
      [  (*push in occurrences of X...*)
       (REPEAT o CHANGED)
           (res_inst_tac [("x1","X")] (insert_commute RS ssubst) 1),
       (*...allowing further simplifications*)
       simp_tac ss 1,
       REPEAT (FIRSTGOAL (resolve_tac [allI,impI,notI,conjI,iffI])),
       DEPTH_SOLVE (atomic_spy_analz_tac (cs,ss) 1)]) i)

fun spy_analz_tac i = gen_spy_analz_tac (claset(), simpset()) i
*}

(*By default only o_apply is built-in.  But in the presence of eta-expansion
  this means that some terms displayed as (f o g) will be rewritten, and others
  will not!*)
declare o_def [simp]


lemma Crypt_notin_image_Key [simp]: "Crypt K X \<notin> Key ` A"
by auto

lemma Hash_notin_image_Key [simp] :"Hash X \<notin> Key ` A"
by auto

lemma synth_analz_mono: "G<=H ==> synth (analz(G)) <= synth (analz(H))"
by (simp add: synth_mono analz_mono)

lemma Fake_analz_eq [simp]:
     "X \<in> synth(analz H) ==> synth (analz (insert X H)) = synth (analz H)"
apply (drule Fake_analz_insert[of _ _ "H"])
apply (simp add: synth_increasing[THEN Un_absorb2])
apply (drule synth_mono)
apply (simp add: synth_idem)
apply (blast intro: synth_analz_mono [THEN [2] rev_subsetD])
done

text{*Two generalizations of @{text analz_insert_eq}*}
lemma gen_analz_insert_eq [rule_format]:
     "X \<in> analz H ==> ALL G. H \<subseteq> G --> analz (insert X G) = analz G";
by (blast intro: analz_cut analz_insertI analz_mono [THEN [2] rev_subsetD])

lemma synth_analz_insert_eq [rule_format]:
     "X \<in> synth (analz H)
      ==> ALL G. H \<subseteq> G --> (Key K \<in> analz (insert X G)) = (Key K \<in> analz G)";
apply (erule synth.induct)
apply (simp_all add: gen_analz_insert_eq subset_trans [OF _ subset_insertI])
done

lemma Fake_parts_sing:
     "X \<in> synth (analz H) ==> parts{X} \<subseteq> synth (analz H) \<union> parts H";
apply (rule subset_trans)
 apply (erule_tac [2] Fake_parts_insert)
apply (simp add: parts_mono)
done

lemmas Fake_parts_sing_imp_Un = Fake_parts_sing [THEN [2] rev_subsetD]

method_setup spy_analz = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts =>
            gen_spy_analz_tac (Classical.get_local_claset ctxt,
                               Simplifier.get_local_simpset ctxt) 1))*}
    "for proving the Fake case when analz is involved"

method_setup atomic_spy_analz = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts =>
            atomic_spy_analz_tac (Classical.get_local_claset ctxt,
                                  Simplifier.get_local_simpset ctxt) 1))*}
    "for debugging spy_analz"

method_setup Fake_insert_simp = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts =>
            Fake_insert_simp_tac (Simplifier.get_local_simpset ctxt) 1))*}
    "for debugging spy_analz"


end
