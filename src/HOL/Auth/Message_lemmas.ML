(*  Title:      HOL/Auth/Message
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatypes of agents and messages;
Inductive relations "parts", "analz" and "synth"
*)

(*ML bindings for definitions and axioms*)
val invKey = thm "invKey";
val keysFor_def = thm "keysFor_def";
val parts_mono = thm "parts_mono";
val analz_mono = thm "analz_mono";
val synth_mono = thm "synth_mono";
val HPair_def = thm "HPair_def";
val isSymKey_def = thm "isSymKey_def";

structure parts =
  struct
  val induct = thm "parts.induct";
  val Inj    = thm "parts.Inj";
  val Fst    = thm "parts.Fst";
  val Snd    = thm "parts.Snd";
  val Body   = thm "parts.Body";
  end;

structure analz =
  struct
  val induct = thm "analz.induct";
  val Inj    = thm "analz.Inj";
  val Fst    = thm "analz.Fst";
  val Snd    = thm "analz.Snd";
  val Decrypt = thm "analz.Decrypt";
  end;

structure synth =
  struct
  val induct = thm "synth.induct";
  val Inj    = thm "synth.Inj";
  val Agent  = thm "synth.Agent";
  val Number = thm "synth.Number";
  val Hash   = thm "synth.Hash";
  val Crypt  = thm "synth.Crypt";
  end;


(*Equations hold because constructors are injective; cannot prove for all f*)
Goal "(Friend x \\<in> Friend`A) = (x:A)";
by Auto_tac;
qed "Friend_image_eq";

Goal "(Key x \\<in> Key`A) = (x:A)";
by Auto_tac;
qed "Key_image_eq";

Goal "(Nonce x \\<notin> Key`A)";
by Auto_tac;
qed "Nonce_Key_image_eq";
Addsimps [Friend_image_eq, Key_image_eq, Nonce_Key_image_eq];


(** Inverse of keys **)

Goal "(invKey K = invKey K') = (K=K')";
by Safe_tac;
by (rtac box_equals 1);
by (REPEAT (rtac invKey 2));
by (Asm_simp_tac 1);
qed "invKey_eq";

Addsimps [invKey_eq];


(**** keysFor operator ****)

Goalw [keysFor_def] "keysFor {} = {}";
by (Blast_tac 1);
qed "keysFor_empty";

Goalw [keysFor_def] "keysFor (H Un H') = keysFor H Un keysFor H'";
by (Blast_tac 1);
qed "keysFor_Un";

Goalw [keysFor_def] "keysFor (UN i:A. H i) = (UN i:A. keysFor (H i))";
by (Blast_tac 1);
qed "keysFor_UN";

(*Monotonicity*)
Goalw [keysFor_def] "G<=H ==> keysFor(G) <= keysFor(H)";
by (Blast_tac 1);
qed "keysFor_mono";

Goalw [keysFor_def] "keysFor (insert (Agent A) H) = keysFor H";
by Auto_tac;
qed "keysFor_insert_Agent";

Goalw [keysFor_def] "keysFor (insert (Nonce N) H) = keysFor H";
by Auto_tac;
qed "keysFor_insert_Nonce";

Goalw [keysFor_def] "keysFor (insert (Number N) H) = keysFor H";
by Auto_tac;
qed "keysFor_insert_Number";

Goalw [keysFor_def] "keysFor (insert (Key K) H) = keysFor H";
by Auto_tac;
qed "keysFor_insert_Key";

Goalw [keysFor_def] "keysFor (insert (Hash X) H) = keysFor H";
by Auto_tac;
qed "keysFor_insert_Hash";

Goalw [keysFor_def] "keysFor (insert {|X,Y|} H) = keysFor H";
by Auto_tac;
qed "keysFor_insert_MPair";

Goalw [keysFor_def]
    "keysFor (insert (Crypt K X) H) = insert (invKey K) (keysFor H)";
by Auto_tac;
qed "keysFor_insert_Crypt";

Addsimps [keysFor_empty, keysFor_Un, keysFor_UN, 
          keysFor_insert_Agent, keysFor_insert_Nonce, 
	  keysFor_insert_Number, keysFor_insert_Key, 
          keysFor_insert_Hash, keysFor_insert_MPair, keysFor_insert_Crypt];
AddSEs [keysFor_Un RS equalityD1 RS subsetD RS UnE,
	keysFor_UN RS equalityD1 RS subsetD RS UN_E];

Goalw [keysFor_def] "keysFor (Key`E) = {}";
by Auto_tac;
qed "keysFor_image_Key";
Addsimps [keysFor_image_Key];

Goalw [keysFor_def] "Crypt K X \\<in> H ==> invKey K \\<in> keysFor H";
by (Blast_tac 1);
qed "Crypt_imp_invKey_keysFor";


(**** Inductive relation "parts" ****)

val major::prems = 
Goal "[| {|X,Y|} \\<in> parts H;       \
\         [| X \\<in> parts H; Y \\<in> parts H |] ==> P  \
\     |] ==> P";
by (cut_facts_tac [major] 1);
by (resolve_tac prems 1);
by (REPEAT (eresolve_tac [asm_rl, parts.Fst, parts.Snd] 1));
qed "MPair_parts";

AddSEs [MPair_parts, make_elim parts.Body];
(*NB These two rules are UNSAFE in the formal sense, as they discard the
     compound message.  They work well on THIS FILE.  
  MPair_parts is left as SAFE because it speeds up proofs.
  The Crypt rule is normally kept UNSAFE to avoid breaking up certificates.*)

Goal "H <= parts(H)";
by (Blast_tac 1);
qed "parts_increasing";

val parts_insertI = impOfSubs (subset_insertI RS parts_mono);

Goal "parts{} = {}";
by Safe_tac;
by (etac parts.induct 1);
by (ALLGOALS Blast_tac);
qed "parts_empty";
Addsimps [parts_empty];

Goal "X: parts{} ==> P";
by (Asm_full_simp_tac 1);
qed "parts_emptyE";
AddSEs [parts_emptyE];

(*WARNING: loops if H = {Y}, therefore must not be repeated!*)
Goal "X: parts H ==> EX Y:H. X: parts {Y}";
by (etac parts.induct 1);
by (ALLGOALS Blast_tac);
qed "parts_singleton";


(** Unions **)

Goal "parts(G) Un parts(H) <= parts(G Un H)";
by (REPEAT (ares_tac [Un_least, parts_mono, Un_upper1, Un_upper2] 1));
val parts_Un_subset1 = result();

Goal "parts(G Un H) <= parts(G) Un parts(H)";
by (rtac subsetI 1);
by (etac parts.induct 1);
by (ALLGOALS Blast_tac);
val parts_Un_subset2 = result();

Goal "parts(G Un H) = parts(G) Un parts(H)";
by (REPEAT (ares_tac [equalityI, parts_Un_subset1, parts_Un_subset2] 1));
qed "parts_Un";

Goal "parts (insert X H) = parts {X} Un parts H";
by (stac (read_instantiate [("A","H")] insert_is_Un) 1);
by (simp_tac (HOL_ss addsimps [parts_Un]) 1);
qed "parts_insert";

(*TWO inserts to avoid looping.  This rewrite is better than nothing.
  Not suitable for Addsimps: its behaviour can be strange.*)
Goal "parts (insert X (insert Y H)) = parts {X} Un parts {Y} Un parts H";
by (simp_tac (simpset() addsimps [Un_assoc]) 1);
by (simp_tac (simpset() addsimps [parts_insert RS sym]) 1);
qed "parts_insert2";

Goal "(UN x:A. parts(H x)) <= parts(UN x:A. H x)";
by (REPEAT (ares_tac [UN_least, parts_mono, UN_upper] 1));
val parts_UN_subset1 = result();

Goal "parts(UN x:A. H x) <= (UN x:A. parts(H x))";
by (rtac subsetI 1);
by (etac parts.induct 1);
by (ALLGOALS Blast_tac);
val parts_UN_subset2 = result();

Goal "parts(UN x:A. H x) = (UN x:A. parts(H x))";
by (REPEAT (ares_tac [equalityI, parts_UN_subset1, parts_UN_subset2] 1));
qed "parts_UN";

(*Added to simplify arguments to parts, analz and synth.
  NOTE: the UN versions are no longer used!*)
Addsimps [parts_Un, parts_UN];
AddSEs [parts_Un RS equalityD1 RS subsetD RS UnE,
	parts_UN RS equalityD1 RS subsetD RS UN_E];

Goal "insert X (parts H) <= parts(insert X H)";
by (blast_tac (claset() addIs [impOfSubs parts_mono]) 1);
qed "parts_insert_subset";

(** Idempotence and transitivity **)

Goal "X: parts (parts H) ==> X: parts H";
by (etac parts.induct 1);
by (ALLGOALS Blast_tac);
qed "parts_partsD";
AddSDs [parts_partsD];

Goal "parts (parts H) = parts H";
by (Blast_tac 1);
qed "parts_idem";
Addsimps [parts_idem];

Goal "[| X: parts G;  G <= parts H |] ==> X: parts H";
by (dtac parts_mono 1);
by (Blast_tac 1);
qed "parts_trans";

(*Cut*)
Goal "[| Y: parts (insert X G);  X: parts H |] \
\              ==> Y: parts (G Un H)";
by (etac parts_trans 1);
by Auto_tac;
qed "parts_cut";

Goal "X: parts H ==> parts (insert X H) = parts H";
by (fast_tac (claset() addSDs [parts_cut]
                       addIs  [parts_insertI] 
                       addss (simpset())) 1);
qed "parts_cut_eq";

Addsimps [parts_cut_eq];


(** Rewrite rules for pulling out atomic messages **)

fun parts_tac i =
  EVERY [rtac ([subsetI, parts_insert_subset] MRS equalityI) i,
         etac parts.induct i,
         Auto_tac];

Goal "parts (insert (Agent agt) H) = insert (Agent agt) (parts H)";
by (parts_tac 1);
qed "parts_insert_Agent";

Goal "parts (insert (Nonce N) H) = insert (Nonce N) (parts H)";
by (parts_tac 1);
qed "parts_insert_Nonce";

Goal "parts (insert (Number N) H) = insert (Number N) (parts H)";
by (parts_tac 1);
qed "parts_insert_Number";

Goal "parts (insert (Key K) H) = insert (Key K) (parts H)";
by (parts_tac 1);
qed "parts_insert_Key";

Goal "parts (insert (Hash X) H) = insert (Hash X) (parts H)";
by (parts_tac 1);
qed "parts_insert_Hash";

Goal "parts (insert (Crypt K X) H) = \
\         insert (Crypt K X) (parts (insert X H))";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac parts.induct 1);
by Auto_tac;
by (etac parts.induct 1);
by (ALLGOALS (blast_tac (claset() addIs [parts.Body])));
qed "parts_insert_Crypt";

Goal "parts (insert {|X,Y|} H) = \
\         insert {|X,Y|} (parts (insert X (insert Y H)))";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac parts.induct 1);
by Auto_tac;
by (etac parts.induct 1);
by (ALLGOALS (blast_tac (claset() addIs [parts.Fst, parts.Snd])));
qed "parts_insert_MPair";

Addsimps [parts_insert_Agent, parts_insert_Nonce, 
	  parts_insert_Number, parts_insert_Key, 
          parts_insert_Hash, parts_insert_Crypt, parts_insert_MPair];


Goal "parts (Key`N) = Key`N";
by Auto_tac;
by (etac parts.induct 1);
by Auto_tac;
qed "parts_image_Key";
Addsimps [parts_image_Key];


(*In any message, there is an upper bound N on its greatest nonce.*)
Goal "EX N. ALL n. N<=n --> Nonce n \\<notin> parts {msg}";
by (induct_tac "msg" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [exI, parts_insert2])));
(*MPair case: blast_tac works out the necessary sum itself!*)
by (blast_tac (claset() addSEs [add_leE]) 2);
(*Nonce case*)
by (res_inst_tac [("x","N + Suc nat")] exI 1);
by (auto_tac (claset() addSEs [add_leE], simpset()));
qed "msg_Nonce_supply";


(**** Inductive relation "analz" ****)

val major::prems = 
Goal "[| {|X,Y|} \\<in> analz H;       \
\            [| X \\<in> analz H; Y \\<in> analz H |] ==> P  \
\         |] ==> P";
by (cut_facts_tac [major] 1);
by (resolve_tac prems 1);
by (REPEAT (eresolve_tac [asm_rl, analz.Fst, analz.Snd] 1));
qed "MPair_analz";

AddSEs [MPair_analz];     (*Making it safe speeds up proofs*)

Goal "H <= analz(H)";
by (Blast_tac 1);
qed "analz_increasing";

Goal "analz H <= parts H";
by (rtac subsetI 1);
by (etac analz.induct 1);
by (ALLGOALS Blast_tac);
qed "analz_subset_parts";

bind_thm ("not_parts_not_analz", analz_subset_parts RS contra_subsetD);


Goal "parts (analz H) = parts H";
by (rtac equalityI 1);
by (rtac (analz_subset_parts RS parts_mono RS subset_trans) 1);
by (Simp_tac 1);
by (blast_tac (claset() addIs [analz_increasing RS parts_mono RS subsetD]) 1);
qed "parts_analz";
Addsimps [parts_analz];

Goal "analz (parts H) = parts H";
by Auto_tac;
by (etac analz.induct 1);
by Auto_tac;
qed "analz_parts";
Addsimps [analz_parts];

bind_thm ("analz_insertI", impOfSubs (subset_insertI RS analz_mono));

(** General equational properties **)

Goal "analz{} = {}";
by Safe_tac;
by (etac analz.induct 1);
by (ALLGOALS Blast_tac);
qed "analz_empty";
Addsimps [analz_empty];

(*Converse fails: we can analz more from the union than from the 
  separate parts, as a key in one might decrypt a message in the other*)
Goal "analz(G) Un analz(H) <= analz(G Un H)";
by (REPEAT (ares_tac [Un_least, analz_mono, Un_upper1, Un_upper2] 1));
qed "analz_Un";

Goal "insert X (analz H) <= analz(insert X H)";
by (blast_tac (claset() addIs [impOfSubs analz_mono]) 1);
qed "analz_insert";

(** Rewrite rules for pulling out atomic messages **)

fun analz_tac i =
  EVERY [rtac ([subsetI, analz_insert] MRS equalityI) i,
         etac analz.induct i,
         Auto_tac];

Goal "analz (insert (Agent agt) H) = insert (Agent agt) (analz H)";
by (analz_tac 1);
qed "analz_insert_Agent";

Goal "analz (insert (Nonce N) H) = insert (Nonce N) (analz H)";
by (analz_tac 1);
qed "analz_insert_Nonce";

Goal "analz (insert (Number N) H) = insert (Number N) (analz H)";
by (analz_tac 1);
qed "analz_insert_Number";

Goal "analz (insert (Hash X) H) = insert (Hash X) (analz H)";
by (analz_tac 1);
qed "analz_insert_Hash";

(*Can only pull out Keys if they are not needed to decrypt the rest*)
Goalw [keysFor_def]
    "K \\<notin> keysFor (analz H) ==>  \
\         analz (insert (Key K) H) = insert (Key K) (analz H)";
by (analz_tac 1);
qed "analz_insert_Key";

Goal "analz (insert {|X,Y|} H) = \
\         insert {|X,Y|} (analz (insert X (insert Y H)))";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac analz.induct 1);
by Auto_tac;
by (etac analz.induct 1);
by (ALLGOALS (blast_tac (claset() addIs [analz.Fst, analz.Snd])));
qed "analz_insert_MPair";

(*Can pull out enCrypted message if the Key is not known*)
Goal "Key (invKey K) \\<notin> analz H ==>  \
\              analz (insert (Crypt K X) H) = \
\              insert (Crypt K X) (analz H)";
by (analz_tac 1);
qed "analz_insert_Crypt";

Goal "Key (invKey K) \\<in> analz H ==>  \
\              analz (insert (Crypt K X) H) <= \
\              insert (Crypt K X) (analz (insert X H))";
by (rtac subsetI 1);
by (eres_inst_tac [("xa","x")] analz.induct 1);
by Auto_tac;
val lemma1 = result();

Goal "Key (invKey K) \\<in> analz H ==>  \
\              insert (Crypt K X) (analz (insert X H)) <= \
\              analz (insert (Crypt K X) H)";
by Auto_tac;
by (eres_inst_tac [("xa","x")] analz.induct 1);
by Auto_tac;
by (blast_tac (claset() addIs [analz_insertI, analz.Decrypt]) 1);
val lemma2 = result();

Goal "Key (invKey K) \\<in> analz H ==>  \
\              analz (insert (Crypt K X) H) = \
\              insert (Crypt K X) (analz (insert X H))";
by (REPEAT (ares_tac [equalityI, lemma1, lemma2] 1));
qed "analz_insert_Decrypt";

(*Case analysis: either the message is secure, or it is not!
  Effective, but can cause subgoals to blow up!
  Use with split_if;  apparently split_tac does not cope with patterns
  such as "analz (insert (Crypt K X) H)" *)
Goal "analz (insert (Crypt K X) H) =                \
\         (if (Key (invKey K) \\<in> analz H)                \
\          then insert (Crypt K X) (analz (insert X H)) \
\          else insert (Crypt K X) (analz H))";
by (case_tac "Key (invKey K)  \\<in> analz H " 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [analz_insert_Crypt, 
						analz_insert_Decrypt])));
qed "analz_Crypt_if";

Addsimps [analz_insert_Agent, analz_insert_Nonce, 
	  analz_insert_Number, analz_insert_Key, 
          analz_insert_Hash, analz_insert_MPair, analz_Crypt_if];

(*This rule supposes "for the sake of argument" that we have the key.*)
Goal  "analz (insert (Crypt K X) H) <=  \
\          insert (Crypt K X) (analz (insert X H))";
by (rtac subsetI 1);
by (etac analz.induct 1);
by Auto_tac;
qed "analz_insert_Crypt_subset";


Goal "analz (Key`N) = Key`N";
by Auto_tac;
by (etac analz.induct 1);
by Auto_tac;
qed "analz_image_Key";

Addsimps [analz_image_Key];


(** Idempotence and transitivity **)

Goal "X: analz (analz H) ==> X: analz H";
by (etac analz.induct 1);
by (ALLGOALS Blast_tac);
qed "analz_analzD";
AddSDs [analz_analzD];

Goal "analz (analz H) = analz H";
by (Blast_tac 1);
qed "analz_idem";
Addsimps [analz_idem];

Goal "[| X: analz G;  G <= analz H |] ==> X: analz H";
by (dtac analz_mono 1);
by (Blast_tac 1);
qed "analz_trans";

(*Cut; Lemma 2 of Lowe*)
Goal "[| Y: analz (insert X H);  X: analz H |] ==> Y: analz H";
by (etac analz_trans 1);
by (Blast_tac 1);
qed "analz_cut";

(*Cut can be proved easily by induction on
   "Y: analz (insert X H) ==> X: analz H --> Y: analz H"
*)

(*This rewrite rule helps in the simplification of messages that involve
  the forwarding of unknown components (X).  Without it, removing occurrences
  of X can be very complicated. *)
Goal "X: analz H ==> analz (insert X H) = analz H";
by (blast_tac (claset() addIs [analz_cut, analz_insertI]) 1);
qed "analz_insert_eq";


(** A congruence rule for "analz" **)

Goal "[| analz G <= analz G'; analz H <= analz H' \
\              |] ==> analz (G Un H) <= analz (G' Un H')";
by (Clarify_tac 1);
by (etac analz.induct 1);
by (ALLGOALS (best_tac (claset() addIs [analz_mono RS subsetD])));
qed "analz_subset_cong";

Goal "[| analz G = analz G'; analz H = analz H' \
\              |] ==> analz (G Un H) = analz (G' Un H')";
by (REPEAT_FIRST (ares_tac [equalityI, analz_subset_cong]
          ORELSE' etac equalityE));
qed "analz_cong";


Goal "analz H = analz H' ==> analz(insert X H) = analz(insert X H')";
by (asm_simp_tac (simpset() addsimps [insert_def] delsimps [singleton_conv]
                            setloop (rtac analz_cong)) 1);
qed "analz_insert_cong";

(*If there are no pairs or encryptions then analz does nothing*)
Goal "[| ALL X Y. {|X,Y|} \\<notin> H;  ALL X K. Crypt K X \\<notin> H |] ==> \
\         analz H = H";
by Safe_tac;
by (etac analz.induct 1);
by (ALLGOALS Blast_tac);
qed "analz_trivial";

(*These two are obsolete (with a single Spy) but cost little to prove...*)
Goal "X: analz (UN i:A. analz (H i)) ==> X: analz (UN i:A. H i)";
by (etac analz.induct 1);
by (ALLGOALS (blast_tac (claset() addIs [impOfSubs analz_mono])));
val lemma = result();

Goal "analz (UN i:A. analz (H i)) = analz (UN i:A. H i)";
by (blast_tac (claset() addIs [lemma, impOfSubs analz_mono]) 1);
qed "analz_UN_analz";
Addsimps [analz_UN_analz];


(**** Inductive relation "synth" ****)

Goal "H <= synth(H)";
by (Blast_tac 1);
qed "synth_increasing";

(** Unions **)

(*Converse fails: we can synth more from the union than from the 
  separate parts, building a compound message using elements of each.*)
Goal "synth(G) Un synth(H) <= synth(G Un H)";
by (REPEAT (ares_tac [Un_least, synth_mono, Un_upper1, Un_upper2] 1));
qed "synth_Un";

Goal "insert X (synth H) <= synth(insert X H)";
by (blast_tac (claset() addIs [impOfSubs synth_mono]) 1);
qed "synth_insert";

(** Idempotence and transitivity **)

Goal "X: synth (synth H) ==> X: synth H";
by (etac synth.induct 1);
by (ALLGOALS Blast_tac);
qed "synth_synthD";
AddSDs [synth_synthD];

Goal "synth (synth H) = synth H";
by (Blast_tac 1);
qed "synth_idem";

Goal "[| X: synth G;  G <= synth H |] ==> X: synth H";
by (dtac synth_mono 1);
by (Blast_tac 1);
qed "synth_trans";

(*Cut; Lemma 2 of Lowe*)
Goal "[| Y: synth (insert X H);  X: synth H |] ==> Y: synth H";
by (etac synth_trans 1);
by (Blast_tac 1);
qed "synth_cut";

Goal "Agent A \\<in> synth H";
by (Blast_tac 1);
qed "Agent_synth";

Goal "Number n \\<in> synth H";
by (Blast_tac 1);
qed "Number_synth";

Goal "(Nonce N \\<in> synth H) = (Nonce N \\<in> H)";
by (Blast_tac 1);
qed "Nonce_synth_eq";

Goal "(Key K \\<in> synth H) = (Key K \\<in> H)";
by (Blast_tac 1);
qed "Key_synth_eq";

Goal "Key K \\<notin> H ==> (Crypt K X \\<in> synth H) = (Crypt K X \\<in> H)";
by (Blast_tac 1);
qed "Crypt_synth_eq";

Addsimps [Agent_synth, Number_synth, 
	  Nonce_synth_eq, Key_synth_eq, Crypt_synth_eq];


Goalw [keysFor_def]
    "keysFor (synth H) = keysFor H Un invKey`{K. Key K \\<in> H}";
by (Blast_tac 1);
qed "keysFor_synth";
Addsimps [keysFor_synth];


(*** Combinations of parts, analz and synth ***)

Goal "parts (synth H) = parts H Un synth H";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac parts.induct 1);
by (ALLGOALS
    (blast_tac (claset() addIs [synth_increasing RS parts_mono RS subsetD,
                                parts.Fst, parts.Snd, parts.Body])));
qed "parts_synth";
Addsimps [parts_synth];

Goal "analz (analz G Un H) = analz (G Un H)";
by (REPEAT_FIRST (resolve_tac [equalityI, analz_subset_cong]));
by (ALLGOALS Simp_tac);
qed "analz_analz_Un";

Goal "analz (synth G Un H) = analz (G Un H) Un synth G";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac analz.induct 1);
by (blast_tac (claset() addIs [impOfSubs analz_mono]) 5);
by (ALLGOALS 
    (blast_tac (claset() addIs [analz.Fst, analz.Snd, analz.Decrypt])));
qed "analz_synth_Un";

Goal "analz (synth H) = analz H Un synth H";
by (cut_inst_tac [("H","{}")] analz_synth_Un 1);
by (Full_simp_tac 1);
qed "analz_synth";
Addsimps [analz_analz_Un, analz_synth_Un, analz_synth];


(** For reasoning about the Fake rule in traces **)

Goal "X: G ==> parts(insert X H) <= parts G Un parts H";
by (rtac ([parts_mono, parts_Un_subset2] MRS subset_trans) 1);
by (Blast_tac 1);
qed "parts_insert_subset_Un";

(*More specifically for Fake.  Very occasionally we could do with a version
  of the form  parts{X} <= synth (analz H) Un parts H *)
Goal "X: synth (analz H) ==> \
\     parts (insert X H) <= synth (analz H) Un parts H";
by (dtac parts_insert_subset_Un 1);
by (Full_simp_tac 1);
by (Blast_tac 1);
qed "Fake_parts_insert";

(*H is sometimes (Key ` KK Un spies evs), so can't put G=H*)
Goal "X: synth (analz G) ==> \
\     analz (insert X H) <= synth (analz G) Un analz (G Un H)";
by (rtac subsetI 1);
by (subgoal_tac "x \\<in> analz (synth (analz G) Un H)" 1);
by (blast_tac (claset() addIs [impOfSubs analz_mono,
			       impOfSubs (analz_mono RS synth_mono)]) 2);
by (Full_simp_tac 1);
by (Blast_tac 1);
qed "Fake_analz_insert";

Goal "(X: analz H & X: parts H) = (X: analz H)";
by (blast_tac (claset() addIs [impOfSubs analz_subset_parts]) 1);
val analz_conj_parts = result();

Goal "(X: analz H | X: parts H) = (X: parts H)";
by (blast_tac (claset() addIs [impOfSubs analz_subset_parts]) 1);
val analz_disj_parts = result();

AddIffs [analz_conj_parts, analz_disj_parts];

(*Without this equation, other rules for synth and analz would yield
  redundant cases*)
Goal "({|X,Y|} \\<in> synth (analz H)) = \
\     (X \\<in> synth (analz H) & Y \\<in> synth (analz H))";
by (Blast_tac 1);
qed "MPair_synth_analz";

AddIffs [MPair_synth_analz];

Goal "[| Key K \\<in> analz H;  Key (invKey K) \\<in> analz H |] \
\      ==> (Crypt K X \\<in> synth (analz H)) = (X \\<in> synth (analz H))";
by (Blast_tac 1);
qed "Crypt_synth_analz";


Goal "X \\<notin> synth (analz H) \
\     ==> (Hash{|X,Y|} \\<in> synth (analz H)) = (Hash{|X,Y|} \\<in> analz H)";
by (Blast_tac 1);
qed "Hash_synth_analz";
Addsimps [Hash_synth_analz];


(**** HPair: a combination of Hash and MPair ****)

(*** Freeness ***)

Goalw [HPair_def] "Agent A ~= Hash[X] Y";
by (Simp_tac 1);
qed "Agent_neq_HPair";

Goalw [HPair_def] "Nonce N ~= Hash[X] Y";
by (Simp_tac 1);
qed "Nonce_neq_HPair";

Goalw [HPair_def] "Number N ~= Hash[X] Y";
by (Simp_tac 1);
qed "Number_neq_HPair";

Goalw [HPair_def] "Key K ~= Hash[X] Y";
by (Simp_tac 1);
qed "Key_neq_HPair";

Goalw [HPair_def] "Hash Z ~= Hash[X] Y";
by (Simp_tac 1);
qed "Hash_neq_HPair";

Goalw [HPair_def] "Crypt K X' ~= Hash[X] Y";
by (Simp_tac 1);
qed "Crypt_neq_HPair";

val HPair_neqs = [Agent_neq_HPair, Nonce_neq_HPair, Number_neq_HPair, 
                  Key_neq_HPair, Hash_neq_HPair, Crypt_neq_HPair];

AddIffs HPair_neqs;
AddIffs (HPair_neqs RL [not_sym]);

Goalw [HPair_def] "(Hash[X'] Y' = Hash[X] Y) = (X' = X & Y'=Y)";
by (Simp_tac 1);
qed "HPair_eq";

Goalw [HPair_def] "({|X',Y'|} = Hash[X] Y) = (X' = Hash{|X,Y|} & Y'=Y)";
by (Simp_tac 1);
qed "MPair_eq_HPair";

Goalw [HPair_def] "(Hash[X] Y = {|X',Y'|}) = (X' = Hash{|X,Y|} & Y'=Y)";
by Auto_tac;
qed "HPair_eq_MPair";

AddIffs [HPair_eq, MPair_eq_HPair, HPair_eq_MPair];


(*** Specialized laws, proved in terms of those for Hash and MPair ***)

Goalw [HPair_def] "keysFor (insert (Hash[X] Y) H) = keysFor H";
by (Simp_tac 1);
qed "keysFor_insert_HPair";

Goalw [HPair_def]
    "parts (insert (Hash[X] Y) H) = \
\    insert (Hash[X] Y) (insert (Hash{|X,Y|}) (parts (insert Y H)))";
by (Simp_tac 1);
qed "parts_insert_HPair";

Goalw [HPair_def]
    "analz (insert (Hash[X] Y) H) = \
\    insert (Hash[X] Y) (insert (Hash{|X,Y|}) (analz (insert Y H)))";
by (Simp_tac 1);
qed "analz_insert_HPair";

Goalw [HPair_def] "X \\<notin> synth (analz H) \
\   ==> (Hash[X] Y \\<in> synth (analz H)) = \
\       (Hash {|X, Y|} \\<in> analz H & Y \\<in> synth (analz H))";
by (Simp_tac 1);
by (Blast_tac 1);
qed "HPair_synth_analz";

Addsimps [keysFor_insert_HPair, parts_insert_HPair, analz_insert_HPair, 
          HPair_synth_analz, HPair_synth_analz];


(*We do NOT want Crypt... messages broken up in protocols!!*)
Delrules [make_elim parts.Body];


(** Rewrites to push in Key and Crypt messages, so that other messages can
    be pulled out using the analz_insert rules **)

fun insComm x y = inst "x" x (inst "y" y insert_commute);

val pushKeys = map (insComm "Key ?K") 
                   ["Agent ?C", "Nonce ?N", "Number ?N", 
		    "Hash ?X", "MPair ?X ?Y", "Crypt ?X ?K'"];

val pushCrypts = map (insComm "Crypt ?X ?K") 
                     ["Agent ?C", "Nonce ?N", "Number ?N", 
		      "Hash ?X'", "MPair ?X' ?Y"];

(*Cannot be added with Addsimps -- we don't always want to re-order messages*)
bind_thms ("pushes", pushKeys@pushCrypts);


(*** Tactics useful for many protocol proofs ***)

(*Prove base case (subgoal i) and simplify others.  A typical base case
  concerns  Crypt K X \\<notin> Key`shrK`bad  and cannot be proved by rewriting
  alone.*)
fun prove_simple_subgoals_tac i = 
    force_tac (claset(), simpset() addsimps [image_eq_UN]) i THEN
    ALLGOALS Asm_simp_tac;

fun Fake_parts_insert_tac i = 
    blast_tac (claset() addIs [parts_insertI]
			addDs [impOfSubs analz_subset_parts,
			       impOfSubs Fake_parts_insert]) i;

(*Apply rules to break down assumptions of the form
  Y \\<in> parts(insert X H)  and  Y \\<in> analz(insert X H)
*)
val Fake_insert_tac = 
    dresolve_tac [impOfSubs Fake_analz_insert,
                  impOfSubs Fake_parts_insert] THEN'
    eresolve_tac [asm_rl, synth.Inj];

fun Fake_insert_simp_tac i = 
    REPEAT (Fake_insert_tac i) THEN Asm_full_simp_tac i;


(*Analysis of Fake cases.  Also works for messages that forward unknown parts,
  but this application is no longer necessary if analz_insert_eq is used.
  Abstraction over i is ESSENTIAL: it delays the dereferencing of claset
  DEPENDS UPON "X" REFERRING TO THE FRADULENT MESSAGE *)

val atomic_spy_analz_tac = SELECT_GOAL
    (Fake_insert_simp_tac 1
     THEN
     IF_UNSOLVED (Blast.depth_tac
		  (claset() addIs [analz_insertI,
				   impOfSubs analz_subset_parts]) 4 1));

fun spy_analz_tac i =
  DETERM
   (SELECT_GOAL
     (EVERY 
      [  (*push in occurrences of X...*)
       (REPEAT o CHANGED)
           (res_inst_tac [("x1","X")] (insert_commute RS ssubst) 1),
       (*...allowing further simplifications*)
       Simp_tac 1,
       REPEAT (FIRSTGOAL (resolve_tac [allI,impI,notI,conjI,iffI])),
       DEPTH_SOLVE (atomic_spy_analz_tac 1)]) i);

(*By default only o_apply is built-in.  But in the presence of eta-expansion
  this means that some terms displayed as (f o g) will be rewritten, and others
  will not!*)
Addsimps [o_def];
