(*  Title:      HOL/Auth/Message
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatypes of agents and messages;
Inductive relations "parts", "analz" and "synth"
*)

theory Message = Main
files ("Message_lemmas.ML"):

(*Needed occasionally with spy_analz_tac, e.g. in analz_insert_Key_newK*)
lemma [simp] : "A Un (B Un A) = B Un A"
by blast

types 
  key = nat

consts
  invKey :: "key=>key"

axioms
  invKey [simp] : "invKey (invKey K) = K"

  (*The inverse of a symmetric key is itself;
    that of a public key is the private key and vice versa*)

constdefs
  symKeys :: "key set"
  "symKeys == {K. invKey K = K}"

datatype  (*We allow any number of friendly agents*)
  agent = Server | Friend nat | Spy

datatype
     msg = Agent  agent	    (*Agent names*)
         | Number nat       (*Ordinary integers, timestamps, ...*)
         | Nonce  nat       (*Unguessable nonces*)
         | Key    key       (*Crypto keys*)
	 | Hash   msg       (*Hashing*)
	 | MPair  msg msg   (*Compound messages*)
	 | Crypt  key msg   (*Encryption, public- or shared-key*)


(*Concrete syntax: messages appear as {|A,B,NA|}, etc...*)
syntax
  "@MTuple"      :: "['a, args] => 'a * 'b"       ("(2{|_,/ _|})")

syntax (xsymbols)
  "@MTuple"      :: "['a, args] => 'a * 'b"       ("(2\<lbrace>_,/ _\<rbrace>)")

translations
  "{|x, y, z|}"   == "{|x, {|y, z|}|}"
  "{|x, y|}"      == "MPair x y"


constdefs
  (*Message Y, paired with a MAC computed with the help of X*)
  HPair :: "[msg,msg] => msg"                       ("(4Hash[_] /_)" [0, 1000])
    "Hash[X] Y == {| Hash{|X,Y|}, Y|}"

  (*Keys useful to decrypt elements of a message set*)
  keysFor :: "msg set => key set"
  "keysFor H == invKey ` {K. \<exists>X. Crypt K X \<in> H}"

(** Inductive definition of all "parts" of a message.  **)

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


(** Inductive definition of "analz" -- what can be broken down from a set of
    messages, including keys.  A form of downward closure.  Pairs can
    be taken apart; messages decrypted with known keys.  **)

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

(** Inductive definition of "synth" -- what can be built up from a set of
    messages.  A form of upward closure.  Pairs can be built, messages
    encrypted with known keys.  Agent names are public domain.
    Numbers can be guessed, but Nonces cannot be.  **)

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

use "Message_lemmas.ML"

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


lemmas analz_into_parts = analz_subset_parts [THEN subsetD, standard]

lemma Fake_parts_insert_in_Un:
     "[|Z \<in> parts (insert X H);  X: synth (analz H)|] 
      ==> Z \<in>  synth (analz H) \<union> parts H";
by (blast dest: Fake_parts_insert  [THEN subsetD, dest])

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
     "X \<in> synth (analz H) ==> parts{X} \<subseteq> synth (analz H) Un parts H";
apply (rule subset_trans) 
 apply (erule_tac [2] Fake_parts_insert) 
apply (simp add: parts_mono) 
done

method_setup spy_analz = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts => 
            gen_spy_analz_tac (Classical.get_local_claset ctxt,
                               Simplifier.get_local_simpset ctxt) 1)) *}
    "for proving the Fake case when analz is involved"

method_setup atomic_spy_analz = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts => 
            atomic_spy_analz_tac (Classical.get_local_claset ctxt,
                                  Simplifier.get_local_simpset ctxt) 1)) *}
    "for debugging spy_analz"

method_setup Fake_insert_simp = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts =>
            Fake_insert_simp_tac (Simplifier.get_local_simpset ctxt) 1)) *}
    "for debugging spy_analz"

end
