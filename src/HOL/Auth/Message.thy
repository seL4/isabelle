(*  Title:      HOL/Auth/Message
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatypes of agents and messages;
Inductive relations "parts", "analz" and "synth"
*)

theory Message = Main
files ("Message_lemmas.ML"):

(*Eliminates a commonly-occurring expression*)
lemma [simp] : "~ (ALL x. x~=y)"
by blast

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
  isSymKey :: "key=>bool"
  "isSymKey K == (invKey K = K)"

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
  "keysFor H == invKey ` {K. EX X. Crypt K X : H}"

(** Inductive definition of all "parts" of a message.  **)

consts  parts   :: "msg set => msg set"
inductive "parts H"
  intros 
    Inj [intro]          : "X: H  ==> X : parts H"
    Fst:     "{|X,Y|}   : parts H ==> X : parts H"
    Snd:     "{|X,Y|}   : parts H ==> Y : parts H"
    Body:    "Crypt K X : parts H ==> X : parts H"


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
    Inj [intro,simp] :    "X: H ==> X: analz H"
    Fst:     "{|X,Y|} : analz H ==> X : analz H"
    Snd:     "{|X,Y|} : analz H ==> Y : analz H"
    Decrypt [dest]: 
             "[|Crypt K X : analz H; Key(invKey K): analz H|] ==> X : analz H"


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
    Inj    [intro]:   "X: H ==> X: synth H"
    Agent  [intro]:   "Agent agt : synth H"
    Number [intro]:   "Number n  : synth H"
    Hash   [intro]:   "X: synth H ==> Hash X : synth H"
    MPair  [intro]:   "[|X: synth H;  Y: synth H|] ==> {|X,Y|} : synth H"
    Crypt  [intro]:   "[|X: synth H;  Key(K) : H|] ==> Crypt K X : synth H"

(*Monotonicity*)
lemma synth_mono: "G<=H ==> synth(G) <= synth(H)"
apply auto
apply (erule synth.induct) 
apply (auto dest: Fst Snd Body) 
done

(*NO Agent_synth, as any Agent name can be synthesized.  Ditto for Number*)
inductive_cases Nonce_synth [elim!]: "Nonce n : synth H"
inductive_cases Key_synth   [elim!]: "Key K : synth H"
inductive_cases Hash_synth  [elim!]: "Hash X : synth H"
inductive_cases MPair_synth [elim!]: "{|X,Y|} : synth H"
inductive_cases Crypt_synth [elim!]: "Crypt K X : synth H"

use "Message_lemmas.ML"

method_setup spy_analz = {*
    Method.no_args (Method.METHOD (fn facts => spy_analz_tac 1)) *}
    "for proving the Fake case when analz is involved"

end
