(*  Title:      HOL/Auth/Message
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatypes of agents and messages;
Inductive relations "parts", "analz" and "synth"
*)

Message = Arith +

(*Is there a difference between a nonce and arbitrary numerical data?
  Do we need a type of nonces?*)

types 
  key = nat

consts
  invKey :: key=>key

rules
  invKey "invKey (invKey K) = K"

  (*The inverse of a symmetric key is itself;
    that of a public key is the private key and vice versa*)

constdefs
  isSymKey :: key=>bool
  "isSymKey K == (invKey K = K)"

datatype  (*We allow any number of friendly agents*)
  agent = Server | Friend nat | Spy

datatype  (*Messages are agent names, nonces, keys, pairs and encryptions*)
  msg = Agent agent
      | Nonce nat
      | Key   key
      | Hash  msg
      | MPair msg msg
      | Crypt key msg

(*Allows messages of the form {|A,B,NA|}, etc...*)
syntax
  "@MTuple"      :: "['a, args] => 'a * 'b"       ("(2{|_,/ _|})")

translations
  "{|x, y, z|}"   == "{|x, {|y, z|}|}"
  "{|x, y|}"      == "MPair x y"


constdefs
  (*Message Y, paired with a MAC computed with the help of X*)
  HPair :: "[msg,msg]=>msg"                       ("(4Hash[_] /_)" [0, 1000])
    "Hash[X] Y == {| Hash{|X,Y|}, Y|}"

  (*Keys useful to decrypt elements of a message set*)
  keysFor :: msg set => key set
  "keysFor H == invKey `` {K. EX X. Crypt K X : H}"

(** Inductive definition of all "parts" of a message.  **)

consts  parts   :: msg set => msg set
inductive "parts H"
  intrs 
    Inj     "X: H  ==>  X: parts H"
    Fst     "{|X,Y|}   : parts H ==> X : parts H"
    Snd     "{|X,Y|}   : parts H ==> Y : parts H"
    Body    "Crypt K X : parts H ==> X : parts H"


(** Inductive definition of "analz" -- what can be broken down from a set of
    messages, including keys.  A form of downward closure.  Pairs can
    be taken apart; messages decrypted with known keys.  **)

consts  analz   :: msg set => msg set
inductive "analz H"
  intrs 
    Inj     "X: H ==> X: analz H"
    Fst     "{|X,Y|} : analz H ==> X : analz H"
    Snd     "{|X,Y|} : analz H ==> Y : analz H"
    Decrypt "[| Crypt K X : analz H; Key(invKey K): analz H |] ==> X : analz H"


(** Inductive definition of "synth" -- what can be built up from a set of
    messages.  A form of upward closure.  Pairs can be built, messages
    encrypted with known keys.  Agent names may be quoted.  **)

consts  synth   :: msg set => msg set
inductive "synth H"
  intrs 
    Inj     "X: H ==> X: synth H"
    Agent   "Agent agt : synth H"
    Hash    "X: synth H ==> Hash X : synth H"
    MPair   "[| X: synth H;  Y: synth H |] ==> {|X,Y|} : synth H"
    Crypt   "[| X: synth H;  Key(K) : H |] ==> Crypt K X : synth H"

end
