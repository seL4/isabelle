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

  (*We do not assume  Crypt (Crypt X K) (invKey K) = X
    because Crypt is a constructor!  We assume that encryption is injective,
    which is not true in the real world.  The alternative is to take
    Crypt as an uninterpreted function symbol satisfying the equation
    above.  This seems to require moving to ZF and regarding msg as an
    inductive definition instead of a datatype.*) 

datatype  (*We allow any number of friendly agents*)
  agent = Server | Friend nat | Enemy

consts  
  isEnemy :: agent => bool

primrec isEnemy agent
  isEnemy_Server  "isEnemy Server  = False"
  isEnemy_Friend  "isEnemy (Friend i) = False"
  isEnemy_Enemy   "isEnemy Enemy = True"

datatype  (*Messages are agent names, nonces, keys, pairs and encryptions*)
  msg = Agent agent
      | Nonce nat
      | Key   key
      | MPair msg msg
      | Crypt msg key

(*Allows messages of the form {|A,B,NA|}, etc...*)
syntax
  "@MTuple"      :: "['a, args] => 'a * 'b"            ("(1{|_,/ _|})")

translations
  "{|x, y, z|}"   == "{|x, {|y, z|}|}"
  "{|x, y|}"      == "MPair x y"


constdefs  (*Keys useful to decrypt elements of a message set*)
  keysFor :: msg set => key set
  "keysFor H == invKey `` {K. EX X. Crypt X K : H}"

(** Inductive definition of all "parts" of a message.  **)

consts  parts   :: msg set => msg set
inductive "parts H"
  intrs 
    Inj     "X: H ==> X: parts H"
    Fst     "{|X,Y|} : parts H ==> X : parts H"
    Snd     "{|X,Y|} : parts H ==> Y : parts H"
    Body    "Crypt X K : parts H ==> X : parts H"


(** Inductive definition of "analz" -- what can be broken down from a set of
    messages, including keys.  A form of downward closure.  Pairs can
    be taken apart; messages decrypted with known keys.  **)

consts  analz   :: msg set => msg set
inductive "analz H"
  intrs 
    Inj     "X: H ==> X: analz H"
    Fst     "{|X,Y|} : analz H ==> X : analz H"
    Snd     "{|X,Y|} : analz H ==> Y : analz H"
    Decrypt "[| Crypt X K : analz H; Key(invKey K): analz H |] ==> X : analz H"


(** Inductive definition of "synth" -- what can be built up from a set of
    messages.  A form of upward closure.  Pairs can be built, messages
    encrypted with known keys.  Agent names may be quoted.  **)

consts  synth   :: msg set => msg set
inductive "synth H"
  intrs 
    Inj     "X: H ==> X: synth H"
    Agent   "Agent agt : synth H"
    MPair   "[| X: synth H;  Y: synth H |] ==> {|X,Y|} : synth H"
    Crypt   "[| X: synth H; Key(K): synth H |] ==> Crypt X K : synth H"

end
