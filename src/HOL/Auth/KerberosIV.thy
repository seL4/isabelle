(*  Title:      HOL/Auth/KerberosIV
    ID:         $Id$
    Author:     Giampaolo Bella, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Kerberos protocol, version IV.
*)

KerberosIV = Shared +

syntax
  Kas, Tgs :: agent    (*the two servers are translations...*)


translations
  "Kas"       == "Server"
  "Tgs"       == "Friend 0"   


rules
  (*Tgs is secure --- we already know that Kas is secure*)
  Tgs_not_bad "Tgs \\<notin> bad"
  
(*The current time is just the length of the trace!*)
syntax
    CT :: event list=>nat

    ExpirAuth :: [nat, event list] => bool

    ExpirServ :: [nat, event list] => bool 

    ExpirAutc :: [nat, event list] => bool 

    RecentResp :: [nat, nat] => bool


constdefs
 (* AuthKeys are those contained in an AuthTicket *)
    AuthKeys :: event list => key set
    "AuthKeys evs == {AuthKey. \\<exists>A Peer Tk. Says Kas A
                        (Crypt (shrK A) {|Key AuthKey, Agent Peer, Tk, 
                   (Crypt (shrK Peer) {|Agent A, Agent Peer, Key AuthKey, Tk|})
                  |}) \\<in> set evs}"
                      
 (* A is the true creator of X if she has sent X and X never appeared on
    the trace before this event. Recall that traces grow from head. *)
  Issues :: [agent , agent, msg, event list] => bool ("_ Issues _ with _ on _")
   "A Issues B with X on evs == 
      \\<exists>Y. Says A B Y \\<in> set evs & X \\<in> parts {Y} &
      X \\<notin> parts (spies (takeWhile (% z. z  \\<noteq> Says A B Y) (rev evs)))"


consts

    (*Duration of the authentication key*)
    AuthLife   :: nat

    (*Duration of the service key*)
    ServLife   :: nat

    (*Duration of an authenticator*)
    AutcLife   :: nat

    (*Upper bound on the time of reaction of a server*)
    RespLife   :: nat 

rules
     AuthLife_LB    "#2 <= AuthLife"
     ServLife_LB    "#2 <= ServLife"
     AutcLife_LB    "1' <= AutcLife" 
     RespLife_LB    "1' <= RespLife"

translations
   "CT" == "length"

   "ExpirAuth T evs" == "AuthLife + T < CT evs"

   "ExpirServ T evs" == "ServLife + T < CT evs"

   "ExpirAutc T evs" == "AutcLife + T < CT evs"

   "RecentResp T1 T2" == "T1 <= RespLife + T2"

(*---------------------------------------------------------------------*)


(* Predicate formalising the association between AuthKeys and ServKeys *)
constdefs 
  KeyCryptKey :: [key, key, event list] => bool
  "KeyCryptKey AuthKey ServKey evs ==
     \\<exists>A B tt. 
       Says Tgs A (Crypt AuthKey
                     {|Key ServKey, Agent B, tt,
                       Crypt (shrK B) {|Agent A, Agent B, Key ServKey, tt|} |})
         \\<in> set evs"

consts

kerberos   :: event list set
inductive "kerberos"
  intrs 
        
    Nil  "[] \\<in> kerberos"

    Fake "[| evsf \\<in> kerberos;  X \\<in> synth (analz (spies evsf)) |]
          ==> Says Spy B X  # evsf \\<in> kerberos"

(* FROM the initiator *)
    K1   "[| evs1 \\<in> kerberos |]
          ==> Says A Kas {|Agent A, Agent Tgs, Number (CT evs1)|} # evs1 
          \\<in> kerberos"

(* Adding the timestamp serves to A in K3 to check that
   she doesn't get a reply too late. This kind of timeouts are ordinary. 
   If a server's reply is late, then it is likely to be fake. *)

(*---------------------------------------------------------------------*)

(*FROM Kas *)
    K2  "[| evs2 \\<in> kerberos; Key AuthKey \\<notin> used evs2;
            Says A' Kas {|Agent A, Agent Tgs, Number Ta|} \\<in> set evs2 |]
          ==> Says Kas A
                (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number (CT evs2), 
                      (Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, 
                          Number (CT evs2)|})|}) # evs2 \\<in> kerberos"
(* 
  The internal encryption builds the AuthTicket.
  The timestamp doesn't change inside the two encryptions: the external copy
  will be used by the initiator in K3; the one inside the 
  AuthTicket by Tgs in K4.
*)

(*---------------------------------------------------------------------*)

(* FROM the initiator *)
    K3  "[| evs3 \\<in> kerberos; 
            Says A Kas {|Agent A, Agent Tgs, Number Ta|} \\<in> set evs3;
            Says Kas' A (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, 
              AuthTicket|}) \\<in> set evs3; 
            RecentResp Tk Ta
         |]
          ==> Says A Tgs {|AuthTicket, 
                           (Crypt AuthKey {|Agent A, Number (CT evs3)|}), 
                           Agent B|} # evs3 \\<in> kerberos"
(*The two events amongst the premises allow A to accept only those AuthKeys 
  that are not issued late. *)

(*---------------------------------------------------------------------*)

(* FROM Tgs *)
(* Note that the last temporal check is not mentioned in the original MIT
   specification. Adding it strengthens the guarantees assessed by the 
   protocol. Theorems that exploit it have the suffix `_refined'
*) 
    K4  "[| evs4 \\<in> kerberos; Key ServKey \\<notin> used evs4; B \\<noteq> Tgs; 
            Says A' Tgs {|
             (Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey,
				 Number Tk|}),
             (Crypt AuthKey {|Agent A, Number Ta1|}), Agent B|}
	        \\<in> set evs4;
            ~ ExpirAuth Tk evs4;
            ~ ExpirAutc Ta1 evs4; 
            ServLife + (CT evs4) <= AuthLife + Tk
         |]
          ==> Says Tgs A 
                (Crypt AuthKey {|Key ServKey, Agent B, Number (CT evs4),  
			       Crypt (shrK B) {|Agent A, Agent B, Key ServKey,
		 			        Number (CT evs4)|} |})
	        # evs4 \\<in> kerberos"
(* Tgs creates a new session key per each request for a service, without 
   checking if there is still a fresh one for that service.
   The cipher under Tgs' key is the AuthTicket, the cipher under B's key
   is the ServTicket, which is built now.
   NOTE that the last temporal check is not present in the MIT specification.
  
*)

(*---------------------------------------------------------------------*)

(* FROM the initiator *)
    K5  "[| evs5 \\<in> kerberos;  
            Says A Tgs 
                {|AuthTicket, (Crypt AuthKey {|Agent A, Number Ta1|} ),
		  Agent B|}
              \\<in> set evs5;
            Says Tgs' A 
             (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|} ) 
                \\<in> set evs5;
            RecentResp Tt Ta1 |]
          ==> Says A B {|ServTicket,
			 Crypt ServKey {|Agent A, Number (CT evs5)|} |}
               # evs5 \\<in> kerberos"
(* Checks similar to those in K3. *)

(*---------------------------------------------------------------------*)

(* FROM the responder*)
     K6  "[| evs6 \\<in> kerberos;
            Says A' B {|           
              (Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|} ),
              (Crypt ServKey {|Agent A, Number Ta2|} )|}
            \\<in> set evs6;
            ~ ExpirServ Tt evs6;
            ~ ExpirAutc Ta2 evs6
         |]
          ==> Says B A (Crypt ServKey (Number Ta2) )
               # evs6 \\<in> kerberos"
(* Checks similar to those in K4. *)

(*---------------------------------------------------------------------*)

(* Leaking an AuthKey... *)
    Oops1 "[| evsO1 \\<in> kerberos;  A \\<noteq> Spy;
              Says Kas A
                (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, 
                                  AuthTicket|})  \\<in> set evsO1;
              ExpirAuth Tk evsO1 |]
          ==> Says A Spy {|Agent A, Agent Tgs, Number Tk, Key AuthKey|} 
               # evsO1 \\<in> kerberos"

(*---------------------------------------------------------------------*)

(*Leaking a ServKey... *)
    Oops2 "[| evsO2 \\<in> kerberos;  A \\<noteq> Spy;
              Says Tgs A 
                (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|})
                   \\<in> set evsO2;
              ExpirServ Tt evsO2 |]
          ==> Says A Spy {|Agent A, Agent B, Number Tt, Key ServKey|} 
               # evsO2 \\<in> kerberos"

(*---------------------------------------------------------------------*)


end
