(*  Title:      HOL/Auth/NSP_Bad
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

add_path "../Auth"; use_thy"NSP_Bad";

Security protocols in UNITY: Needham-Schroeder, public keys (flawed version).

Original file is ../Auth/NS_Public_Bad
*)

NSP_Bad = Public + UNITY_Main + 

types state = event list

constdefs
  
  (*The spy MAY say anything he CAN say.  We do not expect him to
    invent new nonces here, but he can also use NS1.  Common to
    all similar protocols.*)
  Fake :: "(state*state) set"
    "Fake == {(s,s').
	      EX B X. s' = Says Spy B X # s
		    & X: synth (analz (spies s))}"
  
  (*The numeric suffixes on A identify the rule*)

  (*Alice initiates a protocol run, sending a nonce to Bob*)
  NS1 :: "(state*state) set"
    "NS1 == {(s1,s').
	     EX A1 B NA.
	         s' = Says A1 B (Crypt (pubK B) {|Nonce NA, Agent A1|}) # s1
	       & Nonce NA ~: used s1}"
  
  (*Bob responds to Alice's message with a further nonce*)
  NS2 :: "(state*state) set"
    "NS2 == {(s2,s').
	     EX A' A2 B NA NB.
	         s' = Says B A2 (Crypt (pubK A2) {|Nonce NA, Nonce NB|}) # s2
               & Says A' B (Crypt (pubK B) {|Nonce NA, Agent A2|}) : set s2
	       & Nonce NB ~: used s2}"
 
  (*Alice proves her existence by sending NB back to Bob.*)
  NS3 :: "(state*state) set"
    "NS3 == {(s3,s').
	     EX A3 B' B NA NB.
	         s' = Says A3 B (Crypt (pubK B) (Nonce NB)) # s3
               & Says A3  B (Crypt (pubK B) {|Nonce NA, Agent A3|}) : set s3
	       & Says B' A3 (Crypt (pubK A3) {|Nonce NA, Nonce NB|}) : set s3}"



constdefs
  Nprg :: state program
    (*Initial trace is empty*)
    "Nprg == mk_total_program({[]}, {Fake, NS1, NS2, NS3}, UNIV)"

end
