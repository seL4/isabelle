(*  Title: 	HOL/Lambda/Confluence.thy
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1995  TU Muenchen

Abstract confluence notions.
*)

Confluence = Trancl +

consts
  confluent, confluent1, diamondP :: "('a*'a)set => bool"

defs
  diamondP_def
  "diamondP(R) ==   \
\  !x y. (x,y):R --> (!z. (x,z):R --> (EX u. (y,u):R & (z,u):R))" 

  confluent_def "confluent(R) == diamondP(R^*)"

  confluent1_def
  "confluent1(R) ==
   !x y. (x,y):R --> (!z. (x,z):R^* --> (EX u. (y,u):R^* & (z,u):R^*))"

rules
  diamondP_confluent1 "diamondP R ==> confluent1(R)"
end
