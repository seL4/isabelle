(*  Title: 	ZF/bool.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Booleans in Zermelo-Fraenkel Set Theory 

2 is equal to bool, but serves a different purpose
*)

Bool = ZF + "simpdata" +
consts
    "1"		:: "i"     	   ("1")
    "2"         :: "i"             ("2")
    bool        :: "i"
    cond        :: "[i,i,i]=>i"
    not		:: "i=>i"
    "and"       :: "[i,i]=>i"      (infixl 70)
    or		:: "[i,i]=>i"      (infixl 65)
    xor		:: "[i,i]=>i"      (infixl 65)

translations
   "1"  == "succ(0)"
   "2"  == "succ(1)"

defs
    bool_def	"bool == {0,1}"
    cond_def	"cond(b,c,d) == if(b=1,c,d)"
    not_def	"not(b) == cond(b,0,1)"
    and_def	"a and b == cond(a,b,0)"
    or_def	"a or b == cond(a,1,b)"
    xor_def	"a xor b == cond(a,not(b),b)"
end
