(*  Title:      FOCUS/Witness.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1995 Technical University Munich

Witnesses for introduction of type cleasse in theory Classlib

The type one of HOLCF/One.thy is a witness for all the introduced classes.

the trivial instance for ++ -- ** // is circ 
the trivial instance for .= and .<=  is bullet

*)

Witness = HOLCF +

ops curried 
	"bullet":: "one -> one -> tr"			(cinfixl 55)

defs 

bullet_def	"(op bullet) Ú flift1(flift2 o (op =))"

end
