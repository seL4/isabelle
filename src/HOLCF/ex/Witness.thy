(*  Title:      FOCUS/Witness.thy
    ID:         $ $
    Author:     Franz Regensburger
    Copyright   1995 Technical University Munich

Witnesses for introduction of type cleasse in theory Classlib

The 8bit package is needed for this theory

The type void of HOLCF/Void.thy is a witness for all the introduced classes.

the trivial instance for ++ -- ** // is LAM x y.(UU::void) 
the trivial instance for .= and .<=  is LAM x y.(UU::tr)

*)

Witness = HOLCF +

ops curried 
	"circ"	:: "void -> void -> void"		(cinfixl 65)
	"bullet":: "void -> void -> tr"			(cinfixl 55)

defs 

circ_def	"(op circ) Ú (LAM x y.UU)"

bullet_def	"(op bullet) Ú (LAM x y.UU)"

end
