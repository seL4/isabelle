(*  Title:      HOL/IMP/Transition.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Robert Sandner, TUM
    Copyright   1996 TUM

Transition semantics of commands
*)

Transition = Natural + RelPow +

consts  evalc1    :: "((com*state)*(com*state))set"        
	"@evalc1" :: "[(com*state),(com*state)] => bool"   
				("_ -1-> _" [81,81] 100)
	"@evalcn" :: "[(com*state),(com*state)] => nat => bool"
				("_ -_-> _" [81,81] 100)
	"@evalc*" :: "[(com*state),(com*state)] => bool"   
				("_ -*-> _" [81,81] 100)

translations
       	"cs0 -1-> cs1" == "(cs0,cs1) : evalc1"
	"cs0 -n-> cs1" == "(cs0,cs1) : evalc1^n"
	"cs0 -*-> cs1" == "(cs0,cs1) : evalc1^*"


inductive evalc1
  intrs
    Assign "(x := a,s) -1-> (SKIP,s[x := a s])"

    Semi1   "(SKIP;c,s) -1-> (c,s)"	
    Semi2   "(c0,s) -1-> (c2,s1) ==> (c0;c1,s) -1-> (c2;c1,s1)"

    IfTrue "b s ==> (IF b THEN c1 ELSE c2,s) -1-> (c1,s)"
    IfFalse "~b s ==> (IF b THEN c1 ELSE c2,s) -1-> (c2,s)"

    WhileFalse "~b s ==> (WHILE b DO c,s) -1-> (SKIP,s)"
    WhileTrue "b s ==> (WHILE b DO c,s) -1-> (c;WHILE b DO c,s)"

end
