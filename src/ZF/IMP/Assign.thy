(*  Title: 	ZF/IMP/Assign.thy
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

Assign = Aexp +
consts 
	"assign" :: "[i,i,i] => i"	("_[_'/_]" [900,0,0] 900)

rules 
	assign_def	"sigma[m/x] == lam y:loc. if(y=x,m,sigma`y)"
end
