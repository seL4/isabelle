(*  Title: 	ZF/IMP/Evala0.thy
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

Evala0 = Aexp +

consts  evala    :: "i"
       "@evala"  :: "[i,i,i] => o"	("<_,_>/ -a-> _")

translations
 "<ae,sig> -a-> n" == "<ae,sig,n> : evala"
end
