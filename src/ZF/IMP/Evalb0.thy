(*  Title: 	ZF/IMP/Evalb0.thy
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

Evalb0 = Evala + Bexp +

consts 
        evalb	 :: "i"	
        "@evalb" :: "[i,i,i] => o"	("<_,_>/ -b-> _")

translations
	"<be,sig> -b-> b" == "<be,sig,b> : evalb"
end
