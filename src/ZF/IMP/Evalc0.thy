(*  Title: 	ZF/IMP/Evalc0.thy
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

Evalc0 = Evalb + Com + Assign +

consts
       evalc    :: "i"
       "@evalc" :: "[i,i,i] => o"   ("<_,_>/ -c-> _")

translations
       "<ce,sig> -c-> s" == "<ce,sig,s> : evalc"
end
