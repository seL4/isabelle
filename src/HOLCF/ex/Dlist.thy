(*  Title:      HOLCF/Dlist.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Theory for finite lists  'a dlist = one ++ ('a ** 'a dlist)
*)

Dlist = Classlib +

domain 'a dlist = dnil | "##" (dhd::'a) (dtl::'a dlist) (cinfixr 65)


consts

lmap	:: "('a -> 'b) -> 'a dlist -> 'b dlist"
lmem	:: "('a::eq)  -> 'a dlist -> tr"

defs

lmap_def "lmap == fix`(LAM h f s. case s of dnil => dnil
			          | x ## xs => f`x ## h`f`xs)"

lmem_def "lmem == fix`(LAM h e l. case l of dnil => FF
     	 	  		  | x ## xs => If e Ù x then TT else h`e`xs fi)"

end
