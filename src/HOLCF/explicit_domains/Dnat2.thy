(*  Title: 	HOLCF/Dnat2.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Additional constants for dnat

*)

Dnat2 = Dnat +

consts

iterator	:: "dnat -> ('a -> 'a) -> 'a -> 'a"


defs

iterator_def	"iterator == fix`(LAM h n f x.
			dnat_when `x `(LAM m.f`(h`m`f`x)) `n)"
end

(*

		iterator`UU`f`x = UU
		iterator`dzero`f`x = x
      n~=UU --> iterator`(dsucc`n)`f`x = f`(iterator`n`f`x)
*)

