(*  Title:      HOLCF/Dnat.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Theory for the domain of natural numbers  dnat = one ++ dnat
*)

Dnat = HOLCF +

domain dnat = dzero | dsucc (dpred :: dnat)

constdefs

iterator :: "dnat -> ('a -> 'a) -> 'a -> 'a"
            "iterator == fix$(LAM h n f x . case n of dzero   => x
                                                    | dsucc$m => f$(h$m$f$x))"

end
