(*  Title:      HOL/BCV/Orders0.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM

Orderings on various types.
*)

Orders0 = Main +

instance option :: (ord)ord
instance list   :: (ord)ord
instance "*" :: (ord,ord)ord

defs
le_option "o1 <= o2 == case o2 of None => o1=None |
                         Some y => (case o1 of None => True | Some x => x<=y)"
less_option "(o1::('a::ord)option) < o2 == o1 <= o2 & o1 ~= o2"

le_list "xs <= ys == size xs = size ys & (!i. i<size xs --> xs!i <= ys!i)"
less_list "(xs::('a::ord)list) < ys == xs <= ys & xs ~= ys"

le_prod "p1 <= p2 == fst p1 <= fst p2 & snd p1 <= snd p2"
less_prod "(p1::('a::ord * 'b::ord)) < p2 == p1 <= p2 & p1 ~= p2"

end
