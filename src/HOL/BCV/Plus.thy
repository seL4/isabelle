(*  Title:      HOL/BCV/Plus.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM

Supremum operation on various domains.
*)

Plus = Orders +

instance option :: (plus)plus
instance list   :: (plus)plus
instance "*"    :: (plus,plus)plus

consts list_plus :: "('a::plus)list => 'a list => 'a list"
primrec
"list_plus [] ys = ys"
"list_plus (x#xs) ys = (case ys of [] => x#xs | z#zs => (x+z)#list_plus xs zs)"
defs
plus_option "o1 + o2 == case o1 of None => o2
                        | Some x => (case o2 of None => o1
                                     | Some y => Some(x+y))"
plus_list "op + == list_plus"
plus_prod "op + == %(a,b) (c,d). (a+c,b+d)"

end
