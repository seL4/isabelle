(*  Title:      HOL/Lex/AutoMaxChop.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

AutoMaxChop = Auto + MaxChop +

consts
 auto_split :: "('a,'s)auto => 's => 'a list => 'a list => 'a list * 'a list
                => 'a list * 'a list"
primrec auto_split list
"auto_split A q ps []     res = (if fin A q then (ps,[]) else res)"
"auto_split A q ps (x#xs) res = auto_split A (next A q x) (ps@[x]) xs
                                     (if fin A q then (ps,x#xs) else res)"

constdefs
 auto_chop :: "('a,'s)auto => 'a chopper"
"auto_chop A == chop (%xs. auto_split A (start A) [] xs ([],xs))"
end
