(*  Title:      HOL/Lex/AutoMaxChop.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

theory AutoMaxChop = DA + MaxChop:

consts
 auto_split :: "('a,'s)da => 's  => 'a list * 'a list => 'a list => 'a splitter"
primrec
"auto_split A q res ps []     = (if fin A q then (ps,[]) else res)"
"auto_split A q res ps (x#xs) =
   auto_split A (next A x q) (if fin A q then (ps,x#xs) else res) (ps@[x]) xs"

constdefs
 auto_chop :: "('a,'s)da => 'a chopper"
"auto_chop A == chop (%xs. auto_split A (start A) ([],xs) [] xs)"
end
