(*  Title:      HOL/Lex/RegExp.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Regular expressions
*)

RegExp = RegSet +

datatype 'a rexp = Empty
                 | Atom 'a
                 | Union ('a rexp) ('a rexp)
                 | Conc ('a rexp) ('a rexp)
                 | Star ('a rexp)

consts lang :: 'a rexp => 'a list set
primrec
"lang Empty = {}"
"lang (Atom a) = {[a]}"
"lang (Union el er) = (lang el) Un (lang er)"
"lang (Conc el er) = RegSet.conc (lang el) (lang er)"
"lang (Star e) = RegSet.star(lang e)"

end
