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
primrec lang rexp
lang_Emp  "lang Empty = {}"
lang_Atom "lang (Atom a) = {[a]}"
lang_Un   "lang (Union el er) = (lang el) Un (lang er)"
lang_Conc "lang (Conc el er) = RegSet.conc (lang el) (lang er)"
lang_Star "lang (Star e) = RegSet.star(lang e)"

end
