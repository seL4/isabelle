(*  Title:      HOL/Lex/MaxPrefix.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

MaxPrefix = Prefix +

constdefs
 is_maxpref :: ('a list => bool) => 'a list => 'a list => bool
"is_maxpref P xs ys ==
 xs <= ys & (xs=[] | P xs) & (!zs. zs <= ys & P zs --> zs <= xs)"

types 'a splitter = "'a list => 'a list * 'a list"
constdefs
 is_maxsplitter :: "('a list => bool) => 'a splitter => bool"
"is_maxsplitter P f ==
 (!xs ps qs. f xs = (ps,qs) = (xs=ps@qs & is_maxpref P ps xs))"

consts
 maxsplit :: "('a list => bool) => 'a list * 'a list => 'a list => 'a splitter"
primrec maxsplit list
"maxsplit P res ps []     = (if P ps then (ps,[]) else res)"
"maxsplit P res ps (q#qs) = maxsplit P (if P ps then (ps,q#qs) else res)
                                     (ps@[q]) qs"
end
