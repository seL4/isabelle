(*  Title:      HOL/Lex/RegExp2NAe.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Conversion of regular expressions
into nondeterministic automata with epsilon transitions
*)

RegExp2NAe = RegExp + NAe +

types 'a bitsNAe = ('a,bool list)nae

syntax "##" :: 'a => 'a list set => 'a list set (infixr 65)
translations "x ## S" == "Cons x ` S"

constdefs
 atom  :: 'a => 'a bitsNAe
"atom a == ([True],
            %b s. if s=[True] & b=Some a then {[False]} else {},
            %s. s=[False])"

 or :: 'a bitsNAe => 'a bitsNAe => 'a bitsNAe
"or == %(ql,dl,fl)(qr,dr,fr).
   ([],
    %a s. case s of
            [] => if a=None then {True#ql,False#qr} else {}
          | left#s => if left then True ## dl a s
                              else False ## dr a s,
    %s. case s of [] => False | left#s => if left then fl s else fr s)"

 conc :: 'a bitsNAe => 'a bitsNAe => 'a bitsNAe
"conc == %(ql,dl,fl)(qr,dr,fr).
   (True#ql,
    %a s. case s of
            [] => {}
          | left#s => if left then (True ## dl a s) Un
                                   (if fl s & a=None then {False#qr} else {})
                              else False ## dr a s,
    %s. case s of [] => False | left#s => ~left & fr s)"

 star :: 'a bitsNAe => 'a bitsNAe
"star == %(q,d,f).
   ([],
    %a s. case s of
            [] => if a=None then {True#q} else {}
          | left#s => if left then (True ## d a s) Un
                                   (if f s & a=None then {True#q} else {})
                              else {},
    %s. case s of [] => True | left#s => left & f s)"

consts rexp2nae :: 'a rexp => 'a bitsNAe
primrec
"rexp2nae Empty      = ([], %a s. {}, %s. False)"
"rexp2nae(Atom a)    = atom a"
"rexp2nae(Or r s)    = or   (rexp2nae r) (rexp2nae s)"
"rexp2nae(Conc r s)  = conc (rexp2nae r) (rexp2nae s)"
"rexp2nae(Star r)    = star (rexp2nae r)"

end
