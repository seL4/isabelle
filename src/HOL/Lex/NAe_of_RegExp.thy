(*  Title:      HOL/Lex/NAe_of_RegExp.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Conversion of regular expressions
into nondeterministic automata with epsilon transitions
*)

NAe_of_RegExp = NAe + RegExp +

types 'a r2nae = ('a,bool list)nae

syntax "##" :: 'a => 'a list set => 'a list set (infixr 65)
translations "x ## S" == "op # x `` S"

constdefs
 atom  :: 'a => 'a r2nae
"atom a == ([True],
            %b s. if s=[True] & b=Some a then {[False]} else {},
            %s. s=[False])"

 union :: 'a r2nae => 'a r2nae => 'a r2nae
"union == %(ql,dl,fl)(qr,dr,fr).
   ([],
    %a s. case s of
            [] => if a=None then {True#ql,False#qr} else {}
          | left#s => if left then True ## dl a s
                              else False ## dr a s,
    %s. case s of [] => False | left#s => if left then fl s else fr s)"

 conc :: 'a r2nae => 'a r2nae => 'a r2nae
"conc == %(ql,dl,fl)(qr,dr,fr).
   (True#ql,
    %a s. case s of
            [] => {}
          | left#s => if left then (True ## dl a s) Un
                                   (if fl s & a=None then {False#qr} else {})
                              else False ## dr a s,
    %s. case s of [] => False | left#s => ~left & fr s)"

 star :: 'a r2nae => 'a r2nae
"star == %(q,d,f).
   ([],
    %a s. case s of
            [] => if a=None then {True#q} else {}
          | left#s => if left then (True ## d a s) Un
                                   (if f s & a=None then {True#q} else {})
                              else {},
    %s. case s of [] => True | left#s => left & f s)"

consts r2n :: 'a rexp => 'a r2nae
primrec r2n rexp
"r2n Empty = ([], %a s. {}, %s. False)"
"r2n(Atom a) = atom a"
"r2n(Union el er) = union(r2n el)(r2n er)"
"r2n(Conc el er) = conc(r2n el)(r2n er)"
"r2n(Star e) = star(r2n e)"

end
