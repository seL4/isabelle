(*  Title:      HOL/Lex/RegExp2NA.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Conversion of regular expressions *directly*
into nondeterministic automata *without* epsilon transitions
*)

RegExp2NA = NA + RegExp +

types 'a bitsNA = ('a,bool list)na

syntax "##" :: 'a => 'a list set => 'a list set (infixr 65)
translations "x ## S" == "Cons x `` S"

constdefs
 atom  :: 'a => 'a bitsNA
"atom a == ([True],
            %b s. if s=[True] & b=a then {[False]} else {},
            %s. s=[False])"

 union :: 'a bitsNA => 'a bitsNA => 'a bitsNA
"union == %(ql,dl,fl)(qr,dr,fr).
   ([],
    %a s. case s of
            [] => (True ## dl a ql) Un (False ## dr a qr)
          | left#s => if left then True ## dl a s
                              else False ## dr a s,
    %s. case s of [] => (fl ql | fr qr)
                | left#s => if left then fl s else fr s)"

 conc :: 'a bitsNA => 'a bitsNA => 'a bitsNA
"conc == %(ql,dl,fl)(qr,dr,fr).
   (True#ql,
    %a s. case s of
            [] => {}
          | left#s => if left then (True ## dl a s) Un
                                   (if fl s then False ## dr a qr else {})
                              else False ## dr a s,
    %s. case s of [] => False | left#s => left & fl s & fr qr | ~left & fr s)"

 epsilon :: 'a bitsNA
"epsilon == ([],%a s. {}, %s. s=[])"

 plus :: 'a bitsNA => 'a bitsNA
"plus == %(q,d,f). (q, %a s. d a s Un (if f s then d a q else {}), f)"

 star :: 'a bitsNA => 'a bitsNA
"star A == union epsilon (plus A)"

consts rexp2na :: 'a rexp => 'a bitsNA
primrec
"rexp2na Empty      = ([], %a s. {}, %s. False)"
"rexp2na(Atom a)    = atom a"
"rexp2na(Union r s) = union (rexp2na r) (rexp2na s)"
"rexp2na(Conc r s)  = conc  (rexp2na r) (rexp2na s)"
"rexp2na(Star r)    = star  (rexp2na r)"

end
