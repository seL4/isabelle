(*  ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

*)

header{*Association Lists*}

theory AList
imports Main
begin

consts
  alist_rec  :: "[('a*'b)list, 'c, ['a, 'b, ('a*'b)list, 'c]=>'c] => 'c"
  assoc      :: "['a,'b,('a*'b) list] => 'b"

primrec
  "alist_rec [] c d = c"
  "alist_rec (p # al) c d = d (fst p) (snd p) al (alist_rec al c d)"

primrec
  "assoc v d [] = d"
  "assoc v d (p # al) = (if v = fst p then snd p else assoc v d al)"


lemma alist_induct:
    "[| P([]);    
        !!x y xs. P(xs) ==> P((x,y)#xs) |]  ==> P(l)"
by (induct_tac "l", auto)

end
