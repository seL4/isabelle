(*  Title:      Substitutions/alist.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Association lists.
*)

AList = List + 

consts

  alist_rec  :: "[('a*'b)list, 'c, ['a, 'b, ('a*'b)list, 'c]=>'c] => 'c"
  assoc      :: "['a,'b,('a*'b) list] => 'b"

rules

  alist_rec_def "alist_rec al b c == list_rec b (split c) al"

  assoc_def   "assoc v d al == alist_rec al d (%x y xs g.if v=x then y else g)"

end
