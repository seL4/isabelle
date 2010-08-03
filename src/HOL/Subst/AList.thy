(*  Title:      HOL/Subst/AList.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header {* Association Lists *}

theory AList
imports Main
begin

primrec alist_rec :: "[('a*'b)list, 'c, ['a, 'b, ('a*'b)list, 'c]=>'c] => 'c"
where
  "alist_rec [] c d = c"
| "alist_rec (p # al) c d = d (fst p) (snd p) al (alist_rec al c d)"

primrec assoc :: "['a,'b,('a*'b) list] => 'b"
where
  "assoc v d [] = d"
| "assoc v d (p # al) = (if v = fst p then snd p else assoc v d al)"

lemma alist_induct:
    "P [] \<Longrightarrow> (!!x y xs. P xs \<Longrightarrow> P ((x,y) # xs)) \<Longrightarrow> P l"
  by (induct l) auto

end
