(*  Title:      HOL/BCV/Fixpoint.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM

Searching for a fixpoint.
*)

Fixpoint = SemiLattice +

consts fix :: "('a => 'a option) * 'a => bool"
recdef fix
 "{((nxt,t),(nxs,s)) . nxt=nxs &
      ~(? f. f 0 = s & (!i. nxt (f i) = Some(f(i+1)) & f(i+1) ~= f i)) &
      nxs s = Some t & t ~= s}"
"fix(next,s) =
  (if (? f. f 0 = s & (!i. next (f i) = Some(f(i+1)) & f(i+1) ~= f i))
   then arbitrary
   else case next s of None => False |
                       Some t => if t=s then True else fix(next,t))"


end
