(*  Title:      HOL/BCV/Kildall.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Kildall's algorithm
*)

Kildall = DFA_Framework +

constdefs
 bounded :: "(nat => nat list) => nat => bool"
"bounded succs n == !p<n. !q:set(succs p). q<n"

 pres_type :: "(nat => 's => 's) => nat => 's set => bool"
"pres_type step n A == !s:A. !p<n. step p s : A"

 mono :: "'s ord => (nat => 's => 's) => nat => 's set => bool"
"mono r step n A ==
 !s p t. s : A & p < n & s <=_r t --> step p s <=_r step p t"

consts
 iter :: "('s sl * (nat => 's => 's) * (nat => nat list))
          * 's list * nat set => 's list"
 propa :: "'s binop => nat list => 's => 's list => nat set => 's list * nat set"

primrec
"propa f []     t ss w = (ss,w)"
"propa f (q#qs) t ss w = (let u = t +_f ss!q;
                              w' = (if u = ss!q then w else insert q w)
                          in propa f qs t (ss[q := u]) w')"

recdef iter
 "same_fst (%((A,r,f),step,succs). semilat(A,r,f) & acc r)
         (%((A,r,f),step,succs).
  {(ss',ss) . ss <[r] ss'} <*lex*> finite_psubset)"
"iter(((A,r,f),step,succs),ss,w) =
  (if semilat(A,r,f) & acc r & (!p:w. p < size ss) &
      bounded succs (size ss) & set ss <= A & pres_type step (size ss) A
   then if w={} then ss
        else let p = SOME p. p : w
             in iter(((A,r,f),step,succs),
                     propa f (succs p) (step p (ss!p)) ss (w-{p}))
   else arbitrary)"

constdefs
 unstables ::
 "'s binop => (nat => 's => 's) => (nat => nat list) => 's list => nat set"
"unstables f step succs ss ==
 {p. p < size ss & (? q:set(succs p). step p (ss!p) +_f ss!q ~= ss!q)}"

 kildall :: "'s sl => (nat => 's => 's) => (nat => nat list)
             => 's list => 's list"
"kildall Arf step succs ss ==
 iter((Arf,step,succs),ss,unstables (snd(snd Arf)) step succs ss)"

consts merges :: "'s binop => 's => nat list => 's list => 's list"
primrec
"merges f s []     ss = ss"
"merges f s (p#ps) ss = merges f s ps (ss[p := s +_f ss!p])"

end
