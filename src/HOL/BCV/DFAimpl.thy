(*  Title:      HOL/BCV/DFAimpl.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM

Implementations of data-flow analysis.
*)

DFAimpl = DFAandWTI + Fixpoint +

consts merges :: "('s::plus) => nat list => 's os => 's os"
primrec
"merges a []     s = s"
"merges a (p#ps) s = merges a ps (s[p := Some(a) + s!p])"

constdefs
 succs_bounded :: "(nat => nat list) => nat => bool"
"succs_bounded succs n == !p<n. !q:set(succs p). q<n"

 is_next :: "((nat => 's => ('s::plus)option) => (nat => nat list)
              => 's os => 's os option)
             => bool"
"is_next next == !step succs sos sos'.
   succs_bounded succs (size sos) -->
   (next step succs sos = None -->
      (? p<size sos. ? s. sos!p = Some s & step p s = None))  &
   (next step succs sos = Some sos -->
      (!p<size sos. !s. sos!p = Some s --> (? t.
          step p s = Some(t) & merges t (succs p) sos = sos))) &
   (next step succs sos = Some sos' & sos' ~= sos -->
      (? p<size sos. ? s. sos!p = Some s & (? t.
          step p s = Some(t) & merges t (succs p) sos = sos')))"

 step_pres_type :: "(nat => 's => 's option) => nat => 's set => bool"
"step_pres_type step n L == !s:L. !p<n. !t. step p s = Some(t) --> t:L"

 step_mono_None :: "(nat => 's::ord => 's option) => nat => 's set => bool"
"step_mono_None step n L == !s p t.
   s : L & p < n & s <= t & step p s = None --> step p t = None"

 step_mono :: "(nat => 's::ord => 's option) => nat => 's set => bool"
"step_mono step n L == !s p t u.
   s : L & p < n & s <= t & step p s = Some(u)
   --> (!v. step p t = Some(v) --> u <= v)"

consts
itnext :: nat => (nat => 's => 's option) => (nat => nat list)
          => 's os => ('s::plus) os option
primrec
"itnext 0       step succs sos = Some sos"
"itnext (Suc p) step succs sos =
   (case sos!p of
      None => itnext p step succs sos
    | Some s => (case step p s of None => None
                 | Some t => let sos' = merges t (succs p) sos
                             in if sos' = sos
                                then itnext p step succs sos
                                else Some sos'))"

end
