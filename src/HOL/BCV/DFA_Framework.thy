(*  Title:      HOL/BCV/DFA_Framework.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

The relationship between dataflow analysis and a welltyped-insruction predicate.
*)

DFA_Framework = Listn +

constdefs

 stable :: 's ord =>
           (nat => 's => 's)
           => (nat => nat list) => 's list => nat => bool
"stable r step succs ss p == !q:set(succs p). step p (ss!p) <=_r ss!q"

 stables :: 's ord => (nat => 's => 's)
            => (nat => nat list) => 's list => bool
"stables r step succs ss == !p<size ss. stable r step succs ss p"

 is_dfa :: 's ord
           => ('s list => 's list)
           => (nat => 's => 's)
           => (nat => nat list)
           => nat => 's set => bool
"is_dfa r dfa step succs n A == !ss : list n A.
   dfa ss : list n A & stables r step succs (dfa ss) & ss <=[r] dfa ss &
   (!ts: list n A. ss <=[r] ts & stables r step succs ts
                     --> dfa ss <=[r] ts)"

 is_bcv :: 's ord => 's => ('s list => nat => bool)
           => nat => 's set => ('s list => 's list) => bool
"is_bcv r T wti n A bcv == !ss : list n A.
   (!p<n. (bcv ss)!p ~= T) =
   (? ts: list n A. ss <=[r] ts & welltyping T wti ts)"

 wti_is_stable_topless ::
    's ord => 's
    => (nat => 's => 's)
    => ('s list => nat => bool)
    => (nat => nat list)
    => nat => 's set => bool
"wti_is_stable_topless r T step wti succs n A == !ss p.
   ss : list n A & (!p<n. ss!p ~= T) & p < n -->
   wti ss p = stable r step succs ss p"

 welltyping :: 's => ('s list => nat => bool) => 's list => bool
"welltyping T wti ts == !p<size(ts). ts!p ~= T & wti ts p"

end
