(*  Title:      HOL/BCV/DFAandWTI.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM

The relationship between dataflow analysis and a welltyped-insruction predicate.
*)

DFAandWTI = SemiLattice +

types 's os = 's option list

constdefs

 stable :: (nat => 's => 's option) => (nat => nat list) => nat => 's os => bool
"stable step succs p sos ==
 !s. sos!p = Some s --> (? t. step p s = Some(t) &
                              (!q:set(succs p). Some t <= sos!q))"

 wti_is_fix_step ::
   "(nat => 's => 's option)
    => (nat => 's os => bool)
    => (nat => nat list)
    => nat => 's set => bool"
"wti_is_fix_step step wti succs n L == !sos p.
   sos : listsn n (option L) & p < n -->
   wti p sos = stable step succs p sos"

 welltyping :: (nat => 's os => bool) => 's os => bool
"welltyping wti tos == !p<size(tos). wti p tos"

 is_dfa ::  ('s os => bool)
            => (nat => 's => 's option)
            => (nat => nat list)
            => nat => 's set => bool
"is_dfa dfa step succs n L == !sos : listsn n (option L).
   dfa sos =
   (? tos : listsn n (option L).
      sos <= tos & (!p < n. stable step succs p tos))"

end
