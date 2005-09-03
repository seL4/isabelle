(*  Title:      HOL/IOA/NTP/Correctness.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
*)

header {* The main correctness proof: Impl implements Spec *}

theory Correctness
imports Impl Spec
begin

constdefs
  hom :: "'m impl_state => 'm list"
  "hom(s) == rq(rec(s)) @ (if rbit(rec s) = sbit(sen s) then sq(sen s)
                           else tl(sq(sen s)))"

ML {* use_legacy_bindings (the_context ()) *}

end
