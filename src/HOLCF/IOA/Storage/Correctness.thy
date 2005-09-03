(*  Title:      HOL/IOA/example/Correctness.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* Correctness Proof *}

theory Correctness
imports SimCorrectness Spec Impl
begin

defaultsort type

constdefs
  sim_relation   :: "((nat * bool) * (nat set * bool)) set"
  "sim_relation == {qua. let c = fst qua; a = snd qua ;
                             k = fst c;   b = snd c;
                             used = fst a; c = snd a
                         in
                         (! l:used. l < k) & b=c }"

ML {* use_legacy_bindings (the_context ()) *}

end
