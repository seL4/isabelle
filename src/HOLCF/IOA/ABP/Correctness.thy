(*  Title:      HOLCF/IOA/ABP/Correctness.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* The main correctness proof: System_fin implements System *}

theory Correctness
imports IOA Env Impl Impl_finite
begin

consts
  reduce         :: "'a list => 'a list"
primrec
  reduce_Nil:  "reduce [] = []"
  reduce_Cons: "reduce(x#xs) =
                 (case xs of
                     [] => [x]
               |   y#ys => (if (x=y)
                              then reduce xs
                              else (x#(reduce xs))))"

constdefs
  abs where
    "abs  ==
      (%p.(fst(p),(fst(snd(p)),(fst(snd(snd(p))),
       (reduce(fst(snd(snd(snd(p))))),reduce(snd(snd(snd(snd(p))))))))))"

  system_ioa       :: "('m action, bool * 'm impl_state)ioa"
  "system_ioa == (env_ioa || impl_ioa)"

  system_fin_ioa   :: "('m action, bool * 'm impl_state)ioa"
  "system_fin_ioa == (env_ioa || impl_fin_ioa)"


axioms

  sys_IOA:     "IOA system_ioa"
  sys_fin_IOA: "IOA system_fin_ioa"

ML {* use_legacy_bindings (the_context ()) *}

end
