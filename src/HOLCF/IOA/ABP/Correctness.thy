(*  Title:      HOLCF/IOA/ABP/Correctness.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* The main correctness proof: System_fin implements System *}

theory Correctness
imports IOA Env Impl Impl_finite
begin

consts

reduce           :: "'a list => 'a list"

abs              :: 'c
system_ioa       :: "('m action, bool * 'm impl_state)ioa"
system_fin_ioa   :: "('m action, bool * 'm impl_state)ioa"

primrec
  reduce_Nil:  "reduce [] = []"
  reduce_Cons: "reduce(x#xs) =
                 (case xs of
                     [] => [x]
               |   y#ys => (if (x=y)
                              then reduce xs
                              else (x#(reduce xs))))"


defs

system_def:
  "system_ioa == (env_ioa || impl_ioa)"

system_fin_def:
  "system_fin_ioa == (env_ioa || impl_fin_ioa)"

abs_def: "abs  ==
        (%p.(fst(p),(fst(snd(p)),(fst(snd(snd(p))),
         (reduce(fst(snd(snd(snd(p))))),reduce(snd(snd(snd(snd(p))))))))))"

axioms

  sys_IOA:     "IOA system_ioa"
  sys_fin_IOA: "IOA system_fin_ioa"

ML {* use_legacy_bindings (the_context ()) *}

end
