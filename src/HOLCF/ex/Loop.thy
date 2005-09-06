(*  Title:      HOLCF/ex/Loop.thy
    ID:         $Id$
    Author:     Franz Regensburger
*)

header {* Theory for a loop primitive like while *}

theory Loop
imports HOLCF
begin

constdefs
  step  :: "('a -> tr)->('a -> 'a)->'a->'a"
  "step == (LAM b g x. If b$x then g$x else x fi)"
  while :: "('a -> tr)->('a -> 'a)->'a->'a"
  "while == (LAM b g. fix$(LAM f x.
    If b$x then f$(g$x) else x fi))"

ML {* use_legacy_bindings (the_context ()) *}

end

