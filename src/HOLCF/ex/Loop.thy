(*  Title:      HOLCF/ex/Loop.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Theory for a loop primitive like while
*)

Loop = Tr2 +

consts

        step  :: "('a -> tr)->('a -> 'a)->'a->'a"
        while :: "('a -> tr)->('a -> 'a)->'a->'a"

defs

  step_def      "step == (LAM b g x. If b`x then g`x else x fi)"
  while_def     "while == (LAM b g. fix`(LAM f x.
                   If b`x then f`(g`x) else x fi))"

end
 
