(*  Title:      HOL/Modelcheck/MuckeExample2.thy
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)


MuckeExample2 = MuckeSyn +

consts

  Init  :: "bool pred"
  R	:: "[bool,bool] => bool"
  Reach	:: "bool pred"
  Reach2:: "bool pred"

defs

  Init_def " Init x == x"

  R_def "R x y == (x & ~y) | (~x & y)"

  Reach_def "Reach == mu (%Q x. Init x | (? y. Q y & R y x))"

  Reach2_def "Reach2 == mu (%Q x. Reach x | (? y. Q y & R y x))"

end