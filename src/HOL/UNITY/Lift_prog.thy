(*  Title:      HOL/UNITY/Lift_prog.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

lift_prog, etc: replication of components
*)

Lift_prog = Rename +

constdefs

  insert_map :: "[nat, 'b, nat=>'b] => (nat=>'b)"
    "insert_map i z f k == if k<i then f k
                           else if k=i then z
                           else f(k-1)"

  delete_map :: "[nat, nat=>'b] => (nat=>'b)"
    "delete_map i g k == if k<i then g k else g (Suc k)"

  lift_map :: "[nat, 'b * ((nat=>'b) * 'c)] => (nat=>'b) * 'c"
    "lift_map i == %(s,(f,uu)). (insert_map i s f, uu)"

  drop_map :: "[nat, (nat=>'b) * 'c] => 'b * ((nat=>'b) * 'c)"
    "drop_map i == %(g, uu). (g i, (delete_map i g, uu))"

  lift_set :: "[nat, ('b * ((nat=>'b) * 'c)) set] => ((nat=>'b) * 'c) set"
    "lift_set i A == lift_map i `` A"

  lift :: "[nat, ('b * ((nat=>'b) * 'c)) program] => ((nat=>'b) * 'c) program"
    "lift i == rename (lift_map i)"

  (*simplifies the expression of specifications*)
  constdefs
    sub :: ['a, 'a=>'b] => 'b
      "sub == %i f. f i"


end
