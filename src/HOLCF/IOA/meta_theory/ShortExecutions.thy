(*  Title:      HOLCF/IOA/meta_theory/ShortExecutions.thy
    ID:        
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

Some properties about cut(ex), defined as follows:

For every execution ex there is another shorter execution cut(ex) 
that has the same trace as ex, but its schedule ends with an external action.

*) 


ShortExecutions = Traces + 

consts 

  LastActExtsch     ::"'a Seq  => bool"
  cutsch            ::"'a Seq => 'a Seq"


defs

LastActExtsch_def
  "LastActExtsch sch == (cutsch sch = sch)"


rules

exists_LastActExtsch
  "[|sch : schedules A ; tr = Filter (%a.a:ext A)`sch|]
   ==> ? sch. sch : schedules A & 
              tr = Filter (%a.a:ext A)`sch &
              LastActExtsch sch"

(* FIX: 1. LastActExtsch should have argument A also? 
        2. use equality: (I) f P x =UU <-> (II) (fa ~P x) & ~finite(x) to prove it for (II) instead *)
LastActExtimplUU
  "[|LastActExtsch sch; Filter (%x.x:ext A)`sch = UU |]
   ==> sch=UU"

(* FIX: see above *)
LastActExtimplnil
  "[|LastActExtsch sch; Filter (%x.x:ext A)`sch = nil |]
   ==> sch=nil"

LastActExtsmall1
  "LastActExtsch sch ==> LastActExtsch (TL`(Dropwhile P`sch))"

LastActExtsmall2
  "[| Finite sch1; LastActExtsch (sch1 @@ sch2) |] ==> LastActExtsch (sch2)"

end

