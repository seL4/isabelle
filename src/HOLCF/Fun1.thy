(*  Title: 	HOLCF/fun1.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen


Definition of the partial ordering for the type of all functions => (fun)

REMARK: The ordering on 'a => 'b is only defined if 'b is in class po !!

*)

Fun1 = Pcpo +

(* default class is still term *)

consts
  less_fun	:: "['a=>'b::po,'a=>'b] => bool"	

defs
   (* definition of the ordering less_fun            *)
   (* in fun1.ML it is proved that less_fun is a po *)
   
  less_fun_def "less_fun f1 f2 == ! x. f1(x) << f2(x)"  

end




