(*  Title:      ZF/AC/recfunAC16.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

A recursive definition used in the proof of WO2 ==> AC16
*)

recfunAC16 = Cardinal + Epsilon +

constdefs
  recfunAC16 :: [i, i, i, i] => i

    "recfunAC16(f,fa,i,a) == 
         transrec2(i, 0, 
              %g r. if(\\<exists>y \\<in> r. fa`g \\<subseteq> y, r, 
                       r Un {f`(LEAST i. fa`g \\<subseteq> f`i & 
                       (\\<forall>b<a. (fa`b \\<subseteq> f`i --> (\\<forall>t \\<in> r. ~ fa`b \\<subseteq> t))))}))"

end
