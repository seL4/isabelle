(*  Title: 	ZF/AC/recfunAC16.thy
    ID:         $Id$
    Author: 	Krzysztof Grabczewski

A recursive definition used in the proof of WO2 ==> AC16
*)

recfunAC16 = Transrec2 + Cardinal +

consts

  recfunAC16              :: "[i, i, i, i] => i"

defs

  recfunAC16_def
    "recfunAC16(f,fa,i,a) == 
	 transrec2(i, 0, 
	      %g r. if(EX y:r. fa`g <= y, r, 
		       r Un {f`(LEAST i. fa`g <= f`i & 
		       (ALL b<a. (fa`b <= f`i --> (ALL t:r. ~ fa`b <= t))))}))"

end
