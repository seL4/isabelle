Pcpo = Porder +

classes pcpo < po
arities void :: pcpo

consts  
        UU :: "'a::pcpo"        

rules

        minimal "UU << x"       
        cpo     "is_chain(S) ==> ? x. range(S) <<| (x::'a::pcpo)" 

inst_void_pcpo  "(UU::void) = UU_void"

(* start 8bit 1 *)
syntax
	"GUU" :: "'a::pcpo"	("Ø")	

translations
  "Ø"		== "UU"

(* end 8bit 1 *)
end 
