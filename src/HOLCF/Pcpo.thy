Pcpo = Porder +

classes pcpo < po
arities void :: pcpo

consts	
	UU :: "'a::pcpo"	
rules

minimal	"UU << x"	
cpo	"is_chain(S) ==> ? x. range(S) <<| (x::'a::pcpo)" 

inst_void_pcpo	"(UU::void) = UU_void"

end 
