(*  Title: 	HOLCF/cprod3.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen


Class instance of  * for class pcpo

*)

Cprod3 = Cprod2 +

arities "*" :: (pcpo,pcpo)pcpo			(* Witness cprod2.ML *)

consts  
	"@cpair"     :: "'a => 'b => ('a*'b)" ("_#_" [101,100] 100)
	"cop @cpair" :: "'a -> 'b -> ('a*'b)" ("cpair")
					(* continuous  pairing *)
	cfst         :: "('a*'b)->'a"
	csnd         :: "('a*'b)->'b"
	csplit       :: "('a->'b->'c)->('a*'b)->'c"

translations "x#y" => "cpair[x][y]"

rules 

inst_cprod_pcpo	"(UU::'a*'b) = <UU,UU>"

cpair_def	"cpair  == (LAM x y.<x,y>)"
cfst_def	"cfst   == (LAM p.fst(p))"
csnd_def	"csnd   == (LAM p.snd(p))"	
csplit_def	"csplit == (LAM f p.f[cfst[p]][csnd[p]])"

end




