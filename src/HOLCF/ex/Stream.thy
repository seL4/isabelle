(*  Title: 	HOLCF/ex/Stream.thy
    ID:         $Id$
    Author: 	Franz Regensburger, David von Oheimb
    Copyright   1993, 1995 Technische Universitaet Muenchen

general Stream domain
*)

Stream = HOLCF + Nat_Infinity +

domain 'a stream = "&&" (ft::'a) (lazy rt::'a stream) (infixr 65)

consts

  smap		:: "('a \\<rightarrow> 'b) \\<rightarrow> 'a stream \\<rightarrow> 'b stream"
  sfilter	:: "('a \\<rightarrow> tr) \\<rightarrow> 'a stream \\<rightarrow> 'a stream"
  slen		:: "'a stream \\<Rightarrow> inat"			("#_" [1000] 1000)

defs

  smap_def	"smap	 \\<equiv> fix\\<cdot>(\\<Lambda>h f s. case s of x && xs => f\\<cdot>x && h\\<cdot>f\\<cdot>xs)"
  sfilter_def	"sfilter \\<equiv> fix\\<cdot>(\\<Lambda>h p s. case s of x && xs => 
				     If p\\<cdot>x then x && h\\<cdot>p\\<cdot>xs else h\\<cdot>p\\<cdot>xs fi)"
  slen_def	"#s \\<equiv> if stream_finite s 
		      then Fin (LEAST n. stream_take n\\<cdot>s = s) else \\<infinity>"

end


