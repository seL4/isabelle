(*  Title: 	HOLCF/ex/Stream.thy
    ID:         $Id$
    Author: 	Franz Regensburger, David von Oheimb

General Stream domain.
TODO: should be integrated with HOLCF/Streams
*)

Stream = HOLCF + Nat_Infinity +

domain 'a stream = "&&" (ft::'a) (lazy rt::'a stream) (infixr 65)

consts

  smap		:: "('a -> 'b) -> 'a stream -> 'b stream"
  sfilter	:: "('a -> tr) -> 'a stream -> 'a stream"
  slen		:: "'a stream => inat"			("#_" [1000] 1000)

defs

  smap_def	"smap	 == fix\\<cdot>(\\<Lambda> h f s. case s of x && xs => f\\<cdot>x && h\\<cdot>f\\<cdot>xs)"
  sfilter_def	"sfilter == fix\\<cdot>(\\<Lambda> h p s. case s of x && xs => 
				     If p\\<cdot>x then x && h\\<cdot>p\\<cdot>xs else h\\<cdot>p\\<cdot>xs fi)"
  slen_def	"#s == if stream_finite s 
		      then Fin (LEAST n. stream_take n\\<cdot>s = s) else \\<infinity>"

end


