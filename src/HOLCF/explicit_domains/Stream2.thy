(* 
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Additional constants for stream
*)

Stream2 = Stream +

consts

smap		:: "('a -> 'b) -> 'a stream -> 'b stream"

defs

smap_def
  "smap == fix`(LAM h f s. stream_when`(LAM x l.scons `(f`x) `(h`f`l)) `s)"


end
      

(*
		smap`f`UU = UU
      x~=UU --> smap`f`(scons`x`xs) = scons `(f`x) `(smap`f`xs)

*)

