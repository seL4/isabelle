(*  Title:      HOL/Lex/DA.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Deterministic automata
*)

DA = List + AutoProj +

types ('a,'s)da = "'s * ('a => 's => 's) * ('s => bool)"

constdefs
 foldl2 :: ('a => 'b => 'b) => 'a list => 'b => 'b
"foldl2 f xs a == foldl (%a b. f b a) a xs"

 delta :: ('a,'s)da => 'a list => 's => 's
"delta A == foldl2 (next A)"

 accepts ::  ('a,'s)da => 'a list => bool
"accepts A == %w. fin A (delta A w (start A))"

end
