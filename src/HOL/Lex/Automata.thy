(*  Title:      HOL/Lex/Automata.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Conversions between different kinds of automata
*)

Automata = DA + NAe +

constdefs
 na2da :: ('a,'s)na => ('a,'s set)da
"na2da A == ({start A}, %a Q. lift(next A a) Q, %Q. ? q:Q. fin A q)"

 nae2da :: ('a,'s)nae => ('a,'s set)da
"nae2da A == ({start A},
              %a Q. lift (next A (Some a)) ((eps A)^* ^^ Q),
              %Q. ? p: (eps A)^* ^^ Q. fin A p)"

end
