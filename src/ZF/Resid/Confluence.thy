(*  Title: 	Confluence.thy
    ID:         $Id$
    Author: 	Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

Confluence = Reduction+

consts
  confluence	:: "i=>o"
  strip		:: "o"

defs
  confluence_def "confluence(R) ==   \
\		  ALL x y. <x,y>:R --> (ALL z.<x,z>:R -->   \
\		                         (EX u.<y,u>:R & <z,u>:R))"
  strip_def      "strip == ALL x y. (x ===> y) --> (ALL z.(x =1=> z) -->   \
\		                         (EX u.(y =1=> u) & (z===>u)))" 
end

