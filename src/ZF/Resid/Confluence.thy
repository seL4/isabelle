(*  Title:      Confluence.thy
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

Confluence = Reduction+

consts
  confluence    :: i=>o
  strip         :: o

defs
  confluence_def "confluence(R) ==   
                  \\<forall>x y. <x,y>:R --> (\\<forall>z.<x,z>:R -->   
                                         (\\<exists>u.<y,u>:R & <z,u>:R))"
  strip_def      "strip == \\<forall>x y. (x ===> y) --> (\\<forall>z.(x =1=> z) -->   
                                         (\\<exists>u.(y =1=> u) & (z===>u)))" 
end

