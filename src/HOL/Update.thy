(*  Title:      HOL/UNITY/Update.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Function updates: like the standard theory Map, but for ordinary functions
*)

Update = Fun +

consts
  update  :: "('a => 'b) => 'a => 'b => ('a => 'b)"
           ("_/[_/:=/_]" [900,0,0] 900)

syntax (symbols)
  update    :: "('a => 'b) => 'a => 'b => ('a => 'b)"
               ("_/[_/\\<mapsto>/_]" [900,0,0] 900)

defs
  update_def "f[a:=b] == %x. if x=a then b else f x"

end
