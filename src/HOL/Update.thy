(*  Title:      HOL/Update.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Function updates: like theory Map, but for ordinary functions
*)

Update = Fun +

consts
  update  :: "('a => 'b) => 'a => 'b => ('a => 'b)"

nonterminals
  updbinds  updbind

syntax

  (* Let expressions *)

  "_updbind"       :: ['a, 'a] => updbind             ("(2_ :=/ _)")
  ""               :: updbind => updbinds             ("_")
  "_updbinds"      :: [updbind, updbinds] => updbinds ("_,/ _")
  "_Update"        :: ['a, updbinds] => 'a            ("_/'((_)')" [900,0] 900)

translations
  "_Update f (_updbinds b bs)"  == "_Update (_Update f b) bs"
  "f(x:=y)"                     == "update f x y"

defs
  update_def "f(a:=b) == %x. if x=a then b else f x"

end
