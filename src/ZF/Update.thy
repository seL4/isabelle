(*  Title:      ZF/Update.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Function updates: like theory Map, but for ordinary functions
*)

Update = func +

consts
  update  :: "[i,i,i] => i"

nonterminals
  updbinds  updbind

syntax

  (* Let expressions *)

  "_updbind"       :: [i, i] => updbind             ("(2_ :=/ _)")
  ""               :: updbind => updbinds             ("_")
  "_updbinds"      :: [updbind, updbinds] => updbinds ("_,/ _")
  "_Update"        :: [i, updbinds] => i            ("_/'((_)')" [900,0] 900)

translations
  "_Update (f, _updbinds(b,bs))"  == "_Update (_Update(f,b), bs)"
  "f(x:=y)"                     == "update(f,x,y)"

defs
  update_def "f(a:=b) == lam x: cons(a, domain(f)). if(x=a, b, f`x)"

end
