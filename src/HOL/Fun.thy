(*  Title:      HOL/Fun.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Notions about functions.
*)

Fun = Vimage +

instance set :: (term) order
                       (subset_refl,subset_trans,subset_antisym,psubset_eq)
consts

  Id          ::  'a => 'a
  o           :: ['b => 'c, 'a => 'b, 'a] => 'c   (infixl 55)
  inj, surj   :: ('a => 'b) => bool                   (*inj/surjective*)
  inj_on      :: ['a => 'b, 'a set] => bool
  inv         :: ('a => 'b) => ('b => 'a)
  fun_upd  :: "('a => 'b) => 'a => 'b => ('a => 'b)"

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
  "f(x:=y)"                     == "fun_upd f x y"

defs

  Id_def	"Id             == %x. x"
  o_def   	"f o g          == %x. f(g(x))"
  inj_def	"inj f          == ! x y. f(x)=f(y) --> x=y"
  inj_on_def	"inj_on f A     == ! x:A. ! y:A. f(x)=f(y) --> x=y"
  surj_def	"surj f         == ! y. ? x. y=f(x)"
  inv_def	"inv(f::'a=>'b) == % y. @x. f(x)=y"
  fun_upd_def	"f(a:=b)        == % x. if x=a then b else f x"

end
