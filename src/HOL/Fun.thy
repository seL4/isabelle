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

  inj, surj   :: ('a => 'b) => bool                   (*inj/surjective*)
  inj_on      :: ['a => 'b, 'a set] => bool
  inv         :: ('a => 'b) => ('b => 'a)

defs

  inj_def     "inj f          == ! x y. f(x)=f(y) --> x=y"
  inj_on_def  "inj_on f A     == ! x:A. ! y:A. f(x)=f(y) --> x=y"
  surj_def    "surj f         == ! y. ? x. y=f(x)"
  inv_def     "inv(f::'a=>'b) == (% y. @x. f(x)=y)"

end
