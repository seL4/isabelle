(*  Title:      HOL/Wellfounded_Recursion.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1992  University of Cambridge

Well-founded Recursion
*)

Wellfounded_Recursion = Transitive_Closure +

consts
  wfrec_rel :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => ('a * 'b) set"

inductive "wfrec_rel R F"
intrs
  wfrecI "ALL z. (z, x) : R --> (z, g z) : wfrec_rel R F ==>
            (x, F g x) : wfrec_rel R F"

constdefs
  wf         :: "('a * 'a)set => bool"
  "wf(r) == (!P. (!x. (!y. (y,x):r --> P(y)) --> P(x)) --> (!x. P(x)))"

  acyclic :: "('a*'a)set => bool"
  "acyclic r == !x. (x,x) ~: r^+"

  cut        :: "('a => 'b) => ('a * 'a)set => 'a => 'a => 'b"
  "cut f r x == (%y. if (y,x):r then f y else arbitrary)"

  adm_wf :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => bool"
  "adm_wf R F == ALL f g x.
     (ALL z. (z, x) : R --> f z = g z) --> F f x = F g x"

  wfrec :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => 'a => 'b"
  "wfrec R F == %x. @y. (x, y) : wfrec_rel R (%f x. F (cut f R x) x)"

axclass
  wellorder < linorder
  wf "wf {(x,y::'a::ord). x<y}"

end
