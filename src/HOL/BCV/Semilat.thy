(*  Title:      HOL/BCV/Semilat.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Semilattices
*)

Semilat = Main +

types 'a ord    = 'a => 'a => bool
      'a binop  = 'a => 'a => 'a
      'a sl     = "'a set * 'a ord * 'a binop"

consts
 "@lesub"   :: 'a => 'a ord => 'a => bool ("(_ /<='__ _)" [50, 1000, 51] 50)
 "@lesssub" :: 'a => 'a ord => 'a => bool ("(_ /<'__ _)" [50, 1000, 51] 50)
defs
lesub_def   "x <=_r y == r x y"
lesssub_def "x <_r y  == x <=_r y & x ~= y"

consts
 "@plussub" :: 'a => ('a => 'b => 'c) => 'b => 'c ("(_ /+'__ _)" [65, 1000, 66] 65)
defs
plussub_def   "x +_f y == f x y"


constdefs
 ord :: "('a*'a)set => 'a ord"
"ord r == %x y. (x,y):r"

 order :: 'a ord => bool
"order r == (!x. x <=_r x) &
            (!x y. x <=_r y & y <=_r x --> x=y) &
            (!x y z. x <=_r y & y <=_r z --> x <=_r z)"

 acc :: 'a ord => bool
"acc r == wf{(y,x) . x <_r y}"

 top :: 'a ord => 'a => bool
"top r T == !x. x <=_r T"

 closed :: 'a set => 'a binop => bool
"closed A f == !x:A. !y:A. x +_f y : A"

 semilat :: "'a sl => bool"
"semilat == %(A,r,f). order r & closed A f &
                (!x:A. !y:A. x <=_r x +_f y)  &
                (!x:A. !y:A. y <=_r x +_f y)  &
                (!x:A. !y:A. !z:A. x <=_r z & y <=_r z --> x +_f y <=_r z)"

 is_ub :: "('a*'a)set => 'a => 'a => 'a => bool"
"is_ub r x y u == (x,u):r & (y,u):r"

 is_lub :: "('a*'a)set => 'a => 'a => 'a => bool"
"is_lub r x y u == is_ub r x y u & (!z. is_ub r x y z --> (u,z):r)"

 some_lub :: "('a*'a)set => 'a => 'a => 'a"
"some_lub r x y == SOME z. is_lub r x y z"

end
