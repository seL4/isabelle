(*  Title:      CCL/ex/list.thy
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Programs defined over lists.
*)

List = Nat + 

consts
  map       :: "[i=>i,i]=>i"
  "o"       :: "[i=>i,i=>i]=>i=>i"             (infixr 55)
  "@"       :: "[i,i]=>i"             (infixr 55)
  mem       :: "[i,i]=>i"             (infixr 55)
  filter    :: "[i,i]=>i"
  flat      :: "i=>i"
  partition :: "[i,i]=>i"
  insert    :: "[i,i,i]=>i"
  isort     :: "i=>i"
  qsort     :: "i=>i"

rules 

  map_def     "map(f,l)   == lrec(l,[],%x xs g.f(x)$g)"
  comp_def    "f o g == (%x.f(g(x)))"
  append_def  "l @ m == lrec(l,m,%x xs g.x$g)"
  mem_def     "a mem l == lrec(l,false,%h t g.if eq(a,h) then true else g)"
  filter_def  "filter(f,l) == lrec(l,[],%x xs g.if f`x then x$g else g)"
  flat_def    "flat(l) == lrec(l,[],%h t g.h @ g)"

  insert_def  "insert(f,a,l) == lrec(l,a$[],%h t g.if f`a`h then a$h$t else h$g)"
  isort_def   "isort(f) == lam l.lrec(l,[],%h t g.insert(f,h,g))"

  partition_def 
  "partition(f,l) == letrec part l a b be lcase(l,<a,b>,%x xs.
                            if f`x then part(xs,x$a,b) else part(xs,a,x$b)) 
                    in part(l,[],[])"
  qsort_def   "qsort(f) == lam l. letrec qsortx l be lcase(l,[],%h t. 
                                   let p be partition(f`h,t) 
                                   in split(p,%x y.qsortx(x) @ h$qsortx(y))) 
                          in qsortx(l)"

end
