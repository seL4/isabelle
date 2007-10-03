(*  Title:      CCL/ex/List.thy
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header {* Programs defined over lists *}

theory List
imports Nat
begin

consts
  map       :: "[i=>i,i]=>i"
  comp      :: "[i=>i,i=>i]=>i=>i"    (infixr "o" 55)
  append    :: "[i,i]=>i"             (infixr "@" 55)
  member    :: "[i,i]=>i"             (infixr "mem" 55)
  filter    :: "[i,i]=>i"
  flat      :: "i=>i"
  partition :: "[i,i]=>i"
  insert    :: "[i,i,i]=>i"
  isort     :: "i=>i"
  qsort     :: "i=>i"

axioms

  map_def:     "map(f,l)   == lrec(l,[],%x xs g. f(x)$g)"
  comp_def:    "f o g == (%x. f(g(x)))"
  append_def:  "l @ m == lrec(l,m,%x xs g. x$g)"
  member_def:  "a mem l == lrec(l,false,%h t g. if eq(a,h) then true else g)"
  filter_def:  "filter(f,l) == lrec(l,[],%x xs g. if f`x then x$g else g)"
  flat_def:    "flat(l) == lrec(l,[],%h t g. h @ g)"

  insert_def:  "insert(f,a,l) == lrec(l,a$[],%h t g. if f`a`h then a$h$t else h$g)"
  isort_def:   "isort(f) == lam l. lrec(l,[],%h t g. insert(f,h,g))"

  partition_def:
  "partition(f,l) == letrec part l a b be lcase(l,<a,b>,%x xs.
                            if f`x then part(xs,x$a,b) else part(xs,a,x$b))
                    in part(l,[],[])"
  qsort_def:   "qsort(f) == lam l. letrec qsortx l be lcase(l,[],%h t.
                                   let p be partition(f`h,t)
                                   in split(p,%x y. qsortx(x) @ h$qsortx(y)))
                          in qsortx(l)"


lemmas list_defs = map_def comp_def append_def filter_def flat_def
  insert_def isort_def partition_def qsort_def

lemma listBs [simp]:
  "!!f g. (f o g) = (%a. f(g(a)))"
  "!!a f g. (f o g)(a) = f(g(a))"
  "!!f. map(f,[]) = []"
  "!!f x xs. map(f,x$xs) = f(x)$map(f,xs)"
  "!!m. [] @ m = m"
  "!!x xs m. x$xs @ m = x$(xs @ m)"
  "!!f. filter(f,[]) = []"
  "!!f x xs. filter(f,x$xs) = if f`x then x$filter(f,xs) else filter(f,xs)"
  "flat([]) = []"
  "!!x xs. flat(x$xs) = x @ flat(xs)"
  "!!a f. insert(f,a,[]) = a$[]"
  "!!a f xs. insert(f,a,x$xs) = if f`a`x then a$x$xs else x$insert(f,a,xs)"
  by (simp_all add: list_defs)

lemma nmapBnil: "n:Nat ==> map(f) ^ n ` [] = []"
  apply (erule Nat_ind)
   apply simp_all
  done

lemma nmapBcons: "n:Nat ==> map(f)^n`(x$xs) = (f^n`x)$(map(f)^n`xs)"
  apply (erule Nat_ind)
   apply simp_all
  done


lemma mapT: "[| !!x. x:A==>f(x):B;  l : List(A) |] ==> map(f,l) : List(B)"
  apply (unfold map_def)
  apply (tactic "typechk_tac [] 1")
  apply blast
  done

lemma appendT: "[| l : List(A);  m : List(A) |] ==> l @ m : List(A)"
  apply (unfold append_def)
  apply (tactic "typechk_tac [] 1")
  done

lemma appendTS:
  "[| l : {l:List(A). m : {m:List(A).P(l @ m)}} |] ==> l @ m : {x:List(A). P(x)}"
  by (blast intro!: SubtypeI appendT elim!: SubtypeE)

lemma filterT: "[| f:A->Bool;   l : List(A) |] ==> filter(f,l) : List(A)"
  apply (unfold filter_def)
  apply (tactic "typechk_tac [] 1")
  done

lemma flatT: "l : List(List(A)) ==> flat(l) : List(A)"
  apply (unfold flat_def)
  apply (tactic {* typechk_tac [thm "appendT"] 1 *})
  done

lemma insertT: "[|  f : A->A->Bool; a:A; l : List(A) |] ==> insert(f,a,l) : List(A)"
  apply (unfold insert_def)
  apply (tactic "typechk_tac [] 1")
  done

lemma insertTS:
  "[| f : {f:A->A->Bool. a : {a:A. l : {l:List(A).P(insert(f,a,l))}}} |] ==>  
   insert(f,a,l)  : {x:List(A). P(x)}"
  by (blast intro!: SubtypeI insertT elim!: SubtypeE)

lemma partitionT:
  "[| f:A->Bool;  l : List(A) |] ==> partition(f,l) : List(A)*List(A)"
  apply (unfold partition_def)
  apply (tactic "typechk_tac [] 1")
  apply (tactic clean_ccs_tac)
  apply (rule ListPRI [THEN wfstI, THEN ListPR_wf [THEN wmap_wf, THEN wfI]])
    apply assumption+
  apply (rule ListPRI [THEN wfstI, THEN ListPR_wf [THEN wmap_wf, THEN wfI]])
   apply assumption+
  done

end
