(*  Title:      CCL/ex/List.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header {* Programs defined over lists *}

theory List
imports Nat
begin

definition map :: "[i=>i,i]=>i"
  where "map(f,l) == lrec(l,[],%x xs g. f(x)$g)"

definition comp :: "[i=>i,i=>i]=>i=>i"  (infixr "\<circ>" 55)
  where "f \<circ> g == (%x. f(g(x)))"

definition append :: "[i,i]=>i"  (infixr "@" 55)
  where "l @ m == lrec(l,m,%x xs g. x$g)"

axiomatization member :: "[i,i]=>i"  (infixr "mem" 55)  (* FIXME dangling eq *)
  where member_ax: "a mem l == lrec(l,false,%h t g. if eq(a,h) then true else g)"

definition filter :: "[i,i]=>i"
  where "filter(f,l) == lrec(l,[],%x xs g. if f`x then x$g else g)"

definition flat :: "i=>i"
  where "flat(l) == lrec(l,[],%h t g. h @ g)"

definition partition :: "[i,i]=>i" where
  "partition(f,l) == letrec part l a b be lcase(l,<a,b>,%x xs.
                            if f`x then part(xs,x$a,b) else part(xs,a,x$b))
                    in part(l,[],[])"

definition insert :: "[i,i,i]=>i"
  where "insert(f,a,l) == lrec(l,a$[],%h t g. if f`a`h then a$h$t else h$g)"

definition isort :: "i=>i"
  where "isort(f) == lam l. lrec(l,[],%h t g. insert(f,h,g))"

definition qsort :: "i=>i" where
  "qsort(f) == lam l. letrec qsortx l be lcase(l,[],%h t.
                                   let p be partition(f`h,t)
                                   in split(p,%x y. qsortx(x) @ h$qsortx(y)))
                          in qsortx(l)"

lemmas list_defs = map_def comp_def append_def filter_def flat_def
  insert_def isort_def partition_def qsort_def

lemma listBs [simp]:
  "!!f g. (f \<circ> g) = (%a. f(g(a)))"
  "!!a f g. (f \<circ> g)(a) = f(g(a))"
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
  apply (tactic "typechk_tac @{context} [] 1")
  apply blast
  done

lemma appendT: "[| l : List(A);  m : List(A) |] ==> l @ m : List(A)"
  apply (unfold append_def)
  apply (tactic "typechk_tac @{context} [] 1")
  done

lemma appendTS:
  "[| l : {l:List(A). m : {m:List(A).P(l @ m)}} |] ==> l @ m : {x:List(A). P(x)}"
  by (blast intro!: appendT)

lemma filterT: "[| f:A->Bool;   l : List(A) |] ==> filter(f,l) : List(A)"
  apply (unfold filter_def)
  apply (tactic "typechk_tac @{context} [] 1")
  done

lemma flatT: "l : List(List(A)) ==> flat(l) : List(A)"
  apply (unfold flat_def)
  apply (tactic {* typechk_tac @{context} @{thms appendT} 1 *})
  done

lemma insertT: "[|  f : A->A->Bool; a:A; l : List(A) |] ==> insert(f,a,l) : List(A)"
  apply (unfold insert_def)
  apply (tactic "typechk_tac @{context} [] 1")
  done

lemma insertTS:
  "[| f : {f:A->A->Bool. a : {a:A. l : {l:List(A).P(insert(f,a,l))}}} |] ==>  
   insert(f,a,l)  : {x:List(A). P(x)}"
  by (blast intro!: insertT)

lemma partitionT:
  "[| f:A->Bool;  l : List(A) |] ==> partition(f,l) : List(A)*List(A)"
  apply (unfold partition_def)
  apply (tactic "typechk_tac @{context} [] 1")
  apply (tactic "clean_ccs_tac @{context}")
  apply (rule ListPRI [THEN wfstI, THEN ListPR_wf [THEN wmap_wf, THEN wfI]])
    apply assumption+
  apply (rule ListPRI [THEN wfstI, THEN ListPR_wf [THEN wmap_wf, THEN wfI]])
   apply assumption+
  done

end
