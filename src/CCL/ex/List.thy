(*  Title:      CCL/ex/List.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section \<open>Programs defined over lists\<close>

theory List
imports Nat
begin

definition map :: "[i\<Rightarrow>i,i]\<Rightarrow>i"
  where "map(f,l) == lrec(l, [], \<lambda>x xs g. f(x)$g)"

definition comp :: "[i\<Rightarrow>i,i\<Rightarrow>i]\<Rightarrow>i\<Rightarrow>i"  (infixr \<open>\<circ>\<close> 55)
  where "f \<circ> g == (\<lambda>x. f(g(x)))"

definition append :: "[i,i]\<Rightarrow>i"  (infixr \<open>@\<close> 55)
  where "l @ m == lrec(l, m, \<lambda>x xs g. x$g)"

axiomatization member :: "[i,i]\<Rightarrow>i"  (infixr \<open>mem\<close> 55)  (* FIXME dangling eq *)
  where member_ax: "a mem l == lrec(l, false, \<lambda>h t g. if eq(a,h) then true else g)"

definition filter :: "[i,i]\<Rightarrow>i"
  where "filter(f,l) == lrec(l, [], \<lambda>x xs g. if f`x then x$g else g)"

definition flat :: "i\<Rightarrow>i"
  where "flat(l) == lrec(l, [], \<lambda>h t g. h @ g)"

definition partition :: "[i,i]\<Rightarrow>i" where
  "partition(f,l) == letrec part l a b be lcase(l, <a,b>, \<lambda>x xs.
                            if f`x then part(xs,x$a,b) else part(xs,a,x$b))
                    in part(l,[],[])"

definition insert :: "[i,i,i]\<Rightarrow>i"
  where "insert(f,a,l) == lrec(l, a$[], \<lambda>h t g. if f`a`h then a$h$t else h$g)"

definition isort :: "i\<Rightarrow>i"
  where "isort(f) == lam l. lrec(l, [], \<lambda>h t g. insert(f,h,g))"

definition qsort :: "i\<Rightarrow>i" where
  "qsort(f) == lam l. letrec qsortx l be lcase(l, [], \<lambda>h t.
                                   let p be partition(f`h,t)
                                   in split(p, \<lambda>x y. qsortx(x) @ h$qsortx(y)))
                          in qsortx(l)"

lemmas list_defs = map_def comp_def append_def filter_def flat_def
  insert_def isort_def partition_def qsort_def

lemma listBs [simp]:
  "\<And>f g. (f \<circ> g) = (\<lambda>a. f(g(a)))"
  "\<And>a f g. (f \<circ> g)(a) = f(g(a))"
  "\<And>f. map(f,[]) = []"
  "\<And>f x xs. map(f,x$xs) = f(x)$map(f,xs)"
  "\<And>m. [] @ m = m"
  "\<And>x xs m. x$xs @ m = x$(xs @ m)"
  "\<And>f. filter(f,[]) = []"
  "\<And>f x xs. filter(f,x$xs) = if f`x then x$filter(f,xs) else filter(f,xs)"
  "flat([]) = []"
  "\<And>x xs. flat(x$xs) = x @ flat(xs)"
  "\<And>a f. insert(f,a,[]) = a$[]"
  "\<And>a f xs. insert(f,a,x$xs) = if f`a`x then a$x$xs else x$insert(f,a,xs)"
  by (simp_all add: list_defs)

lemma nmapBnil: "n:Nat \<Longrightarrow> map(f) ^ n ` [] = []"
  apply (erule Nat_ind)
   apply simp_all
  done

lemma nmapBcons: "n:Nat \<Longrightarrow> map(f)^n`(x$xs) = (f^n`x)$(map(f)^n`xs)"
  apply (erule Nat_ind)
   apply simp_all
  done


lemma mapT: "\<lbrakk>\<And>x. x:A \<Longrightarrow> f(x):B; l : List(A)\<rbrakk> \<Longrightarrow> map(f,l) : List(B)"
  apply (unfold map_def)
  apply typechk
  apply blast
  done

lemma appendT: "\<lbrakk>l : List(A); m : List(A)\<rbrakk> \<Longrightarrow> l @ m : List(A)"
  apply (unfold append_def)
  apply typechk
  done

lemma appendTS:
  "\<lbrakk>l : {l:List(A). m : {m:List(A).P(l @ m)}}\<rbrakk> \<Longrightarrow> l @ m : {x:List(A). P(x)}"
  by (blast intro!: appendT)

lemma filterT: "\<lbrakk>f:A->Bool; l : List(A)\<rbrakk> \<Longrightarrow> filter(f,l) : List(A)"
  apply (unfold filter_def)
  apply typechk
  done

lemma flatT: "l : List(List(A)) \<Longrightarrow> flat(l) : List(A)"
  apply (unfold flat_def)
  apply (typechk appendT)
  done

lemma insertT: "\<lbrakk>f : A->A->Bool; a:A; l : List(A)\<rbrakk> \<Longrightarrow> insert(f,a,l) : List(A)"
  apply (unfold insert_def)
  apply typechk
  done

lemma insertTS:
  "\<lbrakk>f : {f:A->A->Bool. a : {a:A. l : {l:List(A).P(insert(f,a,l))}}} \<rbrakk> \<Longrightarrow>
   insert(f,a,l)  : {x:List(A). P(x)}"
  by (blast intro!: insertT)

lemma partitionT: "\<lbrakk>f:A->Bool; l : List(A)\<rbrakk> \<Longrightarrow> partition(f,l) : List(A)*List(A)"
  apply (unfold partition_def)
  apply typechk
  apply clean_ccs
  apply (rule ListPRI [THEN wfstI, THEN ListPR_wf [THEN wmap_wf, THEN wfI]])
    apply assumption+
  apply (rule ListPRI [THEN wfstI, THEN ListPR_wf [THEN wmap_wf, THEN wfI]])
   apply assumption+
  done

end
