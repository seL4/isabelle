(*  Title:      CCL/ex/list
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For list.thy.
*)

open List;

val list_defs = [map_def,comp_def,append_def,filter_def,flat_def,
                 insert_def,isort_def,partition_def,qsort_def];

(****)

val listBs = map (fn s=>prove_goalw List.thy list_defs s (fn _ => [simp_tac term_ss 1]))
     ["(f o g) = (%a. f(g(a)))",
      "(f o g)(a) = f(g(a))",
      "map(f,[]) = []",
      "map(f,x$xs) = f(x)$map(f,xs)",
      "[] @ m = m",
      "x$xs @ m = x$(xs @ m)",
      "filter(f,[]) = []",
      "filter(f,x$xs) = if f`x then x$filter(f,xs) else filter(f,xs)",
      "flat([]) = []",
      "flat(x$xs) = x @ flat(xs)",
      "insert(f,a,[]) = a$[]",
      "insert(f,a,x$xs) = if f`a`x then a$x$xs else x$insert(f,a,xs)"];

val list_ss = nat_ss addsimps listBs;

(****)

val [prem] = goal List.thy "n:Nat ==> map(f) ^ n ` [] = []";
by (rtac (prem RS Nat_ind) 1);
by (ALLGOALS (asm_simp_tac list_ss));
qed "nmapBnil";

val [prem] = goal List.thy "n:Nat ==> map(f)^n`(x$xs) = (f^n`x)$(map(f)^n`xs)";
by (rtac (prem RS Nat_ind) 1);
by (ALLGOALS (asm_simp_tac list_ss));
qed "nmapBcons";

(***)

val prems = goalw List.thy [map_def]
  "[| !!x. x:A==>f(x):B;  l : List(A) |] ==> map(f,l) : List(B)";
by (typechk_tac prems 1);
qed "mapT";

val prems = goalw List.thy [append_def]
  "[| l : List(A);  m : List(A) |] ==> l @ m : List(A)";
by (typechk_tac prems 1);
qed "appendT";

val prems = goal List.thy
  "[| l : {l:List(A). m : {m:List(A).P(l @ m)}} |] ==> l @ m : {x:List(A). P(x)}";
by (cut_facts_tac prems 1);
by (fast_tac (set_cs addSIs [SubtypeI,appendT] addSEs [SubtypeE]) 1);
qed "appendTS";

val prems = goalw List.thy [filter_def]
  "[| f:A->Bool;   l : List(A) |] ==> filter(f,l) : List(A)";
by (typechk_tac prems 1);
qed "filterT";

val prems = goalw List.thy [flat_def]
  "l : List(List(A)) ==> flat(l) : List(A)";
by (typechk_tac (appendT::prems) 1);
qed "flatT";

val prems = goalw List.thy [insert_def]
  "[|  f : A->A->Bool; a:A; l : List(A) |] ==> insert(f,a,l) : List(A)";
by (typechk_tac prems 1);
qed "insertT";

val prems = goal List.thy
  "[| f : {f:A->A->Bool. a : {a:A. l : {l:List(A).P(insert(f,a,l))}}} |] ==> \
\  insert(f,a,l)  : {x:List(A). P(x)}";
by (cut_facts_tac prems 1);
by (fast_tac (set_cs addSIs [SubtypeI,insertT] addSEs [SubtypeE]) 1);
qed "insertTS";

val prems = goalw List.thy [partition_def]
  "[| f:A->Bool;  l : List(A) |] ==> partition(f,l) : List(A)*List(A)";
by (typechk_tac prems 1);
by clean_ccs_tac;
by (rtac (ListPRI RS wfstI RS (ListPR_wf RS wmap_wf RS wfI)) 2);
by (rtac (ListPRI RS wfstI RS (ListPR_wf RS wmap_wf RS wfI)) 1);
by (REPEAT (atac 1));
qed "partitionT";

(*** Correctness Conditions for Insertion Sort ***)


val prems = goalw List.thy [isort_def] 
    "f:A->A->Bool ==> isort(f) : PROD l:List(A).{x: List(A). Ord(f,x) & Perm(x,l)}";
by (gen_ccs_tac  ([insertTS,insertT]@prems) 1);


(*** Correctness Conditions for Quick Sort ***)

val prems = goalw List.thy [qsort_def] 
    "f:A->A->Bool ==> qsort(f) : PROD l:List(A).{x: List(A). Ord(f,x) & Perm(x,l)}";
by (gen_ccs_tac  ([partitionT,appendTS,appendT]@prems) 1);

