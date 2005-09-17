(*  Title:      CCL/ex/List.ML
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

val list_defs = [map_def,comp_def,append_def,filter_def,flat_def,
                 insert_def,isort_def,partition_def,qsort_def];

(****)

val listBs = map (fn s=>prove_goalw (the_context ()) list_defs s (fn _ => [simp_tac term_ss 1]))
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

val [prem] = goal (the_context ()) "n:Nat ==> map(f) ^ n ` [] = []";
by (rtac (prem RS Nat_ind) 1);
by (ALLGOALS (asm_simp_tac list_ss));
qed "nmapBnil";

val [prem] = goal (the_context ()) "n:Nat ==> map(f)^n`(x$xs) = (f^n`x)$(map(f)^n`xs)";
by (rtac (prem RS Nat_ind) 1);
by (ALLGOALS (asm_simp_tac list_ss));
qed "nmapBcons";

(***)

val prems = goalw (the_context ()) [map_def]
  "[| !!x. x:A==>f(x):B;  l : List(A) |] ==> map(f,l) : List(B)";
by (typechk_tac prems 1);
qed "mapT";

val prems = goalw (the_context ()) [append_def]
  "[| l : List(A);  m : List(A) |] ==> l @ m : List(A)";
by (typechk_tac prems 1);
qed "appendT";

val prems = goal (the_context ())
  "[| l : {l:List(A). m : {m:List(A).P(l @ m)}} |] ==> l @ m : {x:List(A). P(x)}";
by (cut_facts_tac prems 1);
by (fast_tac (set_cs addSIs [SubtypeI,appendT] addSEs [SubtypeE]) 1);
qed "appendTS";

val prems = goalw (the_context ()) [filter_def]
  "[| f:A->Bool;   l : List(A) |] ==> filter(f,l) : List(A)";
by (typechk_tac prems 1);
qed "filterT";

val prems = goalw (the_context ()) [flat_def]
  "l : List(List(A)) ==> flat(l) : List(A)";
by (typechk_tac (appendT::prems) 1);
qed "flatT";

val prems = goalw (the_context ()) [insert_def]
  "[|  f : A->A->Bool; a:A; l : List(A) |] ==> insert(f,a,l) : List(A)";
by (typechk_tac prems 1);
qed "insertT";

val prems = goal (the_context ())
  "[| f : {f:A->A->Bool. a : {a:A. l : {l:List(A).P(insert(f,a,l))}}} |] ==> \
\  insert(f,a,l)  : {x:List(A). P(x)}";
by (cut_facts_tac prems 1);
by (fast_tac (set_cs addSIs [SubtypeI,insertT] addSEs [SubtypeE]) 1);
qed "insertTS";

val prems = goalw (the_context ()) [partition_def]
  "[| f:A->Bool;  l : List(A) |] ==> partition(f,l) : List(A)*List(A)";
by (typechk_tac prems 1);
by clean_ccs_tac;
by (rtac (ListPRI RS wfstI RS (ListPR_wf RS wmap_wf RS wfI)) 2);
by (rtac (ListPRI RS wfstI RS (ListPR_wf RS wmap_wf RS wfI)) 1);
by (REPEAT (atac 1));
qed "partitionT";

(*** Correctness Conditions for Insertion Sort ***)


val prems = goalw (the_context ()) [isort_def]
    "f:A->A->Bool ==> isort(f) : PROD l:List(A).{x: List(A). Ord(f,x) & Perm(x,l)}";
by (gen_ccs_tac  ([insertTS,insertT]@prems) 1);


(*** Correctness Conditions for Quick Sort ***)

val prems = goalw (the_context ()) [qsort_def]
    "f:A->A->Bool ==> qsort(f) : PROD l:List(A).{x: List(A). Ord(f,x) & Perm(x,l)}";
by (gen_ccs_tac  ([partitionT,appendTS,appendT]@prems) 1);
