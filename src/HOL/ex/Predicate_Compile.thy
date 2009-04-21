theory Predicate_Compile
imports Complex_Main Code_Index Lattice_Syntax
uses "predicate_compile.ML"
begin

setup {* Predicate_Compile.setup *}

primrec "next" :: "('a Predicate.pred \<Rightarrow> ('a \<times> 'a Predicate.pred) option)
  \<Rightarrow> 'a Predicate.seq \<Rightarrow> ('a \<times> 'a Predicate.pred) option" where
    "next yield Predicate.Empty = None"
  | "next yield (Predicate.Insert x P) = Some (x, P)"
  | "next yield (Predicate.Join P xq) = (case yield P
   of None \<Rightarrow> next yield xq | Some (x, Q) \<Rightarrow> Some (x, Predicate.Seq (\<lambda>_. Predicate.Join Q xq)))"

fun anamorph :: "('b \<Rightarrow> ('a \<times> 'b) option) \<Rightarrow> index \<Rightarrow> 'b \<Rightarrow> 'a list \<times> 'b" where
  "anamorph f k x = (if k = 0 then ([], x)
    else case f x of None \<Rightarrow> ([], x) | Some (v, y) \<Rightarrow> let (vs, z) = anamorph f (k - 1) y in (v # vs, z))"

ML {*
structure Predicate =
struct

open Predicate;

fun yield (Predicate.Seq f) = @{code next} yield (f ());

fun yieldn k = @{code anamorph} yield k;

end;
*}

end