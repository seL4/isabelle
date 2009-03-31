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

ML {*
let
  fun yield (@{code Predicate.Seq} f) = @{code next} yield (f ())
in
  yield @{code "\<bottom> :: 'a Predicate.pred"} (*replace bottom with sequence to evaluate*)
end
*}

fun pull :: "('a Predicate.pred \<Rightarrow> ('a \<times> 'a Predicate.pred) option)
  \<Rightarrow> index \<Rightarrow> 'a Predicate.pred \<Rightarrow> 'a list \<times> 'a Predicate.pred" where
  "pull yield k P = (if k = 0 then ([], \<bottom>)
    else case yield P of None \<Rightarrow> ([], \<bottom>) | Some (x, Q) \<Rightarrow> let (xs, R) = pull yield (k - 1) Q in (x # xs, R))"

ML {*
let
  fun yield (@{code Predicate.Seq} f) = @{code next} yield (f ())
  fun yieldn k = @{code pull} yield k
in
  yieldn 0 (*replace with number of elements to retrieve*)
    @{code "\<bottom> :: 'a Predicate.pred"} (*replace bottom with sequence to evaluate*)
end
*}

end