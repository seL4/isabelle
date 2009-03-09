theory Predicate_Compile
imports Complex_Main Lattice_Syntax
uses "predicate_compile.ML"
begin

setup {* Predicate_Compile.setup *}

primrec "next" :: "('a Predicate.pred \<Rightarrow> ('a \<times> 'a Predicate.pred) option)
  \<Rightarrow> 'a Predicate.seq \<Rightarrow> ('a \<times> 'a Predicate.pred) option" where
    "next yield Predicate.Empty = None"
  | "next yield (Predicate.Insert x P) = Some (x, P)"
  | "next yield (Predicate.Join P xq) = (case yield P
   of None \<Rightarrow> next yield xq | Some (x, Q) \<Rightarrow> Some (x, Predicate.Seq (\<lambda>_. Predicate.Join Q xq)))"

primrec pull :: "('a Predicate.pred \<Rightarrow> ('a \<times> 'a Predicate.pred) option)
  \<Rightarrow> nat \<Rightarrow> 'a Predicate.pred \<Rightarrow> 'a list \<times> 'a Predicate.pred" where
    "pull yield 0 P = ([], \<bottom>)"
  | "pull yield (Suc n) P = (case yield P
      of None \<Rightarrow> ([], \<bottom>) | Some (x, Q) \<Rightarrow> let (xs, R) = pull yield n Q in (x # xs, R))"

end