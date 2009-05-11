theory Predicate_Compile
imports Complex_Main Code_Index Lattice_Syntax
uses "predicate_compile.ML"
begin

setup {* Predicate_Compile.setup *}

ML {*
  OuterSyntax.local_theory_to_proof "code_pred" "sets up goal for cases rule from given introduction rules and compiles predicate"
  OuterKeyword.thy_goal (OuterParse.term_group >> Predicate_Compile.code_pred_cmd)
*}

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

fun anamorph :: "('b \<Rightarrow> ('a \<times> 'b) option) \<Rightarrow> index \<Rightarrow> 'b \<Rightarrow> 'a list \<times> 'b" where
  "anamorph f k x = (if k = 0 then ([], x)
    else case f x of None \<Rightarrow> ([], x) | Some (v, y) \<Rightarrow> let (vs, z) = anamorph f (k - 1) y in (v # vs, z))"

ML {*
let
  fun yield (@{code Predicate.Seq} f) = @{code next} yield (f ())
  fun yieldn k = @{code anamorph} yield k
in
  yieldn 0 (*replace with number of elements to retrieve*)
    @{code "\<bottom> :: 'a Predicate.pred"} (*replace bottom with sequence to evaluate*)
end
*}

section {* Example for user interface *}

inductive append ::  "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "append [] ys ys"
| "append xs' ys zs' \<Longrightarrow> append (x#xs') ys (x#zs')"

code_pred append
  using assms by (rule append.cases)

thm append_codegen
thm append_cases


end