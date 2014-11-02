
(* Author: Lukas Bulwahn, TU Muenchen *)

section {* The Random-Predicate Monad *}

theory Random_Pred
imports Quickcheck_Random
begin

fun iter' :: "'a itself \<Rightarrow> natural \<Rightarrow> natural \<Rightarrow> Random.seed \<Rightarrow> ('a::random) Predicate.pred"
where
  "iter' T nrandom sz seed = (if nrandom = 0 then bot_class.bot else
     let ((x, _), seed') = Quickcheck_Random.random sz seed
   in Predicate.Seq (%u. Predicate.Insert x (iter' T (nrandom - 1) sz seed')))"

definition iter :: "natural \<Rightarrow> natural \<Rightarrow> Random.seed \<Rightarrow> ('a::random) Predicate.pred"
where
  "iter nrandom sz seed = iter' (TYPE('a)) nrandom sz seed"

lemma [code]:
  "iter nrandom sz seed = (if nrandom = 0 then bot_class.bot else
     let ((x, _), seed') = Quickcheck_Random.random sz seed
   in Predicate.Seq (%u. Predicate.Insert x (iter (nrandom - 1) sz seed')))"
   unfolding iter_def iter'.simps [of _ nrandom] ..

type_synonym 'a random_pred = "Random.seed \<Rightarrow> ('a Predicate.pred \<times> Random.seed)"

definition empty :: "'a random_pred"
  where "empty = Pair bot"

definition single :: "'a => 'a random_pred"
  where "single x = Pair (Predicate.single x)"

definition bind :: "'a random_pred \<Rightarrow> ('a \<Rightarrow> 'b random_pred) \<Rightarrow> 'b random_pred"
  where
    "bind R f = (\<lambda>s. let
       (P, s') = R s;
       (s1, s2) = Random.split_seed s'
     in (Predicate.bind P (%a. fst (f a s1)), s2))"

definition union :: "'a random_pred \<Rightarrow> 'a random_pred \<Rightarrow> 'a random_pred"
where
  "union R1 R2 = (\<lambda>s. let
     (P1, s') = R1 s; (P2, s'') = R2 s'
   in (sup_class.sup P1 P2, s''))"

definition if_randompred :: "bool \<Rightarrow> unit random_pred"
where
  "if_randompred b = (if b then single () else empty)"

definition iterate_upto :: "(natural \<Rightarrow> 'a) => natural \<Rightarrow> natural \<Rightarrow> 'a random_pred"
where
  "iterate_upto f n m = Pair (Predicate.iterate_upto f n m)"

definition not_randompred :: "unit random_pred \<Rightarrow> unit random_pred"
where
  "not_randompred P = (\<lambda>s. let
     (P', s') = P s
   in if Predicate.eval P' () then (Orderings.bot, s') else (Predicate.single (), s'))"

definition Random :: "(Random.seed \<Rightarrow> ('a \<times> (unit \<Rightarrow> term)) \<times> Random.seed) \<Rightarrow> 'a random_pred"
  where "Random g = scomp g (Pair o (Predicate.single o fst))"

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a random_pred \<Rightarrow> 'b random_pred"
  where "map f P = bind P (single o f)"

hide_const (open) iter' iter empty single bind union if_randompred
  iterate_upto not_randompred Random map

hide_fact iter'.simps
  
hide_fact (open) iter_def empty_def single_def bind_def union_def
  if_randompred_def iterate_upto_def not_randompred_def Random_def map_def 

end

