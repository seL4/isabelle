theory RPred
imports Quickcheck Random Predicate
begin

types 'a "rpred" = "Random.seed \<Rightarrow> ('a Predicate.pred \<times> Random.seed)"

section {* The RandomPred Monad *}

text {* A monad to combine the random state monad and the predicate monad *}

definition bot :: "'a rpred"
  where "bot = Pair (bot_class.bot)"

definition return :: "'a => 'a rpred"
  where "return x = Pair (Predicate.single x)"

definition bind :: "'a rpred \<Rightarrow> ('a \<Rightarrow> 'b rpred) \<Rightarrow> 'b rpred"
(* (infixl "\<guillemotright>=" 60) *)
  where "bind RP f =
  (\<lambda>s. let (P, s') = RP s;
        (s1, s2) = Random.split_seed s'
    in (Predicate.bind P (%a. fst (f a s1)), s2))"

definition supp :: "'a rpred \<Rightarrow> 'a rpred \<Rightarrow> 'a rpred"
(* (infixl "\<squnion>" 80) *)
where
  "supp RP1 RP2 = (\<lambda>s. let (P1, s') = RP1 s; (P2, s'') = RP2 s'
  in (upper_semilattice_class.sup P1 P2, s''))"

definition if_rpred :: "bool \<Rightarrow> unit rpred"
where
  "if_rpred b = (if b then return () else bot)"

(* Missing a good definition for negation: not_rpred *)

definition not_rpred :: "unit rpred \<Rightarrow> unit rpred"
where
  "not_rpred P = (\<lambda>s. let (P', s') = P s in if Predicate.eval P' () then (Orderings.bot, s') else (Predicate.single (), s'))"

definition lift_pred :: "'a Predicate.pred \<Rightarrow> 'a rpred"
  where
  "lift_pred = Pair"

definition lift_random :: "(Random.seed \<Rightarrow> ('a \<times> (unit \<Rightarrow> term)) \<times> Random.seed) \<Rightarrow> 'a rpred"
  where "lift_random g = scomp g (Pair o (Predicate.single o fst))"

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a rpred \<Rightarrow> 'b rpred)"
  where "map f P = bind P (return o f)"

hide (open) const return bind supp map
  
end