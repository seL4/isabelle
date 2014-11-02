
(* Author: Lukas Bulwahn, TU Muenchen *)

section {* Various kind of sequences inside the random monad *}

theory Random_Sequence
imports Random_Pred
begin

type_synonym 'a random_dseq = "natural \<Rightarrow> natural \<Rightarrow> Random.seed \<Rightarrow> ('a Limited_Sequence.dseq \<times> Random.seed)"

definition empty :: "'a random_dseq"
where
  "empty = (%nrandom size. Pair (Limited_Sequence.empty))"

definition single :: "'a => 'a random_dseq"
where
  "single x = (%nrandom size. Pair (Limited_Sequence.single x))"

definition bind :: "'a random_dseq => ('a \<Rightarrow> 'b random_dseq) \<Rightarrow> 'b random_dseq"
where
  "bind R f = (\<lambda>nrandom size s. let
     (P, s') = R nrandom size s;
     (s1, s2) = Random.split_seed s'
  in (Limited_Sequence.bind P (%a. fst (f a nrandom size s1)), s2))"

definition union :: "'a random_dseq => 'a random_dseq => 'a random_dseq"
where
  "union R1 R2 = (\<lambda>nrandom size s. let
     (S1, s') = R1 nrandom size s; (S2, s'') = R2 nrandom size s'
  in (Limited_Sequence.union S1 S2, s''))"

definition if_random_dseq :: "bool => unit random_dseq"
where
  "if_random_dseq b = (if b then single () else empty)"

definition not_random_dseq :: "unit random_dseq => unit random_dseq"
where
  "not_random_dseq R = (\<lambda>nrandom size s. let
     (S, s') = R nrandom size s
   in (Limited_Sequence.not_seq S, s'))"

definition map :: "('a => 'b) => 'a random_dseq => 'b random_dseq"
where
  "map f P = bind P (single o f)"

fun Random :: "(natural \<Rightarrow> Random.seed \<Rightarrow> (('a \<times> (unit \<Rightarrow> term)) \<times> Random.seed)) \<Rightarrow> 'a random_dseq"
where
  "Random g nrandom = (%size. if nrandom <= 0 then (Pair Limited_Sequence.empty) else
     (scomp (g size) (%r. scomp (Random g (nrandom - 1) size) (%rs. Pair (Limited_Sequence.union (Limited_Sequence.single (fst r)) rs)))))"


type_synonym 'a pos_random_dseq = "natural \<Rightarrow> natural \<Rightarrow> Random.seed \<Rightarrow> 'a Limited_Sequence.pos_dseq"

definition pos_empty :: "'a pos_random_dseq"
where
  "pos_empty = (%nrandom size seed. Limited_Sequence.pos_empty)"

definition pos_single :: "'a => 'a pos_random_dseq"
where
  "pos_single x = (%nrandom size seed. Limited_Sequence.pos_single x)"

definition pos_bind :: "'a pos_random_dseq => ('a \<Rightarrow> 'b pos_random_dseq) \<Rightarrow> 'b pos_random_dseq"
where
  "pos_bind R f = (\<lambda>nrandom size seed. Limited_Sequence.pos_bind (R nrandom size seed) (%a. f a nrandom size seed))"

definition pos_decr_bind :: "'a pos_random_dseq => ('a \<Rightarrow> 'b pos_random_dseq) \<Rightarrow> 'b pos_random_dseq"
where
  "pos_decr_bind R f = (\<lambda>nrandom size seed. Limited_Sequence.pos_decr_bind (R nrandom size seed) (%a. f a nrandom size seed))"

definition pos_union :: "'a pos_random_dseq => 'a pos_random_dseq => 'a pos_random_dseq"
where
  "pos_union R1 R2 = (\<lambda>nrandom size seed. Limited_Sequence.pos_union (R1 nrandom size seed) (R2 nrandom size seed))"

definition pos_if_random_dseq :: "bool => unit pos_random_dseq"
where
  "pos_if_random_dseq b = (if b then pos_single () else pos_empty)"

definition pos_iterate_upto :: "(natural => 'a) => natural => natural => 'a pos_random_dseq"
where
  "pos_iterate_upto f n m = (\<lambda>nrandom size seed. Limited_Sequence.pos_iterate_upto f n m)"

definition pos_map :: "('a => 'b) => 'a pos_random_dseq => 'b pos_random_dseq"
where
  "pos_map f P = pos_bind P (pos_single o f)"

fun iter :: "(Random.seed \<Rightarrow> ('a \<times> (unit \<Rightarrow> term)) \<times> Random.seed)
  \<Rightarrow> natural \<Rightarrow> Random.seed \<Rightarrow> 'a Lazy_Sequence.lazy_sequence"
where
  "iter random nrandom seed =
    (if nrandom = 0 then Lazy_Sequence.empty else Lazy_Sequence.Lazy_Sequence (%u. let ((x, _), seed') = random seed in Some (x, iter random (nrandom - 1) seed')))"

definition pos_Random :: "(natural \<Rightarrow> Random.seed \<Rightarrow> ('a \<times> (unit \<Rightarrow> term)) \<times> Random.seed)
  \<Rightarrow> 'a pos_random_dseq"
where
  "pos_Random g = (%nrandom size seed depth. iter (g size) nrandom seed)"


type_synonym 'a neg_random_dseq = "natural \<Rightarrow> natural \<Rightarrow> Random.seed \<Rightarrow> 'a Limited_Sequence.neg_dseq"

definition neg_empty :: "'a neg_random_dseq"
where
  "neg_empty = (%nrandom size seed. Limited_Sequence.neg_empty)"

definition neg_single :: "'a => 'a neg_random_dseq"
where
  "neg_single x = (%nrandom size seed. Limited_Sequence.neg_single x)"

definition neg_bind :: "'a neg_random_dseq => ('a \<Rightarrow> 'b neg_random_dseq) \<Rightarrow> 'b neg_random_dseq"
where
  "neg_bind R f = (\<lambda>nrandom size seed. Limited_Sequence.neg_bind (R nrandom size seed) (%a. f a nrandom size seed))"

definition neg_decr_bind :: "'a neg_random_dseq => ('a \<Rightarrow> 'b neg_random_dseq) \<Rightarrow> 'b neg_random_dseq"
where
  "neg_decr_bind R f = (\<lambda>nrandom size seed. Limited_Sequence.neg_decr_bind (R nrandom size seed) (%a. f a nrandom size seed))"

definition neg_union :: "'a neg_random_dseq => 'a neg_random_dseq => 'a neg_random_dseq"
where
  "neg_union R1 R2 = (\<lambda>nrandom size seed. Limited_Sequence.neg_union (R1 nrandom size seed) (R2 nrandom size seed))"

definition neg_if_random_dseq :: "bool => unit neg_random_dseq"
where
  "neg_if_random_dseq b = (if b then neg_single () else neg_empty)"

definition neg_iterate_upto :: "(natural => 'a) => natural => natural => 'a neg_random_dseq"
where
  "neg_iterate_upto f n m = (\<lambda>nrandom size seed. Limited_Sequence.neg_iterate_upto f n m)"

definition neg_not_random_dseq :: "unit pos_random_dseq => unit neg_random_dseq"
where
  "neg_not_random_dseq R = (\<lambda>nrandom size seed. Limited_Sequence.neg_not_seq (R nrandom size seed))"

definition neg_map :: "('a => 'b) => 'a neg_random_dseq => 'b neg_random_dseq"
where
  "neg_map f P = neg_bind P (neg_single o f)"

definition pos_not_random_dseq :: "unit neg_random_dseq => unit pos_random_dseq"
where
  "pos_not_random_dseq R = (\<lambda>nrandom size seed. Limited_Sequence.pos_not_seq (R nrandom size seed))"


hide_const (open)
  empty single bind union if_random_dseq not_random_dseq map Random
  pos_empty pos_single pos_bind pos_decr_bind pos_union pos_if_random_dseq pos_iterate_upto
  pos_not_random_dseq pos_map iter pos_Random
  neg_empty neg_single neg_bind neg_decr_bind neg_union neg_if_random_dseq neg_iterate_upto
  neg_not_random_dseq neg_map

hide_fact (open) empty_def single_def bind_def union_def if_random_dseq_def not_random_dseq_def
  map_def Random.simps
  pos_empty_def pos_single_def pos_bind_def pos_decr_bind_def pos_union_def pos_if_random_dseq_def
  pos_iterate_upto_def pos_not_random_dseq_def pos_map_def iter.simps pos_Random_def
  neg_empty_def neg_single_def neg_bind_def neg_decr_bind_def neg_union_def neg_if_random_dseq_def
  neg_iterate_upto_def neg_not_random_dseq_def neg_map_def

end

