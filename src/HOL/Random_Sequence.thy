
(* Author: Lukas Bulwahn, TU Muenchen *)

theory Random_Sequence
imports Quickcheck DSequence
begin

types 'a random_dseq = "code_numeral \<Rightarrow> code_numeral \<Rightarrow> Random.seed \<Rightarrow> ('a DSequence.dseq \<times> Random.seed)"

definition empty :: "'a random_dseq"
where
  "empty = (%nrandom size. Pair (DSequence.empty))"

definition single :: "'a => 'a random_dseq"
where
  "single x = (%nrandom size. Pair (DSequence.single x))"

definition bind :: "'a random_dseq => ('a \<Rightarrow> 'b random_dseq) \<Rightarrow> 'b random_dseq"
where
  "bind R f = (\<lambda>nrandom size s. let
     (P, s') = R nrandom size s;
     (s1, s2) = Random.split_seed s'
  in (DSequence.bind P (%a. fst (f a nrandom size s1)), s2))"

definition union :: "'a random_dseq => 'a random_dseq => 'a random_dseq"
where
  "union R1 R2 = (\<lambda>nrandom size s. let
     (S1, s') = R1 nrandom size s; (S2, s'') = R2 nrandom size s'
  in (DSequence.union S1 S2, s''))"

definition if_random_dseq :: "bool => unit random_dseq"
where
  "if_random_dseq b = (if b then single () else empty)"

definition not_random_dseq :: "unit random_dseq => unit random_dseq"
where
  "not_random_dseq R = (\<lambda>nrandom size s. let
     (S, s') = R nrandom size s
   in (DSequence.not_seq S, s'))"

fun Random :: "(code_numeral \<Rightarrow> Random.seed \<Rightarrow> (('a \<times> (unit \<Rightarrow> term)) \<times> Random.seed)) \<Rightarrow> 'a random_dseq"
where
  "Random g nrandom = (%size. if nrandom <= 0 then (Pair DSequence.empty) else
     (scomp (g size) (%r. scomp (Random g (nrandom - 1) size) (%rs. Pair (DSequence.union (DSequence.single (fst r)) rs)))))"

definition map :: "('a => 'b) => 'a random_dseq => 'b random_dseq"
where
  "map f P = bind P (single o f)"

(*
hide const DSequence.empty DSequence.single DSequence.eval
  DSequence.map_seq DSequence.bind DSequence.union DSequence.if_seq DSequence.not_seq
  DSequence.map
*)

hide (open) const empty single bind union if_random_dseq not_random_dseq Random map

hide type DSequence.dseq random_dseq
hide (open) fact empty_def single_def bind_def union_def if_random_dseq_def not_random_dseq_def Random_def map_def

end