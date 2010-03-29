
(* Author: Lukas Bulwahn, TU Muenchen *)

theory New_Random_Sequence
imports Quickcheck New_DSequence
begin

types 'a pos_random_dseq = "code_numeral \<Rightarrow> code_numeral \<Rightarrow> Random.seed \<Rightarrow> 'a New_DSequence.pos_dseq"
types 'a neg_random_dseq = "code_numeral \<Rightarrow> code_numeral \<Rightarrow> Random.seed \<Rightarrow> 'a New_DSequence.neg_dseq"

definition pos_empty :: "'a pos_random_dseq"
where
  "pos_empty = (%nrandom size seed. New_DSequence.pos_empty)"

definition pos_single :: "'a => 'a pos_random_dseq"
where
  "pos_single x = (%nrandom size seed. New_DSequence.pos_single x)"

definition pos_bind :: "'a pos_random_dseq => ('a \<Rightarrow> 'b pos_random_dseq) \<Rightarrow> 'b pos_random_dseq"
where
  "pos_bind R f = (\<lambda>nrandom size seed. New_DSequence.pos_bind (R nrandom size seed) (%a. f a nrandom size seed))"

definition pos_union :: "'a pos_random_dseq => 'a pos_random_dseq => 'a pos_random_dseq"
where
  "pos_union R1 R2 = (\<lambda>nrandom size seed. New_DSequence.pos_union (R1 nrandom size seed) (R2 nrandom size seed))"

definition pos_if_random_dseq :: "bool => unit pos_random_dseq"
where
  "pos_if_random_dseq b = (if b then pos_single () else pos_empty)"

definition pos_not_random_dseq :: "unit neg_random_dseq => unit pos_random_dseq"
where
  "pos_not_random_dseq R = (\<lambda>nrandom size seed. New_DSequence.pos_not_seq (R nrandom size seed))"

fun iter :: "(code_numeral * code_numeral => ('a * (unit => term)) * code_numeral * code_numeral) => code_numeral => code_numeral * code_numeral => 'a Lazy_Sequence.lazy_sequence"
where
  "iter random nrandom seed =
    (if nrandom = 0 then Lazy_Sequence.empty else Lazy_Sequence.Lazy_Sequence (%u. let ((x, _), seed') = random seed in Some (x, iter random (nrandom - 1) seed')))"

definition Random :: "(code_numeral \<Rightarrow> Random.seed \<Rightarrow> (('a \<times> (unit \<Rightarrow> term)) \<times> Random.seed)) \<Rightarrow> 'a pos_random_dseq"
where
  "Random g = (%nrandom size seed depth. iter (g size) nrandom seed)"

definition pos_map :: "('a => 'b) => 'a pos_random_dseq => 'b pos_random_dseq"
where
  "pos_map f P = pos_bind P (pos_single o f)"


definition neg_empty :: "'a neg_random_dseq"
where
  "neg_empty = (%nrandom size seed. New_DSequence.neg_empty)"

definition neg_single :: "'a => 'a neg_random_dseq"
where
  "neg_single x = (%nrandom size seed. New_DSequence.neg_single x)"

definition neg_bind :: "'a neg_random_dseq => ('a \<Rightarrow> 'b neg_random_dseq) \<Rightarrow> 'b neg_random_dseq"
where
  "neg_bind R f = (\<lambda>nrandom size seed. New_DSequence.neg_bind (R nrandom size seed) (%a. f a nrandom size seed))"

definition neg_union :: "'a neg_random_dseq => 'a neg_random_dseq => 'a neg_random_dseq"
where
  "neg_union R1 R2 = (\<lambda>nrandom size seed. New_DSequence.neg_union (R1 nrandom size seed) (R2 nrandom size seed))"

definition neg_if_random_dseq :: "bool => unit neg_random_dseq"
where
  "neg_if_random_dseq b = (if b then neg_single () else neg_empty)"

definition neg_not_random_dseq :: "unit pos_random_dseq => unit neg_random_dseq"
where
  "neg_not_random_dseq R = (\<lambda>nrandom size seed. New_DSequence.neg_not_seq (R nrandom size seed))"
(*
fun iter :: "(code_numeral * code_numeral => ('a * (unit => term)) * code_numeral * code_numeral) => code_numeral => code_numeral * code_numeral => 'a Lazy_Sequence.lazy_sequence"
where
  "iter random nrandom seed =
    (if nrandom = 0 then Lazy_Sequence.empty else Lazy_Sequence.Lazy_Sequence (%u. let ((x, _), seed') = random seed in Some (x, iter random (nrandom - 1) seed')))"

definition Random :: "(code_numeral \<Rightarrow> Random.seed \<Rightarrow> (('a \<times> (unit \<Rightarrow> term)) \<times> Random.seed)) \<Rightarrow> 'a pos_random_dseq"
where
  "Random g = (%nrandom size seed depth. iter (g size) nrandom seed)"
*)
definition neg_map :: "('a => 'b) => 'a neg_random_dseq => 'b neg_random_dseq"
where
  "neg_map f P = neg_bind P (neg_single o f)"
(*
hide const DSequence.empty DSequence.single DSequence.eval
  DSequence.map_seq DSequence.bind DSequence.union DSequence.if_seq DSequence.not_seq
  DSequence.map
*)

hide (open) const pos_empty pos_single pos_bind pos_union pos_if_random_dseq pos_not_random_dseq iter Random pos_map
  neg_empty neg_single neg_bind neg_union neg_if_random_dseq neg_not_random_dseq neg_map
hide type New_DSequence.pos_dseq New_DSequence.neg_dseq pos_random_dseq neg_random_dseq
(* FIXME: hide facts *)
(*hide (open) fact empty_def single_def bind_def union_def if_random_dseq_def not_random_dseq_def Random.simps map_def*)

end