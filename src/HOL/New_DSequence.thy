
(* Author: Lukas Bulwahn, TU Muenchen *)

header {* Depth-Limited Sequences with failure element *}

theory New_DSequence
imports Random_Sequence
begin

section {* Positive Depth-Limited Sequence *}

types 'a pos_dseq = "code_numeral => 'a Lazy_Sequence.lazy_sequence"

definition pos_empty :: "'a pos_dseq"
where
  "pos_empty = (%i. Lazy_Sequence.empty)"

definition pos_single :: "'a => 'a pos_dseq"
where
  "pos_single x = (%i. Lazy_Sequence.single x)"

definition pos_bind :: "'a pos_dseq => ('a => 'b pos_dseq) => 'b pos_dseq"
where
  "pos_bind x f = (%i. 
     if i = 0 then
       Lazy_Sequence.empty
     else
       Lazy_Sequence.bind (x (i - 1)) (%a. f a i))"

definition pos_union :: "'a pos_dseq => 'a pos_dseq => 'a pos_dseq"
where
  "pos_union xq yq = (%i. Lazy_Sequence.append (xq i) (yq i))"

definition pos_if_seq :: "bool => unit pos_dseq"
where
  "pos_if_seq b = (if b then pos_single () else pos_empty)"

definition pos_iterate_upto :: "(code_numeral => 'a) => code_numeral => code_numeral => 'a pos_dseq"
where
  "pos_iterate_upto f n m = (%i. Lazy_Sequence.iterate_upto f n m)"
 
definition pos_map :: "('a => 'b) => 'a pos_dseq => 'b pos_dseq"
where
  "pos_map f xq = (%i. Lazy_Sequence.map f (xq i))"

section {* Negative Depth-Limited Sequence *}

types 'a neg_dseq = "code_numeral => 'a Lazy_Sequence.hit_bound_lazy_sequence"

definition neg_empty :: "'a neg_dseq"
where
  "neg_empty = (%i. Lazy_Sequence.empty)"

definition neg_single :: "'a => 'a neg_dseq"
where
  "neg_single x = (%i. Lazy_Sequence.hb_single x)"

definition neg_bind :: "'a neg_dseq => ('a => 'b neg_dseq) => 'b neg_dseq"
where
  "neg_bind x f = (%i. 
     if i = 0 then
       Lazy_Sequence.hit_bound
     else
       hb_bind (x (i - 1)) (%a. f a i))"

definition neg_union :: "'a neg_dseq => 'a neg_dseq => 'a neg_dseq"
where
  "neg_union x y = (%i. Lazy_Sequence.append (x i) (y i))"

definition neg_if_seq :: "bool => unit neg_dseq"
where
  "neg_if_seq b = (if b then neg_single () else neg_empty)"

definition neg_iterate_upto 
where
  "neg_iterate_upto f n m = (%i. Lazy_Sequence.iterate_upto (%i. Some (f i)) n m)"

definition neg_map :: "('a => 'b) => 'a neg_dseq => 'b neg_dseq"
where
  "neg_map f xq = (%i. Lazy_Sequence.hb_map f (xq i))"

section {* Negation *}

definition pos_not_seq :: "unit neg_dseq => unit pos_dseq"
where
  "pos_not_seq xq = (%i. Lazy_Sequence.hb_not_seq (xq i))"

definition neg_not_seq :: "unit pos_dseq => unit neg_dseq"
where
  "neg_not_seq x = (%i. case Lazy_Sequence.yield (x i) of
    None => Lazy_Sequence.hb_single ()
  | Some ((), xq) => Lazy_Sequence.empty)"

hide (open) type pos_dseq neg_dseq

hide (open) const 
  pos_empty pos_single pos_bind pos_union pos_if_seq pos_iterate_upto pos_not_seq pos_map
  neg_empty neg_single neg_bind neg_union neg_if_seq neg_iterate_upto neg_not_seq neg_map
hide (open) fact
  pos_empty_def pos_single_def pos_bind_def pos_union_def pos_if_seq_def pos_iterate_upto_def pos_not_seq_def pos_map_def
  neg_empty_def neg_single_def neg_bind_def neg_union_def neg_if_seq_def neg_iterate_upto_def neg_not_seq_def neg_map_def

end
