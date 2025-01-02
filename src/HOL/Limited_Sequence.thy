
(* Author: Lukas Bulwahn, TU Muenchen *)

section \<open>Depth-Limited Sequences with failure element\<close>

theory Limited_Sequence
imports Lazy_Sequence
begin

subsection \<open>Depth-Limited Sequence\<close>

type_synonym 'a dseq = "natural \<Rightarrow> bool \<Rightarrow> 'a lazy_sequence option"

definition empty :: "'a dseq"
where
  "empty = (\<lambda>_ _. Some Lazy_Sequence.empty)"

definition single :: "'a \<Rightarrow> 'a dseq"
where
  "single x = (\<lambda>_ _. Some (Lazy_Sequence.single x))"

definition eval :: "'a dseq \<Rightarrow> natural \<Rightarrow> bool \<Rightarrow> 'a lazy_sequence option"
where
  [simp]: "eval f i pol = f i pol"

definition yield :: "'a dseq \<Rightarrow> natural \<Rightarrow> bool \<Rightarrow> ('a \<times> 'a dseq) option" 
where
  "yield f i pol = (case eval f i pol of
    None \<Rightarrow> None
  | Some s \<Rightarrow> (map_option \<circ> apsnd) (\<lambda>r _ _. Some r) (Lazy_Sequence.yield s))"

definition map_seq :: "('a \<Rightarrow> 'b dseq) \<Rightarrow> 'a lazy_sequence \<Rightarrow> 'b dseq"
where
  "map_seq f xq i pol = map_option Lazy_Sequence.flat
    (Lazy_Sequence.those (Lazy_Sequence.map (\<lambda>x. f x i pol) xq))"

lemma map_seq_code [code]:
  "map_seq f xq i pol = (case Lazy_Sequence.yield xq of
    None \<Rightarrow> Some Lazy_Sequence.empty
  | Some (x, xq') \<Rightarrow> (case eval (f x) i pol of
      None \<Rightarrow> None
    | Some yq \<Rightarrow> (case map_seq f xq' i pol of
        None \<Rightarrow> None
      | Some zq \<Rightarrow> Some (Lazy_Sequence.append yq zq))))"
  by (cases xq)
    (auto simp add: map_seq_def Lazy_Sequence.those_def lazy_sequence_eq_iff split: list.splits option.splits)

definition bind :: "'a dseq \<Rightarrow> ('a \<Rightarrow> 'b dseq) \<Rightarrow> 'b dseq"
where
  "bind x f = (\<lambda>i pol. 
     if i = 0 then
       (if pol then Some Lazy_Sequence.empty else None)
     else
       (case x (i - 1) pol of
         None \<Rightarrow> None
       | Some xq \<Rightarrow> map_seq f xq i pol))"

definition union :: "'a dseq \<Rightarrow> 'a dseq \<Rightarrow> 'a dseq"
where
  "union x y = (\<lambda>i pol. case (x i pol, y i pol) of
      (Some xq, Some yq) \<Rightarrow> Some (Lazy_Sequence.append xq yq)
    | _ \<Rightarrow> None)"

definition if_seq :: "bool \<Rightarrow> unit dseq"
where
  "if_seq b = (if b then single () else empty)"

definition not_seq :: "unit dseq \<Rightarrow> unit dseq"
where
  "not_seq x = (\<lambda>i pol. case x i (\<not> pol) of
    None \<Rightarrow> Some Lazy_Sequence.empty
  | Some xq \<Rightarrow> (case Lazy_Sequence.yield xq of
      None \<Rightarrow> Some (Lazy_Sequence.single ())
    | Some _ \<Rightarrow> Some (Lazy_Sequence.empty)))"

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a dseq \<Rightarrow> 'b dseq"
where
  "map f g = (\<lambda>i pol. case g i pol of
     None \<Rightarrow> None
   | Some xq \<Rightarrow> Some (Lazy_Sequence.map f xq))"


subsection \<open>Positive Depth-Limited Sequence\<close>

type_synonym 'a pos_dseq = "natural \<Rightarrow> 'a Lazy_Sequence.lazy_sequence"

definition pos_empty :: "'a pos_dseq"
where
  "pos_empty = (\<lambda>i. Lazy_Sequence.empty)"

definition pos_single :: "'a \<Rightarrow> 'a pos_dseq"
where
  "pos_single x = (\<lambda>i. Lazy_Sequence.single x)"

definition pos_bind :: "'a pos_dseq \<Rightarrow> ('a \<Rightarrow> 'b pos_dseq) \<Rightarrow> 'b pos_dseq"
where
  "pos_bind x f = (\<lambda>i. Lazy_Sequence.bind (x i) (\<lambda>a. f a i))"

definition pos_decr_bind :: "'a pos_dseq \<Rightarrow> ('a \<Rightarrow> 'b pos_dseq) \<Rightarrow> 'b pos_dseq"
where
  "pos_decr_bind x f = (\<lambda>i. 
     if i = 0 then
       Lazy_Sequence.empty
     else
       Lazy_Sequence.bind (x (i - 1)) (\<lambda>a. f a i))"

definition pos_union :: "'a pos_dseq \<Rightarrow> 'a pos_dseq \<Rightarrow> 'a pos_dseq"
where
  "pos_union xq yq = (\<lambda>i. Lazy_Sequence.append (xq i) (yq i))"

definition pos_if_seq :: "bool \<Rightarrow> unit pos_dseq"
where
  "pos_if_seq b = (if b then pos_single () else pos_empty)"

definition pos_iterate_upto :: "(natural \<Rightarrow> 'a) \<Rightarrow> natural \<Rightarrow> natural \<Rightarrow> 'a pos_dseq"
where
  "pos_iterate_upto f n m = (\<lambda>i. Lazy_Sequence.iterate_upto f n m)"
 
definition pos_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a pos_dseq \<Rightarrow> 'b pos_dseq"
where
  "pos_map f xq = (\<lambda>i. Lazy_Sequence.map f (xq i))"


subsection \<open>Negative Depth-Limited Sequence\<close>

type_synonym 'a neg_dseq = "natural \<Rightarrow> 'a Lazy_Sequence.hit_bound_lazy_sequence"

definition neg_empty :: "'a neg_dseq"
where
  "neg_empty = (\<lambda>i. Lazy_Sequence.empty)"

definition neg_single :: "'a \<Rightarrow> 'a neg_dseq"
where
  "neg_single x = (\<lambda>i. Lazy_Sequence.hb_single x)"

definition neg_bind :: "'a neg_dseq \<Rightarrow> ('a \<Rightarrow> 'b neg_dseq) \<Rightarrow> 'b neg_dseq"
where
  "neg_bind x f = (\<lambda>i. hb_bind (x i) (\<lambda>a. f a i))"

definition neg_decr_bind :: "'a neg_dseq \<Rightarrow> ('a \<Rightarrow> 'b neg_dseq) \<Rightarrow> 'b neg_dseq"
where
  "neg_decr_bind x f = (\<lambda>i. 
     if i = 0 then
       Lazy_Sequence.hit_bound
     else
       hb_bind (x (i - 1)) (\<lambda>a. f a i))"

definition neg_union :: "'a neg_dseq \<Rightarrow> 'a neg_dseq \<Rightarrow> 'a neg_dseq"
where
  "neg_union x y = (\<lambda>i. Lazy_Sequence.append (x i) (y i))"

definition neg_if_seq :: "bool \<Rightarrow> unit neg_dseq"
where
  "neg_if_seq b = (if b then neg_single () else neg_empty)"

definition neg_iterate_upto 
where
  "neg_iterate_upto f n m = (\<lambda>i. Lazy_Sequence.iterate_upto (\<lambda>i. Some (f i)) n m)"

definition neg_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a neg_dseq \<Rightarrow> 'b neg_dseq"
where
  "neg_map f xq = (\<lambda>i. Lazy_Sequence.hb_map f (xq i))"


subsection \<open>Negation\<close>

definition pos_not_seq :: "unit neg_dseq \<Rightarrow> unit pos_dseq"
where
  "pos_not_seq xq = (\<lambda>i. Lazy_Sequence.hb_not_seq (xq (3 * i)))"

definition neg_not_seq :: "unit pos_dseq \<Rightarrow> unit neg_dseq"
where
  "neg_not_seq x = (\<lambda>i. case Lazy_Sequence.yield (x i) of
    None \<Rightarrow> Lazy_Sequence.hb_single ()
  | Some ((), xq) \<Rightarrow> Lazy_Sequence.empty)"


ML \<open>
signature LIMITED_SEQUENCE =
sig
  type 'a dseq = Code_Numeral.natural -> bool -> 'a Lazy_Sequence.lazy_sequence option
  val map : ('a -> 'b) -> 'a dseq -> 'b dseq
  val yield : 'a dseq -> Code_Numeral.natural -> bool -> ('a * 'a dseq) option
  val yieldn : int -> 'a dseq -> Code_Numeral.natural -> bool -> 'a list * 'a dseq
end;

structure Limited_Sequence : LIMITED_SEQUENCE =
struct

type 'a dseq = Code_Numeral.natural -> bool -> 'a Lazy_Sequence.lazy_sequence option

fun map f = @{code Limited_Sequence.map} f;

fun yield f = @{code Limited_Sequence.yield} f;

fun yieldn n f i pol = (case f i pol of
    NONE => ([], fn _ => fn _ => NONE)
  | SOME s => let val (xs, s') = Lazy_Sequence.yieldn n s in (xs, fn _ => fn _ => SOME s') end);

end;
\<close>

code_reserved
  (Eval) Limited_Sequence

hide_const (open) yield empty single eval map_seq bind union if_seq not_seq map
  pos_empty pos_single pos_bind pos_decr_bind pos_union pos_if_seq pos_iterate_upto pos_not_seq pos_map
  neg_empty neg_single neg_bind neg_decr_bind neg_union neg_if_seq neg_iterate_upto neg_not_seq neg_map

hide_fact (open) yield_def empty_def single_def eval_def map_seq_def bind_def union_def
  if_seq_def not_seq_def map_def
  pos_empty_def pos_single_def pos_bind_def pos_union_def pos_if_seq_def pos_iterate_upto_def pos_not_seq_def pos_map_def
  neg_empty_def neg_single_def neg_bind_def neg_union_def neg_if_seq_def neg_iterate_upto_def neg_not_seq_def neg_map_def

end
