
(* Author: Lukas Bulwahn, TU Muenchen *)

header {* Lazy sequences *}

theory Lazy_Sequence
imports List Code_Numeral
begin

datatype 'a lazy_sequence = Empty | Insert 'a "'a lazy_sequence"

definition Lazy_Sequence :: "(unit => ('a * 'a lazy_sequence) option) => 'a lazy_sequence"
where
  "Lazy_Sequence f = (case f () of None => Empty | Some (x, xq) => Insert x xq)"

code_datatype Lazy_Sequence 

primrec yield :: "'a lazy_sequence => ('a * 'a lazy_sequence) option"
where
  "yield Empty = None"
| "yield (Insert x xq) = Some (x, xq)"

fun yieldn :: "code_numeral => 'a lazy_sequence => 'a list * 'a lazy_sequence"
where
  "yieldn i S = (if i = 0 then ([], S) else
    case yield S of
      None => ([], S)
    | Some (x, S') => let
       (xs, S'') = yieldn (i - 1) S'
      in (x # xs, S''))"

lemma [simp]: "yield xq = Some (x, xq') ==> size xq' < size xq"
by (cases xq) auto

lemma yield_Seq [code]:
  "yield (Lazy_Sequence f) = f ()"
unfolding Lazy_Sequence_def by (cases "f ()") auto

lemma Seq_yield:
  "Lazy_Sequence (%u. yield f) = f"
unfolding Lazy_Sequence_def by (cases f) auto

lemma lazy_sequence_size_code [code]:
  "lazy_sequence_size s xq = (case yield xq of None => 0 | Some (x, xq') => s x + lazy_sequence_size s xq' + 1)"
by (cases xq) auto

lemma size_code [code]:
  "size xq = (case yield xq of None => 0 | Some (x, xq') => size xq' + 1)"
by (cases xq) auto

lemma [code]: "eq_class.eq xq yq = (case (yield xq, yield yq) of
  (None, None) => True | (Some (x, xq'), Some (y, yq')) => (HOL.eq x y) \<and> (eq_class.eq xq yq) | _ => False)"
apply (cases xq) apply (cases yq) apply (auto simp add: eq_class.eq_equals) 
apply (cases yq) apply (auto simp add: eq_class.eq_equals) done

lemma seq_case [code]:
  "lazy_sequence_case f g xq = (case (yield xq) of None => f | Some (x, xq') => g x xq')"
by (cases xq) auto

lemma [code]: "lazy_sequence_rec f g xq = (case (yield xq) of None => f | Some (x, xq') => g x xq' (lazy_sequence_rec f g xq'))"
by (cases xq) auto

definition empty :: "'a lazy_sequence"
where
  [code]: "empty = Lazy_Sequence (%u. None)"

definition single :: "'a => 'a lazy_sequence"
where
  [code]: "single x = Lazy_Sequence (%u. Some (x, empty))"

primrec append :: "'a lazy_sequence => 'a lazy_sequence => 'a lazy_sequence"
where
  "append Empty yq = yq"
| "append (Insert x xq) yq = Insert x (append xq yq)"

lemma [code]:
  "append xq yq = Lazy_Sequence (%u. case yield xq of
     None => yield yq
  | Some (x, xq') => Some (x, append xq' yq))"
unfolding Lazy_Sequence_def
apply (cases "xq")
apply auto
apply (cases "yq")
apply auto
done

primrec flat :: "'a lazy_sequence lazy_sequence => 'a lazy_sequence"
where
  "flat Empty = Empty"
| "flat (Insert xq xqq) = append xq (flat xqq)"
 
lemma [code]:
  "flat xqq = Lazy_Sequence (%u. case yield xqq of
    None => None
  | Some (xq, xqq') => yield (append xq (flat xqq')))"
apply (cases "xqq")
apply (auto simp add: Seq_yield)
unfolding Lazy_Sequence_def
by auto

primrec map :: "('a => 'b) => 'a lazy_sequence => 'b lazy_sequence"
where
  "map f Empty = Empty"
| "map f (Insert x xq) = Insert (f x) (map f xq)"

lemma [code]:
  "map f xq = Lazy_Sequence (%u. Option.map (%(x, xq'). (f x, map f xq')) (yield xq))"
apply (cases xq)
apply (auto simp add: Seq_yield)
unfolding Lazy_Sequence_def
apply auto
done

definition bind :: "'a lazy_sequence => ('a => 'b lazy_sequence) => 'b lazy_sequence"
where
  [code]: "bind xq f = flat (map f xq)"

definition if_seq :: "bool => unit lazy_sequence"
where
  "if_seq b = (if b then single () else empty)"

definition not_seq :: "unit lazy_sequence => unit lazy_sequence"
where
  "not_seq xq = (case yield xq of None => single () | Some ((), xq) => empty)"

subsection {* Code setup *}

ML {*
signature LAZY_SEQUENCE =
sig
  datatype 'a lazy_sequence = Lazy_Sequence of unit -> ('a * 'a lazy_sequence) option
  val yield : 'a lazy_sequence -> ('a * 'a lazy_sequence) option
  val yieldn : int -> 'a lazy_sequence -> ('a list * 'a lazy_sequence)
end;

structure Lazy_Sequence : LAZY_SEQUENCE =
struct

@{code_datatype lazy_sequence = Lazy_Sequence}

val yield = @{code yield}

val yieldn = @{code yieldn}

end;
*}

code_reserved Eval Lazy_Sequence

code_type lazy_sequence (Eval "_/ Lazy'_Sequence.lazy'_sequence")

code_const Lazy_Sequence (Eval "Lazy'_Sequence.Lazy'_Sequence")

hide (open) type lazy_sequence
hide (open) const Empty Insert Lazy_Sequence yield yieldn empty single append flat map bind if_seq not_seq
hide fact yield.simps yieldn.simps empty_def single_def append.simps flat.simps map.simps bind_def if_seq_def not_seq_def

end
