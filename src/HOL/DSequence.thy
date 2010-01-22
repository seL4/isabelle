
(* Author: Lukas Bulwahn, TU Muenchen *)

header {* Depth-Limited Sequences with failure element *}

theory DSequence
imports Lazy_Sequence Code_Numeral
begin

types 'a dseq = "code_numeral => bool => 'a Lazy_Sequence.lazy_sequence option"

definition empty :: "'a dseq"
where
  "empty = (%i pol. Some Lazy_Sequence.empty)"

definition single :: "'a => 'a dseq"
where
  "single x = (%i pol. Some (Lazy_Sequence.single x))"

fun eval :: "'a dseq => code_numeral => bool => 'a Lazy_Sequence.lazy_sequence option"
where
  "eval f i pol = f i pol"

definition yield :: "'a dseq => code_numeral => bool => ('a * 'a dseq) option" 
where
  "yield dseq i pol = (case eval dseq i pol of
    None => None
  | Some s => Option.map (apsnd (%r i pol. Some r)) (Lazy_Sequence.yield s))"

definition yieldn :: "code_numeral => 'a dseq => code_numeral => bool => 'a list * 'a dseq"
where
  "yieldn n dseq i pol = (case eval dseq i pol of
    None => ([], %i pol. None)
  | Some s => let (xs, s') = Lazy_Sequence.yieldn n s in (xs, %i pol. Some s))"

fun map_seq :: "('a => 'b dseq) => 'a Lazy_Sequence.lazy_sequence => 'b dseq"
where
  "map_seq f xq i pol = (case Lazy_Sequence.yield xq of
    None => Some Lazy_Sequence.empty
  | Some (x, xq') => (case eval (f x) i pol of
      None => None
    | Some yq => (case map_seq f xq' i pol of
        None => None
      | Some zq => Some (Lazy_Sequence.append yq zq))))"

definition bind :: "'a dseq => ('a => 'b dseq) => 'b dseq"
where
  "bind x f = (%i pol. 
     if i = 0 then
       (if pol then Some Lazy_Sequence.empty else None)
     else
       (case x (i - 1) pol of
         None => None
       | Some xq => map_seq f xq i pol))"

definition union :: "'a dseq => 'a dseq => 'a dseq"
where
  "union x y = (%i pol. case (x i pol, y i pol) of
      (Some xq, Some yq) => Some (Lazy_Sequence.append xq yq)
    | _ => None)"

definition if_seq :: "bool => unit dseq"
where
  "if_seq b = (if b then single () else empty)"

definition not_seq :: "unit dseq => unit dseq"
where
  "not_seq x = (%i pol. case x i (\<not>pol) of
    None => Some Lazy_Sequence.empty
  | Some xq => (case Lazy_Sequence.yield xq of
      None => Some (Lazy_Sequence.single ())
    | Some _ => Some (Lazy_Sequence.empty)))"

definition map :: "('a => 'b) => 'a dseq => 'b dseq"
where
  "map f g = (%i pol. case g i pol of
     None => None
   | Some xq => Some (Lazy_Sequence.map f xq))"

ML {*
signature DSEQUENCE =
sig
  type 'a dseq = int -> bool -> 'a Lazy_Sequence.lazy_sequence option
  val yield : 'a dseq -> int -> bool -> ('a * 'a dseq) option
  val yieldn : int -> 'a dseq -> int -> bool -> 'a list * 'a dseq
  val map : ('a -> 'b) -> 'a dseq -> 'b dseq
end;

structure DSequence : DSEQUENCE =
struct

type 'a dseq = int -> bool -> 'a Lazy_Sequence.lazy_sequence option

val yieldn = @{code yieldn}
val yield = @{code yield}
val map = @{code map}

end;
*}

code_reserved Eval DSequence
(*
hide type Sequence.seq

hide const Sequence.Seq Sequence.yield Sequence.yieldn Sequence.empty Sequence.single
  Sequence.append Sequence.flat Sequence.map Sequence.bind Sequence.ifpred Sequence.not_seq
*)
hide (open) const empty single eval map_seq bind union if_seq not_seq map
hide (open) fact empty_def single_def eval.simps map_seq.simps bind_def union_def
  if_seq_def not_seq_def map_def

end
