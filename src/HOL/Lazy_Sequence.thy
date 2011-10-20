
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

lemma [code]: "HOL.equal xq yq = (case (yield xq, yield yq) of
  (None, None) => True | (Some (x, xq'), Some (y, yq')) => (HOL.equal x y) \<and> (HOL.equal xq yq) | _ => False)"
apply (cases xq) apply (cases yq) apply (auto simp add: equal_eq) 
apply (cases yq) apply (auto simp add: equal_eq) done

lemma [code nbe]:
  "HOL.equal (x :: 'a lazy_sequence) x \<longleftrightarrow> True"
  by (fact equal_refl)

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

function iterate_upto :: "(code_numeral => 'a) => code_numeral => code_numeral => 'a Lazy_Sequence.lazy_sequence"
where
  "iterate_upto f n m = Lazy_Sequence.Lazy_Sequence (%u. if n > m then None else Some (f n, iterate_upto f (n + 1) m))"
by pat_completeness auto

termination by (relation "measure (%(f, n, m). Code_Numeral.nat_of (m + 1 - n))") auto

definition not_seq :: "unit lazy_sequence => unit lazy_sequence"
where
  "not_seq xq = (case yield xq of None => single () | Some ((), xq) => empty)"

subsection {* Code setup *}

fun anamorph :: "('a \<Rightarrow> ('b \<times> 'a) option) \<Rightarrow> code_numeral \<Rightarrow> 'a \<Rightarrow> 'b list \<times> 'a" where
  "anamorph f k x = (if k = 0 then ([], x)
    else case f x of None \<Rightarrow> ([], x) | Some (v, y) \<Rightarrow>
      let (vs, z) = anamorph f (k - 1) y
    in (v # vs, z))"

definition yieldn :: "code_numeral \<Rightarrow> 'a lazy_sequence \<Rightarrow> 'a list \<times> 'a lazy_sequence" where
  "yieldn = anamorph yield"

code_reflect Lazy_Sequence
  datatypes lazy_sequence = Lazy_Sequence
  functions map yield yieldn

subsection {* Generator Sequences *}


subsubsection {* General lazy sequence operation *}

definition product :: "'a Lazy_Sequence.lazy_sequence \<Rightarrow> 'b Lazy_Sequence.lazy_sequence \<Rightarrow> ('a * 'b) Lazy_Sequence.lazy_sequence"
where
  "product s1 s2 = Lazy_Sequence.bind s1 (%a. Lazy_Sequence.bind s2 (%b. Lazy_Sequence.single (a, b)))"


subsubsection {* Small lazy typeclasses *}

class small_lazy =
  fixes small_lazy :: "code_numeral \<Rightarrow> 'a Lazy_Sequence.lazy_sequence"

instantiation unit :: small_lazy
begin

definition "small_lazy d = Lazy_Sequence.single ()"

instance ..

end

instantiation int :: small_lazy
begin

text {* maybe optimise this expression -> append (single x) xs == cons x xs 
Performance difference? *}

function small_lazy' :: "int => int => int Lazy_Sequence.lazy_sequence"
where "small_lazy' d i = (if d < i then Lazy_Sequence.empty else
  Lazy_Sequence.append (Lazy_Sequence.single i) (small_lazy' d (i + 1)))"
by pat_completeness auto

termination 
  by (relation "measure (%(d, i). nat (d + 1 - i))") auto

definition "small_lazy d = small_lazy' (Code_Numeral.int_of d) (- (Code_Numeral.int_of d))"

instance ..

end

instantiation prod :: (small_lazy, small_lazy) small_lazy
begin

definition
  "small_lazy d = product (small_lazy d) (small_lazy d)"

instance ..

end

instantiation list :: (small_lazy) small_lazy
begin

fun small_lazy_list :: "code_numeral => 'a list Lazy_Sequence.lazy_sequence"
where
  "small_lazy_list d = Lazy_Sequence.append (Lazy_Sequence.single []) (if d > 0 then Lazy_Sequence.bind (product (small_lazy (d - 1)) (small_lazy (d - 1))) (%(x, xs). Lazy_Sequence.single (x # xs)) else Lazy_Sequence.empty)"

instance ..

end

subsection {* With Hit Bound Value *}
text {* assuming in negative context *}

type_synonym 'a hit_bound_lazy_sequence = "'a option lazy_sequence"

definition hit_bound :: "'a hit_bound_lazy_sequence"
where
  [code]: "hit_bound = Lazy_Sequence (%u. Some (None, empty))"

definition hb_single :: "'a => 'a hit_bound_lazy_sequence"
where
  [code]: "hb_single x = Lazy_Sequence (%u. Some (Some x, empty))"

primrec hb_flat :: "'a hit_bound_lazy_sequence hit_bound_lazy_sequence => 'a hit_bound_lazy_sequence"
where
  "hb_flat Empty = Empty"
| "hb_flat (Insert xq xqq) = append (case xq of None => hit_bound | Some xq => xq) (hb_flat xqq)"

lemma [code]:
  "hb_flat xqq = Lazy_Sequence (%u. case yield xqq of
    None => None
  | Some (xq, xqq') => yield (append (case xq of None => hit_bound | Some xq => xq) (hb_flat xqq')))"
apply (cases "xqq")
apply (auto simp add: Seq_yield)
unfolding Lazy_Sequence_def
by auto

primrec hb_map :: "('a => 'b) => 'a hit_bound_lazy_sequence => 'b hit_bound_lazy_sequence"
where
  "hb_map f Empty = Empty"
| "hb_map f (Insert x xq) = Insert (Option.map f x) (hb_map f xq)"

lemma [code]:
  "hb_map f xq = Lazy_Sequence (%u. Option.map (%(x, xq'). (Option.map f x, hb_map f xq')) (yield xq))"
apply (cases xq)
apply (auto simp add: Seq_yield)
unfolding Lazy_Sequence_def
apply auto
done

definition hb_bind :: "'a hit_bound_lazy_sequence => ('a => 'b hit_bound_lazy_sequence) => 'b hit_bound_lazy_sequence"
where
  [code]: "hb_bind xq f = hb_flat (hb_map f xq)"

definition hb_if_seq :: "bool => unit hit_bound_lazy_sequence"
where
  "hb_if_seq b = (if b then hb_single () else empty)"

definition hb_not_seq :: "unit hit_bound_lazy_sequence => unit lazy_sequence"
where
  "hb_not_seq xq = (case yield xq of None => single () | Some (x, xq) => empty)"

hide_type (open) lazy_sequence
hide_const (open) Empty Insert Lazy_Sequence yield empty single append flat map bind if_seq
  iterate_upto not_seq product
  
hide_fact yield.simps empty_def single_def append.simps flat.simps map.simps bind_def
  iterate_upto.simps product_def if_seq_def not_seq_def

end
