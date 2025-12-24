(* Author: Lukas Bulwahn, TU Muenchen *)

section \<open>Lazy sequences\<close>

theory Lazy_Sequence
imports Predicate
begin

subsection \<open>Type of lazy sequences\<close>

datatype (plugins only: code extraction) (dead 'a) lazy_sequence =
  lazy_sequence_of_list "'a list"

primrec list_of_lazy_sequence :: "'a lazy_sequence \<Rightarrow> 'a list"
where
  "list_of_lazy_sequence (lazy_sequence_of_list xs) = xs"

lemma lazy_sequence_of_list_of_lazy_sequence [simp]:
  "lazy_sequence_of_list (list_of_lazy_sequence xq) = xq"
  by (cases xq) simp_all

lemma lazy_sequence_eqI:
  "list_of_lazy_sequence xq = list_of_lazy_sequence yq \<Longrightarrow> xq = yq"
  by (cases xq, cases yq) simp

lemma lazy_sequence_eq_iff:
  "xq = yq \<longleftrightarrow> list_of_lazy_sequence xq = list_of_lazy_sequence yq"
  by (auto intro: lazy_sequence_eqI)

lemma case_lazy_sequence [simp]:
  "case_lazy_sequence f xq = f (list_of_lazy_sequence xq)"
  by (cases xq) auto

lemma rec_lazy_sequence [simp]:
  "rec_lazy_sequence f xq = f (list_of_lazy_sequence xq)"
  by (cases xq) auto

definition Lazy_Sequence :: "(unit \<Rightarrow> ('a \<times> 'a lazy_sequence) option) \<Rightarrow> 'a lazy_sequence"
where
  "Lazy_Sequence f = lazy_sequence_of_list (case f () of
    None \<Rightarrow> []
  | Some (x, xq) \<Rightarrow> x # list_of_lazy_sequence xq)"

code_datatype Lazy_Sequence

declare [[code drop: list_of_lazy_sequence rec_lazy_sequence case_lazy_sequence]]

lemma list_of_Lazy_Sequence [simp]:
  "list_of_lazy_sequence (Lazy_Sequence f) = (case f () of
    None \<Rightarrow> []
  | Some (x, xq) \<Rightarrow> x # list_of_lazy_sequence xq)"
  by (simp add: Lazy_Sequence_def)

definition yield :: "'a lazy_sequence \<Rightarrow> ('a \<times> 'a lazy_sequence) option"
where
  "yield xq = (case list_of_lazy_sequence xq of
    [] \<Rightarrow> None
  | x # xs \<Rightarrow> Some (x, lazy_sequence_of_list xs))" 

lemma yield_Seq [simp, code]:
  "yield (Lazy_Sequence f) = f ()"
  by (cases "f ()") (simp_all add: yield_def split_def)

lemma case_yield_eq [simp]: "case_option g h (yield xq) =
  case_list g (\<lambda>x. curry h x \<circ> lazy_sequence_of_list) (list_of_lazy_sequence xq)"
  by (cases "list_of_lazy_sequence xq") (simp_all add: yield_def)

lemma equal_lazy_sequence_code [code]:
  "HOL.equal xq yq = (case (yield xq, yield yq) of
    (None, None) \<Rightarrow> True
  | (Some (x, xq'), Some (y, yq')) \<Rightarrow> HOL.equal x y \<and> HOL.equal xq yq
  | _ \<Rightarrow> False)"
  by (simp_all add: lazy_sequence_eq_iff equal_eq split: list.splits)

lemma [code nbe]:
  "HOL.equal (x :: 'a lazy_sequence) x \<longleftrightarrow> True"
  by (fact equal_refl)

definition empty :: "'a lazy_sequence"
where
  "empty = lazy_sequence_of_list []"

lemma list_of_lazy_sequence_empty [simp]:
  "list_of_lazy_sequence empty = []"
  by (simp add: empty_def)

lemma empty_code [code]:
  "empty = Lazy_Sequence (\<lambda>_. None)"
  by (simp add: lazy_sequence_eq_iff)

definition single :: "'a \<Rightarrow> 'a lazy_sequence"
where
  "single x = lazy_sequence_of_list [x]"

lemma list_of_lazy_sequence_single [simp]:
  "list_of_lazy_sequence (single x) = [x]"
  by (simp add: single_def)

lemma single_code [code]:
  "single x = Lazy_Sequence (\<lambda>_. Some (x, empty))"
  by (simp add: lazy_sequence_eq_iff)

definition append :: "'a lazy_sequence \<Rightarrow> 'a lazy_sequence \<Rightarrow> 'a lazy_sequence"
where
  "append xq yq = lazy_sequence_of_list (list_of_lazy_sequence xq @ list_of_lazy_sequence yq)"

lemma list_of_lazy_sequence_append [simp]:
  "list_of_lazy_sequence (append xq yq) = list_of_lazy_sequence xq @ list_of_lazy_sequence yq"
  by (simp add: append_def)

lemma append_code [code]:
  "append xq yq = Lazy_Sequence (\<lambda>_. case yield xq of
    None \<Rightarrow> yield yq
  | Some (x, xq') \<Rightarrow> Some (x, append xq' yq))"
  by (simp_all add: lazy_sequence_eq_iff split: list.splits)

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a lazy_sequence \<Rightarrow> 'b lazy_sequence"
where
  "map f xq = lazy_sequence_of_list (List.map f (list_of_lazy_sequence xq))"

lemma list_of_lazy_sequence_map [simp]:
  "list_of_lazy_sequence (map f xq) = List.map f (list_of_lazy_sequence xq)"
  by (simp add: map_def)

lemma map_code [code]:
  "map f xq =
    Lazy_Sequence (\<lambda>_. map_option (\<lambda>(x, xq'). (f x, map f xq')) (yield xq))"
  by (simp_all add: lazy_sequence_eq_iff split: list.splits)

definition flat :: "'a lazy_sequence lazy_sequence \<Rightarrow> 'a lazy_sequence"
where
  "flat xqq = lazy_sequence_of_list (concat (List.map list_of_lazy_sequence (list_of_lazy_sequence xqq)))"

lemma list_of_lazy_sequence_flat [simp]:
  "list_of_lazy_sequence (flat xqq) = concat (List.map list_of_lazy_sequence (list_of_lazy_sequence xqq))"
  by (simp add: flat_def)

lemma flat_code [code]:
  "flat xqq = Lazy_Sequence (\<lambda>_. case yield xqq of
    None \<Rightarrow> None
  | Some (xq, xqq') \<Rightarrow> yield (append xq (flat xqq')))"
  by (simp add: lazy_sequence_eq_iff split: list.splits)

definition bind :: "'a lazy_sequence \<Rightarrow> ('a \<Rightarrow> 'b lazy_sequence) \<Rightarrow> 'b lazy_sequence"
where
  "bind xq f = flat (map f xq)"

definition if_seq :: "bool \<Rightarrow> unit lazy_sequence"
where
  "if_seq b = (if b then single () else empty)"

definition those :: "'a option lazy_sequence \<Rightarrow> 'a lazy_sequence option"
where
  "those xq = map_option lazy_sequence_of_list (List.those (list_of_lazy_sequence xq))"
  
function iterate_upto :: "(natural \<Rightarrow> 'a) \<Rightarrow> natural \<Rightarrow> natural \<Rightarrow> 'a lazy_sequence"
where
  "iterate_upto f n m =
    Lazy_Sequence (\<lambda>_. if n > m then None else Some (f n, iterate_upto f (n + 1) m))"
  by pat_completeness auto

termination by (relation "measure (\<lambda>(f, n, m). nat_of_natural (m + 1 - n))")
  (auto simp add: less_natural_def)

definition not_seq :: "unit lazy_sequence \<Rightarrow> unit lazy_sequence"
where
  "not_seq xq = (case yield xq of
    None \<Rightarrow> single ()
  | Some ((), xq) \<Rightarrow> empty)"

  
subsection \<open>Code setup\<close>

code_reflect Lazy_Sequence
  datatypes lazy_sequence = Lazy_Sequence

ML \<open>
signature LAZY_SEQUENCE =
sig
  datatype 'a lazy_sequence = Lazy_Sequence of (unit -> ('a * 'a Lazy_Sequence.lazy_sequence) option)
  val map: ('a -> 'b) -> 'a lazy_sequence -> 'b lazy_sequence
  val yield: 'a lazy_sequence -> ('a * 'a lazy_sequence) option
  val yieldn: int -> 'a lazy_sequence -> 'a list * 'a lazy_sequence
end;

structure Lazy_Sequence : LAZY_SEQUENCE =
struct

datatype lazy_sequence = datatype Lazy_Sequence.lazy_sequence;

fun map f = @{code Lazy_Sequence.map} f;

fun yield P = @{code Lazy_Sequence.yield} P;

fun yieldn k = Predicate.anamorph yield k;

end;
\<close>


subsection \<open>Generator Sequences\<close>

subsubsection \<open>General lazy sequence operation\<close>

definition product :: "'a lazy_sequence \<Rightarrow> 'b lazy_sequence \<Rightarrow> ('a \<times> 'b) lazy_sequence"
where
  "product s1 s2 = bind s1 (\<lambda>a. bind s2 (\<lambda>b. single (a, b)))"


subsubsection \<open>Small lazy typeclasses\<close>

class small_lazy =
  fixes small_lazy :: "natural \<Rightarrow> 'a lazy_sequence"

instantiation unit :: small_lazy
begin

definition "small_lazy d = single ()"

instance ..

end

instantiation int :: small_lazy
begin

text \<open>maybe optimise this expression -> append (single x) xs == cons x xs 
Performance difference?\<close>

function small_lazy' :: "int \<Rightarrow> int \<Rightarrow> int lazy_sequence"
where
  "small_lazy' d i = (if d < i then empty
    else append (single i) (small_lazy' d (i + 1)))"
    by pat_completeness auto

termination 
  by (relation "measure (%(d, i). nat (d + 1 - i))") auto

definition
  "small_lazy d = small_lazy' (int (nat_of_natural d)) (- (int (nat_of_natural d)))"

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

fun small_lazy_list :: "natural \<Rightarrow> 'a list lazy_sequence"
where
  "small_lazy_list d = append (single [])
    (if d > 0 then bind (product (small_lazy (d - 1))
      (small_lazy (d - 1))) (\<lambda>(x, xs). single (x # xs)) else empty)"

instance ..

end

subsection \<open>With Hit Bound Value\<close>
text \<open>assuming in negative context\<close>

type_synonym 'a hit_bound_lazy_sequence = "'a option lazy_sequence"

definition hit_bound :: "'a hit_bound_lazy_sequence"
where
  "hit_bound = Lazy_Sequence (\<lambda>_. Some (None, empty))"

lemma list_of_lazy_sequence_hit_bound [simp]:
  "list_of_lazy_sequence hit_bound = [None]"
  by (simp add: hit_bound_def)
  
definition hb_single :: "'a \<Rightarrow> 'a hit_bound_lazy_sequence"
where
  "hb_single x = Lazy_Sequence (\<lambda>_. Some (Some x, empty))"

definition hb_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a hit_bound_lazy_sequence \<Rightarrow> 'b hit_bound_lazy_sequence"
where
  "hb_map f xq = map (map_option f) xq"

lemma hb_map_code [code]:
  "hb_map f xq =
    Lazy_Sequence (\<lambda>_. map_option (\<lambda>(x, xq'). (map_option f x, hb_map f xq')) (yield xq))"
  using map_code [of "map_option f" xq] by (simp add: hb_map_def)

definition hb_flat :: "'a hit_bound_lazy_sequence hit_bound_lazy_sequence \<Rightarrow> 'a hit_bound_lazy_sequence"
where
  "hb_flat xqq = lazy_sequence_of_list (concat
    (List.map ((\<lambda>x. case x of None \<Rightarrow> [None] | Some xs \<Rightarrow> xs) \<circ> map_option list_of_lazy_sequence) (list_of_lazy_sequence xqq)))"

lemma list_of_lazy_sequence_hb_flat [simp]:
  "list_of_lazy_sequence (hb_flat xqq) =
    concat (List.map ((\<lambda>x. case x of None \<Rightarrow> [None] | Some xs \<Rightarrow> xs) \<circ> map_option list_of_lazy_sequence) (list_of_lazy_sequence xqq))"
  by (simp add: hb_flat_def)

lemma hb_flat_code [code]:
  "hb_flat xqq = Lazy_Sequence (\<lambda>_. case yield xqq of
    None \<Rightarrow> None
  | Some (xq, xqq') \<Rightarrow> yield
     (append (case xq of None \<Rightarrow> hit_bound | Some xq \<Rightarrow> xq) (hb_flat xqq')))"
  by (simp add: lazy_sequence_eq_iff split: list.splits option.splits)

definition hb_bind :: "'a hit_bound_lazy_sequence \<Rightarrow> ('a \<Rightarrow> 'b hit_bound_lazy_sequence) \<Rightarrow> 'b hit_bound_lazy_sequence"
where
  "hb_bind xq f = hb_flat (hb_map f xq)"

definition hb_if_seq :: "bool \<Rightarrow> unit hit_bound_lazy_sequence"
where
  "hb_if_seq b = (if b then hb_single () else empty)"

definition hb_not_seq :: "unit hit_bound_lazy_sequence \<Rightarrow> unit lazy_sequence"
where
  "hb_not_seq xq = (case yield xq of
    None \<Rightarrow> single ()
  | Some (x, xq) \<Rightarrow> empty)"

hide_const (open) yield empty single append flat map bind
  if_seq those iterate_upto not_seq product

hide_fact (open) yield_def empty_def single_def append_def flat_def map_def bind_def
  if_seq_def those_def not_seq_def product_def 

end
