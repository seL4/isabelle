(*  Title:      HOL/Induct/Multiset.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

A definitional theory of multisets,
including a wellfoundedness proof for the multiset order.
use_thy"Multiset";

*)

Multiset = Multiset0 + Acc +

typedef
  'a multiset = "{f :: 'a => nat . finite{x . 0 < f x}}" (multiset_witness)

instance multiset :: (term){ord,zero,plus,minus}

consts
  "{#}"  :: 'a multiset                        ("{#}")
  single :: 'a                => 'a multiset   ("{#_#}")
  count  :: ['a multiset, 'a] => nat
  set_of :: 'a multiset => 'a set

syntax
  elem   :: ['a multiset, 'a] => bool          ("(_/ :# _)" [50, 51] 50)

translations
  "M :# a" == "0 < count M a"

defs
  count_def  "count == Rep_multiset"
  empty_def  "{#}   == Abs_multiset(%a. 0)"
  single_def "{#a#} == Abs_multiset(%b. if b=a then 1 else 0)"
  union_def  "M+N   == Abs_multiset(%a. Rep_multiset M a + Rep_multiset N a)"
  diff_def  "M-N    == Abs_multiset(%a. Rep_multiset M a - Rep_multiset N a)"
  set_of_def "set_of M == {x. M :# x}"
  size_def "size (M) == setsum (count M) (set_of M)"

constdefs
  mult1 :: "('a * 'a)set => ('a multiset * 'a multiset)set"
 "mult1(r) == {(N,M) . ? a M0 K. M = M0 + {#a#} & N = M0 + K &
                                 (!b. K :# b --> (b,a) : r)}"

  mult :: "('a * 'a)set => ('a multiset * 'a multiset)set"
 "mult(r) == (mult1 r)^+"

locale MSOrd =
  fixes
    r :: "('a * 'a)set"
    W :: "'a multiset set"

  defines
    W_def       "W == acc(mult1 r)"

defs
  mult_less_def  "M' < M  ==  (M',M) : mult {(x',x). x'<x}"
  mult_le_def    "M' <= M  ==  M'=M | M' < (M :: 'a multiset)"

end
