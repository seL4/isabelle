(*  Title:      ZF/Induct/Multiset.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory

A definitional theory of multisets,
including a wellfoundedness proof for the multiset order.

The theory features ordinal multisets and the usual ordering.
*)

Multiset =  FoldSet + Acc +

constdefs
  (* M is a multiset *)
  multiset :: i => o
  "multiset(M) == EX A. M:A->nat-{0} & Finite(A)"

  mset_of :: "i=>i"
  "mset_of(M) == domain(M)"

  (* M is a multiset over A *)
  multiset_on :: [i,i]=>o  ("multiset[_]'(_')")
  "multiset[A](M) == multiset(M) & mset_of(M) <= A"

  munion    :: "[i, i] => i" (infixl "+#" 65)
  "M +# N == lam x:mset_of(M) Un mset_of(N).
     if x:mset_of(M) Int mset_of(N) then  (M`x) #+ (N`x)
     else (if x:mset_of(M) then M`x else N`x)"

  (* eliminating zeros from a function *)
  normalize :: i => i   
  "normalize(M) == restrict(M, {x:mset_of(M). 0<M`x})"

  mdiff  :: "[i, i] => i" (infixl "-#" 65)
  "M -# N ==  normalize(lam x:mset_of(M).
			if x:mset_of(N) then M`x #- N`x else M`x)"

  (* set of elements of a multiset *)
  msingle :: "i => i"    ("{#_#}")
  "{#a#} == {<a, 1>}"
  
  MCollect :: [i, i=>o] => i (*comprehension*)
  "MCollect(M, P) == restrict(M, {x:mset_of(M). P(x)})"

  (* Counts the number of occurences of an element in a multiset *)
  mcount :: [i, i] => i
  "mcount(M, a) == if a:mset_of(M) then  M`a else 0"
  
  msize :: i => i
  "msize(M) == setsum(%a. $# mcount(M,a), mset_of(M))"  

syntax
  melem :: "[i,i] => o"    ("(_/ :# _)" [50, 51] 50)  
  "@MColl" :: "[pttrn, i, o] => i" ("(1{# _ : _./ _#})")

translations
  "a :# M" == "a:mset_of(M)"
  "{#x:M. P#}" == "MCollect(M, %x. P)"

  (* multiset orderings *)
  
constdefs
   (* multirel1 has to be a set (not a predicate) so that we can form
      its transitive closure and reason about wf(.) and acc(.) *)
  
  multirel1 :: "[i,i]=>i"
  "multirel1(A, r) ==
     {<M, N> : (A-||>nat-{0})*(A-||>nat-{0}).
      EX a:A. EX M0:A-||>nat-{0}. EX K:A-||>nat-{0}.
	N=M0 +# {#a#} & M=M0 +# K & (ALL b:mset_of(K). <b,a>:r)}"
  
  multirel :: "[i, i] => i"
  "multirel(A, r) == multirel1(A, r)^+" 		    

  (* ordinal multisets orderings *)
  
  omultiset :: i => o
  "omultiset(M) == EX i. Ord(i) & multiset[field(Memrel(i))](M)"
  
  mless :: [i, i] => o (infixl "<#" 50)
  "M <# N ==  EX i. Ord(i) & <M, N>:multirel(field(Memrel(i)), Memrel(i))"

  mle  :: [i, i] => o  (infixl "<#=" 50)
  "M <#= N == (omultiset(M) & M = N) | M <# N"
  
end
