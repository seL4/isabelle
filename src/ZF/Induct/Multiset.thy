(*  Title:      ZF/Induct/Multiset.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory

A definitional theory of multisets,
including a wellfoundedness proof for the multiset order.

The theory features ordinal multisets and the usual ordering.
*)

Multiset =  FoldSet + Acc +
consts
  (* Short cut for multiset space *)
  Mult :: i=>i 
translations 
  "Mult(A)" => "A -||> nat-{0}"
  
constdefs
  
  (* This is the original "restrict" from ZF.thy.
     Restricts the function f to the domain A 
     FIXME: adapt Multiset to the new "restrict". *)

  funrestrict :: "[i,i] => i"
  "funrestrict(f,A) == lam x:A. f`x"

  (* M is a multiset *)
  multiset :: i => o
  "multiset(M) == EX A. M : A -> nat-{0} & Finite(A)"

  mset_of :: "i=>i"
  "mset_of(M) == domain(M)"

  munion    :: "[i, i] => i" (infixl "+#" 65)
  "M +# N == lam x:mset_of(M) Un mset_of(N).
     if x:mset_of(M) Int mset_of(N) then  (M`x) #+ (N`x)
     else (if x:mset_of(M) then M`x else N`x)"

  (*convert a function to a multiset by eliminating 0*)
  normalize :: i => i   
  "normalize(f) ==
       if (EX A. f : A -> nat & Finite(A)) then
            funrestrict(f, {x:mset_of(f). 0 < f`x})
       else 0"

  mdiff  :: "[i, i] => i" (infixl "-#" 65)
  "M -# N ==  normalize(lam x:mset_of(M).
			if x:mset_of(N) then M`x #- N`x else M`x)"

  (* set of elements of a multiset *)
  msingle :: "i => i"    ("{#_#}")
  "{#a#} == {<a, 1>}"
  
  MCollect :: [i, i=>o] => i (*comprehension*)
  "MCollect(M, P) == funrestrict(M, {x:mset_of(M). P(x)})"

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
     {<M, N> : Mult(A)*Mult(A).
      EX a:A. EX M0:Mult(A). EX K:Mult(A).
      N=M0 +# {#a#} & M=M0 +# K & (ALL b:mset_of(K). <b,a>:r)}"
  
  multirel :: "[i, i] => i"
  "multirel(A, r) == multirel1(A, r)^+" 		    

  (* ordinal multiset orderings *)
  
  omultiset :: i => o
  "omultiset(M) == EX i. Ord(i) & M:Mult(field(Memrel(i)))"
  
  mless :: [i, i] => o (infixl "<#" 50)
  "M <# N ==  EX i. Ord(i) & <M, N>:multirel(field(Memrel(i)), Memrel(i))"

  mle  :: [i, i] => o  (infixl "<#=" 50)
  "M <#= N == (omultiset(M) & M = N) | M <# N"
  
end
