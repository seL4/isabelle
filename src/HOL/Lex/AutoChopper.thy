(*  Title: 	HOL/Lex/AutoChopper.thy
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1995 TUM

auto_chopper turns an automaton into a chopper. Tricky, because primrec.

is_auto_chopper requires its argument to produce longest_prefix_choppers
wrt the language accepted by the automaton.

Main result: auto_chopper satisfies the is_auto_chopper specification.

WARNING: auto_chopper is exponential(?)
if the recursive calls in the penultimate argument are evaluated eagerly.
*)

AutoChopper = Auto + Chopper +

consts
  is_auto_chopper :: "(('a,'b)auto => 'a chopper) => bool"
  auto_chopper :: "('a,'b)auto => 'a chopper"
  acc :: "['a list, 'b, 'a list, 'a list, 'a list list*'a list, ('a,'b)auto]
	  => 'a list list * 'a list"

defs
  is_auto_chopper_def "is_auto_chopper(chopperf) ==
		       !A. is_longest_prefix_chopper(accepts A)(chopperf A)"

  auto_chopper_def "auto_chopper A xs == acc xs (start A) [] [] ([],xs) A"

primrec acc List.list
  acc_Nil  "acc [] st ys zs chopsr A =
	      (if ys=[] then chopsr else (ys#fst(chopsr),snd(chopsr)))" 
  acc_Cons "acc(x#xs) st ys zs chopsr A =
	    (let s0 = start(A); nxt = next(A); fin = fin(A)
             in if fin(nxt st x)
                then acc xs (nxt st x) (zs@[x]) (zs@[x])
                         (acc xs s0 [] [] ([],xs) A) A
                else acc xs (nxt st x) ys (zs@[x]) chopsr A)"

end

(* The following definition of acc should also work:
consts
  acc1 :: [('a,'b)auto, 'a list, 'b, 'a list list, 'a list, 'a list]
          => 'a list list * 'a list

acc1 A [] s xss zs xs =
  (if xs=[] then (xss, zs)
   else acc1 A zs (start A) (xss @ [xs]) [] [])
acc1 A (y#ys) s xss zs rec =
  let s' = next A s;
      zs' = (if fin A s' then [] else zs@[y])
      xs' = (if fin A s' then xs@zs@[y] else xs)
  in acc1 A ys s' xss zs' xs'

Advantage: does not need lazy evaluation for reasonable (quadratic)
performance.

Disadavantage: not primrec.
  
Termination measure:
  size(A,ys,s,xss,zs,rec) = (|xs| + |ys| + |zs|, |ys|)

Termination proof: the first clause reduces the first component by |xs|,
the second clause leaves the first component alone but reduces the second by 1.

Claim: acc1 A xs s [] [] [] = acc xs s [] [] ([],xs) A
Generalization?
*)
