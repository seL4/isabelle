(*  Title:      HOL/Lex/AutoChopper.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TUM

auto_chopper turns an automaton into a chopper. Tricky, because primrec.

is_auto_chopper requires its argument to produce longest_prefix_choppers
wrt the language accepted by the automaton.

Main result: auto_chopper satisfies the is_auto_chopper specification.

WARNING: auto_chopper is exponential(?)
if the recursive calls in the penultimate argument are evaluated eagerly.

A more efficient version is defined in AutoChopper1.
*)

AutoChopper = Auto + Chopper +

consts
  is_auto_chopper :: (('a,'b)auto => 'a chopper) => bool
  auto_chopper :: ('a,'b)auto => 'a chopper
  acc :: "['a list, 'b, 'a list, 'a list, 'a list list*'a list, ('a,'b)auto]
          => 'a list list * 'a list"

defs
  is_auto_chopper_def "is_auto_chopper(chopperf) ==
                       !A. is_longest_prefix_chopper(accepts A)(chopperf A)"

  auto_chopper_def "auto_chopper A xs == acc xs (start A) [] [] ([],xs) A"

primrec acc List.list
  "acc [] st ys zs chopsr A =
              (if ys=[] then chopsr else (ys#fst(chopsr),snd(chopsr)))" 
  "acc(x#xs) st ys zs chopsr A =
            (let s0 = start(A); nxt = next(A); fin = fin(A)
             in if fin(nxt st x)
                then acc xs (nxt st x) (zs@[x]) (zs@[x])
                         (acc xs s0 [] [] ([],xs) A) A
                else acc xs (nxt st x) ys (zs@[x]) chopsr A)"

end
