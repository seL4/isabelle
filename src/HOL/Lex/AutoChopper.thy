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
  acc :: [('a,'b)auto, 'a list, 'b, 'a list list, 'a list, 'a list maybe]
         => 'a list list * 'a list

acc A [] s xss zs rec =
  (case rec of
     Yes(xs) => acc A zs (start A) (xss @ [xs]) [] No
   | No => (xss, zs))
acc A (y#ys) s xss zs rec =
  let s' = next A s;
      zs' = (if fin A s' then [] else zs@[y])
      rec' = (if fin A s'
              then Yes(case rec of
                         Yes(xs) => xs@zs@[y]
                       | No => zs@[y])
              else rec)
  in acc A ys s' xss zs' rec'

Advantage: does not need lazy evaluation for reasonable (quadartic)
performance.

Termination measure:
  size(A,ys,s,xss,zs,rec) =
    case rec of
      No => |ys|^2 + |ys|
      Yes => (|ys|+|zs|)^2 + 2|ys| + |zs| + 1

Termination proof:
  
  1. size(,[],,,zs,Yes(xs)) = z^2 + z + 1 > z^2 + z = size(,zs,,,[],No)

  2. size(,y#ys,,,zs,No) = (y+1)^2 + y+1 = y^2 + 3y + 2
  
  2.1. fin A s' --> zs' = [] & rec' = Yes
       size(,y#ys,,,zs,No) > y^2 + 2y + 1 = size(,ys,,,[],Yes)
  
  2.2. not(fin A s') --> rec' = rec = No
       size(,y#ys,,,zs,No) > y^2 + y = size(,ys,,,,No)

  3. size(,y#ys,,,zs,Yes) = (y+z+1)^2 + 2y + z + 3

  3.1 fin A s' --> zs' = [] & rec' = Yes
      size(,y#ys,,,zs,Yes) > y^2 + 2y + 1 = size(,ys,,,[],Yes)
  3.2 not(fin A s') --> ze' = zs@[y] & rec' = rec = Yes
      size(,y#ys,,,zs,Yes) > (y+z+1)^2 + 2y + z + 2 = size(,ys,,,zs@[y],Yes)

where y := |ys| and z := |zs|
*)
