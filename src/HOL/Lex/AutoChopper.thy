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

AutoChopper = Prefix + DA + Chopper +

constdefs
 is_auto_chopper :: (('a,'s)da => 'a chopper) => bool
"is_auto_chopper(chopperf) ==
    !A. is_longest_prefix_chopper(accepts A)(chopperf A)"

consts
  acc :: "['a list, 's, 'a list, 'a list, 'a list list*'a list, ('a,'s)da]
          => 'a list list * 'a list"
primrec acc List.list
  "acc [] st ys zs chopsr A =
              (if ys=[] then chopsr else (ys#fst(chopsr),snd(chopsr)))" 
  "acc(x#xs) s ys zs chopsr A =
            (let t = next A x s
             in if fin A t
                then acc xs t (zs@[x]) (zs@[x])
                         (acc xs (start A) [] [] ([],xs) A) A
                else acc xs t ys (zs@[x]) chopsr A)"

constdefs
 auto_chopper :: ('a,'s)da => 'a chopper
"auto_chopper A xs == acc xs (start A) [] [] ([],xs) A"

(* acc_prefix is an auxiliary notion for the proof *)
constdefs
 acc_prefix :: ('a,'s)da => 'a list => 's => bool
"acc_prefix A xs s == ? us. us <= xs & us~=[] & fin A (delta A us s)"

end
