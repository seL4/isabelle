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

But both versions are far too specific. Better development in Scanner.thy and
its antecedents.
*)

AutoChopper = Prefix + DA + Chopper +

constdefs
 is_auto_chopper :: (('a,'s)da => 'a chopper) => bool
"is_auto_chopper(chopperf) ==
    !A. is_longest_prefix_chopper(accepts A)(chopperf A)"

consts
  acc :: "[('a,'s)da, 's, 'a list list*'a list, 'a list, 'a list, 'a list]
          => 'a list list * 'a list"
primrec acc List.list
  "acc A s r ps []     zs = (if ps=[] then r else (ps#fst(r),snd(r)))" 
  "acc A s r ps (x#xs) zs =
            (let t = next A x s
             in if fin A t
                then acc A t (acc A (start A) ([],xs) [] xs [])
                         (zs@[x]) xs (zs@[x])
                else acc A t r ps xs (zs@[x]))"

constdefs
 auto_chopper :: ('a,'s)da => 'a chopper
"auto_chopper A xs == acc A (start A) ([],xs) [] xs []"

(* acc_prefix is an auxiliary notion for the proof *)
constdefs
 acc_prefix :: ('a,'s)da => 'a list => 's => bool
"acc_prefix A xs s == ? us. us <= xs & us~=[] & fin A (delta A us s)"

end
