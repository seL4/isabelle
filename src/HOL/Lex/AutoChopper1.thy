(*  Title:      HOL/Lex/AutoChopper1.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TUM

This is a version of theory AutoChopper base on a non-primrec definition of
`acc'. Advantage: does not need lazy evaluation for reasonable (quadratic?)
performance.

Verification:
1. Via AutoChopper.acc using
   Claim: acc A xs s [] [] [] = AutoChopper.acc xs s [] [] ([],xs) A
   Generalization?
2. Directly.
   Hope: acc is easier to verify than AutoChopper.acc because simpler.

No proofs yet.
*)

theory AutoChopper1 = DA + Chopper:

consts
  acc :: "(('a,'s)da * 'a list * 's * 'a list list * 'a list * 'a list)
          => 'a list list * 'a list"
recdef acc "inv_image (less_than <*lex*> less_than)
              (%(A,ys,s,xss,zs,xs). (length xs + length ys + length zs,
                                     length ys))"
"acc(A,[],s,xss,zs,[]) = (xss, zs)"
"acc(A,[],s,xss,zs,x#xs) = acc(A,zs,start A, xss @ [x#xs],[],[])"
"acc(A,y#ys,s,xss,zs,xs) =
  (let s' = next A y s;
      zs' = (if fin A s' then [] else zs@[y]);
      xs' = (if fin A s' then xs@zs@[y] else xs)
   in acc(A,ys,s',xss,zs',xs'))"

end
