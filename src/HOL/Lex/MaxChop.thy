(*  Title:      HOL/Lex/MaxChop.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

MaxChop = MaxPrefix +

types   'a chopper = "'a list => 'a list list * 'a list"

constdefs
 is_maxchopper :: ('a list => bool) => 'a chopper => bool
"is_maxchopper P chopper ==
 !xs zs yss.
    (chopper(xs) = (yss,zs)) =
    (xs = concat yss @ zs & (!ys : set yss. ys ~= []) &
     (case yss of
        [] => is_maxpref P [] xs
      | us#uss => is_maxpref P us xs & chopper(concat(uss)@zs) = (uss,zs)))"

constdefs
 reducing :: "'a splitter => bool"
"reducing splitf ==
 !xs ys zs. splitf xs = (ys,zs) & ys ~= [] --> length zs < length xs"

consts
 chopr :: "'a splitter * 'a list => 'a list list * 'a list"
recdef chopr "measure (length o snd)"
"chopr (splitf,xs) = (if reducing splitf
                      then let pp = splitf xs
                           in if fst(pp)=[] then ([],xs)
                           else let qq = chopr (splitf,snd pp)
                                in (fst pp # fst qq,snd qq)
                      else arbitrary)"
constdefs
 chop :: 'a splitter  => 'a chopper
"chop splitf xs == chopr(splitf,xs)"

end
