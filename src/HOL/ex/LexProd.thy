(*  Title:      HOL/ex/lex-prod.thy
    ID:         $Id$
    Author:     Tobias Nipkow, TU Munich
    Copyright   1993  TU Munich

The lexicographic product of two relations.
*)

LexProd = WF + Prod +
consts "**" :: "[('a*'a)set, ('b*'b)set] => (('a*'b)*('a*'b))set" (infixl 70)
rules
lex_prod_def "ra**rb == {p. ? a a' b b'. 
        p = ((a,b),(a',b')) & ((a,a') : ra | a=a' & (b,b') : rb)}"
end

