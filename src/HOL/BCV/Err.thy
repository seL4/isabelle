(*  Title:      HOL/BCV/Err.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

The error type
*)

Err = Semilat +

datatype 'a err = Err | OK 'a

types 'a ebinop = 'a => 'a => 'a err
      'a esl =    "'a set * 'a ord * 'a ebinop"

constdefs
 lift :: ('a => 'b err) => ('a err => 'b err)
"lift f e == case e of Err => Err | OK x => f x"

 lift2 :: ('a => 'b => 'c err) => 'a err => 'b err => 'c err
"lift2 f e1 e2 ==
 case e1 of Err  => Err
          | OK x => (case e2 of Err => Err | OK y => f x y)"

 le :: 'a ord => 'a err ord
"le r e1 e2 ==
        case e2 of Err => True |
                   OK y => (case e1 of Err => False | OK x => x <=_r y)"

 sup :: ('a => 'b => 'c) => ('a err => 'b err => 'c err)
"sup f == lift2(%x y. OK(x +_f y))"

 err :: 'a set => 'a err set
"err A == insert Err {x . ? y:A. x = OK y}"

 esl :: 'a sl => 'a esl
"esl == %(A,r,f). (A,r, %x y. OK(f x y))"

 sl :: 'a esl => 'a err sl
"sl == %(A,r,f). (err A, le r, lift2 f)"

syntax
 err_semilat :: 'a esl => bool
translations
"err_semilat L" == "semilat(Err.sl L)"

end
