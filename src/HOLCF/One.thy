(*  Title: 	HOLCF/one.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Introduce atomic type one = (void)u

The type is axiomatized as the least solution of a domain equation.
The functor term that specifies the domain equation is: 

  FT = <U,K_{void}>

For details see chapter 5 of:

[Franz Regensburger] HOLCF: Eine konservative Erweiterung von HOL um LCF,
                     Dissertation, Technische Universit"at M"unchen, 1994

*)

One = ccc1+

types one 0
arities one :: pcpo

consts
	abs_one		:: "(void)u -> one"
	rep_one		:: "one -> (void)u"
	one 		:: "one"
	one_when 	:: "'c -> one -> 'c"

rules
  abs_one_iso	"abs_one`(rep_one`u) = u"
  rep_one_iso	"rep_one`(abs_one`x) = x"

defs
  one_def	"one == abs_one`(up`UU)"
  one_when_def "one_when == (LAM c u.lift`(LAM x.c)`(rep_one`u))"

translations
  "case l of one => t1" == "one_when`t1`l"

end





