(*  Title:      HOL/BCV/Opt.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

More about options
*)

Opt = Semilat +

constdefs
 le :: 'a ord => 'a option ord
"le r o1 o2 == case o2 of None => o1=None |
                              Some y => (case o1 of None => True |
                                                    Some x => x <=_r y)"

 opt :: 'a set => 'a option set
"opt A == insert None {x . ? y:A. x = Some y}"

 sup :: 'a binop => 'a option binop
"sup f o1 o2 ==
 case o1 of None => o2 | Some x => (case o2 of None => o1
                                             | Some y => Some(f x y))"

 sl :: "'a sl => 'a option sl"
"sl == %(A,r,f). (opt A, le r, sup f)"

end
