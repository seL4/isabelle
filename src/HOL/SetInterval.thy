(*  Title:      HOL/SetInterval.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998  TU Muenchen

lessThan, greaterThan, atLeast, atMost
*)

SetInterval = equalities +

constdefs
 lessThan    :: "('a::ord) => 'a set"	("(1{.._'(})")
"{..u(} == {x. x<u}"

 atMost      :: "('a::ord) => 'a set"	("(1{.._})")
"{..u} == {x. x<=u}"

 greaterThan :: "('a::ord) => 'a set"	("(1{')_..})")
"{)l..} == {x. l<x}"

 atLeast     :: "('a::ord) => 'a set"	("(1{_..})")
"{l..} == {x. l<=x}"

end
