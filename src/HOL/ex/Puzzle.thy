(*  Title: 	HOL/ex/puzzle.thy
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1993 TU Muenchen

An question from "Bundeswettbewerb Mathematik"
*)

Puzzle = Nat +
consts f :: "nat => nat"
rules  f_ax "f(f(n)) < f(Suc(n))"
end
