(*  Title:      HOL/Lex/NA.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Nondeterministic automata
*)

theory NA = AutoProj:

types ('a,'s)na = "'s * ('a => 's => 's set) * ('s => bool)"

consts delta :: "('a,'s)na => 'a list => 's => 's set"
primrec
"delta A []    p = {p}"
"delta A (a#w) p = Union(delta A w ` next A a p)"

constdefs
 accepts :: "('a,'s)na => 'a list => bool"
"accepts A w == EX q : delta A w (start A). fin A q"

 step :: "('a,'s)na => 'a => ('s * 's)set"
"step A a == {(p,q) . q : next A a p}"

consts steps :: "('a,'s)na => 'a list => ('s * 's)set"
primrec
"steps A [] = Id"
"steps A (a#w) = steps A w  O  step A a"

lemma steps_append[simp]:
 "steps A (v@w) = steps A w  O  steps A v";
by(induct v, simp_all add:O_assoc)

lemma in_steps_append[iff]:
  "(p,r) : steps A (v@w) = ((p,r) : (steps A w O steps A v))"
apply(rule steps_append[THEN equalityE])
apply blast
done

lemma delta_conv_steps: "!!p. delta A w p = {q. (p,q) : steps A w}"
by(induct w)(auto simp:step_def)

lemma accepts_conv_steps:
 "accepts A w = (? q. (start A,q) : steps A w & fin A q)";
by(simp add: delta_conv_steps accepts_def)

end
