(*  Title:      HOL/Relation.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

Relation = Product_Type +

constdefs
  converse :: "('a * 'b) set => ('b * 'a) set"    ("(_^-1)" [1000] 999)
  "r^-1 == {(y, x). (x, y) : r}"
syntax (xsymbols)
  converse :: "('a * 'b) set => ('b * 'a) set"    ("(_\\<inverse>)" [1000] 999)

constdefs
  comp  :: "[('b * 'c)set, ('a * 'b)set] => ('a * 'c)set"  (infixr "O" 60)
    "r O s == {(x,z). ? y. (x,y):s & (y,z):r}"

  Image :: "[('a*'b) set,'a set] => 'b set"                (infixl "^^" 90)
    "r ^^ s == {y. ? x:s. (x,y):r}"

  Id    :: "('a * 'a)set"                            (*the identity relation*)
    "Id == {p. ? x. p = (x,x)}"

  diag  :: "'a set => ('a * 'a)set"          (*diagonal: identity over a set*)
    "diag(A) == UN x:A. {(x,x)}"
  
  Domain :: "('a*'b) set => 'a set"
    "Domain(r) == {x. ? y. (x,y):r}"

  Range  :: "('a*'b) set => 'b set"
    "Range(r) == Domain(r^-1)"

  refl   :: "['a set, ('a*'a) set] => bool" (*reflexivity over a set*)
    "refl A r == r <= A <*> A & (ALL x: A. (x,x) : r)"

  sym    :: "('a*'a) set=>bool"             (*symmetry predicate*)
    "sym(r) == ALL x y. (x,y): r --> (y,x): r"

  antisym:: "('a * 'a)set => bool"          (*antisymmetry predicate*)
    "antisym(r) == ALL x y. (x,y):r --> (y,x):r --> x=y"

  trans  :: "('a * 'a)set => bool"          (*transitivity predicate*)
    "trans(r) == (!x y z. (x,y):r --> (y,z):r --> (x,z):r)"

  univalent :: "('a * 'b)set => bool"
    "univalent r == !x y. (x,y):r --> (!z. (x,z):r --> y=z)"

  fun_rel_comp :: "['a => 'b, ('b * 'c) set] => ('a => 'c) set"
    "fun_rel_comp f R == {g. !x. (f x, g x) : R}"

syntax
  reflexive :: "('a * 'a)set => bool"       (*reflexivity over a type*)
translations
  "reflexive" == "refl UNIV"

end
