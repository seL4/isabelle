(*  Title:      Relation.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

Relation = Prod +

consts
  O           :: "[('b * 'c)set, ('a * 'b)set] => ('a * 'c)set" (infixr 60)
  converse    :: "('a*'b) set => ('b*'a) set"     ("(_^-1)" [1000] 999)
  "^^"        :: "[('a*'b) set,'a set] => 'b set" (infixl 90)
  
defs
  comp_def      "r O s == {(x,z). ? y. (x,y):s & (y,z):r}"
  converse_def  "r^-1 == {(y,x). (x,y):r}"
  Image_def     "r ^^ s == {y. ? x:s. (x,y):r}"
  
constdefs
  Id     :: "('a * 'a)set"                 (*the identity relation*)
      "Id == {p. ? x. p = (x,x)}"

  diag   :: "'a set => ('a * 'a)set"
    "diag(A) == UN x:A. {(x,x)}"
  
  Domain :: "('a*'b) set => 'a set"
    "Domain(r) == {x. ? y. (x,y):r}"

  Range  :: "('a*'b) set => 'b set"
    "Range(r) == Domain(r^-1)"

  refl   :: "['a set, ('a*'a) set] => bool" (*reflexivity over a set*)
    "refl A r == r <= A Times A & (ALL x: A. (x,x) : r)"

  sym    :: "('a*'a) set=>bool"             (*symmetry predicate*)
    "sym(r) == ALL x y. (x,y): r --> (y,x): r"

  antisym:: "('a * 'a)set => bool"          (*antisymmetry predicate*)
    "antisym(r) == ALL x y. (x,y):r --> (y,x):r --> x=y"

  trans  :: "('a * 'a)set => bool"          (*transitivity predicate*)
    "trans(r) == (!x y z. (x,y):r --> (y,z):r --> (x,z):r)"

  Univalent :: "('a * 'b)set => bool"
    "Univalent r == !x y. (x,y):r --> (!z. (x,z):r --> y=z)"

syntax
  reflexive :: "('a * 'a)set => bool"       (*reflexivity over a type*)

translations
  "reflexive" == "refl UNIV"

end
