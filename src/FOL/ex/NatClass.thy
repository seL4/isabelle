(*  Title:      FOL/ex/NatClass.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

This is an abstract version of Nat.thy. Instead of axiomatizing a
single type "nat" we define the class of all these types (up to
isomorphism).

Note: The "rec" operator had to be made 'monomorphic', because class
axioms may not contain more than one type variable.
*)

NatClass = FOL +

consts
  "0"           :: 'a                                   ("0")
  Suc           :: 'a => 'a  
  rec           :: ['a, 'a, ['a, 'a] => 'a] => 'a  

axclass
  nat < term
  induct        "[| P(0); !!x. P(x) ==> P(Suc(x)) |] ==> P(n)"
  Suc_inject    "Suc(m) = Suc(n) ==> m = n"
  Suc_neq_0     "Suc(m) = 0 ==> R"
  rec_0         "rec(0, a, f) = a"
  rec_Suc       "rec(Suc(m), a, f) = f(m, rec(m, a, f))"

consts
  "+"           :: "['a::nat, 'a] => 'a"                (infixl 60)

defs
  add_def       "m + n == rec(m, n, %x y. Suc(y))"

end
