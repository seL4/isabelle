(*  Title: 	Subst/unifier.thy
    Author: 	Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Definition of most general idempotent unifier
*)

Unifier = Subst +

consts

  Idem       :: "('a*('a uterm))list=> bool"
  Unifier    :: "[('a*('a uterm))list,'a uterm,'a uterm] => bool"
  ">>"       :: "[('a*('a uterm))list,('a*('a uterm))list] => bool" (infixr 52)
  MGUnifier  :: "[('a*('a uterm))list,'a uterm,'a uterm] => bool"
  MGIUnifier :: "[('a*('a uterm))list,'a uterm,'a uterm] => bool"
  UWFD       :: "['a uterm,'a uterm,'a uterm,'a uterm] => bool"

rules  (*Definitions*)

  Idem_def         "Idem(s) == s <> s =s= s"
  Unifier_def      "Unifier s t u == t <| s = u <| s"
  MoreGeneral_def  "r >> s == ? q.s =s= r <> q"
  MGUnifier_def    "MGUnifier s t u == Unifier s t u & \
\		    (! r.Unifier r t u --> s >> r)"
  MGIUnifier_def   "MGIUnifier s t u == MGUnifier s t u & Idem(s)"

  UWFD_def
  "UWFD x y x' y' == \
\    (vars_of(x) Un vars_of(y) < vars_of(x') Un vars_of(y')) |  \
\    (vars_of(x) Un vars_of(y) = vars_of(x') Un vars_of(y') & x <: x')"

end
