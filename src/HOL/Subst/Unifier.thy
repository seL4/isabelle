(*  Title:      Subst/Unifier.thy
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Definition of most general unifier
*)

Unifier = Subst + 

consts

  Unifier   :: "[('a * 'a uterm)list, 'a uterm, 'a uterm] => bool"
  ">>"      :: "[('a * 'a uterm)list, ('a * 'a uterm)list] => bool" (infixr 52)
  MGUnifier :: "[('a * 'a uterm)list, 'a uterm, 'a uterm] => bool"
  Idem      :: "('a * 'a uterm)list => bool"

defs

  Unifier_def      "Unifier s t u == t <| s = u <| s"
  MoreGeneral_def  "r >> s == ? q. s =$= r <> q"
  MGUnifier_def    "MGUnifier s t u == Unifier s t u & 
                                       (!r. Unifier r t u --> s >> r)"
  Idem_def         "Idem(s) == (s <> s) =$= s"
end
