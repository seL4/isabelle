(*  Title:      ZF/UNITY/Follows
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

The "Follows" relation of Charpentier and Sivilotte

Theory ported from HOL.
*)

Follows = SubstAx + Increasing +
constdefs
  Follows :: "[i, i, i=>i, i=>i] => i"
  "Follows(A, r, f, g) == 
            Increasing(A, r, g) Int
            Increasing(A, r,f) Int
            Always({s:state. <f(s), g(s)>:r}) Int
           (INT k:A. {s:state. <k, g(s)>:r} LeadsTo {s:state. <k,f(s)>:r})"
consts
  Incr :: [i=>i]=>i   
  n_Incr :: [i=>i]=>i
  m_Incr :: [i=>i]=>i
  s_Incr :: [i=>i]=>i
  n_Fols :: [i=>i, i=>i]=>i   (infixl "n'_Fols" 65)

syntax
  Follows' :: "[i=>i, i=>i, i, i] => i"
        ("(_ /Fols _ /Wrt (_ /'/ _))" [60, 0, 0, 60] 60)

  
translations
  "Incr(f)" == "Increasing(list(nat), prefix(nat), f)"
  "n_Incr(f)" == "Increasing(nat, Le, f)"
  "s_Incr(f)" == "Increasing(Pow(nat), SetLe(nat), f)"
  "m_Incr(f)" == "Increasing(Mult(nat), MultLe(nat, Le), f)"
  
  "f n_Fols g" == "Follows(nat, Le, f, g)"

  "Follows'(f,g,r,A)" == "Follows(A,r,f,g)"
end
