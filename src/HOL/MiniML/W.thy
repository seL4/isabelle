(* Title:     HOL/MiniML/W.thy
   ID:        $Id$
   Author:    Dieter Nazareth and Tobias Nipkow
   Copyright  1995 TU Muenchen

Type inference algorithm W
*)

W = MiniML + 

types 
        result_W = "(subst * typ * nat)maybe"

(* type inference algorithm W *)
consts
        W :: [expr, typ list, nat] => result_W

primrec W expr
  "W (Var i) a n = (if i < length a then Ok(id_subst, nth i a, n)
                          else Fail)"
  "W (Abs e) a n = ( (s,t,m) := W e ((TVar n)#a) (Suc n);
                           Ok(s, (s n) -> t, m) )"
  "W (App e1 e2) a n =
                 ( (s1,t1,m1) := W e1 a n;
                   (s2,t2,m2) := W e2 ($s1 a) m1;
                   u := mgu ($s2 t1) (t2 -> (TVar m2));
                   Ok( $u o $s2 o s1, $u (TVar m2), Suc m2) )"
end
