(* Title:     HOL/MiniML/W.thy
   ID:        $Id$
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen

Type inference algorithm W
*)


W = MiniML + 

types 
        result_W = "(subst * typ * nat)option"

(* type inference algorithm W *)

consts
        W :: [expr, ctxt, nat] => result_W

primrec W expr
  "W (Var i) A n =  
     (if i < length A then Some( id_subst,   
	                         bound_typ_inst (%b. TVar(b+n)) (nth i A),   
	                         n + (min_new_bound_tv (nth i A)) )  
	              else None)"
  
  "W (Abs e) A n = ( (S,t,m) := W e ((FVar n)#A) (Suc n);
                     Some( S, (S n) -> t, m) )"
  
  "W (App e1 e2) A n = ( (S1,t1,m1) := W e1 A n;
                         (S2,t2,m2) := W e2 ($S1 A) m1;
                         U := mgu ($S2 t1) (t2 -> (TVar m2));
                         Some( $U o $S2 o S1, U m2, Suc m2) )"
  
  "W (LET e1 e2) A n = ( (S1,t1,m1) := W e1 A n;
                         (S2,t2,m2) := W e2 ((gen ($S1 A) t1)#($S1 A)) m1;
                         Some( $S2 o S1, t2, m2) )"
end
