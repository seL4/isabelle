(* Title:     HOL/MiniML/W.thy
   ID:        $Id$
   Author:    Dieter Nazareth and Tobias Nipkow
   Copyright  1995 TU Muenchen

Type inference algorithm W
*)

W = MiniML + 

types 
        result_W = "(subst * type_expr * nat)maybe"

(* type inference algorithm W *)
consts
	W :: "[expr, type_expr list, nat] => result_W"

primrec W expr
  W_Var	"W (Var i) a n = (if i < length a then Ok(id_subst, nth i a, n)
		          else Fail)"
  W_Abs	"W (Abs e) a n = W e ((TVar n)#a) (Suc n)    bind   
		         (%(s,t,m). Ok(s, Fun (s n) t, m) )"
  W_App	"W (App e1 e2) a n =
 		 W e1 a n    bind
		 (%(s1,t1,m1). W e2 ($ s1 a) m1   bind   
		 (%(s2,t2,m2). mgu ($ s2 t1) (Fun t2 (TVar m2)) bind
		 (%u. Ok( ($ u) o (($ s2) o s1), $ u (TVar m2), Suc m2) )))"
end
