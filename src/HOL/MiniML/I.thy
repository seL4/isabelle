(*   Title:         MiniML.thy
     Author:        Thomas Stauner
     Copyright      1995 TU Muenchen

     Recursive definition of type inference algorithm I for Mini_ML.
*)

I = W +

consts
	I :: [expr, type_expr list, nat, subst] => result_W

primrec I expr
        I_Var	"I (Var i) a n s = (if i < length a then Ok(s, nth i a, n)
                                    else Fail)"
        I_Abs	"I (Abs e) a n s = I e ((TVar n)#a) (Suc n) s   bind
                                   (%(s,t,m). Ok(s, Fun (TVar n) t, m) )"
        I_App	"I (App e1 e2) a n s =
 		 I e1 a n s   bind
		 (%(s1,t1,m1). I e2 a m1 s1  bind   
		 (%(s2,t2,m2). mgu ($s2 t1) (Fun ($s2 t2) (TVar m2)) bind
		 (%u. Ok($u o s2, TVar m2, Suc m2) ) ))"

end
