(*  Title:      ZF/ex/CoUnit.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Trivial codatatype definitions, one of which goes wrong!

See discussion in 
  L C Paulson.  A Concrete Final Coalgebra Theorem for ZF Set Theory.
  Report 334,  Cambridge University Computer Laboratory.  1994.
*)

CoUnit = Main +

(*This degenerate definition does not work well because the one constructor's
  definition is trivial!  The same thing occurs with Aczel's Special Final
  Coalgebra Theorem
*)
consts
  counit :: i
codatatype
  "counit" = Con ("x \\<in> counit")


(*A similar example, but the constructor is non-degenerate and it works!
  The resulting set is a singleton.
*)

consts
  counit2 :: i
codatatype
  "counit2" = Con2 ("x \\<in> counit2", "y \\<in> counit2")

end
