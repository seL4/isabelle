(*  Title:      HOLCF/Porder0.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Definition of class porder (partial order).
*)

theory Porder0 = Main:

	(* introduce a (syntactic) class for the constant << *)
axclass sq_ord < type

	(* characteristic constant << for po *)
consts
  "<<"          :: "['a,'a::sq_ord] => bool"        (infixl 55)

syntax (xsymbols)
  "op <<"       :: "['a,'a::sq_ord] => bool"        (infixl "\<sqsubseteq>" 55)

axclass po < sq_ord
        (* class axioms: *)
refl_less:       "x << x"        
antisym_less:    "[|x << y; y << x |] ==> x = y"    
trans_less:      "[|x << y; y << z |] ==> x << z"

declare refl_less [iff]

(* ------------------------------------------------------------------------ *)
(* minimal fixes least element                                              *)
(* ------------------------------------------------------------------------ *)
lemma minimal2UU[OF allI] : "!x::'a::po. uu<<x ==> uu=(@u.!y. u<<y)"
apply (blast intro: someI2 antisym_less)
done

(* ------------------------------------------------------------------------ *)
(* the reverse law of anti--symmetrie of <<                                 *)
(* ------------------------------------------------------------------------ *)

lemma antisym_less_inverse: "(x::'a::po)=y ==> x << y & y << x"
apply blast
done


lemma box_less: "[| (a::'a::po) << b; c << a; b << d|] ==> c << d"
apply (erule trans_less)
apply (erule trans_less)
apply assumption
done

lemma po_eq_conv: "((x::'a::po)=y) = (x << y & y << x)"
apply (fast elim!: antisym_less_inverse intro!: antisym_less)
done
end 


