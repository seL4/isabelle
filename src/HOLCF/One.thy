(*  Title:      HOLCF/One.thy
    ID:         $Id$
    Author:     Oscar Slotosch
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

theory One = Lift:

types one = "unit lift"

constdefs
  ONE :: "one"
  "ONE == Def ()"

translations
  "one" <= (type) "unit lift" 

(*  Title:      HOLCF/One.ML
    ID:         $Id$
    Author:     Oscar Slotosch
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The unit domain.
*)

(* ------------------------------------------------------------------------ *)
(* Exhaustion and Elimination for type one                                  *)
(* ------------------------------------------------------------------------ *)

lemma Exh_one: "t=UU | t = ONE"
apply (unfold ONE_def)
apply (induct t)
apply simp
apply simp
done

lemma oneE: "[| p=UU ==> Q; p = ONE ==>Q|] ==>Q"
apply (rule Exh_one [THEN disjE])
apply fast
apply fast
done

lemma dist_less_one [simp]: "~ONE << UU"
apply (unfold ONE_def)
apply (simp add: inst_lift_po)
done

lemma dist_eq_one [simp]: "ONE~=UU" "UU~=ONE"
apply (unfold ONE_def)
apply (simp_all add: inst_lift_po)
done

end
