(*  Title:      HOLCF/ccc1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for ccc1.thy 
*)

open ccc1;


(* ------------------------------------------------------------------------ *)
(* Access to definitions                                                    *)
(* ------------------------------------------------------------------------ *)


qed_goalw "ID1" ccc1.thy [ID_def] "ID`x=x"
 (fn prems =>
        [
        (stac beta_cfun 1),
        (rtac cont_id 1),
        (rtac refl 1)
        ]);

qed_goalw "cfcomp1" ccc1.thy [oo_def] "(f oo g)=(LAM x.f`(g`x))"
 (fn prems =>
        [
        (stac beta_cfun 1),
        (cont_tacR 1),
        (stac beta_cfun 1),
        (cont_tacR 1),
        (rtac refl 1)
        ]);

qed_goal "cfcomp2" ccc1.thy  "(f oo g)`x=f`(g`x)"
 (fn prems =>
        [
        (stac cfcomp1 1),
        (stac beta_cfun 1),
        (cont_tacR 1),
        (rtac refl 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* Show that interpretation of (pcpo,_->_) is a category                    *)
(* The class of objects is interpretation of syntactical class pcpo         *)
(* The class of arrows  between objects 'a and 'b is interpret. of 'a -> 'b *)
(* The identity arrow is interpretation of ID                               *)
(* The composition of f and g is interpretation of oo                       *)
(* ------------------------------------------------------------------------ *)


qed_goal "ID2" ccc1.thy "f oo ID = f "
 (fn prems =>
        [
        (rtac ext_cfun 1),
        (stac cfcomp2 1),
        (stac ID1 1),
        (rtac refl 1)
        ]);

qed_goal "ID3" ccc1.thy "ID oo f = f "
 (fn prems =>
        [
        (rtac ext_cfun 1),
        (stac cfcomp2 1),
        (stac ID1 1),
        (rtac refl 1)
        ]);


qed_goal "assoc_oo" ccc1.thy "f oo (g oo h) = (f oo g) oo h"
 (fn prems =>
        [
        (rtac ext_cfun 1),
        (res_inst_tac [("s","f`(g`(h`x))")] trans  1),
        (stac cfcomp2 1),
        (stac cfcomp2 1),
        (rtac refl 1),
        (stac cfcomp2 1),
        (stac cfcomp2 1),
        (rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Merge the different rewrite rules for the simplifier                     *)
(* ------------------------------------------------------------------------ *)

Addsimps (up_rews @ [ID1,ID2,ID3,cfcomp2]);




