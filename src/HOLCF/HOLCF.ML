(*  Title: 	HOLCF/HOLCF.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen
*)

open HOLCF;

Addsimps (one_when @ dist_less_one @ dist_eq_one @ dist_less_tr @ dist_eq_tr
          @ tr_when @ andalso_thms @ orelse_thms @ neg_thms @ ifte_thms);
