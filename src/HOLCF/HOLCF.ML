(*  Title: 	HOLCF/HOLCF.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen
*)

open HOLCF;

val HOLCF_ss = ccc1_ss 
		addsimps one_when 
		addsimps dist_less_one
		addsimps dist_eq_one 
		addsimps dist_less_tr
		addsimps dist_eq_tr
		addsimps tr_when
		addsimps andalso_thms
		addsimps orelse_thms
		addsimps ifte_thms;


