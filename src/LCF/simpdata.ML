(*  Title: 	LCF/simpdata
    ID:         $Id$
    Author: 	Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Simplification data for LCF
*)

val LCF_ss = FOL_ss addsimps
        [minimal,
	 UU_app, UU_app RS ap_thm, UU_app RS ap_thm RS ap_thm,
	 not_TT_less_FF,not_FF_less_TT,not_TT_less_UU,not_FF_less_UU,
	 not_UU_eq_TT,not_UU_eq_FF,not_TT_eq_UU,not_TT_eq_FF,
	 not_FF_eq_UU,not_FF_eq_TT,
	 COND_UU,COND_TT,COND_FF,
	 surj_pairing,FST,SND];
