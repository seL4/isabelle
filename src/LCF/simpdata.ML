(*  Title: 	LCF/simpdata
    ID:         $Id$
    Author: 	Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Simplification data for LCF
*)


fun mk_rew_rules r =
let fun basify thm =
	  (case concl_of thm of
             _$(_$t$_) => (case fastype_of([],t) of
	                     Type("fun",_) => basify(thm RS ap_thm)
	                   | _ => thm)
           | _ => thm)
in map (mk_meta_eq o basify) (atomize r) end;

val LCF_rews = [minimal,
	 UU_app, UU_app RS ap_thm, UU_app RS ap_thm RS ap_thm,
	 not_TT_less_FF,not_FF_less_TT,not_TT_less_UU,not_FF_less_UU,
	 not_UU_eq_TT,not_UU_eq_FF,not_TT_eq_UU,not_TT_eq_FF,
	 not_FF_eq_UU,not_FF_eq_TT,
	 COND_UU,COND_TT,COND_FF,
	 surj_pairing,FST,SND];

val LCF_ss = FOL_ss setmksimps mk_rew_rules
                    addsimps LCF_rews;
