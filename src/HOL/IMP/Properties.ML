(*  Title: 	HOL/IMP/Properties.ML
    ID:         $Id$
    Author: 	Tobias Nipkow, TUM
    Copyright   1994 TUM

IMP is deterministic.
*)

(* evaluation of aexp is deterministic *)
goal Com.thy "!m n. <a,s> -a-> m & <a,s> -a-> n --> m=n";
by(res_inst_tac[("aexp","a")]Com.aexp.induct 1);
by(REPEAT(fast_tac (HOL_cs addSIs evala.intrs addSEs evala_elim_cases) 1));
bind_thm("aexp_detD", conjI RS (result() RS spec RS spec RS mp));

(* evaluation of bexp is deterministic *)
goal Com.thy "!v w. <b,s> -b-> v & <b,s> -b-> w --> v=w";
by(res_inst_tac[("bexp","b")]Com.bexp.induct 1);
by(REPEAT(fast_tac (HOL_cs addSIs evalb.intrs addSEs evalb_elim_cases
                           addDs [aexp_detD]) 1));
bind_thm("bexp_detD", conjI RS (result() RS spec RS spec RS mp));


val evalc_elim_cases = map (evalc.mk_cases com.simps)
   ["<skip,s> -c-> t", "<x:=a,s> -c-> t", "<c1;c2, s> -c-> t",
    "<ifc b then c1 else c2, s> -c-> t", "<while b do c,s> -c-> t"];

(* evaluation of com is deterministic *)
goal Com.thy "!!c. <c,s> -c-> t ==> !u. <c,s> -c-> u --> u=t";
(* start with rule induction *)
be (evalc.mutual_induct RS spec RS spec RS spec RSN (2,rev_mp)) 1;
by(fast_tac (set_cs addSEs evalc_elim_cases) 1);
by(fast_tac (set_cs addSEs evalc_elim_cases addDs [aexp_detD]) 1);
by(fast_tac (set_cs addSEs evalc_elim_cases) 1);
by(fast_tac (set_cs addSEs evalc_elim_cases addDs [bexp_detD]) 1);
by(fast_tac (set_cs addSEs evalc_elim_cases addDs [bexp_detD]) 1);
by(EVERY1[strip_tac, eresolve_tac evalc_elim_cases,
          atac, dtac bexp_detD, atac, etac False_neq_True]);
by(EVERY1[strip_tac, eresolve_tac evalc_elim_cases,
          dtac bexp_detD, atac, etac (sym RS False_neq_True),
          fast_tac HOL_cs]);
qed "com_det";
