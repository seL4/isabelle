(*  Title: 	HOLCF/dnat.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Theory for the domain of natural numbers

*)

Dnat = HOLCF +

types dnat 0

(* ----------------------------------------------------------------------- *)
(* arrity axiom is valuated by semantical reasoning                        *)

arities dnat::pcpo

consts

(* ----------------------------------------------------------------------- *)
(* essential constants                                                     *)

dnat_rep	:: " dnat -> (one ++ dnat)"
dnat_abs	:: "(one ++ dnat) -> dnat"

(* ----------------------------------------------------------------------- *)
(* abstract constants and auxiliary constants                              *)

dnat_copy	:: "(dnat -> dnat) -> dnat -> dnat"

dzero		:: "dnat"
dsucc		:: "dnat -> dnat"
dnat_when	:: "'b -> (dnat -> 'b) -> dnat -> 'b"
is_dzero	:: "dnat -> tr"
is_dsucc	:: "dnat -> tr"
dpred		:: "dnat -> dnat"
dnat_take	:: "nat => dnat -> dnat"
dnat_bisim	:: "(dnat => dnat => bool) => bool"

rules

(* ----------------------------------------------------------------------- *)
(* axiomatization of recursive type dnat                                   *)
(* ----------------------------------------------------------------------- *)
(* (dnat,dnat_abs) is the initial F-algebra where                          *)
(* F is the locally continuous functor determined by domain equation       *)
(* X = one ++ X                                                            *)
(* ----------------------------------------------------------------------- *)
(* dnat_abs is an isomorphism with inverse dnat_rep                        *)
(* identity is the least endomorphism on dnat                              *)

dnat_abs_iso	"dnat_rep[dnat_abs[x]] = x"
dnat_rep_iso	"dnat_abs[dnat_rep[x]] = x"
dnat_copy_def	"dnat_copy == (LAM f. dnat_abs oo \
\		 (when[sinl][sinr oo f]) oo dnat_rep )"
dnat_reach	"(fix[dnat_copy])[x]=x"

(* ----------------------------------------------------------------------- *)
(* properties of additional constants                                      *)
(* ----------------------------------------------------------------------- *)
(* constructors                                                            *)

dzero_def	"dzero == dnat_abs[sinl[one]]"
dsucc_def	"dsucc == (LAM n. dnat_abs[sinr[n]])"

(* ----------------------------------------------------------------------- *)
(* discriminator functional                                                *)

dnat_when_def	"dnat_when == (LAM f1 f2 n.when[LAM x.f1][f2][dnat_rep[n]])"


(* ----------------------------------------------------------------------- *)
(* discriminators and selectors                                            *)

is_dzero_def	"is_dzero == dnat_when[TT][LAM x.FF]"
is_dsucc_def	"is_dsucc == dnat_when[FF][LAM x.TT]"
dpred_def	"dpred == dnat_when[UU][LAM x.x]"


(* ----------------------------------------------------------------------- *)
(* the taker for dnats                                                   *)

dnat_take_def "dnat_take == (%n.iterate(n,dnat_copy,UU))"

(* ----------------------------------------------------------------------- *)
(* definition of bisimulation is determined by domain equation             *)
(* simplification and rewriting for abstract constants yields def below    *)

dnat_bisim_def "dnat_bisim ==\
\(%R.!s1 s2.\
\ 	R(s1,s2) -->\
\  ((s1=UU & s2=UU) |(s1=dzero & s2=dzero) |\
\  (? s11 s21. s11~=UU & s21~=UU & s1=dsucc[s11] &\
\		 s2 = dsucc[s21] & R(s11,s21))))"

end




