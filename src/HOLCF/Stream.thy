(*  Title: 	HOLCF/stream.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Theory for streams without defined empty stream 
  'a stream = 'a ** ('a stream)u

The type is axiomatized as the least solution of the domain equation above.
The functor term that specifies the domain equation is: 

  FT = <**,K_{'a},U>

For details see chapter 5 of:

[Franz Regensburger] HOLCF: Eine konservative Erweiterung von HOL um LCF,
                     Dissertation, Technische Universit"at M"unchen, 1994
*)

Stream = Dnat2 +

types stream 1

(* ----------------------------------------------------------------------- *)
(* arity axiom is validated by semantic reasoning                          *)
(* partial ordering is implicit in the isomorphism axioms and their cont.  *)

arities stream::(pcpo)pcpo

consts

(* ----------------------------------------------------------------------- *)
(* essential constants                                                     *)

stream_rep	:: "('a stream) -> ('a ** ('a stream)u)"
stream_abs	:: "('a ** ('a stream)u) -> ('a stream)"

(* ----------------------------------------------------------------------- *)
(* abstract constants and auxiliary constants                              *)

stream_copy	:: "('a stream -> 'a stream) ->'a stream -> 'a stream"

scons		:: "'a -> 'a stream -> 'a stream"
stream_when	:: "('a -> 'a stream -> 'b) -> 'a stream -> 'b"
is_scons	:: "'a stream -> tr"
shd		:: "'a stream -> 'a"
stl		:: "'a stream -> 'a stream"
stream_take	:: "nat => 'a stream -> 'a stream"
stream_finite	:: "'a stream => bool"
stream_bisim	:: "('a stream => 'a stream => bool) => bool"

rules

(* ----------------------------------------------------------------------- *)
(* axiomatization of recursive type 'a stream                              *)
(* ----------------------------------------------------------------------- *)
(* ('a stream,stream_abs) is the initial F-algebra where                   *)
(* F is the locally continuous functor determined by functor term FT.      *)
(* domain equation: 'a stream = 'a ** ('a stream)u                         *)
(* functor term:    FT = <**,K_{'a},U>                                     *)
(* ----------------------------------------------------------------------- *)
(* stream_abs is an isomorphism with inverse stream_rep                    *)
(* identity is the least endomorphism on 'a stream                         *)

stream_abs_iso	"stream_rep[stream_abs[x]] = x"
stream_rep_iso	"stream_abs[stream_rep[x]] = x"
stream_copy_def	"stream_copy == (LAM f. stream_abs oo \
\ 		(ssplit[LAM x y. x ## (lift[up oo f])[y]] oo stream_rep))"
stream_reach	"(fix[stream_copy])[x]=x"

(* ----------------------------------------------------------------------- *)
(* properties of additional constants                                      *)
(* ----------------------------------------------------------------------- *)
(* constructors                                                            *)

scons_def	"scons == (LAM x l. stream_abs[x##up[l]])"

(* ----------------------------------------------------------------------- *)
(* discriminator functional                                                *)

stream_when_def 
"stream_when == (LAM f l.ssplit[LAM x l.f[x][lift[ID][l]]][stream_rep[l]])"

(* ----------------------------------------------------------------------- *)
(* discriminators and selectors                                            *)

is_scons_def	"is_scons == stream_when[LAM x l.TT]"
shd_def		"shd == stream_when[LAM x l.x]"
stl_def		"stl == stream_when[LAM x l.l]"

(* ----------------------------------------------------------------------- *)
(* the taker for streams                                                   *)

stream_take_def "stream_take == (%n.iterate(n,stream_copy,UU))"

(* ----------------------------------------------------------------------- *)

stream_finite_def	"stream_finite == (%s.? n.stream_take(n)[s]=s)"

(* ----------------------------------------------------------------------- *)
(* definition of bisimulation is determined by domain equation             *)
(* simplification and rewriting for abstract constants yields def below    *)

stream_bisim_def "stream_bisim ==\
\(%R.!s1 s2.\
\ 	R(s1,s2) -->\
\  ((s1=UU & s2=UU) |\
\  (? x s11 s21. x~=UU & s1=scons[x][s11] & s2 = scons[x][s21] & R(s11,s21))))"

end




