(*  Title: 	HOLCF/dlist.thy

    Author: 	Franz Regensburger
    ID:         $ $
    Copyright   1994 Technische Universitaet Muenchen

Theory for finite lists  'a dlist = one ++ ('a ** 'a dlist)

The type is axiomatized as the least solution of the domain equation above.
The functor term that specifies the domain equation is: 

  FT = <++,K_{one},<**,K_{'a},I>>

For details see chapter 5 of:

[Franz Regensburger] HOLCF: Eine konservative Erweiterung von HOL um LCF,
                     Dissertation, Technische Universit"at M"unchen, 1994


*)

Dlist = Stream2 +

types dlist 1

(* ----------------------------------------------------------------------- *)
(* arity axiom is validated by semantic reasoning                          *)
(* partial ordering is implicit in the isomorphism axioms and their cont.  *)

arities dlist::(pcpo)pcpo

consts

(* ----------------------------------------------------------------------- *)
(* essential constants                                                     *)

dlist_rep	:: "('a dlist) -> (one ++ 'a ** 'a dlist)"
dlist_abs	:: "(one ++ 'a ** 'a dlist) -> ('a dlist)"

(* ----------------------------------------------------------------------- *)
(* abstract constants and auxiliary constants                              *)

dlist_copy	:: "('a dlist -> 'a dlist) ->'a dlist -> 'a dlist"

dnil            :: "'a dlist"
dcons		:: "'a -> 'a dlist -> 'a dlist"
dlist_when	:: " 'b -> ('a -> 'a dlist -> 'b) -> 'a dlist -> 'b"
is_dnil    	:: "'a dlist -> tr"
is_dcons	:: "'a dlist -> tr"
dhd		:: "'a dlist -> 'a"
dtl		:: "'a dlist -> 'a dlist"
dlist_take	:: "nat => 'a dlist -> 'a dlist"
dlist_finite	:: "'a dlist => bool"
dlist_bisim	:: "('a dlist => 'a dlist => bool) => bool"

rules

(* ----------------------------------------------------------------------- *)
(* axiomatization of recursive type 'a dlist                               *)
(* ----------------------------------------------------------------------- *)
(* ('a dlist,dlist_abs) is the initial F-algebra where                     *)
(* F is the locally continuous functor determined by functor term FT.      *)
(* domain equation: 'a dlist = one ++ ('a ** 'a dlist)                     *)
(* functor term:    FT = <++,K_{one},<**,K_{'a},I>>                        *)
(* ----------------------------------------------------------------------- *)
(* dlist_abs is an isomorphism with inverse dlist_rep                      *)
(* identity is the least endomorphism on 'a dlist                          *)

dlist_abs_iso	"dlist_rep[dlist_abs[x]] = x"
dlist_rep_iso	"dlist_abs[dlist_rep[x]] = x"
dlist_copy_def	"dlist_copy == (LAM f. dlist_abs oo 
 		(when[sinl][sinr oo (ssplit[LAM x y. x ## f[y]])])
                                oo dlist_rep)"
dlist_reach	"(fix[dlist_copy])[x]=x"

(* ----------------------------------------------------------------------- *)
(* properties of additional constants                                      *)
(* ----------------------------------------------------------------------- *)
(* constructors                                                            *)

dnil_def	"dnil  == dlist_abs[sinl[one]]"
dcons_def	"dcons == (LAM x l. dlist_abs[sinr[x##l]])"

(* ----------------------------------------------------------------------- *)
(* discriminator functional                                                *)

dlist_when_def 
"dlist_when == (LAM f1 f2 l.
   when[LAM x.f1][ssplit[LAM x l.f2[x][l]]][dlist_rep[l]])"

(* ----------------------------------------------------------------------- *)
(* discriminators and selectors                                            *)

is_dnil_def	"is_dnil  == dlist_when[TT][LAM x l.FF]"
is_dcons_def	"is_dcons == dlist_when[FF][LAM x l.TT]"
dhd_def		"dhd == dlist_when[UU][LAM x l.x]"
dtl_def		"dtl == dlist_when[UU][LAM x l.l]"

(* ----------------------------------------------------------------------- *)
(* the taker for dlists                                                   *)

dlist_take_def "dlist_take == (%n.iterate(n,dlist_copy,UU))"

(* ----------------------------------------------------------------------- *)

dlist_finite_def	"dlist_finite == (%s.? n.dlist_take(n)[s]=s)"

(* ----------------------------------------------------------------------- *)
(* definition of bisimulation is determined by domain equation             *)
(* simplification and rewriting for abstract constants yields def below    *)

dlist_bisim_def "dlist_bisim ==
 ( %R.!l1 l2.
 	R(l1,l2) -->
  ((l1=UU & l2=UU) |
   (l1=dnil & l2=dnil) |
   (? x l11 l21. x~=UU & l11~=UU & l21~=UU & 
               l1=dcons[x][l11] & l2 = dcons[x][l21] & R(l11,l21))))"

end




