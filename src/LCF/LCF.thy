(*  Title: 	LCF/lcf.thy
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1992  University of Cambridge

Natural Deduction Rules for LCF
*)

LCF = FOL +

classes cpo < term

default cpo

types tr,void 0
      "*" 2 (infixl 6)
      "+" 2 (infixl 5)

arities fun, "*", "+" :: (cpo,cpo)cpo
        tr,void :: cpo

consts
 UU	:: "'a"
 TT,FF	:: "tr"
 FIX	:: "('a => 'a) => 'a"
 FST	:: "'a*'b => 'a"
 SND	:: "'a*'b => 'b"
 INL    :: "'a => 'a+'b"
 INR    :: "'b => 'a+'b"
 WHEN   :: "['a=>'c, 'b=>'c, 'a+'b] => 'c"
 adm	:: "('a => o) => o"
 VOID	:: "void"		("()")
 PAIR	:: "['a,'b] => 'a*'b"	("(1<_,/_>)" [0,0] 100)
 COND	:: "[tr,'a,'a] => 'a"	("(_ =>/ (_ |/ _))" [60,60,60] 60)
 "<<"	:: "['a,'a] => o"	(infixl 50)
rules
  (** DOMAIN THEORY **)

  eq_def	"x=y == x << y & y << x"

  less_trans	"[| x << y; y << z |] ==> x << z"

  less_ext	"(ALL x. f(x) << g(x)) ==> f << g"

  mono		"[| f << g; x << y |] ==> f(x) << g(y)"

  minimal	"UU << x"

  FIX_eq	"f(FIX(f)) = FIX(f)"

  (** TR **)

  tr_cases	"p=UU | p=TT | p=FF"

  not_TT_less_FF "~ TT << FF"
  not_FF_less_TT "~ FF << TT"
  not_TT_less_UU "~ TT << UU"
  not_FF_less_UU "~ FF << UU"

  COND_UU	"UU => x | y  =  UU"
  COND_TT	"TT => x | y  =  x"
  COND_FF	"FF => x | y  =  y"

  (** PAIRS **)

  surj_pairing	"<FST(z),SND(z)> = z"

  FST	"FST(<x,y>) = x"
  SND	"SND(<x,y>) = y"

  (*** STRICT SUM ***)

  INL_DEF "~x=UU ==> ~INL(x)=UU"
  INR_DEF "~x=UU ==> ~INR(x)=UU"

  INL_STRICT "INL(UU) = UU"
  INR_STRICT "INR(UU) = UU"

  WHEN_UU  "WHEN(f,g,UU) = UU"
  WHEN_INL "~x=UU ==> WHEN(f,g,INL(x)) = f(x)"
  WHEN_INR "~x=UU ==> WHEN(f,g,INR(x)) = g(x)"

  SUM_EXHAUSTION
    "z = UU | (EX x. ~x=UU & z = INL(x)) | (EX y. ~y=UU & z = INR(y))"

  (** VOID **)

  void_cases	"(x::void) = UU"

  (** INDUCTION **)

  induct	"[| adm(P); P(UU); ALL x. P(x) --> P(f(x)) |] ==> P(FIX(f))"

  (** Admissibility / Chain Completeness **)
  (* All rules can be found on pages 199--200 of Larry's LCF book.
     Note that "easiness" of types is not taken into account
     because it cannot be expressed schematically; flatness could be. *)

  adm_less	"adm(%x.t(x) << u(x))"
  adm_not_less	"adm(%x.~ t(x) << u)"
  adm_not_free  "adm(%x.A)"
  adm_subst	"adm(P) ==> adm(%x.P(t(x)))"
  adm_conj	"[| adm(P); adm(Q) |] ==> adm(%x.P(x)&Q(x))"
  adm_disj	"[| adm(P); adm(Q) |] ==> adm(%x.P(x)|Q(x))"
  adm_imp	"[| adm(%x.~P(x)); adm(Q) |] ==> adm(%x.P(x)-->Q(x))"
  adm_all	"(!!y.adm(P(y))) ==> adm(%x.ALL y.P(y,x))"
end
