(*  Title:      LK/lk.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Classical First-Order Sequent Calculus

There may be printing problems if a seqent is in expanded normal form
	(eta-expanded, beta-contracted)
*)

LK = Sequents +

classes
  term < logic

default
  term

consts

 Trueprop	:: "two_seqi"
 "@Trueprop"	:: "two_seqe" ("((_)/ |- (_))" [6,6] 5)


  True,False   :: o
  "="          :: ['a,'a] => o       (infixl 50)
  Not          :: o => o             ("~ _" [40] 40)
  "&"          :: [o,o] => o         (infixr 35)
  "|"          :: [o,o] => o         (infixr 30)
  "-->","<->"  :: [o,o] => o         (infixr 25)
  The          :: ('a => o) => 'a    (binder "THE " 10)
  All          :: ('a => o) => o     (binder "ALL " 10)
  Ex           :: ('a => o) => o     (binder "EX " 10)

rules
  (*Structural rules*)

  basic "$H, P, $G |- $E, P, $F"

  thinR "$H |- $E, $F ==> $H |- $E, P, $F"
  thinL "$H, $G |- $E ==> $H, P, $G |- $E"

  cut   "[| $H |- $E, P;  $H, P |- $E |] ==> $H |- $E"

  (*Propositional rules*)

  conjR "[| $H|- $E, P, $F;  $H|- $E, Q, $F |] ==> $H|- $E, P&Q, $F"
  conjL "$H, P, Q, $G |- $E ==> $H, P & Q, $G |- $E"

  disjR "$H |- $E, P, Q, $F ==> $H |- $E, P|Q, $F"
  disjL "[| $H, P, $G |- $E;  $H, Q, $G |- $E |] ==> $H, P|Q, $G |- $E"

  impR  "$H, P |- $E, Q, $F ==> $H |- $E, P-->Q, $F"
  impL  "[| $H,$G |- $E,P;  $H, Q, $G |- $E |] ==> $H, P-->Q, $G |- $E"

  notR  "$H, P |- $E, $F ==> $H |- $E, ~P, $F"
  notL  "$H, $G |- $E, P ==> $H, ~P, $G |- $E"

  FalseL "$H, False, $G |- $E"

  True_def "True == False-->False"
  iff_def  "P<->Q == (P-->Q) & (Q-->P)"

  (*Quantifiers*)

  allR  "(!!x.$H |- $E, P(x), $F) ==> $H |- $E, ALL x. P(x), $F"
  allL  "$H, P(x), $G, ALL x. P(x) |- $E ==> $H, ALL x. P(x), $G |- $E"

  exR   "$H |- $E, P(x), $F, EX x. P(x) ==> $H |- $E, EX x. P(x), $F"
  exL   "(!!x.$H, P(x), $G |- $E) ==> $H, EX x. P(x), $G |- $E"

  (*Equality*)

  refl  "$H |- $E, a=a, $F"
  sym   "$H |- $E, a=b, $F ==> $H |- $E, b=a, $F"
  trans "[| $H|- $E, a=b, $F;  $H|- $E, b=c, $F |] ==> $H|- $E, a=c, $F"


  (*Descriptions*)

  The "[| $H |- $E, P(a), $F;  !!x.$H, P(x) |- $E, x=a, $F |] ==> 
          $H |- $E, P(THE x. P(x)), $F"
end

  ML

val parse_translation = [("@Trueprop",Sequents.two_seq_tr "Trueprop")];
val print_translation = [("Trueprop",Sequents.two_seq_tr' "@Trueprop")];
