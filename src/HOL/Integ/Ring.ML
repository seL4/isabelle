(*  Title:      HOL/Integ/Ring.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996 TU Muenchen

Derives a few equational consequences about rings
and defines cring_simpl, a simplification tactic for commutative rings.
*)

open Ring;

(***
It is not clear if all thsese rules, esp. distributivity, should be part
of the default simpset. At the moment they are because they are used in the
decision procedure.
***)   
Addsimps [times_assoc,times_commute,distribL,distribR];

goal Ring.thy "!!x::'a::cring. x*(y*z)=y*(x*z)";
by (rtac trans 1);
by (rtac times_commute 1);
by (rtac trans 1);
by (rtac times_assoc 1);
by (Simp_tac 1);
qed "times_commuteL";
Addsimps [times_commuteL];

val times_cong = read_instantiate [("f1","op *")] (arg_cong RS cong);

goal Ring.thy "!!x::'a::ring. zero*x = zero";
by (rtac trans 1);
 by (rtac right_inv 2);
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (rtac refl 3);
 by (rtac trans 2);
  by (rtac times_cong 3);
   by (rtac zeroL 3);
  by (rtac refl 3);
 by (rtac (distribR RS sym) 2);
by (rtac trans 1);
 br(plus_assoc RS sym) 2;
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (rtac refl 2);
 by (rtac (right_inv RS sym) 2);
by (rtac (zeroR RS sym) 1);
qed "mult_zeroL";

goal Ring.thy "!!x::'a::ring. x*zero = zero";
by (rtac trans 1);
 by (rtac right_inv 2);
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (rtac refl 3);
 by (rtac trans 2);
  by (rtac times_cong 3);
   by (rtac zeroL 4);
  by (rtac refl 3);
 by (rtac (distribL RS sym) 2);
by (rtac trans 1);
 br(plus_assoc RS sym) 2;
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (rtac refl 2);
 by (rtac (right_inv RS sym) 2);
by (rtac (zeroR RS sym) 1);
qed "mult_zeroR";

goal Ring.thy "!!x::'a::ring. (zero-x)*y = zero-(x*y)";
by (rtac trans 1);
 by (rtac zeroL 2);
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (rtac refl 3);
 by (rtac mult_zeroL 2);
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (rtac refl 3);
 by (rtac times_cong 2);
  by (rtac left_inv 2);
 by (rtac refl 2);
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (rtac refl 3);
 by (rtac (distribR RS sym) 2);
by (rtac trans 1);
 br(plus_assoc RS sym) 2;
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (rtac refl 2);
 by (rtac (right_inv RS sym) 2);
by (rtac (zeroR RS sym) 1);
qed "mult_invL";

goal Ring.thy "!!x::'a::ring. x*(zero-y) = zero-(x*y)";
by (rtac trans 1);
 by (rtac zeroL 2);
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (rtac refl 3);
 by (rtac mult_zeroR 2);
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (rtac refl 3);
 by (rtac times_cong 2);
  by (rtac refl 2);
 by (rtac left_inv 2);
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (rtac refl 3);
 by (rtac (distribL RS sym) 2);
by (rtac trans 1);
 br(plus_assoc RS sym) 2;
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (rtac refl 2);
 by (rtac (right_inv RS sym) 2);
by (rtac (zeroR RS sym) 1);
qed "mult_invR";

Addsimps[mult_invL,mult_invR];


goal Ring.thy "!!x::'a::ring. x*(y-z) = x*y - x*z";
by (stac minus_inv 1);
by (rtac sym 1);
by (stac minus_inv 1);
by (Simp_tac 1);
qed "minus_distribL";

goal Ring.thy "!!x::'a::ring. (x-y)*z = x*z - y*z";
by (stac minus_inv 1);
by (rtac sym 1);
by (stac minus_inv 1);
by (Simp_tac 1);
qed "minus_distribR";

Addsimps [minus_distribL,minus_distribR];

(*** The order [minus_plusL3,minus_plusL2] is important because minus_plusL3
     MUST be tried first ***)
val cring_simp =
  let val phase1 = !simpset addsimps
                   [plus_minusL,minus_plusR,minus_minusR,plus_minusR]
      val phase2 = HOL_ss addsimps [minus_plusL3,minus_plusL2,
                                    zeroL,zeroR,mult_zeroL,mult_zeroR]
  in simp_tac phase1 THEN' simp_tac phase2 end;
