(*  Title:      HOL/Integ/Ring.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996 TU Muenchen

Derives a few equational consequences about rings
and defines cring_simpl, a simplification tactic for commutative rings.
*)

goal Ring.thy "!!x::'a::cring. x*(y*z)=y*(x*z)";
by (rtac trans 1);
by (rtac times_commute 1);
by (rtac trans 1);
by (rtac times_assoc 1);
by (simp_tac (HOL_basic_ss addsimps [times_commute]) 1);
qed "times_commuteL";

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
 by (rtac (plus_assoc RS sym) 2);
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
 by (rtac (plus_assoc RS sym) 2);
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
 by (rtac (plus_assoc RS sym) 2);
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
 by (rtac (plus_assoc RS sym) 2);
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (rtac refl 2);
 by (rtac (right_inv RS sym) 2);
by (rtac (zeroR RS sym) 1);
qed "mult_invR";

goal Ring.thy "x*(y-z) = (x*y - x*z::'a::ring)";
by (mk_group1_tac 1);
by (simp_tac (HOL_basic_ss addsimps [distribL,mult_invR]) 1);
qed "minus_distribL";

goal Ring.thy "(x-y)*z = (x*z - y*z::'a::ring)";
by (mk_group1_tac 1);
by (simp_tac (HOL_basic_ss addsimps [distribR,mult_invL]) 1);
qed "minus_distribR";

val cring_simps = [times_assoc,times_commute,times_commuteL,
                   distribL,distribR,minus_distribL,minus_distribR]
                  @ agroup2_simps;

val cring_tac =
  let val ss = HOL_basic_ss addsimps cring_simps
  in simp_tac ss end;


(*** The order [minus_plusL3,minus_plusL2] is important because minus_plusL3
     MUST be tried first
val cring_simp =
  let val phase1 = simpset() addsimps
                   [plus_minusL,minus_plusR,minus_minusR,plus_minusR]
      val phase2 = HOL_ss addsimps [minus_plusL3,minus_plusL2,
                                    zeroL,zeroR,mult_zeroL,mult_zeroR]
  in simp_tac phase1 THEN' simp_tac phase2 end;
***)
