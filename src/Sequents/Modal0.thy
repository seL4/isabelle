(*  Title:      Sequents/Modal0.thy
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1991  University of Cambridge
*)

theory Modal0
imports LK0
uses "modal.ML"
begin

consts
  box           :: "o=>o"       ("[]_" [50] 50)
  dia           :: "o=>o"       ("<>_" [50] 50)
  strimp        :: "[o,o]=>o"   (infixr "--<" 25)
  streqv        :: "[o,o]=>o"   (infixr ">-<" 25)
  Lstar         :: "two_seqi"
  Rstar         :: "two_seqi"

syntax
  "@Lstar"      :: "two_seqe"   ("(_)|L>(_)" [6,6] 5)
  "@Rstar"      :: "two_seqe"   ("(_)|R>(_)" [6,6] 5)

ML {*
  val Lstar = "Lstar";
  val Rstar = "Rstar";
  val SLstar = "@Lstar";
  val SRstar = "@Rstar";

  fun star_tr c [s1,s2] = Const(c,dummyT)$ seq_tr s1$ seq_tr s2;
  fun star_tr' c [s1,s2] = Const(c,dummyT) $ seq_tr' s1 $ seq_tr' s2;
*}

parse_translation {* [(SLstar,star_tr Lstar), (SRstar,star_tr Rstar)] *}
print_translation {* [(Lstar,star_tr' SLstar), (Rstar,star_tr' SRstar)] *}

defs
  strimp_def:    "P --< Q == [](P --> Q)"
  streqv_def:    "P >-< Q == (P --< Q) & (Q --< P)"


lemmas rewrite_rls = strimp_def streqv_def

lemma iffR:
    "[| $H,P |- $E,Q,$F;  $H,Q |- $E,P,$F |] ==> $H |- $E, P <-> Q, $F"
  apply (unfold iff_def)
  apply (assumption | rule conjR impR)+
  done

lemma iffL:
    "[| $H,$G |- $E,P,Q;  $H,Q,P,$G |- $E |] ==> $H, P <-> Q, $G |- $E"
  apply (unfold iff_def)
  apply (assumption | rule conjL impL basic)+
  done

lemmas safe_rls = basic conjL conjR disjL disjR impL impR notL notR iffL iffR
  and unsafe_rls = allR exL
  and bound_rls = allL exR

end
