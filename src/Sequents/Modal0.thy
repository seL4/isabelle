(*  Title:      Modal/modal0
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1991  University of Cambridge
*)

Modal0 = LK +

consts
  box           :: "o=>o"       ("[]_" [50] 50)
  dia           :: "o=>o"       ("<>_" [50] 50)
  "--<",">-<"   :: "[o,o]=>o"   (infixr 25)
  "@Lstar"      :: "two_seqe"   ("(_)|L>(_)" [6,6] 5)
  "@Rstar"      :: "two_seqe"   ("(_)|R>(_)" [6,6] 5)
  Lstar,Rstar   :: "two_seqi"

rules
  (* Definitions *)

  strimp_def    "P --< Q == [](P --> Q)"
  streqv_def    "P >-< Q == (P --< Q) & (Q --< P)"
end

ML

local

  val Lstar = "Lstar";
  val Rstar = "Rstar";
  val SLstar = "@Lstar";
  val SRstar = "@Rstar";

  fun star_tr c [s1,s2] =
      Const(c,dummyT)$Sequents.seq_tr s1$Sequents.seq_tr s2;
  fun star_tr' c [s1,s2] = 
      Const(c,dummyT) $ Sequents.seq_tr' s1 $ Sequents.seq_tr' s2;
in
val parse_translation = [(SLstar,star_tr Lstar), (SRstar,star_tr Rstar)];
val print_translation = [(Lstar,star_tr' SLstar), (Rstar,star_tr' SRstar)]
end;
