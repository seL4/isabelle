(*  Title: 	91/Modal/modal0
    ID:         $Id$
    Author: 	Martin Coen
    Copyright   1991  University of Cambridge
*)

Modal0 = LK +

consts
  box		:: "o=>o"	("[]_" [50] 50)
  dia		:: "o=>o"	("<>_" [50] 50)
  "--<",">-<"	:: "[o,o]=>o"	(infixr 25)
  "@Lstar"	:: "[sequence,sequence]=>prop"	("(_)|L>(_)" [6,6] 5)
  "@Rstar"	:: "[sequence,sequence]=>prop"	("(_)|R>(_)" [6,6] 5)
  Lstar,Rstar	:: "[sobj=>sobj,sobj=>sobj]=>prop"

rules
  (* Definitions *)

  strimp_def	"P --< Q == [](P --> Q)"
  streqv_def	"P >-< Q == (P --< Q) & (Q --< P)"
end

ML

local

  val Lstar = "Lstar";
  val Rstar = "Rstar";
  val SLstar = "@Lstar";
  val SRstar = "@Rstar";

  fun star_tr c [s1,s2] = Const(c,dummyT)$LK.seq_tr1 s1$LK.seq_tr1 s2;
  fun star_tr' c [Abs(_,_,s1),Abs(_,_,s2)] = 
         Const(c,dummyT) $ LK.seq_tr1' s1 $ LK.seq_tr1' s2;
in
val parse_translation = [(SLstar,star_tr Lstar), (SRstar,star_tr Rstar)];
val print_translation = [(Lstar,star_tr' SLstar), (Rstar,star_tr' SRstar)]
end;
