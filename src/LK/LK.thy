(*  Title: 	LK/lk.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Classical First-Order Sequent Calculus
*)

LK = Pure +

classes term < logic

default term

types
 o sequence seqobj seqcont sequ sobj

arities
 o :: logic

consts
 True,False	:: "o"
 "="		:: "['a,'a] => o"	(infixl 50)
 "Not"		:: "o => o"		("~ _" [40] 40)
 "&"		:: "[o,o] => o"		(infixr 35)
 "|"		:: "[o,o] => o"		(infixr 30)
 "-->","<->"	:: "[o,o] => o"		(infixr 25)
 The		:: "('a => o) => 'a"	(binder "THE " 10)
 All		:: "('a => o) => o"	(binder "ALL " 10)
 Ex		:: "('a => o) => o"	(binder "EX " 10)

 (*Representation of sequents*)
 Trueprop	:: "[sobj=>sobj,sobj=>sobj] => prop"
 Seqof		:: "o => sobj=>sobj"
 "@Trueprop"	:: "[sequence,sequence] => prop" ("((_)/ |- (_))" [6,6] 5)
 "@MtSeq"	:: "sequence"				("" [] 1000)
 "@NmtSeq"	:: "[seqobj,seqcont] => sequence"	("__" [] 1000)
 "@MtSeqCont"	:: "seqcont"				("" [] 1000)
 "@SeqCont"	:: "[seqobj,seqcont] => seqcont"	(",/ __" [] 1000)
 ""		:: "o => seqobj"			("_" [] 1000)
 "@SeqId"	:: "id => seqobj"			("$_" [] 1000)
 "@SeqVar"	:: "var => seqobj"			("$_")

rules
  (*Structural rules*)

  basic	"$H, P, $G |- $E, P, $F"

  thinR	"$H |- $E, $F ==> $H |- $E, P, $F"
  thinL	"$H, $G |- $E ==> $H, P, $G |- $E"

  cut	"[| $H |- $E, P;  $H, P |- $E |] ==> $H |- $E"

  (*Propositional rules*)

  conjR	"[| $H|- $E, P, $F;  $H|- $E, Q, $F |] ==> $H|- $E, P&Q, $F"
  conjL	"$H, P, Q, $G |- $E ==> $H, P & Q, $G |- $E"

  disjR	"$H |- $E, P, Q, $F ==> $H |- $E, P|Q, $F"
  disjL	"[| $H, P, $G |- $E;  $H, Q, $G |- $E |] ==> $H, P|Q, $G |- $E"

  impR	"$H, P |- $E, Q, $F ==> $H |- $E, P-->Q, $F"
  impL	"[| $H,$G |- $E,P;  $H, Q, $G |- $E |] ==> $H, P-->Q, $G |- $E"

  notR	"$H, P |- $E, $F ==> $H |- $E, ~P, $F"
  notL	"$H, $G |- $E, P ==> $H, ~P, $G |- $E"

  FalseL "$H, False, $G |- $E"

  True_def "True == False-->False"
  iff_def  "P<->Q == (P-->Q) & (Q-->P)"

  (*Quantifiers*)

  allR	"(!!x.$H |- $E, P(x), $F) ==> $H |- $E, ALL x.P(x), $F"
  allL	"$H, P(x), $G, ALL x.P(x) |- $E ==> $H, ALL x.P(x), $G |- $E"

  exR	"$H |- $E, P(x), $F, EX x.P(x) ==> $H |- $E, EX x.P(x), $F"
  exL	"(!!x.$H, P(x), $G |- $E) ==> $H, EX x.P(x), $G |- $E"

  (*Equality*)

  refl	"$H |- $E, a=a, $F"
  sym   "$H |- $E, a=b, $F ==> $H |- $E, b=a, $F"
  trans "[| $H|- $E, a=b, $F;  $H|- $E, b=c, $F |] ==> $H|- $E, a=c, $F"


  (*Descriptions*)

  The "[| $H |- $E, P(a), $F;  !!x.$H, P(x) |- $E, x=a, $F |] ==> 
          $H |- $E, P(THE x.P(x)), $F"
end

ML

(*Abstract over "sobj" -- representation of a sequence of formulae *)
fun abs_sobj t = Abs("sobj", Type("sobj",[]), t);

(*Representation of empty sequence*)
val Sempty =  abs_sobj (Bound 0);

fun seq_obj_tr(Const("@SeqId",_)$id) = id |
    seq_obj_tr(Const("@SeqVar",_)$id) = id |
    seq_obj_tr(fm) = Const("Seqof",dummyT)$fm;

fun seq_tr(_$obj$seq) = seq_obj_tr(obj)$seq_tr(seq) |
    seq_tr(_) = Bound 0;

fun seq_tr1(Const("@MtSeq",_)) = Sempty |
    seq_tr1(seq) = abs_sobj(seq_tr seq);

fun true_tr[s1,s2] = Const("Trueprop",dummyT)$seq_tr1 s1$seq_tr1 s2;

fun seq_obj_tr'(Const("Seqof",_)$fm) = fm |
    seq_obj_tr'(id) = Const("@SeqId",dummyT)$id;

fun seq_tr'(obj$sq,C) =
      let val sq' = case sq of
            Bound 0 => Const("@MtSeqCont",dummyT) |
            _ => seq_tr'(sq,Const("@SeqCont",dummyT))
      in C $ seq_obj_tr' obj $ sq' end;

fun seq_tr1'(Bound 0) = Const("@MtSeq",dummyT) |
    seq_tr1' s = seq_tr'(s,Const("@NmtSeq",dummyT));

fun true_tr'[Abs(_,_,s1),Abs(_,_,s2)] =
      Const("@Trueprop",dummyT)$seq_tr1' s1$seq_tr1' s2;

val parse_translation = [("@Trueprop",true_tr)];
val print_translation = [("Trueprop",true_tr')];
