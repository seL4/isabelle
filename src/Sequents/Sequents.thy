(*  Title: 	Sequents/Sequents.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Classical First-Order Sequent Calculus
*)

Sequents = Pure +

types
  o 

arities
  o :: logic


(* Sequences *)

types
 seq'

consts
 SeqO'         :: "[o,seq']=>seq'"
 Seq1'         :: "o=>seq'"
    

(* concrete syntax *)

types
  seq seqobj seqcont


syntax
 SeqEmp         :: "seq"                                ("")
 SeqApp         :: "[seqobj,seqcont] => seq"            ("__")

 SeqContEmp     :: "seqcont"                            ("")
 SeqContApp     :: "[seqobj,seqcont] => seqcont"        (",/ __")
  
 SeqO           :: "o => seqobj"                        ("_")
 SeqId          :: "id => seqobj"                       ("$_")
 SeqVar         :: "var => seqobj"                      ("$_")

types
    
 single_seqe = "[seq,seqobj] => prop"
 single_seqi = "[seq'=>seq',seq'=>seq'] => prop"
 two_seqi = "[seq'=>seq', seq'=>seq'] => prop"
 two_seqe = "[seq, seq] => prop"
 three_seqi = "[seq'=>seq', seq'=>seq', seq'=>seq'] => prop"
 three_seqe = "[seq, seq, seq] => prop"
 four_seqi = "[seq'=>seq', seq'=>seq', seq'=>seq', seq'=>seq'] => prop"
 four_seqe = "[seq, seq, seq, seq] => prop"

end

ML

(* parse translation for sequences *)

fun abs_seq' t = Abs("s", Type("seq'",[]), t);

fun seqobj_tr(Const("SeqO",_) $ f) = Const("SeqO'",dummyT) $ f |
    seqobj_tr(_ $ i) = i;
    
fun seqcont_tr(Const("SeqContEmp",_)) = Bound 0 |
    seqcont_tr(Const("SeqContApp",_) $ so $ sc) = 
      (seqobj_tr so) $ (seqcont_tr sc);

fun seq_tr(Const("SeqEmp",_)) = abs_seq'(Bound 0) |
    seq_tr(Const("SeqApp",_) $ so $ sc) = 
      abs_seq'(seqobj_tr(so) $ seqcont_tr(sc));


fun singlobj_tr(Const("SeqO",_) $ f) =
    abs_seq' ((Const("SeqO'",dummyT) $ f) $ Bound 0);
    

    
(* print translation for sequences *)

fun seqcont_tr' (Bound 0) = 
      Const("SeqContEmp",dummyT) |
    seqcont_tr' (Const("SeqO'",_) $ f $ s) =
      Const("SeqContApp",dummyT) $ 
      (Const("SeqO",dummyT) $ f) $ 
      (seqcont_tr' s) |
(*    seqcont_tr' ((a as Abs(_,_,_)) $ s)= 
      seqcont_tr'(betapply(a,s)) | *)
    seqcont_tr' (i $ s) = 
      Const("SeqContApp",dummyT) $ 
      (Const("SeqId",dummyT) $ i) $ 
      (seqcont_tr' s);

fun seq_tr' s =
    let fun seq_itr' (Bound 0) = 
              Const("SeqEmp",dummyT) |
            seq_itr' (Const("SeqO'",_) $ f $ s) =
              Const("SeqApp",dummyT) $ 
              (Const("SeqO",dummyT) $ f) $ (seqcont_tr' s) |
(*            seq_itr' ((a as Abs(_,_,_)) $ s) =
              seq_itr'(betapply(a,s)) |    *)
            seq_itr' (i $ s) =
              Const("SeqApp",dummyT) $ 
              (Const("SeqId",dummyT) $ i) $ 
              (seqcont_tr' s)
    in case s of 
         Abs(_,_,t) => seq_itr' t |
         _ => s $ (Bound 0)
    end;




fun single_tr c [s1,s2] =
    Const(c,dummyT) $ seq_tr s1 $ singlobj_tr s2;

fun two_seq_tr c [s1,s2] =
    Const(c,dummyT) $ seq_tr s1 $ seq_tr s2;

fun three_seq_tr c [s1,s2,s3] =
    Const(c,dummyT) $ seq_tr s1 $ seq_tr s2 $ seq_tr s3;

fun four_seq_tr c [s1,s2,s3,s4] =
    Const(c,dummyT) $ seq_tr s1 $ seq_tr s2 $ seq_tr s3 $ seq_tr s4;


fun singlobj_tr'(Const("SeqO'",_) $ fm) = fm |
    singlobj_tr'(id) = Const("@SeqId",dummyT) $ id;


fun single_tr' c [s1, s2] =
(Const (c, dummyT) $ seq_tr' s1 $ seq_tr' s2 ); 


fun two_seq_tr' c [s1, s2] =
  Const (c, dummyT) $ seq_tr' s1 $ seq_tr' s2; 

fun three_seq_tr' c [s1, s2, s3] =
  Const (c, dummyT) $ seq_tr' s1 $ seq_tr' s2 $ seq_tr' s3; 

fun four_seq_tr' c [s1, s2, s3, s4] =
  Const (c, dummyT) $ seq_tr' s1 $ seq_tr' s2 $ seq_tr' s3 $ seq_tr' s4; 


			 
