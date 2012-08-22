(*  Title:      Sequents/Sequents.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header {* Parsing and pretty-printing of sequences *}

theory Sequents
imports Pure
begin

setup Pure_Thy.old_appl_syntax_setup

declare [[unify_trace_bound = 20, unify_search_bound = 40]]

typedecl o

(* Sequences *)

typedecl
 seq'

consts
 SeqO'         :: "[o,seq']=>seq'"
 Seq1'         :: "o=>seq'"


(* concrete syntax *)

nonterminal seq and seqobj and seqcont

syntax
 "_SeqEmp"         :: seq                                  ("")
 "_SeqApp"         :: "[seqobj,seqcont] => seq"            ("__")

 "_SeqContEmp"     :: seqcont                              ("")
 "_SeqContApp"     :: "[seqobj,seqcont] => seqcont"        (",/ __")

 "_SeqO"           :: "o => seqobj"                        ("_")
 "_SeqId"          :: "'a => seqobj"                       ("$_")

type_synonym single_seqe = "[seq,seqobj] => prop"
type_synonym single_seqi = "[seq'=>seq',seq'=>seq'] => prop"
type_synonym two_seqi = "[seq'=>seq', seq'=>seq'] => prop"
type_synonym two_seqe = "[seq, seq] => prop"
type_synonym three_seqi = "[seq'=>seq', seq'=>seq', seq'=>seq'] => prop"
type_synonym three_seqe = "[seq, seq, seq] => prop"
type_synonym four_seqi = "[seq'=>seq', seq'=>seq', seq'=>seq', seq'=>seq'] => prop"
type_synonym four_seqe = "[seq, seq, seq, seq] => prop"
type_synonym sequence_name = "seq'=>seq'"


syntax
  (*Constant to allow definitions of SEQUENCES of formulas*)
  "_Side"        :: "seq=>(seq'=>seq')"     ("<<(_)>>")

ML {*

(* parse translation for sequences *)

fun abs_seq' t = Abs ("s", Type (@{type_name seq'}, []), t);

fun seqobj_tr (Const (@{syntax_const "_SeqO"}, _) $ f) =
      Const (@{const_syntax SeqO'}, dummyT) $ f
  | seqobj_tr (_ $ i) = i;

fun seqcont_tr (Const (@{syntax_const "_SeqContEmp"}, _)) = Bound 0
  | seqcont_tr (Const (@{syntax_const "_SeqContApp"}, _) $ so $ sc) =
      seqobj_tr so $ seqcont_tr sc;

fun seq_tr (Const (@{syntax_const "_SeqEmp"}, _)) = abs_seq' (Bound 0)
  | seq_tr (Const (@{syntax_const "_SeqApp"}, _) $ so $ sc) =
      abs_seq'(seqobj_tr so $ seqcont_tr sc);

fun singlobj_tr (Const (@{syntax_const "_SeqO"},_) $ f) =
  abs_seq' ((Const (@{const_syntax SeqO'}, dummyT) $ f) $ Bound 0);


(* print translation for sequences *)

fun seqcont_tr' (Bound 0) =
      Const (@{syntax_const "_SeqContEmp"}, dummyT)
  | seqcont_tr' (Const (@{const_syntax SeqO'}, _) $ f $ s) =
      Const (@{syntax_const "_SeqContApp"}, dummyT) $
        (Const (@{syntax_const "_SeqO"}, dummyT) $ f) $ seqcont_tr' s
  | seqcont_tr' (i $ s) =
      Const (@{syntax_const "_SeqContApp"}, dummyT) $
        (Const (@{syntax_const "_SeqId"}, dummyT) $ i) $ seqcont_tr' s;

fun seq_tr' s =
  let
    fun seq_itr' (Bound 0) = Const (@{syntax_const "_SeqEmp"}, dummyT)
      | seq_itr' (Const (@{const_syntax SeqO'}, _) $ f $ s) =
          Const (@{syntax_const "_SeqApp"}, dummyT) $
            (Const (@{syntax_const "_SeqO"}, dummyT) $ f) $ seqcont_tr' s
      | seq_itr' (i $ s) =
          Const (@{syntax_const "_SeqApp"}, dummyT) $
            (Const (@{syntax_const "_SeqId"}, dummyT) $ i) $ seqcont_tr' s
  in
    case s of
      Abs (_, _, t) => seq_itr' t
    | _ => s $ Bound 0
  end;


fun single_tr c [s1, s2] =
  Const (c, dummyT) $ seq_tr s1 $ singlobj_tr s2;

fun two_seq_tr c [s1, s2] =
  Const (c, dummyT) $ seq_tr s1 $ seq_tr s2;

fun three_seq_tr c [s1, s2, s3] =
  Const (c, dummyT) $ seq_tr s1 $ seq_tr s2 $ seq_tr s3;

fun four_seq_tr c [s1, s2, s3, s4] =
  Const (c, dummyT) $ seq_tr s1 $ seq_tr s2 $ seq_tr s3 $ seq_tr s4;


fun singlobj_tr' (Const (@{const_syntax SeqO'},_) $ fm) = fm
  | singlobj_tr' id = Const (@{syntax_const "_SeqId"}, dummyT) $ id;


fun single_tr' c [s1, s2] =
  Const (c, dummyT) $ seq_tr' s1 $ seq_tr' s2;

fun two_seq_tr' c [s1, s2] =
  Const (c, dummyT) $ seq_tr' s1 $ seq_tr' s2;

fun three_seq_tr' c [s1, s2, s3] =
  Const (c, dummyT) $ seq_tr' s1 $ seq_tr' s2 $ seq_tr' s3;

fun four_seq_tr' c [s1, s2, s3, s4] =
  Const (c, dummyT) $ seq_tr' s1 $ seq_tr' s2 $ seq_tr' s3 $ seq_tr' s4;



(** for the <<...>> notation **)

fun side_tr [s1] = seq_tr s1;
*}

parse_translation {* [(@{syntax_const "_Side"}, side_tr)] *}

ML_file "prover.ML"

end

