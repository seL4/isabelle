(*  Title:      HOL/Import/MakeEqual.thy
    ID:         $Id$
    Author:     Sebastian Skalberg (TU Muenchen)
*)

theory MakeEqual = Main
  files "shuffler.ML":

setup Shuffler.setup

lemma conj_norm [shuffle_rule]: "(A & B ==> PROP C) == ([| A ; B |] ==> PROP C)"
proof
  assume "A & B ==> PROP C" A B
  thus "PROP C"
    by auto
next
  assume "[| A; B |] ==> PROP C" "A & B"
  thus "PROP C"
    by auto
qed

lemma imp_norm [shuffle_rule]: "(Trueprop (A --> B)) == (A ==> B)"
proof
  assume "A --> B" A
  thus B ..
next
  assume "A ==> B"
  thus "A --> B"
    by auto
qed

lemma all_norm [shuffle_rule]: "(Trueprop (ALL x. P x)) == (!!x. P x)"
proof
  fix x
  assume "ALL x. P x"
  thus "P x" ..
next
  assume "!!x. P x"
  thus "ALL x. P x"
    ..
qed

lemma ex_norm [shuffle_rule]: "(EX x. P x ==> PROP Q) == (!!x. P x ==> PROP Q)"
proof
  fix x
  assume ex: "EX x. P x ==> PROP Q"
  assume "P x"
  hence "EX x. P x" ..
  with ex show "PROP Q" .
next
  assume allx: "!!x. P x ==> PROP Q"
  assume "EX x. P x"
  hence p: "P (SOME x. P x)"
    ..
  from allx
  have "P (SOME x. P x) ==> PROP Q"
    .
  with p
  show "PROP Q"
    by auto
qed

lemma eq_norm [shuffle_rule]: "Trueprop (t = u) == (t == u)"
proof
  assume "t = u"
  thus "t == u" by simp
next
  assume "t == u"
  thus "t = u"
    by simp
qed

end
