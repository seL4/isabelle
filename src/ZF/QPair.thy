(*  Title:      ZF/qpair.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Quine-inspired ordered pairs and disjoint sums, for non-well-founded data
structures in ZF.  Does not precisely follow Quine's construction.  Thanks
to Thomas Forster for suggesting this approach!

W. V. Quine, On Ordered Pairs and Relations, in Selected Logic Papers,
1966.
*)

QPair = Sum +

consts
  QPair     :: "[i, i] => i"                      ("<(_;/ _)>")
  qfst,qsnd :: "i => i"
  qsplit    :: "[[i, i] => 'a, i] => 'a::logic"  (*for pattern-matching*)
  qconverse :: "i => i"
  QSigma    :: "[i, i => i] => i"

  "<+>"     :: "[i,i]=>i"                         (infixr 65)
  QInl,QInr :: "i=>i"
  qcase     :: "[i=>i, i=>i, i]=>i"

syntax
  "@QSUM"   :: "[idt, i, i] => i"               ("(3QSUM _:_./ _)" 10)
  "<*>"     :: "[i, i] => i"                      (infixr 80)

translations
  "QSUM x:A. B"  => "QSigma(A, %x. B)"
  "A <*> B"      => "QSigma(A, _K(B))"


defs
  QPair_def       "<a;b> == a+b"
  qfst_def        "qfst(p) == THE a. EX b. p=<a;b>"
  qsnd_def        "qsnd(p) == THE b. EX a. p=<a;b>"
  qsplit_def      "qsplit(c,p) == c(qfst(p), qsnd(p))"

  qconverse_def   "qconverse(r) == {z. w:r, EX x y. w=<x;y> & z=<y;x>}"
  QSigma_def      "QSigma(A,B)  ==  UN x:A. UN y:B(x). {<x;y>}"

  qsum_def        "A <+> B      == ({0} <*> A) Un ({1} <*> B)"
  QInl_def        "QInl(a)      == <0;a>"
  QInr_def        "QInr(b)      == <1;b>"
  qcase_def       "qcase(c,d)   == qsplit(%y z. cond(y, d(z), c(z)))"
end

ML

val print_translation =
  [("QSigma", dependent_tr' ("@QSUM", "op <*>"))];
