(*  Title: 	ZF/bin
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Arithmetic on binary integers.
*)

BinFn = Integ + Bin +
consts
  bin_rec          :: "[i, i, i, [i,i,i]=>i] => i"
  integ_of_bin     :: "i=>i"
  bin_succ         :: "i=>i"
  bin_pred         :: "i=>i"
  bin_minus        :: "i=>i"
  bin_add,bin_mult :: "[i,i]=>i"

rules

  bin_rec_def
      "bin_rec(z,a,b,h) == \
\      Vrec(z, %z g. bin_case(a, b, %w x. h(w, x, g`w), z))"

  integ_of_bin_def 
      "integ_of_bin(w) == bin_rec(w, $#0, $~($#1), %w x r. $#x $+ r $+ r)"

  bin_succ_def
      "bin_succ(w0) == bin_rec(w0, Plus$$1, Plus, %w x r. cond(x, r$$0, w$$1))"

  bin_pred_def
      "bin_pred(w0) == \
\	bin_rec(w0, Minus, Minus$$0, %w x r. cond(x, w$$0, r$$1))"

  bin_minus_def
      "bin_minus(w0) == \
\	bin_rec(w0, Plus, Plus$$1, %w x r. cond(x, bin_pred(r$$0), r$$0))"

  bin_add_def
      "bin_add(v0,w0) == 			\
\       bin_rec(v0, 				\
\         lam w:bin. w,       		\
\         lam w:bin. bin_pred(w),	\
\         %v x r. lam w1:bin. 		\
\	           bin_rec(w1, v$$x, bin_pred(v$$x),	\
\		     %w y s. (r`cond(x and y, bin_succ(w), w)) \
\		             $$ (x xor y)))    ` w0"

  bin_mult_def
      "bin_mult(v0,w) == 			\
\       bin_rec(v0, Plus, bin_minus(w),		\
\         %v x r. cond(x, bin_add(r$$0,w), r$$0))"
end
