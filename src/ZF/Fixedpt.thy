(*  Title: 	ZF/fixedpt.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Least and greatest fixed points
*)

Fixedpt = ZF + "domrange" +
consts
  bnd_mono    :: "[i,i=>i]=>o"
  lfp, gfp    :: "[i,i=>i]=>i"

defs
  (*monotone operator from Pow(D) to itself*)
  bnd_mono_def 
      "bnd_mono(D,h) == h(D)<=D & (ALL W X. W<=X --> X<=D --> h(W) <= h(X))"

  lfp_def     "lfp(D,h) == Inter({X: Pow(D). h(X) <= X})"

  gfp_def     "gfp(D,h) == Union({X: Pow(D). X <= h(X)})"

end
