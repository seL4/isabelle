(*  Title:      CCL/ex/Stream.thy
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header {* Programs defined over streams *}

theory Stream
imports List
begin

consts
  iter1   ::  "[i=>i,i]=>i"
  iter2   ::  "[i=>i,i]=>i"

defs

  iter1_def:   "iter1(f,a) == letrec iter x be x$iter(f(x)) in iter(a)"
  iter2_def:   "iter2(f,a) == letrec iter x be x$map(f,iter(x)) in iter(a)"

ML {* use_legacy_bindings (the_context ()) *}

end
