(*  Title:      $Id$
    Author:     Lawrence C Paulson

Pointer Equality: for Standard ML of New Jersey 110.49 or later.

Thanks to Matthias Blume for providing InlineT.ptreql!
*)

CM.autoload "$smlnj/init/init.cmi";
val pointer_eq = InlineT.ptreql;
