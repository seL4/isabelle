(* $Id$ *)

theory If
imports FOLP
begin

constdefs
  "if" :: "[o,o,o]=>o"
  "if(P,Q,R) == P&Q | ~P&R"

ML {* use_legacy_bindings (the_context ()) *}

end
