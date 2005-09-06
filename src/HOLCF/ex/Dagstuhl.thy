(* $Id$ *)

theory Dagstuhl
imports Stream
begin

consts
  y  :: "'a"

constdefs
  YS :: "'a stream"
  "YS == fix$(LAM x. y && x)"
  YYS :: "'a stream"
  "YYS == fix$(LAM z. y && y && z)"

ML {* use_legacy_bindings (the_context ()) *}

end

