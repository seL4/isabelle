(*  Title:      HOLCF/ex/Fix2.thy
    ID:         $Id$
    Author:     Franz Regensburger

Show that fix is the unique least fixed-point operator.
From axioms gix1_def,gix2_def it follows that fix = gix
*)

theory Fix2
imports HOLCF
begin

consts
  gix     :: "('a->'a)->'a"

axioms
  gix1_def: "F$(gix$F) = gix$F"
  gix2_def: "F$y=y ==> gix$F << y"

ML {* use_legacy_bindings (the_context ()) *}

end
