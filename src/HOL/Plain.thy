header {* Plain HOL *}

theory Plain
imports Datatype FunDef Record Extraction Divides
begin

text {*
  Plain bootstrap of fundamental HOL tools and packages; does not
  include @{text Hilbert_Choice}.
*}

instance option :: (finite) finite
  by default (simp add: insert_None_conv_UNIV [symmetric])

ML {* path_add "~~/src/HOL/Library" *}

end
