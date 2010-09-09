
header {* Install quickcheck of SML code generator *}

theory SML_Quickcheck
imports Main
begin

setup {*
  Inductive_Codegen.quickcheck_setup #>
  Context.theory_map (Quickcheck.add_generator ("SML", Codegen.test_term))
*}

end
