
header {* Install quickcheck of SML code generator *}

theory SML_Quickcheck
imports Main
begin

setup {*
  InductiveCodegen.quickcheck_setup #>
  Quickcheck.add_generator ("SML", Codegen.test_term)
*}

end
