theory Base
imports Pure
begin

ML_file "../../antiquote_setup.ML"

setup {*
  Antiquote_Setup.setup #>
  member (op =) (Session.id ()) "ZF" ? Pure_Thy.old_appl_syntax_setup
*}

declare [[thy_output_source]]

end
