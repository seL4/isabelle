theory Base
imports Pure
uses "../../antiquote_setup.ML"
begin

setup {*
  member (op =) (Session.id ()) "ZF" ? Pure_Thy.old_appl_syntax_setup
*}

declare [[thy_output_source]]

end
