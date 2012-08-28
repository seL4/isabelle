theory Setup
imports Main
begin

ML_file "../../antiquote_setup.ML"
ML_file "../../more_antiquote.ML"

setup {* Antiquote_Setup.setup #> More_Antiquote.setup *}

end