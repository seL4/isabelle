theory Spec_Check
imports Main
begin

ML_file "random.ML"
ML_file "property.ML"
ML_file "base_generator.ML"
ML_file "generator.ML"
ML_file "gen_construction.ML"
ML_file "spec_check.ML"
ML_file "output_style.ML"

setup {* Perl_Style.setup #> CMStyle.setup *}

end