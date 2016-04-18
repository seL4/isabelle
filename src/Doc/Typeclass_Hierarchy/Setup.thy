theory Setup
imports Complex_Main "~~/src/HOL/Library/Lattice_Syntax"
begin

ML_file "../antiquote_setup.ML"
ML_file "../more_antiquote.ML"

attribute_setup all =
  \<open>Scan.succeed (Thm.rule_attribute [] (K Drule.forall_intr_vars))\<close>
  "quantified schematic vars"

setup \<open>Config.put_global Printer.show_type_emphasis false\<close>

declare [[show_sorts]]

end
