(*  Title:      HOL/Types_To_Sets/Examples/Unoverload_Def.thy
    Author:     Fabian Immler, CMU
*)
theory Unoverload_Def
  imports
    "../Types_To_Sets"
    Complex_Main
begin

unoverload_definition closed_def
  and compact_eq_Heine_Borel
  and cauchy_filter_def
  and Cauchy_uniform
  and nhds_def
  and complete_uniform
  and module_def
  and vector_space_def
  and module_hom_axioms_def
  and module_hom_def
  and VS_linear: Vector_Spaces.linear_def
  and linear_def

end