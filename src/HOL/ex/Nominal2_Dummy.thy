header \<open>Dummy theory to anticipate AFP/Nominal2 keywords\<close>  (* Proof General legacy *)

theory Nominal2_Dummy
imports Main
keywords
  "nominal_datatype" :: thy_decl and
  "nominal_function" "nominal_inductive" "nominal_termination" :: thy_goal and
  "atom_decl" "equivariance" :: thy_decl and
  "avoids" "binds"
begin

ML \<open>
Outer_Syntax.command @{command_spec "nominal_datatype"} "dummy" Scan.fail;
Outer_Syntax.command @{command_spec "nominal_function"} "dummy" Scan.fail;
Outer_Syntax.command @{command_spec "nominal_inductive"} "dummy" Scan.fail;
Outer_Syntax.command @{command_spec "nominal_termination"} "dummy" Scan.fail;
Outer_Syntax.command @{command_spec "atom_decl"} "dummy" Scan.fail;
Outer_Syntax.command @{command_spec "equivariance"} "dummy" Scan.fail;
\<close>

end

