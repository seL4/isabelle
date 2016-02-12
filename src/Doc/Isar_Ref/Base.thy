(*:maxLineLen=78:*)

theory Base
imports Pure
keywords "\<proof>" :: "qed" % "proof"
begin

ML \<open>
  Outer_Syntax.command @{command_keyword "\<proof>"} "dummy proof"
    (Scan.succeed Isar_Cmd.skip_proof);
\<close>

ML_file "../antiquote_setup.ML"

end
