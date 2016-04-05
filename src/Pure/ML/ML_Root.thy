(*  Title:      Pure/ML/ML_Root.thy
    Author:     Makarius

Support for ML project ROOT file, with imitation of ML "use" commands.
*)

theory ML_Root
imports "../Pure"
keywords "use" "use_debug" "use_no_debug" :: thy_load
  and "use_thy" :: thy_load
begin

ML \<open>
local

val _ =
  Outer_Syntax.command @{command_keyword use}
    "read and evaluate Isabelle/ML or SML file"
    (Resources.parse_files "use" >> ML_File.use NONE);

val _ =
  Outer_Syntax.command @{command_keyword use_debug}
    "read and evaluate Isabelle/ML or SML file (with debugger information)"
    (Resources.parse_files "use_debug" >> ML_File.use (SOME true));

val _ =
  Outer_Syntax.command @{command_keyword use_no_debug}
    "read and evaluate Isabelle/ML or SML file (no debugger information)"
    (Resources.parse_files "use_no_debug" >> ML_File.use (SOME false));

val _ =
  Outer_Syntax.command @{command_keyword use_thy} "undefined dummy command"
    (Scan.succeed (Toplevel.keep (fn _ => error "Undefined command 'use_thy'")));

in end
\<close>

end
