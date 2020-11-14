(*  Title:      Pure/Sessions.thy
    Author:     Makarius

PIDE markup for session ROOT.
*)

theory Sessions
  imports Pure
  keywords "session" :: thy_decl
    and "description" "directories" "options" "sessions" "theories"
      "document_theories" "document_files" "export_files" :: quasi_command
    and "global"
begin

ML \<open>
  Outer_Syntax.command \<^command_keyword>\<open>session\<close> "PIDE markup for session ROOT"
    Sessions.command_parser;
\<close>

end
