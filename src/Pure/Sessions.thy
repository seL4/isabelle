(*  Title:      Pure/Sessions.thy
    Author:     Makarius

PIDE markup for session ROOT.
*)

theory Sessions
  imports Pure
  keywords "chapter_definition" "session" :: thy_decl
    and "description" "directories" "options" "sessions" "theories"
      "document_theories" "document_files" "export_files" :: quasi_command
    and "global"
begin

ML \<open>
  Outer_Syntax.command \<^command_keyword>\<open>chapter_definition\<close> "PIDE markup for session ROOT"
    Sessions.chapter_definition_parser;

  Outer_Syntax.command \<^command_keyword>\<open>session\<close> "PIDE markup for session ROOT"
    Sessions.session_parser;
\<close>

end
