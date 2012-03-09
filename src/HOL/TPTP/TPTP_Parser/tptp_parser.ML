(*  Title:      HOL/TPTP/TPTP_Parser/tptp_parser.ML
    Author:     Nik Sultana, Cambridge University Computer Laboratory

An interface for a parser, generated using ML-Yacc, to parse TPTP languages.
*)


(* Build the parser structure *)

structure TPTPLrVals = TPTPLrValsFun(structure Token = LrParser.Token)
structure TPTPLex = TPTPLexFun(structure Tokens = TPTPLrVals.Tokens)
structure TPTPParser
  = JoinWithArg
     (structure ParserData = TPTPLrVals.ParserData
      structure Lex = TPTPLex
      structure LrParser = LrParser)


(* Parser interface *)
structure TPTP_Parser :
sig
  val parse_file : string -> TPTP_Syntax.tptp_problem
  val parse_expression : string -> string -> TPTP_Syntax.tptp_problem
  exception TPTP_PARSE_ERROR
end =
struct

exception TPTP_PARSE_ERROR

val LOOKAHEAD = 0 (*usually set to 15*)

local
  fun print_error file_name (msg, line, col) =
    error (file_name ^ "[" ^ Int.toString line ^ ":" ^ Int.toString col ^ "] " ^
      msg ^ "\n")
  fun parse lookahead grab file_name =
    TPTPParser.parse
      (lookahead,
       TPTPParser.makeLexer grab file_name,
       print_error file_name,
       file_name)
in
  fun parse_expression file_name expression =
    (*file_name only used in reporting error messages*)
    let
      val currentPos = Unsynchronized.ref 0
      fun grab n =
        if !currentPos = String.size expression then ""
        else
          let
            fun extractStr n =
              let
                val s = String.extract (expression, !currentPos, SOME n)
              in
                currentPos := !currentPos + n;
                s
              end
            val remaining = String.size expression - !currentPos
          in if remaining < n then extractStr remaining else extractStr n
          end
      val (tree, _ (*remainder*)) =
        parse LOOKAHEAD grab file_name
    in tree end

  fun parse_file' lookahead file_name =
    parse_expression
     file_name
     (File.open_input TextIO.inputAll (Path.explode file_name))
end

val parse_file = parse_file' LOOKAHEAD

end
