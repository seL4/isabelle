(*  Title:      Pure/Syntax/parse_tree.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

TODO:
  move parsetree to parser.ML
  move pt_to_ast before ast_to_term (sextension.ML (?))
  delete this file
*)

signature PARSE_TREE =
sig
  structure Ast: AST
  structure Lexicon: LEXICON
  local open Ast Lexicon in
    datatype parsetree =
      Node of string * parsetree list |
      Tip of token
    val pt_to_ast: (string -> (ast list -> ast) option) -> parsetree -> ast
  end
end;

functor ParseTreeFun(structure Ast: AST and Lexicon: LEXICON): PARSE_TREE =
struct

structure Ast = Ast;
structure Lexicon = Lexicon;
open Ast Lexicon;


(* datatype parsetree *)

datatype parsetree =
  Node of string * parsetree list |
  Tip of token;


(* pt_to_ast *)

fun pt_to_ast trf pt =
  let
    fun trans a args =
      (case trf a of
        None => mk_appl (Constant a) args
      | Some f => f args handle exn
          => (writeln ("Error in parse ast translation for " ^ quote a); raise exn));

    fun ast_of (Node (a, pts)) = trans a (map ast_of pts)
      | ast_of (Tip tok) = Variable (str_of_token tok);
  in
    ast_of pt
  end;


end;

