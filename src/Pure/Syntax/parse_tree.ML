(*  Title:      Pure/Syntax/parse_tree
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
*)

signature PARSE_TREE =
sig
  structure Lexicon: LEXICON
  structure Ast: AST
  local open Lexicon Ast in
    datatype ParseTree =
      Node of string * ParseTree list |
      Tip of Token
    val mk_pt: string * ParseTree list -> ParseTree
    val pt_to_ast: (string -> (ast list -> ast) option) -> ParseTree -> ast
  end
end;

functor ParseTreeFun(structure Lexicon: LEXICON and Ast: AST): PARSE_TREE =
struct

structure Lexicon = Lexicon;
structure Ast = Ast;
open Lexicon Ast;


(* datatype ParseTree *)  (* FIXME rename *)

datatype ParseTree =
  Node of string * ParseTree list |
  Tip of Token;


(* mk_pt *)

fun mk_pt("", [pt]) = pt
  | mk_pt("", _) = error "mk_pt: funny copy op in parse tree"
  | mk_pt(s, ptl) = Node (s, ptl);


(* pt_to_ast *)

fun pt_to_ast trf pt =
  let
    fun trans a args =
      (case trf a of
        None => mk_appl (Constant a) args
      | Some f =>
          (f args) handle _ => error ("pt_to_ast: error in translation for " ^ a));

    fun trav (Node (a, pts)) = trans a (map trav pts)
      | trav (Tip (IdentSy x)) = Variable x
      | trav (Tip (VarSy xi)) = Variable (string_of_vname xi)
      | trav (Tip (TFreeSy x)) = Variable x
      | trav (Tip (TVarSy xi)) = Variable (string_of_vname xi)
      | trav (Tip _) = error "pt_to_ast: unexpected token in parse tree";
  in
    trav pt
  end;


end;

