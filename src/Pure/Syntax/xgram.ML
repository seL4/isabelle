(*  Title:      Pure/Syntax/xgram.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

External grammar representation (internal interface).

TODO:
  prod, xsymb: 'a --> string
  Terminal --> Literal, Nonterminal --> Argument (?)
*)

signature XGRAM =
sig
  structure Ast: AST
  local open Ast in
    datatype 'a xsymb =
      Terminal of 'a |
      Nonterminal of string * int |
      Space of string |
      Bg of int | Brk of int | En
    datatype 'a prod = Prod of string * ('a xsymb list) * string * int
    val max_pri: int
    val chain_pri: int
    val literals_of: string prod list -> string list
    datatype xgram =
      XGram of {
        roots: string list,
        prods: string prod list,
        consts: string list,
        parse_ast_translation: (string * (ast list -> ast)) list,
        parse_rules: (ast * ast) list,
        parse_translation: (string * (term list -> term)) list,
        print_translation: (string * (term list -> term)) list,
        print_rules: (ast * ast) list,
        print_ast_translation: (string * (ast list -> ast)) list}
  end
end;

functor XGramFun(Ast: AST): XGRAM =
struct

structure Ast = Ast;
open Ast;


(** datatype prod **)

(*Terminal s: literal token s
  Nonterminal (s, p): nonterminal s requiring priority >= p, or valued token
  Space s: some white space for printing
  Bg, Brk, En: blocks and breaks for pretty printing*)

datatype 'a xsymb =
  Terminal of 'a |
  Nonterminal of string * int |
  Space of string |
  Bg of int | Brk of int | En;


(*Prod (lhs, syms, c, p):
    lhs: name of nonterminal on the lhs of the production
    syms: list of symbols on the rhs of the production
    c: head of parse tree
    p: priority of this production*)

datatype 'a prod = Prod of string * ('a xsymb list) * string * int;

val max_pri = 1000;   (*maximum legal priority*)
val chain_pri = ~1;   (*dummy for chain productions*)


(* literals_of *)

fun literals_of prods =
  let
    fun lits_of (Prod (_, syn, _, _)) =
      mapfilter (fn Terminal s => Some s | _ => None) syn;
  in
    distinct (flat (map lits_of prods))
  end;



(** datatype xgram **)

datatype xgram =
  XGram of {
    roots: string list,
    prods: string prod list,
    consts: string list,
    parse_ast_translation: (string * (ast list -> ast)) list,
    parse_rules: (ast * ast) list,
    parse_translation: (string * (term list -> term)) list,
    print_translation: (string * (term list -> term)) list,
    print_rules: (ast * ast) list,
    print_ast_translation: (string * (ast list -> ast)) list};


end;

