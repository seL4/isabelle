(*  Title:      Pure/Syntax/xgram
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

External Grammar Representation

Changes:
  XGRAM: added Ast, changed XGram,
    renamed (XSymb, Prod, XGram) to (xsymb, prod, xgram)
  removed Symtab
TODO:
  prod, xsymb, xgram: 'a -> string (?)
*)

signature XGRAM =
sig
  structure Ast: AST
  datatype 'a xsymb =
    Terminal of 'a |
    Nonterminal of string * int |
    Space of string |
    Bg of int | Brk of int | En
  datatype 'a prod = Prod of string * ('a xsymb list) * string * int
  local open Ast in
    datatype 'a xgram =
      XGram of {
        roots: string list,
        prods: 'a prod list,
        consts: string list,
        parse_ast_translation: (string * (ast list -> ast)) list,
        parse_preproc: (ast -> ast) option,
        parse_rules: (ast * ast) list,
        parse_postproc: (ast -> ast) option,
        parse_translation: (string * (term list -> term)) list,
        print_translation: (string * (term list -> term)) list,
        print_preproc: (ast -> ast) option,
        print_rules: (ast * ast) list,
        print_postproc: (ast -> ast) option,
        print_ast_translation: (string * (ast list -> ast)) list}
  end
  val copy_pri: int
  val terminals: 'a xsymb list -> 'a list
  val nonterminals: 'a xsymb list -> string list
  val translate: ('a -> 'b) -> 'a xsymb list -> 'b xsymb list
end;

functor XGramFun(Ast: AST)(*: XGRAM*) =  (* FIXME *)
struct

structure Ast = Ast;
open Ast;

(** datatype 'a xgram **)

(* Terminal a: terminal a
   Nonterminal (s, p): nonterminal named s, require priority >= p
   Space s: some white space for printing
   Bg, Brk, En: see resp. routines in Pretty *)

datatype 'a xsymb =
  Terminal of 'a |
  Nonterminal of string * int |
  Space of string |
  Bg of int | Brk of int | En;


(* Prod (lhs, rhs, opn, p):
    lhs: name of nonterminal on the lhs of the production
    rhs: list of symbols on the rhs of the production
    opn: name of the corresponding Isabelle Const
    p: priority of this production, 0 <= p <= max_pri *)

datatype 'a prod = Prod of string * ('a xsymb list) * string * int;


datatype 'a xgram =
  XGram of {
    roots: string list,
    prods: 'a prod list,
    consts: string list,
    parse_ast_translation: (string * (ast list -> ast)) list,
    parse_preproc: (ast -> ast) option,
    parse_rules: (ast * ast) list,
    parse_postproc: (ast -> ast) option,
    parse_translation: (string * (term list -> term)) list,
    print_translation: (string * (term list -> term)) list,
    print_preproc: (ast -> ast) option,
    print_rules: (ast * ast) list,
    print_postproc: (ast -> ast) option,
    print_ast_translation: (string * (ast list -> ast)) list};



(** misc stuff **)

val copy_pri = ~1;  (* must be < all legal priorities, i.e. 0 *)

fun terminals [] = []
  | terminals (Terminal s :: sl) = s :: terminals sl
  | terminals (_ :: sl) = terminals sl;

fun nonterminals [] = []
  | nonterminals (Nonterminal (s, _) :: sl) = s :: nonterminals sl
  | nonterminals (_ :: sl) = nonterminals sl;

fun translate trfn =
  map
    (fn Terminal t => Terminal (trfn t)
      | Nonterminal s => Nonterminal s
      | Space s => Space s
      | Bg i => Bg i
      | Brk i => Brk i
      | En => En);


end;

