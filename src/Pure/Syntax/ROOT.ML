(*  Title:      Pure/Syntax/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

This file builds the syntax module.
*)

use "pretty.ML";
use "lexicon.ML";
use "ast.ML";
use "syn_ext.ML";
use "parser.ML";
use "type_ext.ML";
use "syn_trans.ML";
use "mixfix.ML";
use "printer.ML";
use "syntax.ML";

structure PrivateSyntax =
struct
  structure Pretty = PrettyFun();
  structure Lexicon = LexiconFun();
  structure Scanner: SCANNER = Lexicon;
  structure Ast = AstFun(Pretty);
  structure SynExt = SynExtFun(structure Lexicon = Lexicon and Ast = Ast);
  structure Parser = ParserFun(structure Symtab = Symtab and Lexicon = Lexicon
    and SynExt = SynExt);
  structure TypeExt = TypeExtFun(structure Lexicon = Lexicon and SynExt = SynExt);
  structure SynTrans = SynTransFun(structure TypeExt = TypeExt and Parser = Parser);
  structure Mixfix = MixfixFun(structure Lexicon = Lexicon and SynExt = SynExt and
    SynTrans = SynTrans);
  structure Printer = PrinterFun(structure Symtab = Symtab and TypeExt = TypeExt
    and SynTrans = SynTrans);
  structure Syntax = SyntaxFun(structure Symtab = Symtab and TypeExt = TypeExt
    and SynTrans = SynTrans and Mixfix = Mixfix and Printer = Printer);
  structure BasicSyntax: BASIC_SYNTAX = Syntax;
end;

structure Pretty = PrivateSyntax.Pretty;
structure Scanner = PrivateSyntax.Scanner;
structure Syntax = PrivateSyntax.Syntax;
structure BasicSyntax = PrivateSyntax.BasicSyntax;

(* hide functors; saves space in PolyML *)
functor PrettyFun() = struct end;
functor LexiconFun() = struct end;
functor AstFun() = struct end;
functor SynExtFun() = struct end;
functor ParserFun() = struct end;
functor TypeExtFun() = struct end;
functor SynTransFun() = struct end;
functor MixfixFun() = struct end;
functor PrinterFun() = struct end;
functor SyntaxFun() = struct end;
