(*  Title:      Pure/Syntax/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

This file builds the syntax module.
*)

use "pretty.ML";

use "ast.ML";
use "xgram.ML";
use "lexicon.ML";
use "extension.ML";
use "parse_tree.ML";
use "parser.ML";
use "earley0A.ML";        (* FIXME *)
use "type_ext.ML";
use "sextension.ML";
use "printer.ML";
use "syntax.ML";

structure Pretty = PrettyFun();

structure Ast = AstFun(Pretty);
structure XGram = XGramFun(Ast);
structure Lexicon = LexiconFun();
structure Extension = ExtensionFun(structure XGram = XGram and Lexicon = Lexicon);
structure ParseTree = ParseTreeFun(structure Ast = Ast and Lexicon = Lexicon);
structure Parser = ParserFun(structure Symtab = Symtab and XGram = XGram
  and ParseTree = ParseTree);
structure Earley = EarleyFun(structure Symtab = Symtab and XGram = XGram
  and ParseTree = ParseTree);     (* FIXME *)
structure TypeExt = TypeExtFun(structure Extension = Extension
  and Lexicon = Lexicon);
structure SExtension = SExtensionFun(structure TypeExt = TypeExt
  and Lexicon = Lexicon);
structure Printer = PrinterFun(structure Symtab = Symtab and Lexicon = Lexicon
  and TypeExt = TypeExt and SExtension = SExtension and Pretty = Pretty);
structure Syntax = SyntaxFun(structure Symtab = Symtab and TypeExt = TypeExt
  and Parser = Earley and SExtension = SExtension and Printer = Printer);
     (* FIXME  ^^^^^^ *)

(*BasicSyntax has the most important primitives, which are made pervasive*)
signature BASIC_SYNTAX = sig include SEXTENSION0 include PRINTER0 end;
structure BasicSyntax: BASIC_SYNTAX = Syntax;

