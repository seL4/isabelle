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
use "sextension.ML";
use "mixfix.ML";
use "printer.ML";
use "syntax.ML";

structure Pretty = PrettyFun();
structure Lexicon = LexiconFun();
structure Scanner: SCANNER = Lexicon;
structure Ast = AstFun(Pretty);
structure SynExt = SynExtFun(structure Lexicon = Lexicon and Ast = Ast);
structure Parser = ParserFun(structure Symtab = Symtab and Lexicon = Lexicon
  and SynExt = SynExt);
structure TypeExt = TypeExtFun(structure Lexicon = Lexicon and SynExt = SynExt);
structure SExtension = SExtensionFun(structure TypeExt = TypeExt and Parser = Parser);
structure Mixfix = MixfixFun(structure Lexicon = Lexicon and SynExt = SynExt and
  SExtension = SExtension);
structure Printer = PrinterFun(structure Symtab = Symtab and TypeExt = TypeExt
  and SExtension = SExtension);
structure Syntax = SyntaxFun(structure Symtab = Symtab and TypeExt = TypeExt
  and SExtension = SExtension and Mixfix = Mixfix and Printer = Printer);
structure BasicSyntax: BASIC_SYNTAX = Syntax;

(* FIXME tmp hacks *)
structure BasicSyntax = struct open BasicSyntax Mixfix end;
structure OldMixfix: SEXTENSION0 = SExtension;
