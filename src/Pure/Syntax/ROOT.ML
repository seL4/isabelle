(*  Title:      Pure/Syntax/ROOT
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

This file builds the syntax module. It assumes the standard Isabelle
environment.
*)

use "ast.ML";
use "xgram.ML";
use "extension.ML";
use "lexicon.ML";
use "parse_tree.ML";
use "earley0A.ML";
use "type_ext.ML";
use "sextension.ML";
use "pretty.ML";
use "printer.ML";
use "syntax.ML";

structure Ast = AstFun();
structure XGram = XGramFun(Ast);
structure Extension = ExtensionFun(XGram);
structure Lexicon = LexiconFun(Extension);
structure ParseTree = ParseTreeFun(structure Lexicon = Lexicon and Ast = Ast);
structure Earley = EarleyFun(structure XGram = XGram and ParseTree = ParseTree);
structure TypeExt = TypeExtFun(structure Extension = Extension
  and Lexicon = Lexicon);
structure SExtension = SExtensionFun(structure TypeExt = TypeExt
  and Lexicon = Lexicon);
structure Pretty = PrettyFun();
structure Printer = PrinterFun(structure Symtab = Symtab and Lexicon = Lexicon
  and TypeExt = TypeExt and SExtension = SExtension and Pretty = Pretty);
structure Syntax = SyntaxFun(structure Symtab = Symtab and TypeExt = TypeExt
  and Parser = Earley and SExtension = SExtension and Printer = Printer);

(*Basic_Syntax has the most important primitives, which are made pervasive*)
signature BASIC_SYNTAX = sig include SEXTENSION0 include PRINTER0 end;
structure Basic_Syntax: BASIC_SYNTAX = Syntax;

