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
(*use "earley0A.ML";*)
use "type_ext.ML";
use "sextension.ML";
use "printer.ML";
use "syntax.ML";

structure Pretty = PrettyFun();
structure Lexicon = LexiconFun();
structure Scanner: SCANNER = Lexicon;
structure Ast = AstFun(Pretty);
structure SynExt = SynExtFun(structure Lexicon = Lexicon and Ast = Ast);
structure Parser = ParserFun(structure Symtab = Symtab and Lexicon = Lexicon
  and SynExt = SynExt);
(*structure Earley = EarleyFun(structure Symtab = Symtab and Lexicon = Lexicon
  and SynExt = SynExt);*)
structure TypeExt = TypeExtFun(structure Lexicon = Lexicon and SynExt = SynExt);
structure SExtension = SExtensionFun(Parser);
structure Printer = PrinterFun(structure Symtab = Symtab and TypeExt = TypeExt
  and SExtension = SExtension);
structure Syntax = SyntaxFun(structure Symtab = Symtab and TypeExt = TypeExt
  and SExtension = SExtension and Printer = Printer);
structure BasicSyntax: BASIC_SYNTAX = Syntax;
