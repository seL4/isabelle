(*  Title:      Pure/Isar/ROOT.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Isar -- Intelligible Semi-Automated Reasoning for Isabelle.
*)

(*proof engine*)
use "proof_context.ML";
use "proof.ML";
use "proof_data.ML";
use "args.ML";
use "attrib.ML";
use "method.ML";

(*outer syntax*)
use "outer_lex.ML";
use "outer_parse.ML";

(*interactive subsystem*)
use "proof_history.ML";
use "toplevel.ML";

(*theory operations*)
use "isar_thy.ML";
use "isar_cmd.ML";

(*theory syntax*)
use "outer_syntax.ML";
use "isar_syn.ML";

(*main ML interface*)
use "isar.ML";

structure PureIsar =
struct
  structure ProofContext = ProofContext;
  structure Proof = Proof;
  structure Args = Args;
  structure Attrib = Attrib;
  structure Method = Method;
  structure OuterLex = OuterLex;
  structure OuterParse = OuterParse;
  structure ProofHistory = ProofHistory;
  structure Toplevel = Toplevel;
  structure OuterSyntax = OuterSyntax;
  structure IsarThy = IsarThy;
  structure IsarCmd = IsarCmd;
  structure IsarSyn = IsarSyn;
  structure Isar = Isar;
end;
