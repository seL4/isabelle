(*  Title:      Pure/Isar/ROOT.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Isar -- Intelligible Semi-Automated Reasoning for Isabelle.
*)

(*basic proof engine*)
use "auto_bind.ML";
use "rule_cases.ML";
use "proof_context.ML";
use "proof.ML";
use "proof_data.ML";
use "proof_history.ML";
use "args.ML";
use "attrib.ML";
use "net_rules.ML";
use "induct_attrib.ML";
use "method.ML";

(*derived proof elements*)
use "local_defs.ML";
use "calculation.ML";
use "skip_proof.ML";

(*outer syntax*)
(*use "outer_lex.ML";*)	  (*see ../Thy/ROOT.ML*)
use "antiquote.ML";
use "comment.ML";
use "outer_parse.ML";

(*toplevel environment*)
use "toplevel.ML";
use "session.ML";
use "isar_output.ML";

(*theory and proof operations*)
use "isar_thy.ML";
use "isar_cmd.ML";

(*theory syntax*)
use "thy_header.ML";
use "outer_syntax.ML";
use "isar_syn.ML";

(*main ML interfaces*)
use "obtain.ML";
use "isar.ML";

structure PureIsar =
struct
  structure AutoBind = AutoBind;
  structure ProofContext = ProofContext;
  structure Proof = Proof;
  structure ProofHistory = ProofHistory;
  structure Args = Args;
  structure Attrib = Attrib;
  structure Method = Method;
  structure LocalDefs = LocalDefs;
  structure Calculation = Calculation;
  structure SkipProof = SkipProof;
  structure OuterLex = OuterLex;
  structure Antiquote = Antiquote;
  structure Comment = Comment;
  structure OuterParse = OuterParse;
  structure Toplevel = Toplevel;
  structure Session = Session;
  structure IsarThy = IsarThy;
  structure IsarOutput = IsarOutput;
  structure IsarCmd = IsarCmd;
  structure ThyHeader = ThyHeader;
  structure OuterSyntax = OuterSyntax;
  structure IsarSyn = IsarSyn;
  structure Obtain = Obtain;
  structure Isar = Isar;
end;
