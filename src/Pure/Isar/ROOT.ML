(*  Title:      Pure/Isar/ROOT.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Isar -- Intelligible Semi-Automated Reasoning for Isabelle.
*)

(*basic proof engine*)
use "object_logic.ML";
use "auto_bind.ML";
use "rule_cases.ML";
use "proof_context.ML";
use "locale.ML";
use "proof.ML";
use "proof_data.ML";
use "proof_history.ML";
use "args.ML";
use "attrib.ML";
use "rule_context.ML";
use "net_rules.ML";
use "induct_attrib.ML";
use "method.ML";

(*derived proof elements*)
use "calculation.ML";
use "obtain.ML";
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
use "isar.ML";

structure PureIsar =
struct
  structure ObjectLogic = ObjectLogic;
  structure AutoBind = AutoBind;
  structure ProofContext = ProofContext;
  structure Locale = Locale;
  structure Proof = Proof;
  structure ProofHistory = ProofHistory;
  structure Args = Args;
  structure Attrib = Attrib;
  structure RuleContext = RuleContext;
  structure Method = Method;
  structure Calculation = Calculation;
  structure Obtain = Obtain;
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
  structure Isar = Isar;
end;
