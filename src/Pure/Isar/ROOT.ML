(*  Title:      Pure/Isar/ROOT.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Isar -- Intelligible Semi-Automated Reasoning for Isabelle.
*)

(*basic proof engine*)
use "auto_bind.ML";
use "proof_context.ML";
use "proof.ML";
use "proof_data.ML";
use "proof_history.ML";
use "args.ML";
use "attrib.ML";
use "method.ML";

(*derived proof elements*)
use "local_defs.ML";
use "calculation.ML";
use "skip_proof.ML";
use "obtain.ML";

(*outer syntax*)
use "comment.ML";
(*use "outer_lex.ML";*)	  (*see ../Thy/ROOT.ML*)
use "outer_parse.ML";

(*toplevel environment*)
use "toplevel.ML";
use "session.ML";

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
  structure Obtain = Obtain;
  structure Comment = Comment;
  structure OuterLex = OuterLex;
  structure OuterParse = OuterParse;
  structure Toplevel = Toplevel;
  structure Session = Session;
  structure IsarThy = IsarThy;
  structure IsarCmd = IsarCmd;
  structure OuterSyntax = OuterSyntax;
  structure IsarSyn = IsarSyn;
  structure Isar = Isar;
end;
