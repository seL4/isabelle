(*  Title:      HOL/TPTP/TPTP_Interpret.thy
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Importing TPTP files into Isabelle/HOL: parsing TPTP formulas and
interpreting them as HOL terms (i.e. importing types and type-checking the terms)
*)

theory TPTP_Interpret
imports Main TPTP_Parser
keywords "import_tptp" :: thy_decl
uses  ("TPTP_Parser/tptp_interpret.ML")

begin
typedecl "ind"
use  "TPTP_Parser/tptp_interpret.ML"
end