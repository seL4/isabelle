(*  Title:      HOL/Metis.thy
    ID:         $Id$
*)

header {* The Metis prover (version 2.0 from 2007) *}

theory Metis
imports Main
uses
  "~~/src/Tools/Metis/metis.ML"
  "Tools/metis_tools.ML"
begin

setup MetisTools.setup

end
