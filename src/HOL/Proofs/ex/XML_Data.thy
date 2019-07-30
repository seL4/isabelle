(*  Title:      HOL/Proofs/ex/XML_Data.thy
    Author:     Makarius
    Author:     Stefan Berghofer

XML data representation of proof terms.
*)

theory XML_Data
  imports "HOL-Isar_Examples.Drinker"
begin

subsection \<open>Export and re-import of global proof terms\<close>

ML \<open>
  fun export_proof ctxt thm =
    Proofterm.encode (Thm.clean_proof_of ctxt true thm);

  fun import_proof thy xml =
    let
      val prf = Proofterm.decode xml;
      val (prf', _) = Proofterm.freeze_thaw_prf prf;
    in Drule.export_without_context (Proof_Checker.thm_of_proof thy prf') end;
\<close>


subsection \<open>Examples\<close>

ML \<open>val thy1 = \<^theory>\<close>

lemma ex: "A \<longrightarrow> A" ..

ML_val \<open>
  val xml = export_proof \<^context> @{thm ex};
  val thm = import_proof thy1 xml;
\<close>

ML_val \<open>
  val xml = export_proof \<^context> @{thm de_Morgan};
  val thm = import_proof thy1 xml;
\<close>

ML_val \<open>
  val xml = export_proof \<^context> @{thm Drinker's_Principle};
  val thm = import_proof thy1 xml;
\<close>

text \<open>Some fairly large proof:\<close>

ML_val \<open>
  val xml = export_proof \<^context> @{thm abs_less_iff};
  val thm = import_proof thy1 xml;
  \<^assert> (size (YXML.string_of_body xml) > 1000000);
\<close>

end
