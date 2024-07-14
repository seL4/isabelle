(*  Title:      HOL/Proofs/ex/XML_Data.thy
    Author:     Makarius
    Author:     Stefan Berghofer

XML data representation of proof terms.
*)

theory XML_Data
  imports "HOL-Examples.Drinker"
begin

subsection \<open>Export and re-import of global proof terms\<close>

ML \<open>
  fun export_proof thy thm = thm
    |> Proof_Syntax.standard_proof_of {full = true, expand_name = Thm.expand_name thm}
    |> Proofterm.encode (Sign.consts_of thy);

  fun import_proof thy xml =
    let
      val prf = Proofterm.decode (Sign.consts_of thy) xml;
      val (prf', _) = Proofterm.freeze_thaw_prf prf;
    in Drule.export_without_context (Proof_Checker.thm_of_proof thy prf') end;
\<close>


subsection \<open>Examples\<close>

ML \<open>val thy1 = \<^theory>\<close>

lemma ex: "A \<longrightarrow> A" ..

ML_val \<open>
  val xml = export_proof thy1 @{thm ex};
  val thm = import_proof thy1 xml;
\<close>

ML_val \<open>
  val xml = export_proof thy1 @{thm de_Morgan};
  val thm = import_proof thy1 xml;
\<close>

ML_val \<open>
  val xml = export_proof thy1 @{thm Drinker's_Principle};
  val thm = import_proof thy1 xml;
\<close>

text \<open>Some fairly large proof:\<close>

ML_val \<open>
  val xml = export_proof thy1 @{thm Int.times_int.abs_eq};
  val thm = import_proof thy1 xml;

  val xml_size = Bytes.length (YXML.bytes_of_body xml);
  \<^assert> (xml_size > 10000000);
\<close>

end
