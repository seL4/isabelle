(*  Title:      HOL/Proofs/ex/XML_Data.thy
    Author:     Makarius
    Author:     Stefan Berghofer

XML data representation of proof terms.
*)

theory XML_Data
imports "~~/src/HOL/Isar_Examples/Drinker"
begin

subsection {* Export and re-import of global proof terms *}

ML {*
  fun export_proof thm =
    let
      val thy = Thm.theory_of_thm thm;
      val {prop, hyps, shyps, ...} = Thm.rep_thm thm;
      val (_, prop) = Logic.unconstrainT shyps (Logic.list_implies (hyps, prop));
      val prf =
        Proofterm.proof_of (Proofterm.strip_thm (Thm.proof_body_of thm)) |>
        Reconstruct.reconstruct_proof thy prop |>
        Reconstruct.expand_proof thy [("", NONE)] |>
        Proofterm.rew_proof thy |>
        Proofterm.no_thm_proofs;
    in Proofterm.encode prf end;

  fun import_proof thy xml =
    let
      val prf = Proofterm.decode xml;
      val (prf', _) = Proofterm.freeze_thaw_prf prf;
    in Drule.export_without_context (Proof_Checker.thm_of_proof thy prf') end;
*}


subsection {* Examples *}

ML {* val thy1 = @{theory} *}

lemma ex: "A \<longrightarrow> A" ..

ML_val {*
  val xml = export_proof @{thm ex};
  val thm = import_proof thy1 xml;
*}

ML_val {*
  val xml = export_proof @{thm de_Morgan};
  val thm = import_proof thy1 xml;
*}

ML_val {*
  val xml = export_proof @{thm Drinker's_Principle};
  val thm = import_proof thy1 xml;
*}

text {* Some fairly large proof: *}

ML_val {*
  val xml = export_proof @{thm Int.times_int.abs_eq};
  val thm = import_proof thy1 xml;
  @{assert} (size (YXML.string_of_body xml) > 50000000);
*}

end
