(*  Title:      HOL/Proofs/ex/XML_Data.thy
    Author:     Makarius

XML data representation of proof terms.
*)

theory XML_Data
imports Main
begin

subsection {* Export and re-import of global proof terms *}

ML {*
  fun export_proof thm0 =
    let
      val thy = Thm.theory_of_thm thm0;
      val ctxt0 = Proof_Context.init_global thy;
      val thy = Proof_Context.theory_of ctxt0;
      val ((_, [thm]), ctxt) = Variable.import true [Thm.transfer thy thm0] ctxt0;

      val prop = Thm.prop_of thm;  (* FIXME proper prop (wrt. import / strip) (!??) *)
      val prf =
        Proofterm.proof_of (Proofterm.strip_thm (Thm.proof_body_of thm))
        |> Proofterm.no_thm_proofs;
    in XML.Encode.pair Term_XML.Encode.term Proofterm.encode (prop, prf) end;

  fun import_proof thy xml =
    let
      val (prop, prf) = XML.Decode.pair Term_XML.Decode.term Proofterm.decode xml;
      val full_prf = Reconstruct.reconstruct_proof thy prop prf;
    in Drule.export_without_context (Proof_Checker.thm_of_proof thy full_prf) end;
*}


subsection {* Example *}

ML {* val thy1 = @{theory} *}

lemma ex: "A \<longrightarrow> A" ..

ML {*
  val xml = export_proof @{thm ex};
  val thm = import_proof thy1 xml;
*}

end

