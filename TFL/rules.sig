signature Rules_sig =
sig
(*  structure USyntax : USyntax_sig *)
  type 'a binding

  val dest_thm : thm -> term list * term

  (* Inference rules *)
  val REFL      :cterm -> thm
  val ASSUME    :cterm -> thm
  val MP        :thm -> thm -> thm
  val MATCH_MP  :thm -> thm -> thm
  val CONJUNCT1 :thm -> thm
  val CONJUNCT2 :thm -> thm
  val CONJUNCTS :thm -> thm list
  val DISCH     :cterm -> thm -> thm
  val UNDISCH   :thm  -> thm
  val INST_TYPE :typ binding list -> thm -> thm
  val SPEC      :cterm -> thm -> thm
  val ISPEC     :cterm -> thm -> thm
  val ISPECL    :cterm list -> thm -> thm
  val GEN       :cterm -> thm -> thm
  val GENL      :cterm list -> thm -> thm
  val LIST_CONJ :thm list -> thm

  val SYM : thm -> thm
  val DISCH_ALL : thm -> thm
  val FILTER_DISCH_ALL : (term -> bool) -> thm -> thm
  val SPEC_ALL  : thm -> thm
  val GEN_ALL   : thm -> thm
  val IMP_TRANS : thm -> thm -> thm
  val PROVE_HYP : thm -> thm -> thm

  val CHOOSE : cterm * thm -> thm -> thm
  val EXISTS : cterm * cterm -> thm -> thm
  val EXISTL : cterm list -> thm -> thm
  val IT_EXISTS : cterm binding list -> thm -> thm

  val EVEN_ORS : thm list -> thm list
  val DISJ_CASESL : thm -> thm list -> thm

  val SUBS : thm list -> thm -> thm
  val simplify : thm list -> thm -> thm
  val simpl_conv : thm list -> cterm -> thm

(* For debugging my isabelle solver in the conditional rewriter *)
(*
  val term_ref : term list ref
  val thm_ref : thm list ref
  val mss_ref : meta_simpset list ref
  val tracing :bool ref
*)
  val CONTEXT_REWRITE_RULE : term * term
                             -> {thms:thm list,congs: thm list, th:thm} 
                             -> thm * term list
  val RIGHT_ASSOC : thm -> thm 

  val prove : cterm * tactic -> thm
end;
