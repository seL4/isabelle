signature Rules_sig =
sig
(*  structure USyntax : USyntax_sig *)
  type Type
  type Preterm
  type Term
  type Thm
  type Tactic
  type 'a binding

  val dest_thm : Thm -> Preterm list * Preterm

  (* Inference rules *)
  val REFL      :Term -> Thm
  val ASSUME    :Term -> Thm
  val MP        :Thm -> Thm -> Thm
  val MATCH_MP  :Thm -> Thm -> Thm
  val CONJUNCT1 :Thm -> Thm
  val CONJUNCT2 :Thm -> Thm
  val CONJUNCTS :Thm -> Thm list
  val DISCH     :Term -> Thm -> Thm
  val UNDISCH   :Thm  -> Thm
  val INST_TYPE :Type binding list -> Thm -> Thm
  val SPEC      :Term -> Thm -> Thm
  val ISPEC     :Term -> Thm -> Thm
  val ISPECL    :Term list -> Thm -> Thm
  val GEN       :Term -> Thm -> Thm
  val GENL      :Term list -> Thm -> Thm
  val BETA_RULE :Thm -> Thm
  val LIST_CONJ :Thm list -> Thm

  val SYM : Thm -> Thm
  val DISCH_ALL : Thm -> Thm
  val FILTER_DISCH_ALL : (Preterm -> bool) -> Thm -> Thm
  val SPEC_ALL  : Thm -> Thm
  val GEN_ALL   : Thm -> Thm
  val IMP_TRANS : Thm -> Thm -> Thm
  val PROVE_HYP : Thm -> Thm -> Thm

  val CHOOSE : Term * Thm -> Thm -> Thm
  val EXISTS : Term * Term -> Thm -> Thm
  val EXISTL : Term list -> Thm -> Thm
  val IT_EXISTS : Term binding list -> Thm -> Thm

  val EVEN_ORS : Thm list -> Thm list
  val DISJ_CASESL : Thm -> Thm list -> Thm

  val SUBS : Thm list -> Thm -> Thm
  val simplify : Thm list -> Thm -> Thm
  val simpl_conv : Thm list -> Term -> Thm

(* For debugging my isabelle solver in the conditional rewriter *)
(*
  val term_ref : Preterm list ref
  val thm_ref : Thm list ref
  val mss_ref : meta_simpset list ref
  val tracing :bool ref
*)
  val CONTEXT_REWRITE_RULE : Preterm * Preterm
                             -> {thms:Thm list,congs: Thm list, th:Thm} 
                             -> Thm * Preterm list
  val RIGHT_ASSOC : Thm -> Thm 

  val prove : Term * Tactic -> Thm
end;
