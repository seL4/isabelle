(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/eqsubst_tac.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    29 Jan 2005
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    A Tactic to perform a substiution using an equation.

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* Logic specific data *)
signature EQRULE_DATA =
sig
  (* to make a meta equality theorem in the current logic *)
  val prep_meta_eq : thm -> thm list
end;

(* the signature of an instance of the SQSUBST tactic *)
signature EQSUBST_TAC = 
sig
  val eqsubst_asm_meth : Thm.thm list -> Proof.method
  val eqsubst_asm_tac : Thm.thm list -> int -> Thm.thm -> Thm.thm Seq.seq
  val eqsubst_asm_tac' : Thm.thm -> int -> Thm.thm -> Thm.thm Seq.seq
  val eqsubst_meth : Thm.thm list -> Proof.method
  val eqsubst_tac : Thm.thm list -> int -> Thm.thm -> Thm.thm Seq.seq
  val eqsubst_tac' : Thm.thm -> int -> Thm.thm -> Thm.thm Seq.seq
  val meth : bool * Thm.thm list -> Proof.context -> Proof.method
  val subst : Thm.thm -> int -> Thm.thm -> Thm.thm Seq.seq
  val subst_asm : Thm.thm -> int -> Thm.thm -> Thm.thm Seq.seq

  val setup : (Theory.theory -> Theory.theory) list
end;

functor EQSubstTacFUN (structure EqRuleData : EQRULE_DATA) 
(* : EQSUBST_TAC *)
= struct

fun search_tb_lr_f f ft = 
    let
      fun maux ft = 
          let val t' = (IsaFTerm.focus_of_fcterm ft) 
     (*   val _ = writeln ("Examining: " ^ (TermLib.string_of_term t')) *)
          in 
          (case t' of 
            (_ $ _) => Seq.append(f ft, 
                       Seq.append(maux (IsaFTerm.focus_left ft), 
                                  maux (IsaFTerm.focus_right ft)))
          | (Abs _) => Seq.append (f ft, maux (IsaFTerm.focus_abs ft))
          | leaf => f ft) end
    in maux ft end;

fun search_for_match sgn lhs maxidx = 
    IsaFTerm.find_fcterm_matches 
      search_tb_lr_f 
      (IsaFTerm.clean_unify_ft sgn maxidx lhs);


(* CLEANUP: lots of duplication of code for substituting in
assumptions and conclusion - this could be cleaned up a little. *)

fun subst_concl rule cfvs i th (conclthm, concl_matches)= 
    let 
      fun apply_subst m = 
          (RWInst.rw m rule conclthm)
            |> IsaND.schemify_frees_to_vars cfvs
            |> RWInst.beta_eta_contract_tac
            |> (fn r => Tactic.rtac r i th)
            |> Seq.map Drule.zero_var_indexes
    in
      Seq.flat (Seq.map apply_subst concl_matches)
    end;


(* substitute within the conclusion of goal i of gth, using a meta
equation rule *)
fun subst rule i gth = 
    let 
      val th = Thm.incr_indexes 1 gth;
      val tgt_term = Thm.prop_of th;
      val maxidx = Term.maxidx_of_term tgt_term;

      val rule' = Drule.zero_var_indexes rule;
      val (lhs,_) = Logic.dest_equals (Thm.concl_of rule');

      val sgn = Thm.sign_of_thm th;
      val ctermify = Thm.cterm_of sgn;
      val trivify = Thm.trivial o ctermify;

      val (fixedbody, fvs) = IsaND.fix_alls_term i tgt_term;
      val cfvs = rev (map ctermify fvs);

      val conclthm = trivify (Logic.strip_imp_concl fixedbody);
      val concl_matches = 
          search_for_match sgn lhs maxidx 
                           ((IsaFTerm.focus_right  
                             o IsaFTerm.focus_left
                             o IsaFTerm.fcterm_of_term 
                             o Thm.prop_of) conclthm);
    in
      subst_concl rule' cfvs i th (conclthm, concl_matches)
    end;

(* substitute using an object or meta level equality *)
fun eqsubst_tac' instepthm i th = 
    let val stepthms = Seq.of_list (EqRuleData.prep_meta_eq instepthm) in
      Seq.flat (Seq.map (fn rule => subst rule i th) stepthms)
    end;
(* substitute using one of the given theorems *)
fun eqsubst_tac instepthms i th = 
    Seq.flat (Seq.map (fn r => eqsubst_tac' r i th) (Seq.of_list instepthms));

(* inthms are the given arguments in Isar, and treated as eqstep with
   the first one, then the second etc *)
fun eqsubst_meth inthms =
    Method.METHOD 
      (fn facts =>  (*first, insert chained facts*)
          HEADGOAL (Method.insert_tac facts THEN' eqsubst_tac inthms));


fun apply_subst_in_asm rule cfvs i th matchseq = 
    let 
      fun apply_subst ((j, pth), mseq) = 
          Seq.flat (Seq.map 
             (fn m =>
                 (RWInst.rw m rule pth)
                   |> Thm.permute_prems 0 ~1
                   |> IsaND.schemify_frees_to_vars cfvs
                   |> RWInst.beta_eta_contract_tac
                   |> (fn r => Tactic.dtac r i th)
                   |> Seq.map Drule.zero_var_indexes)
             mseq)
    in
      Seq.flat (Seq.map apply_subst matchseq)
    end;


(* substitute within an assumption of goal i of gth, using a meta
equation rule *)
fun subst_asm rule i gth = 
    let 
      val th = Thm.incr_indexes 1 gth;
      val tgt_term = Thm.prop_of th;
      val maxidx = Term.maxidx_of_term tgt_term;

      val rule' = Drule.zero_var_indexes rule;
      val (lhs,_) = Logic.dest_equals (Thm.concl_of rule');

      val sgn = Thm.sign_of_thm th;
      val ctermify = Thm.cterm_of sgn;
      val trivify = Thm.trivial o ctermify;

      val (fixedbody, fvs) = IsaND.fix_alls_term i tgt_term;
      val cfvs = rev (map ctermify fvs);

      val premthms = Seq.of_list (IsaPLib.number_list 1
                       (map trivify (Logic.strip_imp_prems fixedbody)));
      val prem_matches = 
          Seq.map (fn (i, pth) => 
                  ((i, pth), search_for_match sgn lhs maxidx 
                                              ((IsaFTerm.focus_right 
                                                o IsaFTerm.fcterm_of_term 
                                                o Thm.prop_of) pth)))
              premthms;
    in
      apply_subst_in_asm rule' cfvs i th prem_matches
    end;

(* substitute using an object or meta level equality *)
fun eqsubst_asm_tac' instepthm i th = 
    let val stepthms = Seq.of_list (EqRuleData.prep_meta_eq instepthm) in
      Seq.flat (Seq.map (fn rule => subst_asm rule i th) stepthms)
    end;

(* substitute using one of the given theorems *)
fun eqsubst_asm_tac instepthms i th = 
    Seq.flat (Seq.map (fn r => eqsubst_asm_tac' r i th) 
                      (Seq.of_list instepthms));

(* inthms are the given arguments in Isar, and treated as eqstep with
   the first one, then the second etc *)
fun eqsubst_asm_meth inthms =
    Method.METHOD 
      (fn facts =>  (*first, insert chained facts*)
          HEADGOAL (Method.insert_tac facts THEN' eqsubst_asm_tac inthms));


(* combination method that takes a flag (true indicates that subst
should be done to an assumption, false = apply to the conclusion of
the goal) as well as the theorems to use *)
fun meth (asmflag, inthms) ctxt = 
    if asmflag then eqsubst_asm_meth inthms else eqsubst_meth inthms;

(* syntax for options, given "(asm)" will give back true, without
   gives back false *)
val options_syntax =
    (Args.parens (Args.$$$ "asm") >> (K true)) ||
     (Scan.succeed false);

(* method syntax, first take options, then theorems *)
fun meth_syntax meth src ctxt =
    meth (snd (Method.syntax ((Scan.lift options_syntax) 
                                -- Attrib.local_thms) src ctxt)) 
         ctxt;

(* setup function for adding method to theory. *)
val setup = 
    [Method.add_method ("subst", meth_syntax meth, "Substiution with an equation. Use \"(asm)\" option to substitute in an assumption.")];

end;