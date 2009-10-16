(*  Title:      HOL/Tools/Function/fundef_core.ML
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions:
Main functionality.
*)

signature FUNDEF_CORE =
sig
    val trace: bool Unsynchronized.ref

    val prepare_fundef : FundefCommon.fundef_config
                         -> string (* defname *)
                         -> ((bstring * typ) * mixfix) list (* defined symbol *)
                         -> ((bstring * typ) list * term list * term * term) list (* specification *)
                         -> local_theory

                         -> (term   (* f *)
                             * thm  (* goalstate *)
                             * (thm -> FundefCommon.fundef_result) (* continuation *)
                            ) * local_theory

end

structure FundefCore : FUNDEF_CORE =
struct

val trace = Unsynchronized.ref false;
fun trace_msg msg = if ! trace then tracing (msg ()) else ();

val boolT = HOLogic.boolT
val mk_eq = HOLogic.mk_eq

open FundefLib
open FundefCommon

datatype globals =
   Globals of {
         fvar: term,
         domT: typ,
         ranT: typ,
         h: term,
         y: term,
         x: term,
         z: term,
         a: term,
         P: term,
         D: term,
         Pbool:term
}


datatype rec_call_info =
  RCInfo of
  {
   RIvs: (string * typ) list,  (* Call context: fixes and assumes *)
   CCas: thm list,
   rcarg: term,                 (* The recursive argument *)

   llRI: thm,
   h_assum: term
  }


datatype clause_context =
  ClauseContext of
  {
    ctxt : Proof.context,

    qs : term list,
    gs : term list,
    lhs: term,
    rhs: term,

    cqs: cterm list,
    ags: thm list,
    case_hyp : thm
  }


fun transfer_clause_ctx thy (ClauseContext { ctxt, qs, gs, lhs, rhs, cqs, ags, case_hyp }) =
    ClauseContext { ctxt = ProofContext.transfer thy ctxt,
                    qs = qs, gs = gs, lhs = lhs, rhs = rhs, cqs = cqs, ags = ags, case_hyp = case_hyp }


datatype clause_info =
  ClauseInfo of
     {
      no: int,
      qglr : ((string * typ) list * term list * term * term),
      cdata : clause_context,

      tree: FundefCtxTree.ctx_tree,
      lGI: thm,
      RCs: rec_call_info list
     }


(* Theory dependencies. *)
val Pair_inject = @{thm Product_Type.Pair_inject};

val acc_induct_rule = @{thm accp_induct_rule};

val ex1_implies_ex = @{thm FunDef.fundef_ex1_existence};
val ex1_implies_un = @{thm FunDef.fundef_ex1_uniqueness};
val ex1_implies_iff = @{thm FunDef.fundef_ex1_iff};

val acc_downward = @{thm accp_downward};
val accI = @{thm accp.accI};
val case_split = @{thm HOL.case_split};
val fundef_default_value = @{thm FunDef.fundef_default_value};
val not_acc_down = @{thm not_accp_down};



fun find_calls tree =
    let
      fun add_Ri (fixes,assumes) (_ $ arg) _ (_, xs) = ([], (fixes, assumes, arg) :: xs)
        | add_Ri _ _ _ _ = raise Match
    in
      rev (FundefCtxTree.traverse_tree add_Ri tree [])
    end


(** building proof obligations *)

fun mk_compat_proof_obligations domT ranT fvar f glrs =
    let
      fun mk_impl ((qs, gs, lhs, rhs),(qs', gs', lhs', rhs')) =
          let
            val shift = incr_boundvars (length qs')
          in
            Logic.mk_implies
              (HOLogic.mk_Trueprop (HOLogic.eq_const domT $ shift lhs $ lhs'),
                HOLogic.mk_Trueprop (HOLogic.eq_const ranT $ shift rhs $ rhs'))
              |> fold_rev (curry Logic.mk_implies) (map shift gs @ gs')
              |> fold_rev (fn (n,T) => fn b => Term.all T $ Abs(n,T,b)) (qs @ qs')
              |> curry abstract_over fvar
              |> curry subst_bound f
          end
    in
      map mk_impl (unordered_pairs glrs)
    end


fun mk_completeness (Globals {x, Pbool, ...}) clauses qglrs =
    let
        fun mk_case (ClauseContext {qs, gs, lhs, ...}, (oqs, _, _, _)) =
            HOLogic.mk_Trueprop Pbool
                     |> curry Logic.mk_implies (HOLogic.mk_Trueprop (mk_eq (x, lhs)))
                     |> fold_rev (curry Logic.mk_implies) gs
                     |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
    in
        HOLogic.mk_Trueprop Pbool
                 |> fold_rev (curry Logic.mk_implies o mk_case) (clauses ~~ qglrs)
                 |> mk_forall_rename ("x", x)
                 |> mk_forall_rename ("P", Pbool)
    end

(** making a context with it's own local bindings **)

fun mk_clause_context x ctxt (pre_qs,pre_gs,pre_lhs,pre_rhs) =
    let
      val (qs, ctxt') = Variable.variant_fixes (map fst pre_qs) ctxt
                                           |>> map2 (fn (_, T) => fn n => Free (n, T)) pre_qs

      val thy = ProofContext.theory_of ctxt'

      fun inst t = subst_bounds (rev qs, t)
      val gs = map inst pre_gs
      val lhs = inst pre_lhs
      val rhs = inst pre_rhs

      val cqs = map (cterm_of thy) qs
      val ags = map (assume o cterm_of thy) gs

      val case_hyp = assume (cterm_of thy (HOLogic.mk_Trueprop (mk_eq (x, lhs))))
    in
      ClauseContext { ctxt = ctxt', qs = qs, gs = gs, lhs = lhs, rhs = rhs,
                      cqs = cqs, ags = ags, case_hyp = case_hyp }
    end


(* lowlevel term function. FIXME: remove *)
fun abstract_over_list vs body =
  let
    fun abs lev v tm =
      if v aconv tm then Bound lev
      else
        (case tm of
          Abs (a, T, t) => Abs (a, T, abs (lev + 1) v t)
        | t $ u => abs lev v t $ abs lev v u
        | t => t);
  in
    fold_index (fn (i, v) => fn t => abs i v t) vs body
  end



fun mk_clause_info globals G f no cdata qglr tree RCs GIntro_thm RIntro_thms =
    let
        val Globals {h, fvar, x, ...} = globals

        val ClauseContext { ctxt, qs, cqs, ags, ... } = cdata
        val cert = Thm.cterm_of (ProofContext.theory_of ctxt)

        (* Instantiate the GIntro thm with "f" and import into the clause context. *)
        val lGI = GIntro_thm
                    |> forall_elim (cert f)
                    |> fold forall_elim cqs
                    |> fold Thm.elim_implies ags

        fun mk_call_info (rcfix, rcassm, rcarg) RI =
            let
                val llRI = RI
                             |> fold forall_elim cqs
                             |> fold (forall_elim o cert o Free) rcfix
                             |> fold Thm.elim_implies ags
                             |> fold Thm.elim_implies rcassm

                val h_assum =
                    HOLogic.mk_Trueprop (G $ rcarg $ (h $ rcarg))
                              |> fold_rev (curry Logic.mk_implies o prop_of) rcassm
                              |> fold_rev (Logic.all o Free) rcfix
                              |> Pattern.rewrite_term (ProofContext.theory_of ctxt) [(f, h)] []
                              |> abstract_over_list (rev qs)
            in
                RCInfo {RIvs=rcfix, rcarg=rcarg, CCas=rcassm, llRI=llRI, h_assum=h_assum}
            end

        val RC_infos = map2 mk_call_info RCs RIntro_thms
    in
        ClauseInfo
            {
             no=no,
             cdata=cdata,
             qglr=qglr,

             lGI=lGI,
             RCs=RC_infos,
             tree=tree
            }
    end







(* replace this by a table later*)
fun store_compat_thms 0 thms = []
  | store_compat_thms n thms =
    let
        val (thms1, thms2) = chop n thms
    in
        (thms1 :: store_compat_thms (n - 1) thms2)
    end

(* expects i <= j *)
fun lookup_compat_thm i j cts =
    nth (nth cts (i - 1)) (j - i)

(* Returns "Gsi, Gsj, lhs_i = lhs_j |-- rhs_j_f = rhs_i_f" *)
(* if j < i, then turn around *)
fun get_compat_thm thy cts i j ctxi ctxj =
    let
      val ClauseContext {cqs=cqsi,ags=agsi,lhs=lhsi,...} = ctxi
      val ClauseContext {cqs=cqsj,ags=agsj,lhs=lhsj,...} = ctxj

      val lhsi_eq_lhsj = cterm_of thy (HOLogic.mk_Trueprop (mk_eq (lhsi, lhsj)))
    in if j < i then
         let
           val compat = lookup_compat_thm j i cts
         in
           compat         (* "!!qj qi. Gsj => Gsi => lhsj = lhsi ==> rhsj = rhsi" *)
                |> fold forall_elim (cqsj @ cqsi) (* "Gsj => Gsi => lhsj = lhsi ==> rhsj = rhsi" *)
                |> fold Thm.elim_implies agsj
                |> fold Thm.elim_implies agsi
                |> Thm.elim_implies ((assume lhsi_eq_lhsj) RS sym) (* "Gsj, Gsi, lhsi = lhsj |-- rhsj = rhsi" *)
         end
       else
         let
           val compat = lookup_compat_thm i j cts
         in
               compat        (* "!!qi qj. Gsi => Gsj => lhsi = lhsj ==> rhsi = rhsj" *)
                 |> fold forall_elim (cqsi @ cqsj) (* "Gsi => Gsj => lhsi = lhsj ==> rhsi = rhsj" *)
                 |> fold Thm.elim_implies agsi
                 |> fold Thm.elim_implies agsj
                 |> Thm.elim_implies (assume lhsi_eq_lhsj)
                 |> (fn thm => thm RS sym) (* "Gsi, Gsj, lhsi = lhsj |-- rhsj = rhsi" *)
         end
    end




(* Generates the replacement lemma in fully quantified form. *)
fun mk_replacement_lemma thy h ih_elim clause =
    let
        val ClauseInfo {cdata=ClauseContext {qs, lhs, rhs, cqs, ags, case_hyp, ...}, RCs, tree, ...} = clause
        local open Conv in
        val ih_conv = arg1_conv o arg_conv o arg_conv
        end

        val ih_elim_case = Conv.fconv_rule (ih_conv (K (case_hyp RS eq_reflection))) ih_elim

        val Ris = map (fn RCInfo {llRI, ...} => llRI) RCs
        val h_assums = map (fn RCInfo {h_assum, ...} => assume (cterm_of thy (subst_bounds (rev qs, h_assum)))) RCs

        val (eql, _) = FundefCtxTree.rewrite_by_tree thy h ih_elim_case (Ris ~~ h_assums) tree

        val replace_lemma = (eql RS meta_eq_to_obj_eq)
                                |> implies_intr (cprop_of case_hyp)
                                |> fold_rev (implies_intr o cprop_of) h_assums
                                |> fold_rev (implies_intr o cprop_of) ags
                                |> fold_rev forall_intr cqs
                                |> Thm.close_derivation
    in
      replace_lemma
    end


fun mk_uniqueness_clause thy globals f compat_store clausei clausej RLj =
    let
        val Globals {h, y, x, fvar, ...} = globals
        val ClauseInfo {no=i, cdata=cctxi as ClauseContext {ctxt=ctxti, lhs=lhsi, case_hyp, ...}, ...} = clausei
        val ClauseInfo {no=j, qglr=cdescj, RCs=RCsj, ...} = clausej

        val cctxj as ClauseContext {ags = agsj', lhs = lhsj', rhs = rhsj', qs = qsj', cqs = cqsj', ...}
            = mk_clause_context x ctxti cdescj

        val rhsj'h = Pattern.rewrite_term thy [(fvar,h)] [] rhsj'
        val compat = get_compat_thm thy compat_store i j cctxi cctxj
        val Ghsj' = map (fn RCInfo {h_assum, ...} => assume (cterm_of thy (subst_bounds (rev qsj', h_assum)))) RCsj

        val RLj_import =
            RLj |> fold forall_elim cqsj'
                |> fold Thm.elim_implies agsj'
                |> fold Thm.elim_implies Ghsj'

        val y_eq_rhsj'h = assume (cterm_of thy (HOLogic.mk_Trueprop (mk_eq (y, rhsj'h))))
        val lhsi_eq_lhsj' = assume (cterm_of thy (HOLogic.mk_Trueprop (mk_eq (lhsi, lhsj')))) (* lhs_i = lhs_j' |-- lhs_i = lhs_j' *)
    in
        (trans OF [case_hyp, lhsi_eq_lhsj']) (* lhs_i = lhs_j' |-- x = lhs_j' *)
        |> implies_elim RLj_import (* Rj1' ... Rjk', lhs_i = lhs_j' |-- rhs_j'_h = rhs_j'_f *)
        |> (fn it => trans OF [it, compat]) (* lhs_i = lhs_j', Gj', Rj1' ... Rjk' |-- rhs_j'_h = rhs_i_f *)
        |> (fn it => trans OF [y_eq_rhsj'h, it]) (* lhs_i = lhs_j', Gj', Rj1' ... Rjk', y = rhs_j_h' |-- y = rhs_i_f *)
        |> fold_rev (implies_intr o cprop_of) Ghsj'
        |> fold_rev (implies_intr o cprop_of) agsj' (* lhs_i = lhs_j' , y = rhs_j_h' |-- Gj', Rj1'...Rjk' ==> y = rhs_i_f *)
        |> implies_intr (cprop_of y_eq_rhsj'h)
        |> implies_intr (cprop_of lhsi_eq_lhsj')
        |> fold_rev forall_intr (cterm_of thy h :: cqsj')
    end



fun mk_uniqueness_case ctxt thy globals G f ihyp ih_intro G_cases compat_store clauses rep_lemmas clausei =
    let
        val Globals {x, y, ranT, fvar, ...} = globals
        val ClauseInfo {cdata = ClauseContext {lhs, rhs, qs, cqs, ags, case_hyp, ...}, lGI, RCs, ...} = clausei
        val rhsC = Pattern.rewrite_term thy [(fvar, f)] [] rhs

        val ih_intro_case = full_simplify (HOL_basic_ss addsimps [case_hyp]) ih_intro

        fun prep_RC (RCInfo {llRI, RIvs, CCas, ...}) = (llRI RS ih_intro_case)
                                                            |> fold_rev (implies_intr o cprop_of) CCas
                                                            |> fold_rev (forall_intr o cterm_of thy o Free) RIvs

        val existence = fold (curry op COMP o prep_RC) RCs lGI

        val P = cterm_of thy (mk_eq (y, rhsC))
        val G_lhs_y = assume (cterm_of thy (HOLogic.mk_Trueprop (G $ lhs $ y)))

        val unique_clauses = map2 (mk_uniqueness_clause thy globals f compat_store clausei) clauses rep_lemmas

        val uniqueness = G_cases
                           |> forall_elim (cterm_of thy lhs)
                           |> forall_elim (cterm_of thy y)
                           |> forall_elim P
                           |> Thm.elim_implies G_lhs_y
                           |> fold Thm.elim_implies unique_clauses
                           |> implies_intr (cprop_of G_lhs_y)
                           |> forall_intr (cterm_of thy y)

        val P2 = cterm_of thy (lambda y (G $ lhs $ y)) (* P2 y := (lhs, y): G *)

        val exactly_one =
            ex1I |> instantiate' [SOME (ctyp_of thy ranT)] [SOME P2, SOME (cterm_of thy rhsC)]
                 |> curry (op COMP) existence
                 |> curry (op COMP) uniqueness
                 |> simplify (HOL_basic_ss addsimps [case_hyp RS sym])
                 |> implies_intr (cprop_of case_hyp)
                 |> fold_rev (implies_intr o cprop_of) ags
                 |> fold_rev forall_intr cqs

        val function_value =
            existence
              |> implies_intr ihyp
              |> implies_intr (cprop_of case_hyp)
              |> forall_intr (cterm_of thy x)
              |> forall_elim (cterm_of thy lhs)
              |> curry (op RS) refl
    in
        (exactly_one, function_value)
    end




fun prove_stuff ctxt globals G f R clauses complete compat compat_store G_elim f_def =
    let
        val Globals {h, domT, ranT, x, ...} = globals
        val thy = ProofContext.theory_of ctxt

        (* Inductive Hypothesis: !!z. (z,x):R ==> EX!y. (z,y):G *)
        val ihyp = Term.all domT $ Abs ("z", domT,
                                   Logic.mk_implies (HOLogic.mk_Trueprop (R $ Bound 0 $ x),
                                     HOLogic.mk_Trueprop (Const ("Ex1", (ranT --> boolT) --> boolT) $
                                                             Abs ("y", ranT, G $ Bound 1 $ Bound 0))))
                       |> cterm_of thy

        val ihyp_thm = assume ihyp |> Thm.forall_elim_vars 0
        val ih_intro = ihyp_thm RS (f_def RS ex1_implies_ex)
        val ih_elim = ihyp_thm RS (f_def RS ex1_implies_un)
                        |> instantiate' [] [NONE, SOME (cterm_of thy h)]

        val _ = trace_msg (K "Proving Replacement lemmas...")
        val repLemmas = map (mk_replacement_lemma thy h ih_elim) clauses

        val _ = trace_msg (K "Proving cases for unique existence...")
        val (ex1s, values) =
            split_list (map (mk_uniqueness_case ctxt thy globals G f ihyp ih_intro G_elim compat_store clauses repLemmas) clauses)

        val _ = trace_msg (K "Proving: Graph is a function")
        val graph_is_function = complete
                                  |> Thm.forall_elim_vars 0
                                  |> fold (curry op COMP) ex1s
                                  |> implies_intr (ihyp)
                                  |> implies_intr (cterm_of thy (HOLogic.mk_Trueprop (mk_acc domT R $ x)))
                                  |> forall_intr (cterm_of thy x)
                                  |> (fn it => Drule.compose_single (it, 2, acc_induct_rule)) (* "EX! y. (?x,y):G" *)
                                  |> (fn it => fold (forall_intr o cterm_of thy o Var) (Term.add_vars (prop_of it) []) it)

        val goalstate =  Conjunction.intr graph_is_function complete
                          |> Thm.close_derivation
                          |> Goal.protect
                          |> fold_rev (implies_intr o cprop_of) compat
                          |> implies_intr (cprop_of complete)
    in
      (goalstate, values)
    end


fun define_graph Gname fvar domT ranT clauses RCss lthy =
    let
      val GT = domT --> ranT --> boolT
      val Gvar = Free (the_single (Variable.variant_frees lthy [] [(Gname, GT)]))

      fun mk_GIntro (ClauseContext {qs, gs, lhs, rhs, ...}) RCs =
          let
            fun mk_h_assm (rcfix, rcassm, rcarg) =
                HOLogic.mk_Trueprop (Gvar $ rcarg $ (fvar $ rcarg))
                          |> fold_rev (curry Logic.mk_implies o prop_of) rcassm
                          |> fold_rev (Logic.all o Free) rcfix
          in
            HOLogic.mk_Trueprop (Gvar $ lhs $ rhs)
                      |> fold_rev (curry Logic.mk_implies o mk_h_assm) RCs
                      |> fold_rev (curry Logic.mk_implies) gs
                      |> fold_rev Logic.all (fvar :: qs)
          end

      val G_intros = map2 mk_GIntro clauses RCss

      val (GIntro_thms, (G, G_elim, G_induct, lthy)) =
          FundefInductiveWrap.inductive_def G_intros ((dest_Free Gvar, NoSyn), lthy)
    in
      ((G, GIntro_thms, G_elim, G_induct), lthy)
    end



fun define_function fdefname (fname, mixfix) domT ranT G default lthy =
    let
      val f_def =
          Abs ("x", domT, Const (@{const_name FunDef.THE_default}, ranT --> (ranT --> boolT) --> ranT) $ (default $ Bound 0) $
                                Abs ("y", ranT, G $ Bound 1 $ Bound 0))
              |> Syntax.check_term lthy

      val ((f, (_, f_defthm)), lthy) =
        LocalTheory.define Thm.internalK ((Binding.name (function_name fname), mixfix), ((Binding.name fdefname, []), f_def)) lthy
    in
      ((f, f_defthm), lthy)
    end


fun define_recursion_relation Rname domT ranT fvar f qglrs clauses RCss lthy =
    let

      val RT = domT --> domT --> boolT
      val Rvar = Free (the_single (Variable.variant_frees lthy [] [(Rname, RT)]))

      fun mk_RIntro (ClauseContext {qs, gs, lhs, ...}, (oqs, _, _, _)) (rcfix, rcassm, rcarg) =
          HOLogic.mk_Trueprop (Rvar $ rcarg $ lhs)
                    |> fold_rev (curry Logic.mk_implies o prop_of) rcassm
                    |> fold_rev (curry Logic.mk_implies) gs
                    |> fold_rev (Logic.all o Free) rcfix
                    |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
                    (* "!!qs xs. CS ==> G => (r, lhs) : R" *)

      val R_intross = map2 (map o mk_RIntro) (clauses ~~ qglrs) RCss

      val (RIntro_thmss, (R, R_elim, _, lthy)) =
          fold_burrow FundefInductiveWrap.inductive_def R_intross ((dest_Free Rvar, NoSyn), lthy)
    in
      ((R, RIntro_thmss, R_elim), lthy)
    end


fun fix_globals domT ranT fvar ctxt =
    let
      val ([h, y, x, z, a, D, P, Pbool],ctxt') =
          Variable.variant_fixes ["h_fd", "y_fd", "x_fd", "z_fd", "a_fd", "D_fd", "P_fd", "Pb_fd"] ctxt
    in
      (Globals {h = Free (h, domT --> ranT),
                y = Free (y, ranT),
                x = Free (x, domT),
                z = Free (z, domT),
                a = Free (a, domT),
                D = Free (D, domT --> boolT),
                P = Free (P, domT --> boolT),
                Pbool = Free (Pbool, boolT),
                fvar = fvar,
                domT = domT,
                ranT = ranT
               },
       ctxt')
    end



fun inst_RC thy fvar f (rcfix, rcassm, rcarg) =
    let
      fun inst_term t = subst_bound(f, abstract_over (fvar, t))
    in
      (rcfix, map (assume o cterm_of thy o inst_term o prop_of) rcassm, inst_term rcarg)
    end



(**********************************************************
 *                   PROVING THE RULES
 **********************************************************)

fun mk_psimps thy globals R clauses valthms f_iff graph_is_function =
    let
      val Globals {domT, z, ...} = globals

      fun mk_psimp (ClauseInfo {qglr = (oqs, _, _, _), cdata = ClauseContext {cqs, lhs, ags, ...}, ...}) valthm =
          let
            val lhs_acc = cterm_of thy (HOLogic.mk_Trueprop (mk_acc domT R $ lhs)) (* "acc R lhs" *)
            val z_smaller = cterm_of thy (HOLogic.mk_Trueprop (R $ z $ lhs)) (* "R z lhs" *)
          in
            ((assume z_smaller) RS ((assume lhs_acc) RS acc_downward))
              |> (fn it => it COMP graph_is_function)
              |> implies_intr z_smaller
              |> forall_intr (cterm_of thy z)
              |> (fn it => it COMP valthm)
              |> implies_intr lhs_acc
              |> asm_simplify (HOL_basic_ss addsimps [f_iff])
              |> fold_rev (implies_intr o cprop_of) ags
              |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)
          end
    in
      map2 mk_psimp clauses valthms
    end


(** Induction rule **)


val acc_subset_induct = @{thm Orderings.predicate1I} RS @{thm accp_subset_induct}


fun mk_partial_induct_rule thy globals R complete_thm clauses =
    let
      val Globals {domT, x, z, a, P, D, ...} = globals
      val acc_R = mk_acc domT R

      val x_D = assume (cterm_of thy (HOLogic.mk_Trueprop (D $ x)))
      val a_D = cterm_of thy (HOLogic.mk_Trueprop (D $ a))

      val D_subset = cterm_of thy (Logic.all x
        (Logic.mk_implies (HOLogic.mk_Trueprop (D $ x), HOLogic.mk_Trueprop (acc_R $ x))))

      val D_dcl = (* "!!x z. [| x: D; (z,x):R |] ==> z:D" *)
                    Logic.all x
                    (Logic.all z (Logic.mk_implies (HOLogic.mk_Trueprop (D $ x),
                                                    Logic.mk_implies (HOLogic.mk_Trueprop (R $ z $ x),
                                                                      HOLogic.mk_Trueprop (D $ z)))))
                    |> cterm_of thy


  (* Inductive Hypothesis: !!z. (z,x):R ==> P z *)
      val ihyp = Term.all domT $ Abs ("z", domT,
               Logic.mk_implies (HOLogic.mk_Trueprop (R $ Bound 0 $ x),
                 HOLogic.mk_Trueprop (P $ Bound 0)))
           |> cterm_of thy

      val aihyp = assume ihyp

  fun prove_case clause =
      let
    val ClauseInfo {cdata = ClauseContext {ctxt, qs, cqs, ags, gs, lhs, case_hyp, ...}, RCs,
                    qglr = (oqs, _, _, _), ...} = clause

    val case_hyp_conv = K (case_hyp RS eq_reflection)
    local open Conv in
    val lhs_D = fconv_rule (arg_conv (arg_conv (case_hyp_conv))) x_D
    val sih = fconv_rule (More_Conv.binder_conv (K (arg1_conv (arg_conv (arg_conv case_hyp_conv)))) ctxt) aihyp
    end

    fun mk_Prec (RCInfo {llRI, RIvs, CCas, rcarg, ...}) =
        sih |> forall_elim (cterm_of thy rcarg)
            |> Thm.elim_implies llRI
            |> fold_rev (implies_intr o cprop_of) CCas
            |> fold_rev (forall_intr o cterm_of thy o Free) RIvs

    val P_recs = map mk_Prec RCs   (*  [P rec1, P rec2, ... ]  *)

    val step = HOLogic.mk_Trueprop (P $ lhs)
            |> fold_rev (curry Logic.mk_implies o prop_of) P_recs
            |> fold_rev (curry Logic.mk_implies) gs
            |> curry Logic.mk_implies (HOLogic.mk_Trueprop (D $ lhs))
            |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
            |> cterm_of thy

    val P_lhs = assume step
           |> fold forall_elim cqs
           |> Thm.elim_implies lhs_D
           |> fold Thm.elim_implies ags
           |> fold Thm.elim_implies P_recs

    val res = cterm_of thy (HOLogic.mk_Trueprop (P $ x))
           |> Conv.arg_conv (Conv.arg_conv case_hyp_conv)
           |> symmetric (* P lhs == P x *)
           |> (fn eql => equal_elim eql P_lhs) (* "P x" *)
           |> implies_intr (cprop_of case_hyp)
           |> fold_rev (implies_intr o cprop_of) ags
           |> fold_rev forall_intr cqs
      in
        (res, step)
      end

  val (cases, steps) = split_list (map prove_case clauses)

  val istep = complete_thm
                |> Thm.forall_elim_vars 0
                |> fold (curry op COMP) cases (*  P x  *)
                |> implies_intr ihyp
                |> implies_intr (cprop_of x_D)
                |> forall_intr (cterm_of thy x)

  val subset_induct_rule =
      acc_subset_induct
        |> (curry op COMP) (assume D_subset)
        |> (curry op COMP) (assume D_dcl)
        |> (curry op COMP) (assume a_D)
        |> (curry op COMP) istep
        |> fold_rev implies_intr steps
        |> implies_intr a_D
        |> implies_intr D_dcl
        |> implies_intr D_subset

  val subset_induct_all = fold_rev (forall_intr o cterm_of thy) [P, a, D] subset_induct_rule

  val simple_induct_rule =
      subset_induct_rule
        |> forall_intr (cterm_of thy D)
        |> forall_elim (cterm_of thy acc_R)
        |> assume_tac 1 |> Seq.hd
        |> (curry op COMP) (acc_downward
                              |> (instantiate' [SOME (ctyp_of thy domT)]
                                               (map (SOME o cterm_of thy) [R, x, z]))
                              |> forall_intr (cterm_of thy z)
                              |> forall_intr (cterm_of thy x))
        |> forall_intr (cterm_of thy a)
        |> forall_intr (cterm_of thy P)
    in
      simple_induct_rule
    end



(* FIXME: This should probably use fixed goals, to be more reliable and faster *)
fun mk_domain_intro ctxt (Globals {domT, ...}) R R_cases clause =
    let
      val thy = ProofContext.theory_of ctxt
      val ClauseInfo {cdata = ClauseContext {qs, gs, lhs, rhs, cqs, ...},
                      qglr = (oqs, _, _, _), ...} = clause
      val goal = HOLogic.mk_Trueprop (mk_acc domT R $ lhs)
                          |> fold_rev (curry Logic.mk_implies) gs
                          |> cterm_of thy
    in
      Goal.init goal
      |> (SINGLE (resolve_tac [accI] 1)) |> the
      |> (SINGLE (eresolve_tac [Thm.forall_elim_vars 0 R_cases] 1))  |> the
      |> (SINGLE (auto_tac (clasimpset_of ctxt))) |> the
      |> Goal.conclude
      |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)
    end



(** Termination rule **)

val wf_induct_rule = @{thm Wellfounded.wfP_induct_rule};
val wf_in_rel = @{thm FunDef.wf_in_rel};
val in_rel_def = @{thm FunDef.in_rel_def};

fun mk_nest_term_case thy globals R' ihyp clause =
    let
      val Globals {x, z, ...} = globals
      val ClauseInfo {cdata = ClauseContext {qs,cqs,ags,lhs,rhs,case_hyp,...},tree,
                      qglr=(oqs, _, _, _), ...} = clause

      val ih_case = full_simplify (HOL_basic_ss addsimps [case_hyp]) ihyp

      fun step (fixes, assumes) (_ $ arg) u (sub,(hyps,thms)) =
          let
            val used = map (fn (ctx,thm) => FundefCtxTree.export_thm thy ctx thm) (u @ sub)

            val hyp = HOLogic.mk_Trueprop (R' $ arg $ lhs)
                      |> fold_rev (curry Logic.mk_implies o prop_of) used (* additional hyps *)
                      |> FundefCtxTree.export_term (fixes, assumes)
                      |> fold_rev (curry Logic.mk_implies o prop_of) ags
                      |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
                      |> cterm_of thy

            val thm = assume hyp
                      |> fold forall_elim cqs
                      |> fold Thm.elim_implies ags
                      |> FundefCtxTree.import_thm thy (fixes, assumes)
                      |> fold Thm.elim_implies used (*  "(arg, lhs) : R'"  *)

            val z_eq_arg = assume (cterm_of thy (HOLogic.mk_Trueprop (mk_eq (z, arg))))

            val acc = thm COMP ih_case
            val z_acc_local = acc
            |> Conv.fconv_rule (Conv.arg_conv (Conv.arg_conv (K (symmetric (z_eq_arg RS eq_reflection)))))

            val ethm = z_acc_local
                         |> FundefCtxTree.export_thm thy (fixes,
                                                          z_eq_arg :: case_hyp :: ags @ assumes)
                         |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)

            val sub' = sub @ [(([],[]), acc)]
          in
            (sub', (hyp :: hyps, ethm :: thms))
          end
        | step _ _ _ _ = raise Match
    in
      FundefCtxTree.traverse_tree step tree
    end


fun mk_nest_term_rule thy globals R R_cases clauses =
    let
      val Globals { domT, x, z, ... } = globals
      val acc_R = mk_acc domT R

      val R' = Free ("R", fastype_of R)

      val Rrel = Free ("R", HOLogic.mk_setT (HOLogic.mk_prodT (domT, domT)))
      val inrel_R = Const (@{const_name FunDef.in_rel}, HOLogic.mk_setT (HOLogic.mk_prodT (domT, domT)) --> fastype_of R) $ Rrel

      val wfR' = cterm_of thy (HOLogic.mk_Trueprop (Const (@{const_name Wellfounded.wfP}, (domT --> domT --> boolT) --> boolT) $ R')) (* "wf R'" *)

      (* Inductive Hypothesis: !!z. (z,x):R' ==> z : acc R *)
      val ihyp = Term.all domT $ Abs ("z", domT,
                                 Logic.mk_implies (HOLogic.mk_Trueprop (R' $ Bound 0 $ x),
                                   HOLogic.mk_Trueprop (acc_R $ Bound 0)))
                     |> cterm_of thy

      val ihyp_a = assume ihyp |> Thm.forall_elim_vars 0

      val R_z_x = cterm_of thy (HOLogic.mk_Trueprop (R $ z $ x))

      val (hyps,cases) = fold (mk_nest_term_case thy globals R' ihyp_a) clauses ([],[])
    in
      R_cases
        |> forall_elim (cterm_of thy z)
        |> forall_elim (cterm_of thy x)
        |> forall_elim (cterm_of thy (acc_R $ z))
        |> curry op COMP (assume R_z_x)
        |> fold_rev (curry op COMP) cases
        |> implies_intr R_z_x
        |> forall_intr (cterm_of thy z)
        |> (fn it => it COMP accI)
        |> implies_intr ihyp
        |> forall_intr (cterm_of thy x)
        |> (fn it => Drule.compose_single(it,2,wf_induct_rule))
        |> curry op RS (assume wfR')
        |> forall_intr_vars
        |> (fn it => it COMP allI)
        |> fold implies_intr hyps
        |> implies_intr wfR'
        |> forall_intr (cterm_of thy R')
        |> forall_elim (cterm_of thy (inrel_R))
        |> curry op RS wf_in_rel
        |> full_simplify (HOL_basic_ss addsimps [in_rel_def])
        |> forall_intr (cterm_of thy Rrel)
    end



(* Tail recursion (probably very fragile)
 *
 * FIXME:
 * - Need to do forall_elim_vars on psimps: Unneccesary, if psimps would be taken from the same context.
 * - Must we really replace the fvar by f here?
 * - Splitting is not configured automatically: Problems with case?
 *)
fun mk_trsimps octxt globals f G R f_def R_cases G_induct clauses psimps =
    let
      val Globals {domT, ranT, fvar, ...} = globals

      val R_cases = Thm.forall_elim_vars 0 R_cases (* FIXME: Should be already in standard form. *)

      val graph_implies_dom = (* "G ?x ?y ==> dom ?x"  *)
          Goal.prove octxt ["x", "y"] [HOLogic.mk_Trueprop (G $ Free ("x", domT) $ Free ("y", ranT))]
                     (HOLogic.mk_Trueprop (mk_acc domT R $ Free ("x", domT)))
                     (fn {prems=[a], ...} =>
                         ((rtac (G_induct OF [a]))
                            THEN_ALL_NEW (rtac accI)
                            THEN_ALL_NEW (etac R_cases)
                            THEN_ALL_NEW (asm_full_simp_tac (simpset_of octxt))) 1)

      val default_thm = (forall_intr_vars graph_implies_dom) COMP (f_def COMP fundef_default_value)

      fun mk_trsimp clause psimp =
          let
            val ClauseInfo {qglr = (oqs, _, _, _), cdata = ClauseContext {ctxt, cqs, qs, gs, lhs, rhs, ...}, ...} = clause
            val thy = ProofContext.theory_of ctxt
            val rhs_f = Pattern.rewrite_term thy [(fvar, f)] [] rhs

            val trsimp = Logic.list_implies(gs, HOLogic.mk_Trueprop (HOLogic.mk_eq(f $ lhs, rhs_f))) (* "f lhs = rhs" *)
            val lhs_acc = (mk_acc domT R $ lhs) (* "acc R lhs" *)
            fun simp_default_tac ss = asm_full_simp_tac (ss addsimps [default_thm, Let_def])
          in
            Goal.prove ctxt [] [] trsimp
                       (fn _ =>
                           rtac (instantiate' [] [SOME (cterm_of thy lhs_acc)] case_split) 1
                                THEN (rtac (Thm.forall_elim_vars 0 psimp) THEN_ALL_NEW assume_tac) 1
                                THEN (simp_default_tac (simpset_of ctxt) 1)
                                THEN (etac not_acc_down 1)
                                THEN ((etac R_cases) THEN_ALL_NEW (simp_default_tac (simpset_of ctxt))) 1)
              |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)
          end
    in
      map2 mk_trsimp clauses psimps
    end


fun prepare_fundef config defname [((fname, fT), mixfix)] abstract_qglrs lthy =
    let
      val FundefConfig {domintros, tailrec, default=default_str, ...} = config

      val fvar = Free (fname, fT)
      val domT = domain_type fT
      val ranT = range_type fT

      val default = Syntax.parse_term lthy default_str
        |> TypeInfer.constrain fT |> Syntax.check_term lthy

      val (globals, ctxt') = fix_globals domT ranT fvar lthy

      val Globals { x, h, ... } = globals

      val clauses = map (mk_clause_context x ctxt') abstract_qglrs

      val n = length abstract_qglrs

      fun build_tree (ClauseContext { ctxt, rhs, ...}) =
            FundefCtxTree.mk_tree (fname, fT) h ctxt rhs

      val trees = map build_tree clauses
      val RCss = map find_calls trees

      val ((G, GIntro_thms, G_elim, G_induct), lthy) =
          PROFILE "def_graph" (define_graph (graph_name defname) fvar domT ranT clauses RCss) lthy

      val ((f, f_defthm), lthy) =
          PROFILE "def_fun" (define_function (defname ^ "_sumC_def") (fname, mixfix) domT ranT G default) lthy

      val RCss = map (map (inst_RC (ProofContext.theory_of lthy) fvar f)) RCss
      val trees = map (FundefCtxTree.inst_tree (ProofContext.theory_of lthy) fvar f) trees

      val ((R, RIntro_thmss, R_elim), lthy) =
          PROFILE "def_rel" (define_recursion_relation (rel_name defname) domT ranT fvar f abstract_qglrs clauses RCss) lthy

      val (_, lthy) =
          LocalTheory.abbrev Syntax.mode_default ((Binding.name (dom_name defname), NoSyn), mk_acc domT R) lthy

      val newthy = ProofContext.theory_of lthy
      val clauses = map (transfer_clause_ctx newthy) clauses

      val cert = cterm_of (ProofContext.theory_of lthy)

      val xclauses = PROFILE "xclauses" (map7 (mk_clause_info globals G f) (1 upto n) clauses abstract_qglrs trees RCss GIntro_thms) RIntro_thmss

      val complete = mk_completeness globals clauses abstract_qglrs |> cert |> assume
      val compat = mk_compat_proof_obligations domT ranT fvar f abstract_qglrs |> map (cert #> assume)

      val compat_store = store_compat_thms n compat

      val (goalstate, values) = PROFILE "prove_stuff" (prove_stuff lthy globals G f R xclauses complete compat compat_store G_elim) f_defthm

      val mk_trsimps = mk_trsimps lthy globals f G R f_defthm R_elim G_induct xclauses

      fun mk_partial_rules provedgoal =
          let
            val newthy = theory_of_thm provedgoal (*FIXME*)

            val (graph_is_function, complete_thm) =
                provedgoal
                  |> Conjunction.elim
                  |> apfst (Thm.forall_elim_vars 0)

            val f_iff = graph_is_function RS (f_defthm RS ex1_implies_iff)

            val psimps = PROFILE "Proving simplification rules" (mk_psimps newthy globals R xclauses values f_iff) graph_is_function

            val simple_pinduct = PROFILE "Proving partial induction rule"
                                                           (mk_partial_induct_rule newthy globals R complete_thm) xclauses


            val total_intro = PROFILE "Proving nested termination rule" (mk_nest_term_rule newthy globals R R_elim) xclauses

            val dom_intros = if domintros
                             then SOME (PROFILE "Proving domain introduction rules" (map (mk_domain_intro lthy globals R R_elim)) xclauses)
                             else NONE
            val trsimps = if tailrec then SOME (mk_trsimps psimps) else NONE

          in
            FundefResult {fs=[f], G=G, R=R, cases=complete_thm,
                          psimps=psimps, simple_pinducts=[simple_pinduct],
                          termination=total_intro, trsimps=trsimps,
                          domintros=dom_intros}
          end
    in
      ((f, goalstate, mk_partial_rules), lthy)
    end


end
