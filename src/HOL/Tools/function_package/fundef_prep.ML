(*  Title:      HOL/Tools/function_package/fundef_prep.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.
Preparation step: makes auxiliary definitions and generates
proof obligations.
*)

signature FUNDEF_PREP =
sig
    val prepare_fundef : string (* defname *)
                         -> (string * typ * mixfix) (* defined symbol *)
                         -> ((string * typ) list * term list * term * term) list (* specification *)
                         -> string (* default_value, not parsed yet *)
                         -> local_theory
                         -> FundefCommon.prep_result * term * local_theory

end

structure FundefPrep : FUNDEF_PREP =
struct


open FundefLib
open FundefCommon
open FundefAbbrev

(* Theory dependencies. *)
val Pair_inject = thm "Product_Type.Pair_inject";

val acc_induct_rule = thm "FunDef.accP_induct_rule"

val ex1_implies_ex = thm "FunDef.fundef_ex1_existence"
val ex1_implies_un = thm "FunDef.fundef_ex1_uniqueness"
val ex1_implies_iff = thm "FunDef.fundef_ex1_iff"

val conjunctionI = thm "conjunctionI";



fun find_calls tree =
    let
      fun add_Ri (fixes,assumes) (_ $ arg) _ (_, xs) = ([], (fixes, assumes, arg) :: xs)
        | add_Ri _ _ _ _ = raise Match
    in
      rev (FundefCtxTree.traverse_tree add_Ri tree [])
    end


fun mk_compat_proof_obligations domT ranT fvar f glrs =
    let
      fun mk_impl ((qs, gs, lhs, rhs),(qs', gs', lhs', rhs')) =
          let
            val shift = incr_boundvars (length qs')
          in
            (implies $ Trueprop (eq_const domT $ shift lhs $ lhs')
                     $ Trueprop (eq_const ranT $ shift rhs $ rhs'))
              |> fold_rev (curry Logic.mk_implies) (map shift gs @ gs')
              |> fold_rev (fn (n,T) => fn b => all T $ Abs(n,T,b)) (qs @ qs')
              |> curry abstract_over fvar
              |> curry subst_bound f
          end
    in
      map mk_impl (unordered_pairs glrs)
    end


fun mk_completeness (Globals {x, Pbool, ...}) clauses qglrs =
    let
        fun mk_case (ClauseContext {qs, gs, lhs, ...}, (oqs, _, _, _)) =
            Trueprop Pbool
                     |> curry Logic.mk_implies (Trueprop (mk_eq (x, lhs)))
                     |> fold_rev (curry Logic.mk_implies) gs
                     |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
    in
        Trueprop Pbool
                 |> fold_rev (curry Logic.mk_implies o mk_case) (clauses ~~ qglrs)
                 |> mk_forall_rename ("x", x)
                 |> mk_forall_rename ("P", Pbool)
    end


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
                  
      val case_hyp = assume (cterm_of thy (Trueprop (mk_eq (x, lhs))))
    in
      ClauseContext { ctxt = ctxt', qs = qs, gs = gs, lhs = lhs, rhs = rhs, 
                      cqs = cqs, ags = ags, case_hyp = case_hyp }
    end
      

(* lowlevel term function *)
fun abstract_over_list vs body =
  let
    exception SAME;
    fun abs lev v tm =
      if v aconv tm then Bound lev
      else
        (case tm of
          Abs (a, T, t) => Abs (a, T, abs (lev + 1) v t)
        | t $ u => (abs lev v t $ (abs lev v u handle SAME => u) handle SAME => t $ abs lev v u)
        | _ => raise SAME);
  in 
    fold_index (fn (i,v) => fn t => abs i v t handle SAME => t) vs body
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
                    |> fold implies_elim_swp ags

        fun mk_call_info (rcfix, rcassm, rcarg) RI =
            let
                val llRI = RI
                             |> fold forall_elim cqs
                             |> fold (forall_elim o cert o Free) rcfix
                             |> fold implies_elim_swp ags
                             |> fold implies_elim_swp rcassm

                val h_assum =
                    Trueprop (G $ rcarg $ (h $ rcarg))
                              |> fold_rev (curry Logic.mk_implies o prop_of) rcassm
                              |> fold_rev (mk_forall o Free) rcfix
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
          
      val lhsi_eq_lhsj = cterm_of thy (Trueprop (mk_eq (lhsi, lhsj)))
    in if j < i then
         let
           val compat = lookup_compat_thm j i cts
         in
           compat         (* "!!qj qi. Gsj => Gsi => lhsj = lhsi ==> rhsj = rhsi" *)
                |> fold forall_elim (cqsj @ cqsi) (* "Gsj => Gsi => lhsj = lhsi ==> rhsj = rhsi" *)
                |> fold implies_elim_swp agsj
                |> fold implies_elim_swp agsi
                |> implies_elim_swp ((assume lhsi_eq_lhsj) RS sym) (* "Gsj, Gsi, lhsi = lhsj |-- rhsj = rhsi" *)
         end
       else
         let
           val compat = lookup_compat_thm i j cts
         in
               compat        (* "!!qi qj. Gsi => Gsj => lhsi = lhsj ==> rhsi = rhsj" *)
                 |> fold forall_elim (cqsi @ cqsj) (* "Gsi => Gsj => lhsi = lhsj ==> rhsi = rhsj" *)
                 |> fold implies_elim_swp agsi
                 |> fold implies_elim_swp agsj
                 |> implies_elim_swp (assume lhsi_eq_lhsj)
                 |> (fn thm => thm RS sym) (* "Gsi, Gsj, lhsi = lhsj |-- rhsj = rhsi" *)
         end
    end




(* Generates the replacement lemma in fully quantified form. *)
fun mk_replacement_lemma thy h ih_elim clause =
    let
        val ClauseInfo {cdata=ClauseContext {qs, lhs, rhs, cqs, ags, case_hyp, ...}, RCs, tree, ...} = clause

        val ih_elim_case = full_simplify (HOL_basic_ss addsimps [case_hyp]) ih_elim

        val Ris = map (fn RCInfo {llRI, ...} => llRI) RCs
        val h_assums = map (fn RCInfo {h_assum, ...} => assume (cterm_of thy (subst_bounds (rev qs, h_assum)))) RCs

        val ih_elim_case_inst = instantiate' [] [NONE, SOME (cterm_of thy h)] ih_elim_case (* Should be done globally *)

        val (eql, _) = FundefCtxTree.rewrite_by_tree thy h ih_elim_case_inst (Ris ~~ h_assums) tree

        val replace_lemma = (eql RS meta_eq_to_obj_eq)
                                |> implies_intr (cprop_of case_hyp)
                                |> fold_rev (implies_intr o cprop_of) h_assums
                                |> fold_rev (implies_intr o cprop_of) ags
                                |> fold_rev forall_intr cqs
                                |> Goal.close_result
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
                |> fold implies_elim_swp agsj'
                |> fold implies_elim_swp Ghsj'

        val y_eq_rhsj'h = assume (cterm_of thy (Trueprop (mk_eq (y, rhsj'h))))
        val lhsi_eq_lhsj' = assume (cterm_of thy (Trueprop (mk_eq (lhsi, lhsj')))) (* lhs_i = lhs_j' |-- lhs_i = lhs_j' *)
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



fun mk_uniqueness_case thy globals G f ihyp ih_intro G_cases compat_store clauses rep_lemmas clausei =
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
        val G_lhs_y = assume (cterm_of thy (Trueprop (G $ lhs $ y)))

        val unique_clauses = map2 (mk_uniqueness_clause thy globals f compat_store clausei) clauses rep_lemmas

        val uniqueness = G_cases
                           |> forall_elim (cterm_of thy lhs)
                           |> forall_elim (cterm_of thy y)
                           |> forall_elim P
                           |> implies_elim_swp G_lhs_y
                           |> fold implies_elim_swp unique_clauses
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




fun prove_stuff thy congs globals G f R clauses complete compat compat_store G_elim f_def =
    let
        val Globals {h, domT, ranT, x, ...} = globals

        val inst_ex1_ex =  f_def RS ex1_implies_ex
        val inst_ex1_un =  f_def RS ex1_implies_un
        val inst_ex1_iff = f_def RS ex1_implies_iff

        (* Inductive Hypothesis: !!z. (z,x):R ==> EX!y. (z,y):G *)
        val ihyp = all domT $ Abs ("z", domT,
                                   implies $ Trueprop (R $ Bound 0 $ x)
                                           $ Trueprop (Const ("Ex1", (ranT --> boolT) --> boolT) $
                                                             Abs ("y", ranT, G $ Bound 1 $ Bound 0)))
                       |> cterm_of thy

        val ihyp_thm = assume ihyp |> forall_elim_vars 0
        val ih_intro = ihyp_thm RS inst_ex1_ex
        val ih_elim = ihyp_thm RS inst_ex1_un

        val _ = Output.debug "Proving Replacement lemmas..."
        val repLemmas = map (mk_replacement_lemma thy h ih_elim) clauses

        val _ = Output.debug "Proving cases for unique existence..."
        val (ex1s, values) = 
            split_list (map (mk_uniqueness_case thy globals G f ihyp ih_intro G_elim compat_store clauses repLemmas) clauses)

        val _ = Output.debug "Proving: Graph is a function" (* FIXME: Rewrite this proof. *)
        val graph_is_function = complete
                                  |> forall_elim_vars 0
                                  |> fold (curry op COMP) ex1s
                                  |> implies_intr (ihyp)
                                  |> implies_intr (cterm_of thy (Trueprop (mk_acc domT R $ x)))
                                  |> forall_intr (cterm_of thy x)
                                  |> (fn it => Drule.compose_single (it, 2, acc_induct_rule)) (* "EX! y. (?x,y):G" *)
                                  |> (fn it => fold (forall_intr o cterm_of thy) (term_vars (prop_of it)) it)

        val goal = complete COMP (graph_is_function COMP conjunctionI)
                            |> Goal.close_result

        val goalI = Goal.protect goal
                                 |> fold_rev (implies_intr o cprop_of) compat
                                 |> implies_intr (cprop_of complete)
    in
      (prop_of goal, goalI, inst_ex1_iff, values)
    end


fun define_graph Gname fvar domT ranT clauses RCss lthy =
    let
      val GT = domT --> ranT --> boolT
      val Gvar = Free (the_single (Variable.variant_frees lthy [] [(Gname, GT)]))

      fun mk_GIntro (ClauseContext {qs, gs, lhs, rhs, ...}) RCs =
          let
            fun mk_h_assm (rcfix, rcassm, rcarg) =
                Trueprop (Gvar $ rcarg $ (fvar $ rcarg))
                          |> fold_rev (curry Logic.mk_implies o prop_of) rcassm
                          |> fold_rev (mk_forall o Free) rcfix
          in
            Trueprop (Gvar $ lhs $ rhs)
                      |> fold_rev (curry Logic.mk_implies o mk_h_assm) RCs
                      |> fold_rev (curry Logic.mk_implies) gs
                      |> fold_rev mk_forall (fvar :: qs)
          end
          
      val G_intros = map2 mk_GIntro clauses RCss
                     
      val (GIntro_thms, (G, G_elim, lthy)) = 
          FundefInductiveWrap.inductive_def G_intros ((dest_Free Gvar, NoSyn), lthy)
    in
      ((G, GIntro_thms, G_elim), lthy)
    end



fun define_function fdefname (fname, mixfix) domT ranT G default lthy =
    let
      val f_def = 
          Abs ("x", domT, Const ("FunDef.THE_default", ranT --> (ranT --> boolT) --> ranT) $ (default $ Bound 0) $
                                Abs ("y", ranT, G $ Bound 1 $ Bound 0))
              |> Envir.beta_norm (* FIXME: LocalTheory.def does not work if not beta-normal *)
          
      val ((f, (_, f_defthm)), lthy) =
        LocalTheory.def Thm.internalK ((fname ^ "C", mixfix), ((fdefname, []), f_def)) lthy
    in
      ((f, f_defthm), lthy)
    end


fun define_recursion_relation Rname domT ranT fvar f qglrs clauses RCss lthy =
    let

      val RT = domT --> domT --> boolT
      val Rvar = Free (the_single (Variable.variant_frees lthy [] [(Rname, RT)]))

      fun mk_RIntro (ClauseContext {qs, gs, lhs, ...}, (oqs, _, _, _)) (rcfix, rcassm, rcarg) =
          Trueprop (Rvar $ rcarg $ lhs)
                    |> fold_rev (curry Logic.mk_implies o prop_of) rcassm
                    |> fold_rev (curry Logic.mk_implies) gs
                    |> fold_rev (mk_forall o Free) rcfix
                    |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
                    (* "!!qs xs. CS ==> G => (r, lhs) : R" *)

      val R_intross = map2 (map o mk_RIntro) (clauses ~~ qglrs) RCss

      val (RIntro_thmss, (R, R_elim, lthy)) = 
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



fun prepare_fundef defname (fname, fT, mixfix) abstract_qglrs default_str lthy =
    let
      val fvar = Free (fname, fT)
      val domT = domain_type fT
      val ranT = range_type fT
                            
      val [default] = fst (Variable.importT_terms (fst (ProofContext.read_termTs lthy (K false) (K NONE) (K NONE) [] [(default_str, fT)])) lthy) (* FIXME *)

      val congs = get_fundef_congs (Context.Proof lthy)
      val (globals, ctxt') = fix_globals domT ranT fvar lthy

      val Globals { x, h, ... } = globals

      val clauses = PROFILE "mk_clause_context" (map (mk_clause_context x ctxt')) abstract_qglrs 

      val n = length abstract_qglrs

      val congs_deps = map (fn c => (c, FundefCtxTree.cong_deps c)) (congs @ FundefCtxTree.add_congs) (* FIXME: Save in theory *)
              
      fun build_tree (ClauseContext { ctxt, rhs, ...}) = 
            FundefCtxTree.mk_tree congs_deps (fname, fT) h ctxt rhs

      val trees = PROFILE "making trees" (map build_tree) clauses
      val RCss = PROFILE "finding calls" (map find_calls) trees

      val ((G, GIntro_thms, G_elim), lthy) = PROFILE "def_graph" (define_graph (graph_name defname) fvar domT ranT clauses RCss) lthy
      val ((f, f_defthm), lthy) = PROFILE "def_fun" (define_function (defname ^ "_sum_def") (fname, mixfix) domT ranT G default) lthy

      val RCss = PROFILE "inst_RCs" (map (map (inst_RC (ProofContext.theory_of lthy) fvar f))) RCss
      val trees = PROFILE "inst_trees" (map (FundefCtxTree.inst_tree (ProofContext.theory_of lthy) fvar f)) trees

      val ((R, RIntro_thmss, R_elim), lthy) = 
          PROFILE "def_rel" (define_recursion_relation (rel_name defname) domT ranT fvar f abstract_qglrs clauses RCss) lthy

      val lthy = PROFILE "abbrev"
        (LocalTheory.abbrev Syntax.default_mode ((defname ^ "_dom", NoSyn), mk_acc domT R)) lthy

      val newthy = ProofContext.theory_of lthy
      val clauses = map (transfer_clause_ctx newthy) clauses

      val cert = cterm_of (ProofContext.theory_of lthy)

      val xclauses = PROFILE "xclauses" (map7 (mk_clause_info globals G f) (1 upto n) clauses abstract_qglrs trees RCss GIntro_thms) RIntro_thmss

      val complete = PROFILE "mk_compl" (mk_completeness globals clauses) abstract_qglrs |> cert |> assume
      val compat = PROFILE "mk_compat" (mk_compat_proof_obligations domT ranT fvar f) abstract_qglrs |> map (cert #> assume)

      val compat_store = store_compat_thms n compat

      val (goal, goalI, ex1_iff, values) = PROFILE "prove_stuff" (prove_stuff newthy congs globals G f R xclauses complete compat compat_store G_elim) f_defthm
    in
        (Prep {globals = globals, f = f, G = G, R = R, goal = goal, goalI = goalI, values = values, clauses = xclauses, ex1_iff = ex1_iff, R_cases = R_elim}, f,
         lthy)
    end




end
