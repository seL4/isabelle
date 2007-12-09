(*  Title:      HOL/Tools/function_package/induction_scheme.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A method to prove induction schemes.
*)

signature INDUCTION_SCHEME =
sig
  val mk_ind_tac : Proof.context -> thm list -> tactic  
  val setup : theory -> theory
end


structure InductionScheme : INDUCTION_SCHEME =
struct

open FundefLib

type rec_call_info = (string * typ) list * term list * term

datatype scheme_case =
  SchemeCase of
  {
   qs: (string * typ) list,
   gs: term list,
   lhs: term,
   rs: rec_call_info list
  }

datatype ind_scheme =
  IndScheme of
  {
   T: typ,
   cases: scheme_case list
  }


fun mk_relT T = HOLogic.mk_setT (HOLogic.mk_prodT (T, T))

fun dest_hhf ctxt t = 
    let 
      val (ctxt', vars, imp) = dest_all_all_ctx ctxt t
    in
      (ctxt', vars, Logic.strip_imp_prems imp, Logic.strip_imp_concl imp)
    end

fun mk_case P ctxt premise =
    let
      val (ctxt', qs, prems, concl) = dest_hhf ctxt premise
      val _ $ (_ $ lhs) = concl 

      fun mk_rcinfo pr =
          let
            val (ctxt'', Gvs, Gas, _ $ (_ $ rcarg)) = dest_hhf ctxt' pr
          in
            (Gvs, Gas, rcarg)
          end

      val (gs, rcprs) = take_prefix (not o exists_aterm (fn Free v => v = P | _ => false)) prems
    in
      SchemeCase {qs=qs, gs=gs, lhs=lhs, rs=map mk_rcinfo rcprs}
    end

fun mk_scheme' ctxt cases (Pn, PT) =
    IndScheme {T=domain_type PT, cases=map (mk_case (Pn,PT) ctxt) cases }

fun mk_completeness ctxt (IndScheme {T, cases}) =
    let
      val allqnames = fold (fn SchemeCase {qs, ...} => fold (insert (op =) o Free) qs) cases []
      val [Pbool, x] = map Free (Variable.variant_frees ctxt allqnames [("P", HOLogic.boolT), ("x", T)])
                       
      fun mk_case (SchemeCase {qs, gs, lhs, ...}) =
          HOLogic.mk_Trueprop Pbool
                     |> curry Logic.mk_implies (HOLogic.mk_Trueprop (HOLogic.mk_eq (x, lhs)))
                     |> fold_rev (curry Logic.mk_implies) gs
                     |> fold_rev (mk_forall o Free) qs
    in
      HOLogic.mk_Trueprop Pbool
       |> fold_rev (curry Logic.mk_implies o mk_case) cases
       |> mk_forall_rename ("x", x)
       |> mk_forall_rename ("P", Pbool)
    end

fun mk_wf ctxt R (IndScheme {T, ...}) =
    HOLogic.Trueprop $ (Const (@{const_name "wf"}, mk_relT T --> HOLogic.boolT) $ R)

fun mk_ineqs R (IndScheme {T, cases}) =
    let
      fun f (SchemeCase {qs, gs, lhs, rs, ...}) = 
          let
            fun g (Gvs, Gas, rcarg) =
                HOLogic.mk_mem (HOLogic.mk_prod (rcarg, lhs), R)
                  |> HOLogic.mk_Trueprop
                  |> fold_rev (curry Logic.mk_implies) Gas
                  |> fold_rev (curry Logic.mk_implies) gs
                  |> fold_rev (mk_forall o Free) Gvs
                  |> fold_rev (mk_forall o Free) qs
          in
            map g rs
          end
    in
      map f cases
    end


fun mk_induct_rule thy R complete_thm wf_thm ineqss (IndScheme {T, cases=scases}) =
    let
      val x = Free ("x", T)
      val P = Free ("P", T --> HOLogic.boolT)

      val cert = cterm_of thy 
                
      (* Inductive Hypothesis: !!z. (z,x):R ==> P z *)
      val ihyp = all T $ Abs ("z", T, 
               implies $ 
                  HOLogic.mk_Trueprop (
                  Const ("op :", HOLogic.mk_prodT (T, T) --> mk_relT T --> HOLogic.boolT) 
                    $ (HOLogic.pair_const T T $ Bound 0 $ x) 
                    $ R)
             $ HOLogic.mk_Trueprop (P $ Bound 0))
           |> cert

      val aihyp = assume ihyp

      fun prove_case (SchemeCase {qs, gs, lhs, rs, ...}) ineqs =
          let
            val case_hyp = assume (cert (HOLogic.Trueprop $ (HOLogic.mk_eq (x, lhs))))
                           
            val cqs = map (cert o Free) qs
            val ags = map (assume o cert) gs
                      
            val replace_x_ss = HOL_basic_ss addsimps [case_hyp]
            val sih = full_simplify replace_x_ss aihyp
                      
            fun mk_Prec (Gvs, Gas, rcarg) ineq =
                let
                  val cGas = map (assume o cert) Gas
                  val cGvs = map (cert o Free) Gvs
                  val loc_ineq = ineq 
                                   |> fold forall_elim (cqs @ cGvs)
                                   |> fold Thm.elim_implies (ags @ cGas)
                in
                  sih |> forall_elim (cert rcarg)
                      |> Thm.elim_implies loc_ineq
                      |> fold_rev (implies_intr o cprop_of) cGas
                      |> fold_rev forall_intr cGvs
                end
                
            val P_recs = map2 mk_Prec rs ineqs   (*  [P rec1, P rec2, ... ]  *)
                         
            val step = HOLogic.mk_Trueprop (P $ lhs)
                                           |> fold_rev (curry Logic.mk_implies o prop_of) P_recs
                                           |> fold_rev (curry Logic.mk_implies) gs
                                           |> fold_rev (mk_forall o Free) qs
                                           |> cert
                       
            val res = assume step
                       |> fold forall_elim cqs
                       |> fold Thm.elim_implies ags
                       |> fold Thm.elim_implies P_recs
                       |> Conv.fconv_rule 
                       (Conv.arg_conv (Conv.arg_conv (K (Thm.symmetric (case_hyp RS eq_reflection))))) 
                       (* "P x" *)
                       |> implies_intr (cprop_of case_hyp)
                       |> fold_rev (implies_intr o cprop_of) ags
                       |> fold_rev forall_intr cqs
          in
            (res, step)
          end
          
      val (cases, steps) = split_list (map2 prove_case scases ineqss)
                           
      val istep = complete_thm 
                |> forall_elim (cert (P $ x))
                |> forall_elim (cert x)
                |> fold (Thm.elim_implies) cases
                |> implies_intr ihyp
                |> forall_intr (cert x) (* "!!x. (!!y<x. P y) ==> P x" *)
         
      val induct_rule =
          @{thm "wf_induct_rule"}
            |> (curry op COMP) wf_thm 
            |> (curry op COMP) istep
            |> fold_rev implies_intr steps
            |> forall_intr (cert P)
    in
      induct_rule
    end

fun mk_ind_tac ctxt facts = (ALLGOALS (Method.insert_tac facts)) THEN HEADGOAL 
(SUBGOAL (fn (t, i) =>
  let
    val (ctxt', _, cases, concl) = dest_hhf ctxt t
                                   
    fun get_types t = 
        let
          val (P, vs) = strip_comb (HOLogic.dest_Trueprop t)
          val Ts = map fastype_of vs
          val tupT = foldr1 HOLogic.mk_prodT Ts
        in 
          ((P, Ts), tupT)
        end
        
    val concls = Logic.dest_conjunction_list (Logic.strip_imp_concl concl)
    val (PTss, tupTs) = split_list (map get_types concls)
                        
    val n = length tupTs
    val ST = BalancedTree.make (uncurry SumTree.mk_sumT) tupTs
    val PsumT = ST --> HOLogic.boolT
    val Psum = ("Psum", PsumT)
               
    fun mk_rews (i, (P, Ts)) = 
        let
          val vs = map_index (fn (j,T) => Free ("x" ^ string_of_int j, T)) Ts 
          val t = Free Psum $ SumTree.mk_inj ST n (i + 1) (foldr1 HOLogic.mk_prod vs)
                       |> fold_rev lambda vs
        in
          (P, t)
        end
        
    val rews = map_index mk_rews PTss
    val thy = ProofContext.theory_of ctxt'
    val cases' = map (Pattern.rewrite_term thy rews []) cases
                 
    val scheme = mk_scheme' ctxt' cases' Psum

    val cert = cterm_of thy

    val R = Free ("R", mk_relT ST)
    val ineqss = mk_ineqs R scheme
                   |> map (map (assume o cert))
    val complete = mk_completeness ctxt scheme |> cert |> assume
    val wf_thm = mk_wf ctxt R scheme |> cert |> assume

    val indthm = mk_induct_rule thy R complete wf_thm ineqss scheme

    fun mk_P (P, Ts) = 
        let
          val avars = map_index (fn (i,T) => Var (("a", i), T)) Ts
          val atup = foldr1 HOLogic.mk_prod avars
        in
          tupled_lambda atup (list_comb (P, avars))
        end
          
    val case_exp = cert (SumTree.mk_sumcases HOLogic.boolT (map mk_P PTss))
    val acases = map (assume o cert) cases
    val indthm' = indthm |> forall_elim case_exp
                         |> full_simplify SumTree.sumcase_split_ss
                         |> fold Thm.elim_implies acases

    fun project (i,t) = 
        let
          val (P, vs) = strip_comb (HOLogic.dest_Trueprop t)
          val inst = cert (SumTree.mk_inj ST n (i + 1) (foldr1 HOLogic.mk_prod vs))
        in
          indthm' |> Drule.instantiate' [] [SOME inst]
                  |> simplify SumTree.sumcase_split_ss
        end                  

    val res = Conjunction.intr_balanced (map_index project concls)
                |> fold_rev (implies_intr o cprop_of) acases
                |> forall_elim_vars 0
        in
          (fn st =>
        Drule.compose_single (res, i, st)
          |> fold_rev (implies_intr o cprop_of) (complete :: wf_thm :: flat ineqss)
          |> forall_intr (cert R)
          |> forall_elim_vars 0
          |> Seq.single
          )
  end))


val setup = Method.add_methods
  [("induct_scheme", Method.ctxt_args (Method.RAW_METHOD o mk_ind_tac),
    "proves an induction principle")]

end
