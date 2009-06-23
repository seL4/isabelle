(*  Title:      HOL/Tools/Function/induction_scheme.ML
    Author:     Alexander Krauss, TU Muenchen

A method to prove induction schemes.
*)

signature INDUCTION_SCHEME =
sig
  val mk_ind_tac : (int -> tactic) -> (int -> tactic) -> (int -> tactic)
                   -> Proof.context -> thm list -> tactic
  val induct_scheme_tac : Proof.context -> thm list -> tactic
  val setup : theory -> theory
end


structure InductionScheme : INDUCTION_SCHEME =
struct

open FundefLib


type rec_call_info = int * (string * typ) list * term list * term list

datatype scheme_case =
  SchemeCase of
  {
   bidx : int,
   qs: (string * typ) list,
   oqnames: string list,
   gs: term list,
   lhs: term list,
   rs: rec_call_info list
  }

datatype scheme_branch = 
  SchemeBranch of
  {
   P : term,
   xs: (string * typ) list,
   ws: (string * typ) list,
   Cs: term list
  }

datatype ind_scheme =
  IndScheme of
  {
   T: typ, (* sum of products *)
   branches: scheme_branch list,
   cases: scheme_case list
  }

val ind_atomize = MetaSimplifier.rewrite true @{thms induct_atomize}
val ind_rulify = MetaSimplifier.rewrite true @{thms induct_rulify}

fun meta thm = thm RS eq_reflection

val sum_prod_conv = MetaSimplifier.rewrite true 
                    (map meta (@{thm split_conv} :: @{thms sum.cases}))

fun term_conv thy cv t = 
    cv (cterm_of thy t)
    |> prop_of |> Logic.dest_equals |> snd

fun mk_relT T = HOLogic.mk_setT (HOLogic.mk_prodT (T, T))

fun dest_hhf ctxt t = 
    let 
      val (ctxt', vars, imp) = dest_all_all_ctx ctxt t
    in
      (ctxt', vars, Logic.strip_imp_prems imp, Logic.strip_imp_concl imp)
    end


fun mk_scheme' ctxt cases concl =
    let
      fun mk_branch concl =
          let
            val (ctxt', ws, Cs, _ $ Pxs) = dest_hhf ctxt concl
            val (P, xs) = strip_comb Pxs
          in
            SchemeBranch { P=P, xs=map dest_Free xs, ws=ws, Cs=Cs }
          end

      val (branches, cases') = (* correction *)
          case Logic.dest_conjunction_list concl of
            [conc] => 
            let 
              val _ $ Pxs = Logic.strip_assums_concl conc
              val (P, _) = strip_comb Pxs
              val (cases', conds) = take_prefix (Term.exists_subterm (curry op aconv P)) cases
              val concl' = fold_rev (curry Logic.mk_implies) conds conc
            in
              ([mk_branch concl'], cases')
            end
          | concls => (map mk_branch concls, cases)

      fun mk_case premise =
          let
            val (ctxt', qs, prems, _ $ Plhs) = dest_hhf ctxt premise
            val (P, lhs) = strip_comb Plhs
                                
            fun bidx Q = find_index (fn SchemeBranch {P=P',...} => Q aconv P') branches

            fun mk_rcinfo pr =
                let
                  val (ctxt'', Gvs, Gas, _ $ Phyp) = dest_hhf ctxt' pr
                  val (P', rcs) = strip_comb Phyp
                in
                  (bidx P', Gvs, Gas, rcs)
                end
                
            fun is_pred v = exists (fn SchemeBranch {P,...} => v aconv P) branches

            val (gs, rcprs) = 
                take_prefix (not o Term.exists_subterm is_pred) prems
          in
            SchemeCase {bidx=bidx P, qs=qs, oqnames=map fst qs(*FIXME*), gs=gs, lhs=lhs, rs=map mk_rcinfo rcprs}
          end

      fun PT_of (SchemeBranch { xs, ...}) =
            foldr1 HOLogic.mk_prodT (map snd xs)

      val ST = BalancedTree.make (uncurry SumTree.mk_sumT) (map PT_of branches)
    in
      IndScheme {T=ST, cases=map mk_case cases', branches=branches }
    end



fun mk_completeness ctxt (IndScheme {cases, branches, ...}) bidx =
    let
      val SchemeBranch { xs, ws, Cs, ... } = nth branches bidx
      val relevant_cases = filter (fn SchemeCase {bidx=bidx', ...} => bidx' = bidx) cases

      val allqnames = fold (fn SchemeCase {qs, ...} => fold (insert (op =) o Free) qs) relevant_cases []
      val (Pbool :: xs') = map Free (Variable.variant_frees ctxt allqnames (("P", HOLogic.boolT) :: xs))
      val Cs' = map (Pattern.rewrite_term (ProofContext.theory_of ctxt) (filter_out (op aconv) (map Free xs ~~ xs')) []) Cs
                       
      fun mk_case (SchemeCase {qs, oqnames, gs, lhs, ...}) =
          HOLogic.mk_Trueprop Pbool
                     |> fold_rev (fn x_l => curry Logic.mk_implies (HOLogic.mk_Trueprop(HOLogic.mk_eq x_l)))
                                 (xs' ~~ lhs)
                     |> fold_rev (curry Logic.mk_implies) gs
                     |> fold_rev mk_forall_rename (oqnames ~~ map Free qs)
    in
      HOLogic.mk_Trueprop Pbool
       |> fold_rev (curry Logic.mk_implies o mk_case) relevant_cases
       |> fold_rev (curry Logic.mk_implies) Cs'
       |> fold_rev (Logic.all o Free) ws
       |> fold_rev mk_forall_rename (map fst xs ~~ xs')
       |> mk_forall_rename ("P", Pbool)
    end

fun mk_wf ctxt R (IndScheme {T, ...}) =
    HOLogic.Trueprop $ (Const (@{const_name "wf"}, mk_relT T --> HOLogic.boolT) $ R)

fun mk_ineqs R (IndScheme {T, cases, branches}) =
    let
      fun inject i ts =
          SumTree.mk_inj T (length branches) (i + 1) (foldr1 HOLogic.mk_prod ts)

      val thesis = Free ("thesis", HOLogic.boolT) (* FIXME *)

      fun mk_pres bdx args = 
          let
            val SchemeBranch { xs, ws, Cs, ... } = nth branches bdx
            fun replace (x, v) t = betapply (lambda (Free x) t, v)
            val Cs' = map (fold replace (xs ~~ args)) Cs
            val cse = 
                HOLogic.mk_Trueprop thesis
                |> fold_rev (curry Logic.mk_implies) Cs'
                |> fold_rev (Logic.all o Free) ws
          in
            Logic.mk_implies (cse, HOLogic.mk_Trueprop thesis)
          end

      fun f (SchemeCase {bidx, qs, oqnames, gs, lhs, rs, ...}) = 
          let
            fun g (bidx', Gvs, Gas, rcarg) =
                let val export = 
                         fold_rev (curry Logic.mk_implies) Gas
                         #> fold_rev (curry Logic.mk_implies) gs
                         #> fold_rev (Logic.all o Free) Gvs
                         #> fold_rev mk_forall_rename (oqnames ~~ map Free qs)
                in
                (HOLogic.mk_mem (HOLogic.mk_prod (inject bidx' rcarg, inject bidx lhs), R)
                 |> HOLogic.mk_Trueprop
                 |> export,
                 mk_pres bidx' rcarg
                 |> export
                 |> Logic.all thesis)
                end
          in
            map g rs
          end
    in
      map f cases
    end


fun mk_hol_imp a b = HOLogic.imp $ a $ b

fun mk_ind_goal thy branches =
    let
      fun brnch (SchemeBranch { P, xs, ws, Cs, ... }) =
          HOLogic.mk_Trueprop (list_comb (P, map Free xs))
          |> fold_rev (curry Logic.mk_implies) Cs
          |> fold_rev (Logic.all o Free) ws
          |> term_conv thy ind_atomize
          |> ObjectLogic.drop_judgment thy
          |> tupled_lambda (foldr1 HOLogic.mk_prod (map Free xs))
    in
      SumTree.mk_sumcases HOLogic.boolT (map brnch branches)
    end


fun mk_induct_rule ctxt R x complete_thms wf_thm ineqss (IndScheme {T, cases=scases, branches}) =
    let
      val n = length branches

      val scases_idx = map_index I scases

      fun inject i ts =
          SumTree.mk_inj T n (i + 1) (foldr1 HOLogic.mk_prod ts)
      val P_of = nth (map (fn (SchemeBranch { P, ... }) => P) branches)

      val thy = ProofContext.theory_of ctxt
      val cert = cterm_of thy 

      val P_comp = mk_ind_goal thy branches

      (* Inductive Hypothesis: !!z. (z,x):R ==> P z *)
      val ihyp = Term.all T $ Abs ("z", T, 
               Logic.mk_implies
                 (HOLogic.mk_Trueprop (
                  Const ("op :", HOLogic.mk_prodT (T, T) --> mk_relT T --> HOLogic.boolT) 
                    $ (HOLogic.pair_const T T $ Bound 0 $ x) 
                    $ R),
                   HOLogic.mk_Trueprop (P_comp $ Bound 0)))
           |> cert

      val aihyp = assume ihyp

     (* Rule for case splitting along the sum types *)
      val xss = map (fn (SchemeBranch { xs, ... }) => map Free xs) branches
      val pats = map_index (uncurry inject) xss
      val sum_split_rule = FundefDatatype.prove_completeness thy [x] (P_comp $ x) xss (map single pats)

      fun prove_branch (bidx, (SchemeBranch { P, xs, ws, Cs, ... }, (complete_thm, pat))) =
          let
            val fxs = map Free xs
            val branch_hyp = assume (cert (HOLogic.mk_Trueprop (HOLogic.mk_eq (x, pat))))
                             
            val C_hyps = map (cert #> assume) Cs

            val (relevant_cases, ineqss') = filter (fn ((_, SchemeCase {bidx=bidx', ...}), _) => bidx' = bidx) (scases_idx ~~ ineqss)
                                            |> split_list
                           
            fun prove_case (cidx, SchemeCase {qs, oqnames, gs, lhs, rs, ...}) ineq_press =
                let
                  val case_hyps = map (assume o cert o HOLogic.mk_Trueprop o HOLogic.mk_eq) (fxs ~~ lhs)
                           
                  val cqs = map (cert o Free) qs
                  val ags = map (assume o cert) gs
                            
                  val replace_x_ss = HOL_basic_ss addsimps (branch_hyp :: case_hyps)
                  val sih = full_simplify replace_x_ss aihyp
                            
                  fun mk_Prec (idx, Gvs, Gas, rcargs) (ineq, pres) =
                      let
                        val cGas = map (assume o cert) Gas
                        val cGvs = map (cert o Free) Gvs
                        val import = fold forall_elim (cqs @ cGvs)
                                     #> fold Thm.elim_implies (ags @ cGas)
                        val ipres = pres
                                     |> forall_elim (cert (list_comb (P_of idx, rcargs)))
                                     |> import
                      in
                        sih |> forall_elim (cert (inject idx rcargs))
                            |> Thm.elim_implies (import ineq) (* Psum rcargs *)
                            |> Conv.fconv_rule sum_prod_conv
                            |> Conv.fconv_rule ind_rulify
                            |> (fn th => th COMP ipres) (* P rs *)
                            |> fold_rev (implies_intr o cprop_of) cGas
                            |> fold_rev forall_intr cGvs
                      end
                      
                  val P_recs = map2 mk_Prec rs ineq_press   (*  [P rec1, P rec2, ... ]  *)
                               
                  val step = HOLogic.mk_Trueprop (list_comb (P, lhs))
                             |> fold_rev (curry Logic.mk_implies o prop_of) P_recs
                             |> fold_rev (curry Logic.mk_implies) gs
                             |> fold_rev (Logic.all o Free) qs
                             |> cert
                             
                  val Plhs_to_Pxs_conv = 
                      foldl1 (uncurry Conv.combination_conv) 
                      (Conv.all_conv :: map (fn ch => K (Thm.symmetric (ch RS eq_reflection))) case_hyps)

                  val res = assume step
                                   |> fold forall_elim cqs
                                   |> fold Thm.elim_implies ags
                                   |> fold Thm.elim_implies P_recs (* P lhs *) 
                                   |> Conv.fconv_rule (Conv.arg_conv Plhs_to_Pxs_conv) (* P xs *)
                                   |> fold_rev (implies_intr o cprop_of) (ags @ case_hyps)
                                   |> fold_rev forall_intr cqs (* !!qs. Gas ==> xs = lhss ==> P xs *)
                in
                  (res, (cidx, step))
                end

            val (cases, steps) = split_list (map2 prove_case relevant_cases ineqss')

            val bstep = complete_thm
                |> forall_elim (cert (list_comb (P, fxs)))
                |> fold (forall_elim o cert) (fxs @ map Free ws)
                |> fold Thm.elim_implies C_hyps             (* FIXME: optimization using rotate_prems *)
                |> fold Thm.elim_implies cases (* P xs *)
                |> fold_rev (implies_intr o cprop_of) C_hyps
                |> fold_rev (forall_intr o cert o Free) ws

            val Pxs = cert (HOLogic.mk_Trueprop (P_comp $ x))
                     |> Goal.init
                     |> (MetaSimplifier.rewrite_goals_tac (map meta (branch_hyp :: @{thm split_conv} :: @{thms sum.cases}))
                         THEN CONVERSION ind_rulify 1)
                     |> Seq.hd
                     |> Thm.elim_implies (Conv.fconv_rule Drule.beta_eta_conversion bstep)
                     |> Goal.finish
                     |> implies_intr (cprop_of branch_hyp)
                     |> fold_rev (forall_intr o cert) fxs
          in
            (Pxs, steps)
          end

      val (branches, steps) = split_list (map_index prove_branch (branches ~~ (complete_thms ~~ pats)))
                              |> apsnd flat
                           
      val istep = sum_split_rule
                |> fold (fn b => fn th => Drule.compose_single (b, 1, th)) branches
                |> implies_intr ihyp
                |> forall_intr (cert x) (* "!!x. (!!y<x. P y) ==> P x" *)
         
      val induct_rule =
          @{thm "wf_induct_rule"}
            |> (curry op COMP) wf_thm 
            |> (curry op COMP) istep

      val steps_sorted = map snd (sort (int_ord o pairself fst) steps)
    in
      (steps_sorted, induct_rule)
    end


fun mk_ind_tac comp_tac pres_tac term_tac ctxt facts = (ALLGOALS (Method.insert_tac facts)) THEN HEADGOAL 
(SUBGOAL (fn (t, i) =>
  let
    val (ctxt', _, cases, concl) = dest_hhf ctxt t
    val scheme as IndScheme {T=ST, branches, ...} = mk_scheme' ctxt' cases concl
(*     val _ = Output.tracing (makestring scheme)*)
    val ([Rn,xn], ctxt'') = Variable.variant_fixes ["R","x"] ctxt'
    val R = Free (Rn, mk_relT ST)
    val x = Free (xn, ST)
    val cert = cterm_of (ProofContext.theory_of ctxt)

    val ineqss = mk_ineqs R scheme
                   |> map (map (pairself (assume o cert)))
    val complete = map (mk_completeness ctxt scheme #> cert #> assume) (0 upto (length branches - 1))
    val wf_thm = mk_wf ctxt R scheme |> cert |> assume

    val (descent, pres) = split_list (flat ineqss)
    val newgoals = complete @ pres @ wf_thm :: descent 

    val (steps, indthm) = mk_induct_rule ctxt'' R x complete wf_thm ineqss scheme

    fun project (i, SchemeBranch {xs, ...}) =
        let
          val inst = cert (SumTree.mk_inj ST (length branches) (i + 1) (foldr1 HOLogic.mk_prod (map Free xs)))
        in
          indthm |> Drule.instantiate' [] [SOME inst]
                 |> simplify SumTree.sumcase_split_ss
                 |> Conv.fconv_rule ind_rulify
(*                 |> (fn thm => (Output.tracing (makestring thm); thm))*)
        end                  

    val res = Conjunction.intr_balanced (map_index project branches)
                 |> fold_rev implies_intr (map cprop_of newgoals @ steps)
                 |> (fn thm => Thm.generalize ([], [Rn]) (Thm.maxidx_of thm + 1) thm)

    val nbranches = length branches
    val npres = length pres
  in
    Thm.compose_no_flatten false (res, length newgoals) i
    THEN term_tac (i + nbranches + npres)
    THEN (EVERY (map (TRY o pres_tac) ((i + nbranches + npres - 1) downto (i + nbranches))))
    THEN (EVERY (map (TRY o comp_tac) ((i + nbranches - 1) downto i)))
  end))


fun induct_scheme_tac ctxt =
  mk_ind_tac (K all_tac) (assume_tac APPEND' Goal.assume_rule_tac ctxt) (K all_tac) ctxt;

val setup =
  Method.setup @{binding induct_scheme} (Scan.succeed (RAW_METHOD o induct_scheme_tac))
    "proves an induction principle"

end
