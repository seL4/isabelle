(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_proof.ML
    Author:     Lukas Bulwahn, TU Muenchen

Proof procedure for the compiler from predicates specified by intro/elim rules to equations.
*)

signature PREDICATE_COMPILE_PROOF =
sig
  type indprem = Predicate_Compile_Aux.indprem;
  type mode = Predicate_Compile_Aux.mode
  val prove_pred : Predicate_Compile_Aux.options -> theory
    -> (string * (term list * indprem list) list) list
    -> (string * typ) list -> string -> bool * mode
    -> (term list * (indprem * Mode_Inference.mode_derivation) list) list * term
    -> thm
end;

structure Predicate_Compile_Proof : PREDICATE_COMPILE_PROOF =
struct

open Predicate_Compile_Aux;
open Mode_Inference;


(* debug stuff *)

fun trace_tac ctxt options s =
  if show_proof_trace options then print_tac ctxt s else Seq.single;

fun assert_tac ctxt pos pred =
  COND pred all_tac (print_tac ctxt ("Assertion failed" ^ Position.here pos) THEN no_tac);


(** special setup for simpset **)

val HOL_basic_ss' =
  simpset_of (put_simpset HOL_basic_ss \<^context>
    addsimps @{thms simp_thms prod.inject}
    |> Simplifier.set_unsafe_solver (mk_solver "all_tac_solver" (fn _ => fn _ => all_tac))
    |> Simplifier.set_unsafe_solver (mk_solver "True_solver" (fn ctxt => resolve_tac ctxt @{thms TrueI})))


(* auxillary functions *)

(* returns true if t is an application of a datatype constructor *)
(* which then consequently would be splitted *)
fun is_constructor ctxt t =
  (case fastype_of t of
    Type (s, _) => s <> \<^type_name>\<open>fun\<close> andalso can (Ctr_Sugar.dest_ctr ctxt s) t
  | _ => false)

(* MAJOR FIXME:  prove_params should be simple
 - different form of introrule for parameters ? *)

fun prove_param options ctxt nargs t deriv =
  let
    val (f, args) = strip_comb (Envir.eta_contract t)
    val mode = head_mode_of deriv
    val param_derivations = param_derivations_of deriv
    val ho_args = ho_args_of mode args
    val f_tac =
      (case f of
        Const (name, _) => simp_tac (put_simpset HOL_basic_ss ctxt addsimps
           [@{thm pred.sel}, Core_Data.predfun_definition_of ctxt name mode,
           @{thm case_prod_eta}, @{thm case_prod_beta}, @{thm fst_conv},
           @{thm snd_conv}, @{thm prod.collapse}, @{thm Product_Type.split_conv}]) 1
      | Free _ =>
        Subgoal.FOCUS_PREMS (fn {context = ctxt', prems, ...} =>
          let
            val prems' = maps dest_conjunct_prem (take nargs prems)
          in
            rewrite_goal_tac ctxt' (map (fn th => th RS @{thm sym} RS @{thm eq_reflection}) prems') 1
          end) ctxt 1
      | Abs _ => raise Fail "prove_param: No valid parameter term")
  in
    REPEAT_DETERM (resolve_tac ctxt @{thms ext} 1)
    THEN trace_tac ctxt options "prove_param"
    THEN f_tac
    THEN trace_tac ctxt options "after prove_param"
    THEN (REPEAT_DETERM (assume_tac ctxt 1))
    THEN (EVERY (map2 (prove_param options ctxt nargs) ho_args param_derivations))
    THEN REPEAT_DETERM (resolve_tac ctxt @{thms refl} 1)
  end

fun prove_expr options ctxt nargs (premposition : int) (t, deriv) =
  (case strip_comb t of
    (Const (name, _), args) =>
      let
        val mode = head_mode_of deriv
        val introrule = Core_Data.predfun_intro_of ctxt name mode
        val param_derivations = param_derivations_of deriv
        val ho_args = ho_args_of mode args
      in
        trace_tac ctxt options "before intro rule:"
        THEN resolve_tac ctxt [introrule] 1
        THEN trace_tac ctxt options "after intro rule"
        (* for the right assumption in first position *)
        THEN rotate_tac premposition 1
        THEN assume_tac ctxt 1
        THEN trace_tac ctxt options "parameter goal"
        (* work with parameter arguments *)
        THEN (EVERY (map2 (prove_param options ctxt nargs) ho_args param_derivations))
        THEN (REPEAT_DETERM (assume_tac ctxt 1))
      end
  | (Free _, _) =>
      trace_tac ctxt options "proving parameter call.."
      THEN Subgoal.FOCUS_PREMS (fn {context = ctxt', prems, concl, ...} =>
          let
            val param_prem = nth prems premposition
            val (param, _) = strip_comb (HOLogic.dest_Trueprop (Thm.prop_of param_prem))
            val prems' = maps dest_conjunct_prem (take nargs prems)
            fun param_rewrite prem =
              param = snd (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of prem)))
            val SOME rew_eq = find_first param_rewrite prems'
            val param_prem' = rewrite_rule ctxt'
              (map (fn th => th RS @{thm eq_reflection})
                [rew_eq RS @{thm sym}, @{thm split_beta}, @{thm fst_conv}, @{thm snd_conv}])
              param_prem
          in
            resolve_tac ctxt' [param_prem'] 1
          end) ctxt 1
      THEN trace_tac ctxt options "after prove parameter call")

fun SOLVED tac st = FILTER (fn st' => Thm.nprems_of st' = Thm.nprems_of st - 1) tac st

fun prove_match options ctxt nargs out_ts =
  let
    val eval_if_P =
      @{lemma "P ==> Predicate.eval x z ==> Predicate.eval (if P then x else y) z" by simp}
    fun get_case_rewrite t =
      if is_constructor ctxt t then
        let
          val SOME {case_thms, ...} = Ctr_Sugar.ctr_sugar_of ctxt (dest_Type_name (fastype_of t))
        in
          fold (union Thm.eq_thm) (case_thms :: map get_case_rewrite (snd (strip_comb t))) []
        end
      else []
    val simprules = insert Thm.eq_thm @{thm "unit.case"} (insert Thm.eq_thm @{thm "prod.case"}
      (fold (union Thm.eq_thm) (map get_case_rewrite out_ts) []))
  (* replace TRY by determining if it necessary - are there equations when calling compile match? *)
  in
    (* make this simpset better! *)
    asm_full_simp_tac (put_simpset HOL_basic_ss' ctxt addsimps simprules) 1
    THEN trace_tac ctxt options "after prove_match:"
    THEN (DETERM (TRY
           (resolve_tac ctxt [eval_if_P] 1
           THEN (SUBPROOF (fn {prems, context = ctxt', ...} =>
             (REPEAT_DETERM (resolve_tac ctxt' @{thms conjI} 1
             THEN (SOLVED (asm_simp_tac (put_simpset HOL_basic_ss' ctxt') 1))))
             THEN trace_tac ctxt' options "if condition to be solved:"
             THEN asm_simp_tac (put_simpset HOL_basic_ss' ctxt') 1
             THEN TRY (
                let
                  val prems' = maps dest_conjunct_prem (take nargs prems)
                    |> filter is_equationlike
                in
                  rewrite_goal_tac ctxt'
                    (map (fn th => th RS @{thm sym} RS @{thm eq_reflection}) prems') 1
                end
             THEN REPEAT_DETERM (resolve_tac ctxt' @{thms refl} 1))
             THEN trace_tac ctxt' options "after if simp; in SUBPROOF") ctxt 1))))
    THEN trace_tac ctxt options "after if simplification"
  end;


(* corresponds to compile_fun -- maybe call that also compile_sidecond? *)

fun prove_sidecond ctxt t =
  let
    fun preds_of t nameTs =
      (case strip_comb t of
        (Const (name, T), args) =>
          if Core_Data.is_registered ctxt name then (name, T) :: nameTs
          else fold preds_of args nameTs
      | _ => nameTs)
    val preds = preds_of t []
    val defs = map
      (fn (pred, T) => Core_Data.predfun_definition_of ctxt pred
        (all_input_of T))
        preds
  in
    simp_tac (put_simpset HOL_basic_ss ctxt
      addsimps (@{thms HOL.simp_thms pred.sel} @ defs)) 1
    (* need better control here! *)
  end

fun prove_clause options ctxt nargs mode (_, clauses) (ts, moded_ps) =
  let
    val (in_ts, clause_out_ts) = split_mode mode ts;
    fun prove_prems out_ts [] =
        (prove_match options ctxt nargs out_ts)
        THEN trace_tac ctxt options "before simplifying assumptions"
        THEN asm_full_simp_tac (put_simpset HOL_basic_ss' ctxt) 1
        THEN trace_tac ctxt options "before single intro rule"
        THEN Subgoal.FOCUS_PREMS
           (fn {context = ctxt', prems, ...} =>
            let
              val prems' = maps dest_conjunct_prem (take nargs prems)
                |> filter is_equationlike
            in
              rewrite_goal_tac ctxt' (map (fn th => th RS @{thm sym} RS @{thm eq_reflection}) prems') 1
            end) ctxt 1
        THEN (resolve_tac ctxt [if null clause_out_ts then @{thm singleI_unit} else @{thm singleI}] 1)
    | prove_prems out_ts ((p, deriv) :: ps) =
        let
          val premposition = (find_index (equal p) clauses) + nargs
          val mode = head_mode_of deriv
          val rest_tac =
            resolve_tac ctxt @{thms bindI} 1
            THEN (case p of Prem t =>
              let
                val (_, us) = strip_comb t
                val (_, out_ts''') = split_mode mode us
                val rec_tac = prove_prems out_ts''' ps
              in
                trace_tac ctxt options "before clause:"
                (*THEN asm_simp_tac (put_simpset HOL_basic_ss ctxt) 1*)
                THEN trace_tac ctxt options "before prove_expr:"
                THEN prove_expr options ctxt nargs premposition (t, deriv)
                THEN trace_tac ctxt options "after prove_expr:"
                THEN rec_tac
              end
            | Negprem t =>
              let
                val (t, args) = strip_comb t
                val (_, out_ts''') = split_mode mode args
                val rec_tac = prove_prems out_ts''' ps
                val name = (case strip_comb t of (Const (c, _), _) => SOME c | _ => NONE)
                val neg_intro_rule =
                  Option.map (fn name =>
                    the (Core_Data.predfun_neg_intro_of ctxt name mode)) name
                val param_derivations = param_derivations_of deriv
                val params = ho_args_of mode args
              in
                trace_tac ctxt options "before prove_neg_expr:"
                THEN full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps
                  [@{thm case_prod_eta}, @{thm case_prod_beta}, @{thm fst_conv},
                   @{thm snd_conv}, @{thm prod.collapse}, @{thm Product_Type.split_conv}]) 1
                THEN (if (is_some name) then
                    trace_tac ctxt options "before applying not introduction rule"
                    THEN Subgoal.FOCUS_PREMS (fn {prems, ...} =>
                      resolve_tac ctxt [the neg_intro_rule] 1
                      THEN resolve_tac ctxt [nth prems premposition] 1) ctxt 1
                    THEN trace_tac ctxt options "after applying not introduction rule"
                    THEN (EVERY (map2 (prove_param options ctxt nargs) params param_derivations))
                    THEN (REPEAT_DETERM (assume_tac ctxt 1))
                  else
                    resolve_tac ctxt @{thms not_predI'} 1
                    (* test: *)
                    THEN dresolve_tac ctxt @{thms sym} 1
                    THEN asm_full_simp_tac
                      (put_simpset HOL_basic_ss ctxt addsimps [@{thm not_False_eq_True}]) 1)
                    THEN simp_tac
                      (put_simpset HOL_basic_ss ctxt addsimps [@{thm not_False_eq_True}]) 1
                THEN rec_tac
              end
            | Sidecond t =>
             resolve_tac ctxt @{thms if_predI} 1
             THEN trace_tac ctxt options "before sidecond:"
             THEN prove_sidecond ctxt t
             THEN trace_tac ctxt options "after sidecond:"
             THEN prove_prems [] ps)
        in (prove_match options ctxt nargs out_ts)
            THEN rest_tac
        end
    val prems_tac = prove_prems in_ts moded_ps
  in
    trace_tac ctxt options "Proving clause..."
    THEN resolve_tac ctxt @{thms bindI} 1
    THEN resolve_tac ctxt @{thms singleI} 1
    THEN prems_tac
  end

fun select_sup _ 1 1 = []
  | select_sup ctxt _ 1 = [resolve_tac ctxt @{thms supI1}]
  | select_sup ctxt n i = resolve_tac ctxt @{thms supI2} :: select_sup ctxt (n - 1) (i - 1);

fun prove_one_direction options ctxt clauses preds pred mode moded_clauses =
  let
    val T = the (AList.lookup (op =) preds pred)
    val nargs = length (binder_types T)
    val pred_case_rule = Core_Data.the_elim_of ctxt pred
  in
    REPEAT_DETERM (CHANGED (rewrite_goals_tac ctxt @{thms split_paired_all}))
    THEN trace_tac ctxt options "before applying elim rule"
    THEN eresolve_tac ctxt [Core_Data.predfun_elim_of ctxt pred mode] 1
    THEN eresolve_tac ctxt [pred_case_rule] 1
    THEN trace_tac ctxt options "after applying elim rule"
    THEN (EVERY (map
           (fn i => EVERY' (select_sup ctxt (length moded_clauses) i) i)
             (1 upto (length moded_clauses))))
    THEN (EVERY (map2 (prove_clause options ctxt nargs mode) clauses moded_clauses))
    THEN trace_tac ctxt options "proved one direction"
  end


(** Proof in the other direction **)

fun prove_match2 options ctxt out_ts =
  let
    fun split_term_tac (Free _) = all_tac
      | split_term_tac t =
        if is_constructor ctxt t then
          let
            val SOME {case_thms, split_asm, ...} =
              Ctr_Sugar.ctr_sugar_of ctxt (dest_Type_name (fastype_of t))
            val num_of_constrs = length case_thms
            val (_, ts) = strip_comb t
          in
            trace_tac ctxt options ("Term " ^ (Syntax.string_of_term ctxt t) ^
              " splitting with rules \n" ^ Thm.string_of_thm ctxt split_asm)
            THEN TRY (Splitter.split_asm_tac ctxt [split_asm] 1
              THEN (trace_tac ctxt options "after splitting with split_asm rules")
            (* THEN (Simplifier.asm_full_simp_tac (put_simpset HOL_basic_ss ctxt) 1)
              THEN (DETERM (TRY (etac @{thm Pair_inject} 1)))*)
              THEN (REPEAT_DETERM_N (num_of_constrs - 1)
                (eresolve_tac ctxt @{thms botE} 1 ORELSE eresolve_tac ctxt @{thms botE} 2)))
            THEN assert_tac ctxt \<^here> (fn st => Thm.nprems_of st <= 2)
            THEN (EVERY (map split_term_tac ts))
          end
      else all_tac
  in
    split_term_tac (HOLogic.mk_tuple out_ts)
    THEN (DETERM (TRY ((Splitter.split_asm_tac ctxt @{thms if_split_asm} 1)
    THEN (eresolve_tac ctxt @{thms botE} 2))))
  end

(* VERY LARGE SIMILIRATIY to function prove_param
-- join both functions
*)
(* TODO: remove function *)

fun prove_param2 options ctxt t deriv =
  let
    val (f, args) = strip_comb (Envir.eta_contract t)
    val mode = head_mode_of deriv
    val param_derivations = param_derivations_of deriv
    val ho_args = ho_args_of mode args
    val f_tac =
      (case f of
        Const (name, _) => full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps
           [@{thm pred.sel}, Core_Data.predfun_definition_of ctxt name mode,
            @{thm Product_Type.split_conv}]) 1
      | Free _ => all_tac
      | _ => error "prove_param2: illegal parameter term")
  in
    trace_tac ctxt options "before simplification in prove_args:"
    THEN f_tac
    THEN trace_tac ctxt options "after simplification in prove_args"
    THEN EVERY (map2 (prove_param2 options ctxt) ho_args param_derivations)
  end

fun prove_expr2 options ctxt (t, deriv) =
  (case strip_comb t of
      (Const (name, _), args) =>
        let
          val mode = head_mode_of deriv
          val param_derivations = param_derivations_of deriv
          val ho_args = ho_args_of mode args
        in
          eresolve_tac ctxt @{thms bindE} 1
          THEN (REPEAT_DETERM (CHANGED (rewrite_goals_tac ctxt @{thms split_paired_all})))
          THEN trace_tac ctxt options "prove_expr2-before"
          THEN eresolve_tac ctxt [Core_Data.predfun_elim_of ctxt name mode] 1
          THEN trace_tac ctxt options "prove_expr2"
          THEN (EVERY (map2 (prove_param2 options ctxt) ho_args param_derivations))
          THEN trace_tac ctxt options "finished prove_expr2"
        end
      | _ => eresolve_tac ctxt @{thms bindE} 1)

fun prove_sidecond2 options ctxt t =
  let
    fun preds_of t nameTs =
      (case strip_comb t of
        (Const (name, T), args) =>
          if Core_Data.is_registered ctxt name then (name, T) :: nameTs
          else fold preds_of args nameTs
      | _ => nameTs)
    val preds = preds_of t []
    val defs = map
      (fn (pred, T) => Core_Data.predfun_definition_of ctxt pred
        (all_input_of T))
        preds
  in
    (* only simplify the one assumption *)
    full_simp_tac (put_simpset HOL_basic_ss' ctxt addsimps @{thm pred.sel} :: defs) 1
    (* need better control here! *)
    THEN trace_tac ctxt options "after sidecond2 simplification"
  end

fun prove_clause2 options ctxt pred mode (ts, ps) i =
  let
    val pred_intro_rule = nth (Core_Data.intros_of ctxt pred) (i - 1)
    val (in_ts, _) = split_mode mode ts;
    val split_simpset =
      put_simpset HOL_basic_ss' ctxt
      addsimps [@{thm case_prod_eta}, @{thm case_prod_beta},
        @{thm fst_conv}, @{thm snd_conv}, @{thm prod.collapse}]
    fun prove_prems2 out_ts [] =
      trace_tac ctxt options "before prove_match2 - last call:"
      THEN prove_match2 options ctxt out_ts
      THEN trace_tac ctxt options "after prove_match2 - last call:"
      THEN (eresolve_tac ctxt @{thms singleE} 1)
      THEN (REPEAT_DETERM (eresolve_tac ctxt @{thms Pair_inject} 1))
      THEN (asm_full_simp_tac (put_simpset HOL_basic_ss' ctxt) 1)
      THEN TRY (
        (REPEAT_DETERM (eresolve_tac ctxt @{thms Pair_inject} 1))
        THEN (asm_full_simp_tac (put_simpset HOL_basic_ss' ctxt) 1)

        THEN SOLVED (trace_tac ctxt options "state before applying intro rule:"
        THEN (resolve_tac ctxt [pred_intro_rule]
        (* How to handle equality correctly? *)
        THEN_ALL_NEW (K (trace_tac ctxt options "state before assumption matching")
        THEN' (assume_tac ctxt ORELSE'
          ((CHANGED o asm_full_simp_tac split_simpset) THEN'
            (TRY o assume_tac ctxt))) THEN'
          (K (trace_tac ctxt options "state after pre-simplification:"))
        THEN' (K (trace_tac ctxt options "state after assumption matching:")))) 1))
    | prove_prems2 out_ts ((p, deriv) :: ps) =
      let
        val mode = head_mode_of deriv
        val rest_tac =
          (case p of
            Prem t =>
              let
                val (_, us) = strip_comb t
                val (_, out_ts''') = split_mode mode us
                val rec_tac = prove_prems2 out_ts''' ps
              in
                (prove_expr2 options ctxt (t, deriv)) THEN rec_tac
              end
          | Negprem t =>
              let
                val (_, args) = strip_comb t
                val (_, out_ts''') = split_mode mode args
                val rec_tac = prove_prems2 out_ts''' ps
                val name = (case strip_comb t of (Const (c, _), _) => SOME c | _ => NONE)
                val param_derivations = param_derivations_of deriv
                val ho_args = ho_args_of mode args
              in
                trace_tac ctxt options "before neg prem 2"
                THEN eresolve_tac ctxt @{thms bindE} 1
                THEN (if is_some name then
                    full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps
                      [Core_Data.predfun_definition_of ctxt (the name) mode]) 1
                    THEN eresolve_tac ctxt @{thms not_predE} 1
                    THEN simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms not_False_eq_True}) 1
                    THEN (EVERY (map2 (prove_param2 options ctxt) ho_args param_derivations))
                  else
                    eresolve_tac ctxt @{thms not_predE'} 1)
                THEN rec_tac
              end
          | Sidecond t =>
              eresolve_tac ctxt @{thms bindE} 1
              THEN eresolve_tac ctxt @{thms if_predE} 1
              THEN prove_sidecond2 options ctxt t
              THEN prove_prems2 [] ps)
      in
        trace_tac ctxt options "before prove_match2:"
        THEN prove_match2 options ctxt out_ts
        THEN trace_tac ctxt options "after prove_match2:"
        THEN rest_tac
      end
    val prems_tac = prove_prems2 in_ts ps
  in
    trace_tac ctxt options "starting prove_clause2"
    THEN eresolve_tac ctxt @{thms bindE} 1
    THEN (eresolve_tac ctxt @{thms singleE'} 1)
    THEN (TRY (eresolve_tac ctxt @{thms Pair_inject} 1))
    THEN trace_tac ctxt options "after singleE':"
    THEN prems_tac
  end;

fun prove_other_direction options ctxt pred mode moded_clauses =
  let
    fun prove_clause clause i =
      (if i < length moded_clauses then eresolve_tac ctxt @{thms supE} 1 else all_tac)
      THEN (prove_clause2 options ctxt pred mode clause i)
  in
    (DETERM (TRY (resolve_tac ctxt @{thms unit.induct} 1)))
     THEN (REPEAT_DETERM (CHANGED (rewrite_goals_tac ctxt @{thms split_paired_all})))
     THEN (resolve_tac ctxt [Core_Data.predfun_intro_of ctxt pred mode] 1)
     THEN (REPEAT_DETERM (resolve_tac ctxt @{thms refl} 2))
     THEN (
       if null moded_clauses then eresolve_tac ctxt @{thms botE} 1
       else EVERY (map2 prove_clause moded_clauses (1 upto (length moded_clauses))))
  end


(** proof procedure **)

fun prove_pred options thy clauses preds pred (_, mode) (moded_clauses, compiled_term) =
  let
    val ctxt = Proof_Context.init_global thy   (* FIXME proper context!? *)
    val clauses = (case AList.lookup (op =) clauses pred of SOME rs => rs | NONE => [])
  in
    Goal.prove ctxt (Term.add_free_names compiled_term []) [] compiled_term
      (if not (skip_proof options) then
        (fn _ =>
        resolve_tac ctxt @{thms pred_iffI} 1
        THEN trace_tac ctxt options "after pred_iffI"
        THEN prove_one_direction options ctxt clauses preds pred mode moded_clauses
        THEN trace_tac ctxt options "proved one direction"
        THEN prove_other_direction options ctxt pred mode moded_clauses
        THEN trace_tac ctxt options "proved other direction")
      else (fn _ => ALLGOALS (Skip_Proof.cheat_tac ctxt)))
  end

end
