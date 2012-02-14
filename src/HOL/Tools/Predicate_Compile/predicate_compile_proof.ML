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
    -> Thm.thm
end;

structure Predicate_Compile_Proof : PREDICATE_COMPILE_PROOF =
struct

open Predicate_Compile_Aux;
open Core_Data;
open Mode_Inference;

(* debug stuff *)

fun print_tac options s = 
  if show_proof_trace options then Tactical.print_tac s else Seq.single;

(** auxiliary **)

datatype assertion = Max_number_of_subgoals of int
fun assert_tac (Max_number_of_subgoals i) st =
  if (nprems_of st <= i) then Seq.single st
  else raise Fail ("assert_tac: Numbers of subgoals mismatch at goal state :"
    ^ "\n" ^ Pretty.string_of (Pretty.chunks
      (Goal_Display.pretty_goals_without_context st)));


(** special setup for simpset **)
val HOL_basic_ss' = HOL_basic_ss addsimps @{thms simp_thms Pair_eq}
  setSolver (mk_solver "all_tac_solver" (fn _ => fn _ => all_tac))
  setSolver (mk_solver "True_solver" (fn _ => rtac @{thm TrueI}))

(* auxillary functions *)

fun is_Type (Type _) = true
  | is_Type _ = false

(* returns true if t is an application of an datatype constructor *)
(* which then consequently would be splitted *)
(* else false *)
fun is_constructor thy t =
  if (is_Type (fastype_of t)) then
    (case Datatype.get_info thy ((fst o dest_Type o fastype_of) t) of
      NONE => false
    | SOME info => (let
      val constr_consts = maps (fn (_, (_, _, constrs)) => map fst constrs) (#descr info)
      val (c, _) = strip_comb t
      in (case c of
        Const (name, _) => member (op =) constr_consts name
        | _ => false) end))
  else false

(* MAJOR FIXME:  prove_params should be simple
 - different form of introrule for parameters ? *)

fun prove_param options ctxt nargs t deriv =
  let
    val  (f, args) = strip_comb (Envir.eta_contract t)
    val mode = head_mode_of deriv
    val param_derivations = param_derivations_of deriv
    val ho_args = ho_args_of mode args
    val f_tac = case f of
      Const (name, T) => simp_tac (HOL_basic_ss addsimps 
         [@{thm eval_pred}, predfun_definition_of ctxt name mode,
         @{thm split_eta}, @{thm split_beta}, @{thm fst_conv},
         @{thm snd_conv}, @{thm pair_collapse}, @{thm Product_Type.split_conv}]) 1
    | Free _ =>
      Subgoal.FOCUS_PREMS (fn {context = ctxt, params = params, prems, asms, concl, schematics} =>
        let
          val prems' = maps dest_conjunct_prem (take nargs prems)
        in
          Simplifier.rewrite_goal_tac
            (map (fn th => th RS @{thm sym} RS @{thm eq_reflection}) prems') 1
        end) ctxt 1
    | Abs _ => raise Fail "prove_param: No valid parameter term"
  in
    REPEAT_DETERM (rtac @{thm ext} 1)
    THEN print_tac options "prove_param"
    THEN f_tac 
    THEN print_tac options "after prove_param"
    THEN (REPEAT_DETERM (atac 1))
    THEN (EVERY (map2 (prove_param options ctxt nargs) ho_args param_derivations))
    THEN REPEAT_DETERM (rtac @{thm refl} 1)
  end

fun prove_expr options ctxt nargs (premposition : int) (t, deriv) =
  case strip_comb t of
    (Const (name, T), args) =>
      let
        val mode = head_mode_of deriv
        val introrule = predfun_intro_of ctxt name mode
        val param_derivations = param_derivations_of deriv
        val ho_args = ho_args_of mode args
      in
        print_tac options "before intro rule:"
        THEN rtac introrule 1
        THEN print_tac options "after intro rule"
        (* for the right assumption in first position *)
        THEN rotate_tac premposition 1
        THEN atac 1
        THEN print_tac options "parameter goal"
        (* work with parameter arguments *)
        THEN (EVERY (map2 (prove_param options ctxt nargs) ho_args param_derivations))
        THEN (REPEAT_DETERM (atac 1))
      end
  | (Free _, _) =>
    print_tac options "proving parameter call.."
    THEN Subgoal.FOCUS_PREMS (fn {context = ctxt, params, prems, asms, concl, schematics} =>
        let
          val param_prem = nth prems premposition
          val (param, _) = strip_comb (HOLogic.dest_Trueprop (prop_of param_prem))
          val prems' = maps dest_conjunct_prem (take nargs prems)
          fun param_rewrite prem =
            param = snd (HOLogic.dest_eq (HOLogic.dest_Trueprop (prop_of prem)))
          val SOME rew_eq = find_first param_rewrite prems'
          val param_prem' = Raw_Simplifier.rewrite_rule
            (map (fn th => th RS @{thm eq_reflection})
              [rew_eq RS @{thm sym}, @{thm split_beta}, @{thm fst_conv}, @{thm snd_conv}])
            param_prem
        in
          rtac param_prem' 1
        end) ctxt 1
    THEN print_tac options "after prove parameter call"

fun SOLVED tac st = FILTER (fn st' => nprems_of st' = nprems_of st - 1) tac st;

fun SOLVEDALL tac st = FILTER (fn st' => nprems_of st' = 0) tac st

fun check_format ctxt st =
  let
    val concl' = Logic.strip_assums_concl (hd (prems_of st))
    val concl = HOLogic.dest_Trueprop concl'
    val expr = fst (strip_comb (fst (Predicate_Comp_Funs.dest_Eval concl)))
    fun valid_expr (Const (@{const_name Predicate.bind}, _)) = true
      | valid_expr (Const (@{const_name Predicate.single}, _)) = true
      | valid_expr _ = false
  in
    if valid_expr expr then
      ((*tracing "expression is valid";*) Seq.single st)
    else
      ((*tracing "expression is not valid";*) Seq.empty) (* error "check_format: wrong format" *)
  end

fun prove_match options ctxt nargs out_ts =
  let
    val thy = Proof_Context.theory_of ctxt
    val eval_if_P =
      @{lemma "P ==> Predicate.eval x z ==> Predicate.eval (if P then x else y) z" by simp} 
    fun get_case_rewrite t =
      if (is_constructor thy t) then
        let
          val {case_rewrites, ...} = Datatype.the_info thy (fst (dest_Type (fastype_of t)))
        in
          fold (union Thm.eq_thm) (case_rewrites :: map get_case_rewrite (snd (strip_comb t))) []
        end
      else []
    val simprules = insert Thm.eq_thm @{thm "unit.cases"} (insert Thm.eq_thm @{thm "prod.cases"}
      (fold (union Thm.eq_thm) (map get_case_rewrite out_ts) []))
  (* replace TRY by determining if it necessary - are there equations when calling compile match? *)
  in
     (* make this simpset better! *)
    asm_full_simp_tac (HOL_basic_ss' addsimps simprules) 1
    THEN print_tac options "after prove_match:"
    THEN (DETERM (TRY 
           (rtac eval_if_P 1
           THEN (SUBPROOF (fn {context = ctxt, params, prems, asms, concl, schematics} =>
             (REPEAT_DETERM (rtac @{thm conjI} 1
             THEN (SOLVED (asm_simp_tac HOL_basic_ss' 1))))
             THEN print_tac options "if condition to be solved:"
             THEN asm_simp_tac HOL_basic_ss' 1
             THEN TRY (
                let
                  val prems' = maps dest_conjunct_prem (take nargs prems)
                in
                  Simplifier.rewrite_goal_tac
                    (map (fn th => th RS @{thm sym} RS @{thm eq_reflection}) prems') 1
                end
             THEN REPEAT_DETERM (rtac @{thm refl} 1))
             THEN print_tac options "after if simp; in SUBPROOF") ctxt 1))))
    THEN print_tac options "after if simplification"
  end;

(* corresponds to compile_fun -- maybe call that also compile_sidecond? *)

fun prove_sidecond ctxt t =
  let
    fun preds_of t nameTs = case strip_comb t of 
      (f as Const (name, T), args) =>
        if is_registered ctxt name then (name, T) :: nameTs
          else fold preds_of args nameTs
      | _ => nameTs
    val preds = preds_of t []
    val defs = map
      (fn (pred, T) => predfun_definition_of ctxt pred
        (all_input_of T))
        preds
  in 
    simp_tac (HOL_basic_ss addsimps
      (@{thms HOL.simp_thms eval_pred} @ defs)) 1 
    (* need better control here! *)
  end

fun prove_clause options ctxt nargs mode (_, clauses) (ts, moded_ps) =
  let
    val (in_ts, clause_out_ts) = split_mode mode ts;
    fun prove_prems out_ts [] =
      (prove_match options ctxt nargs out_ts)
      THEN print_tac options "before simplifying assumptions"
      THEN asm_full_simp_tac HOL_basic_ss' 1
      THEN print_tac options "before single intro rule"
      THEN Subgoal.FOCUS_PREMS
             (fn {context = ctxt, params = params, prems, asms, concl, schematics} =>
              let
                val prems' = maps dest_conjunct_prem (take nargs prems)
              in
                Simplifier.rewrite_goal_tac
                  (map (fn th => th RS @{thm sym} RS @{thm eq_reflection}) prems') 1
              end) ctxt 1
      THEN (rtac (if null clause_out_ts then @{thm singleI_unit} else @{thm singleI}) 1)
    | prove_prems out_ts ((p, deriv) :: ps) =
      let
        val premposition = (find_index (equal p) clauses) + nargs
        val mode = head_mode_of deriv
        val rest_tac =
          rtac @{thm bindI} 1
          THEN (case p of Prem t =>
            let
              val (_, us) = strip_comb t
              val (_, out_ts''') = split_mode mode us
              val rec_tac = prove_prems out_ts''' ps
            in
              print_tac options "before clause:"
              (*THEN asm_simp_tac HOL_basic_ss 1*)
              THEN print_tac options "before prove_expr:"
              THEN prove_expr options ctxt nargs premposition (t, deriv)
              THEN print_tac options "after prove_expr:"
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
                  the (predfun_neg_intro_of ctxt name mode)) name
              val param_derivations = param_derivations_of deriv
              val params = ho_args_of mode args
            in
              print_tac options "before prove_neg_expr:"
              THEN full_simp_tac (HOL_basic_ss addsimps
                [@{thm split_eta}, @{thm split_beta}, @{thm fst_conv},
                 @{thm snd_conv}, @{thm pair_collapse}, @{thm Product_Type.split_conv}]) 1
              THEN (if (is_some name) then
                  print_tac options "before applying not introduction rule"
                  THEN Subgoal.FOCUS_PREMS
                    (fn {context = ctxt, params = params, prems, asms, concl, schematics} =>
                      rtac (the neg_intro_rule) 1
                      THEN rtac (nth prems premposition) 1) ctxt 1
                  THEN print_tac options "after applying not introduction rule"
                  THEN (EVERY (map2 (prove_param options ctxt nargs) params param_derivations))
                  THEN (REPEAT_DETERM (atac 1))
                else
                  rtac @{thm not_predI'} 1
                  (* test: *)
                  THEN dtac @{thm sym} 1
                  THEN asm_full_simp_tac (HOL_basic_ss addsimps [@{thm not_False_eq_True}]) 1)
                  THEN simp_tac (HOL_basic_ss addsimps [@{thm not_False_eq_True}]) 1
              THEN rec_tac
            end
          | Sidecond t =>
           rtac @{thm if_predI} 1
           THEN print_tac options "before sidecond:"
           THEN prove_sidecond ctxt t
           THEN print_tac options "after sidecond:"
           THEN prove_prems [] ps)
      in (prove_match options ctxt nargs out_ts)
          THEN rest_tac
      end;
    val prems_tac = prove_prems in_ts moded_ps
  in
    print_tac options "Proving clause..."
    THEN rtac @{thm bindI} 1
    THEN rtac @{thm singleI} 1
    THEN prems_tac
  end;

fun select_sup 1 1 = []
  | select_sup _ 1 = [rtac @{thm supI1}]
  | select_sup n i = (rtac @{thm supI2})::(select_sup (n - 1) (i - 1));

fun prove_one_direction options ctxt clauses preds pred mode moded_clauses =
  let
    val T = the (AList.lookup (op =) preds pred)
    val nargs = length (binder_types T)
    val pred_case_rule = the_elim_of ctxt pred
  in
    REPEAT_DETERM (CHANGED (rewrite_goals_tac @{thms split_paired_all}))
    THEN print_tac options "before applying elim rule"
    THEN etac (predfun_elim_of ctxt pred mode) 1
    THEN etac pred_case_rule 1
    THEN print_tac options "after applying elim rule"
    THEN (EVERY (map
           (fn i => EVERY' (select_sup (length moded_clauses) i) i) 
             (1 upto (length moded_clauses))))
    THEN (EVERY (map2 (prove_clause options ctxt nargs mode) clauses moded_clauses))
    THEN print_tac options "proved one direction"
  end;

(** Proof in the other direction **)

fun prove_match2 options ctxt out_ts =
  let
    val thy = Proof_Context.theory_of ctxt
    fun split_term_tac (Free _) = all_tac
      | split_term_tac t =
        if (is_constructor thy t) then
          let
            val {case_rewrites, split_asm, ...} =
              Datatype.the_info thy (fst (dest_Type (fastype_of t)))
            val num_of_constrs = length case_rewrites
            val (_, ts) = strip_comb t
          in
            print_tac options ("Term " ^ (Syntax.string_of_term ctxt t) ^ 
              "splitting with rules \n" ^ Display.string_of_thm ctxt split_asm)
            THEN TRY (Splitter.split_asm_tac [split_asm] 1
              THEN (print_tac options "after splitting with split_asm rules")
            (* THEN (Simplifier.asm_full_simp_tac HOL_basic_ss 1)
              THEN (DETERM (TRY (etac @{thm Pair_inject} 1)))*)
              THEN (REPEAT_DETERM_N (num_of_constrs - 1)
                (etac @{thm botE} 1 ORELSE etac @{thm botE} 2)))
            THEN (assert_tac (Max_number_of_subgoals 2))
            THEN (EVERY (map split_term_tac ts))
          end
      else all_tac
  in
    split_term_tac (HOLogic.mk_tuple out_ts)
    THEN (DETERM (TRY ((Splitter.split_asm_tac [@{thm "split_if_asm"}] 1)
    THEN (etac @{thm botE} 2))))
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
    val f_tac = case f of
        Const (name, T) => full_simp_tac (HOL_basic_ss addsimps 
           (@{thm eval_pred}::(predfun_definition_of ctxt name mode)
           :: @{thm "Product_Type.split_conv"}::[])) 1
      | Free _ => all_tac
      | _ => error "prove_param2: illegal parameter term"
  in
    print_tac options "before simplification in prove_args:"
    THEN f_tac
    THEN print_tac options "after simplification in prove_args"
    THEN EVERY (map2 (prove_param2 options ctxt) ho_args param_derivations)
  end

fun prove_expr2 options ctxt (t, deriv) = 
  (case strip_comb t of
      (Const (name, T), args) =>
        let
          val mode = head_mode_of deriv
          val param_derivations = param_derivations_of deriv
          val ho_args = ho_args_of mode args
        in
          etac @{thm bindE} 1
          THEN (REPEAT_DETERM (CHANGED (rewrite_goals_tac @{thms split_paired_all})))
          THEN print_tac options "prove_expr2-before"
          THEN etac (predfun_elim_of ctxt name mode) 1
          THEN print_tac options "prove_expr2"
          THEN (EVERY (map2 (prove_param2 options ctxt) ho_args param_derivations))
          THEN print_tac options "finished prove_expr2"
        end
      | _ => etac @{thm bindE} 1)

fun prove_sidecond2 options ctxt t = let
  fun preds_of t nameTs = case strip_comb t of 
    (f as Const (name, T), args) =>
      if is_registered ctxt name then (name, T) :: nameTs
        else fold preds_of args nameTs
    | _ => nameTs
  val preds = preds_of t []
  val defs = map
    (fn (pred, T) => predfun_definition_of ctxt pred 
      (all_input_of T))
      preds
  in
   (* only simplify the one assumption *)
   full_simp_tac (HOL_basic_ss' addsimps @{thm eval_pred} :: defs) 1 
   (* need better control here! *)
   THEN print_tac options "after sidecond2 simplification"
   end
  
fun prove_clause2 options ctxt pred mode (ts, ps) i =
  let
    val pred_intro_rule = nth (intros_of ctxt pred) (i - 1)
    val (in_ts, clause_out_ts) = split_mode mode ts;
    val split_ss = HOL_basic_ss' addsimps [@{thm split_eta}, @{thm split_beta},
      @{thm fst_conv}, @{thm snd_conv}, @{thm pair_collapse}]
    fun prove_prems2 out_ts [] =
      print_tac options "before prove_match2 - last call:"
      THEN prove_match2 options ctxt out_ts
      THEN print_tac options "after prove_match2 - last call:"
      THEN (etac @{thm singleE} 1)
      THEN (REPEAT_DETERM (etac @{thm Pair_inject} 1))
      THEN (asm_full_simp_tac HOL_basic_ss' 1)
      THEN TRY (
        (REPEAT_DETERM (etac @{thm Pair_inject} 1))
        THEN (asm_full_simp_tac HOL_basic_ss' 1)
        
        THEN SOLVED (print_tac options "state before applying intro rule:"
        THEN (rtac pred_intro_rule
        (* How to handle equality correctly? *)
        THEN_ALL_NEW (K (print_tac options "state before assumption matching")
        THEN' (atac ORELSE' ((CHANGED o asm_full_simp_tac split_ss) THEN' (TRY o atac)))
          THEN' (K (print_tac options "state after pre-simplification:"))
        THEN' (K (print_tac options "state after assumption matching:")))) 1))
    | prove_prems2 out_ts ((p, deriv) :: ps) =
      let
        val mode = head_mode_of deriv
        val rest_tac = (case p of
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
            print_tac options "before neg prem 2"
            THEN etac @{thm bindE} 1
            THEN (if is_some name then
                full_simp_tac (HOL_basic_ss addsimps
                  [predfun_definition_of ctxt (the name) mode]) 1
                THEN etac @{thm not_predE} 1
                THEN simp_tac (HOL_basic_ss addsimps [@{thm not_False_eq_True}]) 1
                THEN (EVERY (map2 (prove_param2 options ctxt) ho_args param_derivations))
              else
                etac @{thm not_predE'} 1)
            THEN rec_tac
          end 
        | Sidecond t =>
          etac @{thm bindE} 1
          THEN etac @{thm if_predE} 1
          THEN prove_sidecond2 options ctxt t
          THEN prove_prems2 [] ps)
      in print_tac options "before prove_match2:"
         THEN prove_match2 options ctxt out_ts
         THEN print_tac options "after prove_match2:"
         THEN rest_tac
      end;
    val prems_tac = prove_prems2 in_ts ps 
  in
    print_tac options "starting prove_clause2"
    THEN etac @{thm bindE} 1
    THEN (etac @{thm singleE'} 1)
    THEN (TRY (etac @{thm Pair_inject} 1))
    THEN print_tac options "after singleE':"
    THEN prems_tac
  end;
 
fun prove_other_direction options ctxt pred mode moded_clauses =
  let
    fun prove_clause clause i =
      (if i < length moded_clauses then etac @{thm supE} 1 else all_tac)
      THEN (prove_clause2 options ctxt pred mode clause i)
  in
    (DETERM (TRY (rtac @{thm unit.induct} 1)))
     THEN (REPEAT_DETERM (CHANGED (rewrite_goals_tac @{thms split_paired_all})))
     THEN (rtac (predfun_intro_of ctxt pred mode) 1)
     THEN (REPEAT_DETERM (rtac @{thm refl} 2))
     THEN (if null moded_clauses then
         etac @{thm botE} 1
       else EVERY (map2 prove_clause moded_clauses (1 upto (length moded_clauses))))
  end;

(** proof procedure **)

fun prove_pred options thy clauses preds pred (pol, mode) (moded_clauses, compiled_term) =
  let
    val ctxt = Proof_Context.init_global thy
    val clauses = case AList.lookup (op =) clauses pred of SOME rs => rs | NONE => []
  in
    Goal.prove ctxt (Term.add_free_names compiled_term []) [] compiled_term
      (if not (skip_proof options) then
        (fn _ =>
        rtac @{thm pred_iffI} 1
        THEN print_tac options "after pred_iffI"
        THEN prove_one_direction options ctxt clauses preds pred mode moded_clauses
        THEN print_tac options "proved one direction"
        THEN prove_other_direction options ctxt pred mode moded_clauses
        THEN print_tac options "proved other direction")
      else (fn _ => Skip_Proof.cheat_tac thy))
  end;

end;