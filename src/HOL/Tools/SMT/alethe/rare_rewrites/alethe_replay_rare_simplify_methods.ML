(*  Title:      HOL/CVC/ML/alethe_replay_rare_simplify_methods.ML
    Author:     Mathias Fleury, MPII, JKU, University Freiburg
    Author:     Hanna Lachnitt, Stanford University

Proof method for replaying Alethe proofs for rare-simplify
*)

signature ALETHE_REPLAY_RARE_SIMPLIFY_METHODS =
sig
  val rare_rewrite: Alethe_Replay_Methods.alethe_tac_step_args
  val rare_rec_mode: int Config.T
  exception RARE_REPLAY of string
end;

structure Alethe_Replay_RARE_Simplify_Methods: ALETHE_REPLAY_RARE_SIMPLIFY_METHODS =
struct

exception RARE_REPLAY of string

(*
0: use lemma & simplify if not possible (default)
1: use only lemma
2: use only simplify

We tested many more configurations (using match, simplify but adding the lemmas to the simpset etc).
*)
val rare_rec_mode = Attrib.setup_config_int \<^binding>\<open>rare_rec_mode\<close> (K 0)


(*imports*)
val TRY' = Alethe_Replay_Methods.TRY'
val simplify_tac = Alethe_Replay_Methods.simplify_tac

val low = SMT_Config.low
val middle = SMT_Config.middle
val high = SMT_Config.high
fun debug_msg ctxt = SMT_Config.alethe_debug_msg ctxt "alethe_replay_rare"
fun debug_msg_tac' ctxt verbosity str = K (SMT_Config.alethe_debug_msg_tac ctxt "alethe_replay_rare" verbosity str)

fun dest_prop (Const (\<^const_name>\<open>Trueprop\<close>, _) $ t) = t
  | dest_prop t = t


(* Evaluation of constants *)

(* Any additional lemmas should be added to cvc_evaluate or cvc_evaluate_bv*)
fun evaluate_tac ctxt _ =
  debug_msg_tac' ctxt high "evaluate start" THEN'
  TRY' (Code_Simp.dynamic_tac ctxt)
  THEN' debug_msg_tac' ctxt high "evaluate after Code_Simp.dynamic_tac"
  THEN' TRY' (Lin_Arith.tac ctxt)
  THEN' debug_msg_tac' ctxt high "evaluate after Linarith"
  THEN' TRY' (simplify_tac ctxt (
    (Named_Theorems.get ctxt @{named_theorems cvc_evaluate})
  @ (Named_Theorems.get ctxt @{named_theorems cvc_evaluate_bv})
  ))
  THEN' debug_msg_tac' ctxt high "evaluate after unfolding cvc_evaluate lemmas"

(*We have to abstract the terms because foralls in if then elses. The code generator cannot
deal with those. This unfortunately includes adding all operators.*)
fun try_evaluate ctxt t =
  SMT_Replay_Methods.prove_abstract' ctxt t evaluate_tac
    (SMT_Replay_Methods.abstract_for_code_eval ctxt (dest_prop t))

(*The simpset is cleared after each step which might not be what we want*)
fun try_simp_tac thms ctxt =
  TRY' (K (HEADGOAL (simplify_tac ctxt thms)))
  THEN' debug_msg_tac' ctxt high "try_simp after (maybe) trying out a subset of lemmas"
  THEN' TRY' (K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems cvc_evaluate})))))
  THEN' TRY' (K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems rare_simplify_temp})))))
  THEN' TRY' (K (HEADGOAL (simplify_tac ctxt @{thms arith_simps alethe_minus_simplify})))
  THEN' TRY' (K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))))
  THEN' TRY' (K (Clasimp.auto_tac ctxt))

fun try_simp ctxt t thms = SMT_Replay_Methods.prove ctxt t (fn ctxt => try_simp_tac thms ctxt)

(* Rare rewrite reconstruction *)

fun normalize_list_arg (Const (\<^const_name>\<open>Alethe_Rare_Nary_Ops.cvc_ListVar.ListVar\<close>, _) $ Const (\<^const_name>\<open>List.Nil\<close>, _)) t =
  (case try hd (dest_Type t |> snd) of
    NONE => @{term "ListVar (List.Nil::dummy List.list) :: dummy cvc_ListVar"} |
    SOME (t') =>
      Const (\<^const_name>\<open>ListVar\<close>, Type(\<^type_name>\<open>List.list\<close>, [t']) --> Type(\<^type_name>\<open>cvc_ListVar\<close>, [t']))
      $ Const (\<^const_name>\<open>List.Nil\<close>, Type(\<^type_name>\<open>List.list\<close>, [t']))
  )
| normalize_list_arg a _ = a

fun rewrite_lemma_inst _ lemma [] [] = lemma
  (* For bit-vectors we need to allow too many arguments but this snippet can be useful for testing:
  | rewrite_lemma_inst _ [] (_::_) =
              raise RARE_REPLAY("Too few arguments for RARE rewrite " ^ rewrite_name)
  | rewrite_lemma_inst _ _ [] =
              raise RARE_REPLAY("Too many arguments for RARE rewrite " ^ rewrite_name)*)
  | rewrite_lemma_inst ctxt lemma (a :: args') (t :: typs') =
  let
    val rec_lemma = rewrite_lemma_inst ctxt lemma args' typs'
    val a_normalized = normalize_list_arg a t |> Thm.cterm_of ctxt |> SOME |> single
    val res = Drule.infer_instantiate' ctxt a_normalized rec_lemma
  in res end
  | rewrite_lemma_inst _ lemma _ _ = lemma

fun instantiate_lemma ctxt args lemma =
  let
    fun get_types lemma = map snd (rev (Term.add_vars (Thm.full_prop_of lemma) []))
    val args_terms = rev (Const ("Groups.zero_class.zero", @{typ int}) :: args) (*The extra term is for the dummy argument we need to add the expected order to the arguments*)
    val all_types = rev (get_types lemma)
    val args_types_from_lemma = drop (length all_types - length args_terms) all_types
    val _ = debug_msg ctxt high (fn () => @{print} ("Argument types extracted from lemma", args_types_from_lemma));
    val _ = debug_msg ctxt high (fn () => @{print} ("Arguments ", args_terms));
  in rewrite_lemma_inst ctxt lemma args_terms args_types_from_lemma end

fun dsl_tac_initialize rewrite_name args ctxt t prems =
  let
    val rare_mode = (Config.get ctxt rare_rec_mode)
    val _ = debug_msg ctxt high (fn () => @{print} ("rare_rec_mode " ^ Int.toString rare_mode))
  in
    if rare_mode = 2 (*Use only simplify*)
    then try_simp ctxt t prems
    else
      (case rewrite_name of (*cheating: hardcoding some common rules, saving around 3ms each time TODO: Should be measured again*)
        "bool_double_not_elim" => SMT_Replay_Methods.prove ctxt t (fn _ =>
          match_tac ctxt [@{thm not_not}])
       | "eq_refl" => SMT_Replay_Methods.prove ctxt t (fn _ =>
          match_tac ctxt [@{lemma \<open>(a=a) = True\<close> by blast}])
       | "eq_symm" => SMT_Replay_Methods.prove ctxt t (fn _ =>
          match_tac ctxt @{thms eq_commute})
       | "distinct_false" => SMT_Replay_Methods.prove ctxt t (fn _ =>
         try_simp_tac [] ctxt)
       | _ =>
          (case CVC5_Rare.rare_lookup (Context.Proof ctxt) ("rewrite_" ^ rewrite_name) of
           NONE =>
             if rare_mode = 1 then
               let
                val _ = debug_msg ctxt high (fn () => @{print} ("undeclared RARE rule: " ^ rewrite_name ^ ". Use cvc5_rare \"full_name\"."))
               in raise RARE_REPLAY("could not find lemma for rare rewrite " ^ rewrite_name) end
              else try_simp ctxt t prems
           | SOME rewrite_lemmas => (*lemma found and we are supposed to use it*)
              let
                val _ = debug_msg ctxt middle (fn () => @{print} ("Lemmas corresponding to the current rewrite rule", rewrite_lemmas));

                val inst_lemmas = map_filter (try (instantiate_lemma ctxt args)) rewrite_lemmas
                val _ = debug_msg ctxt middle (fn () => @{print} ("Instantiated lemmas", inst_lemmas));

                val cvc_list_defs = @{thms cvc_list_right_Nil cvc_list_left_Nil cvc_list_both_Singleton
                  cvc_list_right_Cons cvc_list_left_Cons cvc_list_both_Cons
                  cvc_list_both_Cons_0 cvc_list_both_Cons_1 NO_MATCH_def}
                val inst_lemmas_without_list =
                  map (Local_Defs.unfold ctxt (cvc_list_defs @ (Named_Theorems.get ctxt @{named_theorems smt_rewrite_lemma_simplify}))) inst_lemmas

                (*This is done to get rid of the bogus term used to enforce the expected ordering on the arguments*)
                val inst_lemmas_without_true
                  = map (Tactic.rule_by_tactic ctxt (resolve_tac ctxt [@{thm TrueI}] 1)) inst_lemmas_without_list
                val _ = debug_msg ctxt middle (fn () => @{print} ("Instantiated lemmas without custom list operators", inst_lemmas_without_true));
                val _ = debug_msg ctxt middle (fn () => @{print} ("nr of viable instantiated lemmas", length inst_lemmas_without_true));

                val cvc_evaluate_thms = Named_Theorems.get ctxt @{named_theorems cvc_evaluate}
                fun debug_msg_tac'' ctxt verbosity str = debug_msg_tac' ctxt verbosity ("rare_rewrite: " ^ str)

                fun try_lemma_i _ =
                (fn t => (SMT_Replay_Methods.prove ctxt t (fn ctxt =>
                  TRY' (debug_msg_tac'' ctxt high "reconstruct rewrite")
                  THEN'
                    ((CHANGED_GOAL
                        (EqSubst.eqsubst_tac ctxt [0] [nth inst_lemmas_without_true 0] (*for bv's we will have to find the right lemma here, for now it is fine to just use the first*))
                      THEN' (TRY' (resolve_tac ctxt prems))
                      THEN' debug_msg_tac'' ctxt high "resolved premise if there was one"
                      THEN' TRY' (resolve_tac ctxt [@{thm refl}]))
                    ORELSE'
                      (fn i => fn st => (if rare_mode = 1
                      then
                       (let val _ = debug_msg ctxt middle (fn () => @{print}("lemma,goal", (nth inst_lemmas_without_true 0, Thm.cterm_of ctxt t)));in (K no_tac) end)
                      else try_simp_tac prems ctxt) i st))
                  THEN_ALL_NEW (
                    debug_msg_tac'' ctxt high "trying to discharge assumption of RARE lemma"
                    THEN' TRY' (resolve_tac ctxt prems THEN' TRY' (debug_msg_tac'' ctxt high "discharged via alethe premise"))
                    THEN' TRY' (simplify_tac ctxt cvc_evaluate_thms THEN' TRY' (debug_msg_tac'' ctxt high "simplified goal with cvc_evaluate"))
                    THEN' TRY'
                    (simplify_tac ctxt cvc_evaluate_thms
                    THEN' debug_msg_tac'' ctxt high "simplified goal with cvc_evaluate")
                    THEN' TRY' (Code_Simp.dynamic_tac ctxt THEN' TRY' (debug_msg_tac'' ctxt high "applied code evaluator")) (*slowest method, so at the end*))
                  THEN' (debug_msg_tac'' ctxt high "should be solved now")
                ))) t
              in
                if not (null inst_lemmas_without_true)
                then (if rare_mode = 1 then raise ERROR("Rule could not be used") else try_lemma_i 0)
                else (if rare_mode = 0 then try_simp ctxt t prems else raise ERROR("Rule could not be instantiated") )
              end))
end

local
  fun pretty tag lines = map Pretty.str lines |> Pretty.big_list tag |> Pretty.string_of
in
  fun rare_rewrite ctxt (th : thm list) (x :: args) t =
    let
      val rewrite_name = String.map (fn #"-" => #"_" | x => x) (HOLogic.dest_string x)
    in
      (debug_msg ctxt low (fn () => @{print} "Found rare rewrite " ^ rewrite_name);
      dsl_tac_initialize rewrite_name args ctxt t th)
      handle (RARE_REPLAY msg) => raise (SMT_Failure.SMT (SMT_Failure.Replay("rare-rewrite", ERROR msg)))
    end
  | rare_rewrite ctxt _ args _ =
      (SMT_Config.verbose_msg ctxt (pretty ("No dsl rule found, try to simplify" ^
         List.foldr op^ "" (map ML_Syntax.print_term args))) [];
       raise (SMT_Failure.SMT (SMT_Failure.Replay("rare-rewrite", ERROR "could not find lemma for rare rewrite"))))

  fun evaluate ctxt _ _ = try_evaluate ctxt
end

val rules = [
  ("rare_rewrite", rare_rewrite),
  ("evaluate", evaluate)
]

val _ = Theory.setup (Context.theory_map (
  fold (uncurry Alethe_Replay_Methods.declare_alethe_rule) rules))

end
