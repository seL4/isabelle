(*  Title:      HOL/Tools/list_to_set_comprehension.ML
    Author:     Lukas Bulwahn, TU Muenchen

Simproc for rewriting list comprehensions applied to List.set to set
comprehension.
*)

signature LIST_TO_SET_COMPREHENSION =
sig
  val simproc : simpset -> cterm -> thm option
end

structure List_to_Set_Comprehension : LIST_TO_SET_COMPREHENSION =
struct

(* conversion *)

fun all_exists_conv cv ctxt ct =
  (case Thm.term_of ct of
    Const (@{const_name HOL.Ex}, _) $ Abs _ =>
      Conv.arg_conv (Conv.abs_conv (all_exists_conv cv o #2) ctxt) ct
  | _ => cv ctxt ct)

fun all_but_last_exists_conv cv ctxt ct =
  (case Thm.term_of ct of
    Const (@{const_name HOL.Ex}, _) $ Abs (_, _, Const (@{const_name HOL.Ex}, _) $ _) =>
      Conv.arg_conv (Conv.abs_conv (all_but_last_exists_conv cv o #2) ctxt) ct
  | _ => cv ctxt ct)

fun Collect_conv cv ctxt ct =
  (case Thm.term_of ct of
    Const (@{const_name Set.Collect}, _) $ Abs _ => Conv.arg_conv (Conv.abs_conv cv ctxt) ct
  | _ => raise CTERM ("Collect_conv", [ct]))

fun Trueprop_conv cv ct =
  (case Thm.term_of ct of
    Const (@{const_name Trueprop}, _) $ _ => Conv.arg_conv cv ct
  | _ => raise CTERM ("Trueprop_conv", [ct]))

fun eq_conv cv1 cv2 ct =
  (case Thm.term_of ct of
    Const (@{const_name HOL.eq}, _) $ _ $ _ => Conv.combination_conv (Conv.arg_conv cv1) cv2 ct
  | _ => raise CTERM ("eq_conv", [ct]))

fun conj_conv cv1 cv2 ct =
  (case Thm.term_of ct of
    Const (@{const_name HOL.conj}, _) $ _ $ _ => Conv.combination_conv (Conv.arg_conv cv1) cv2 ct
  | _ => raise CTERM ("conj_conv", [ct]))

fun rewr_conv' th = Conv.rewr_conv (mk_meta_eq th)

fun conjunct_assoc_conv ct =
  Conv.try_conv
    (rewr_conv' @{thm conj_assoc} then_conv conj_conv Conv.all_conv conjunct_assoc_conv) ct

fun right_hand_set_comprehension_conv conv ctxt =
  Trueprop_conv (eq_conv Conv.all_conv
    (Collect_conv (all_exists_conv conv o #2) ctxt))


(* term abstraction of list comprehension patterns *)

datatype termlets = If | Case of (typ * int)

fun simproc ss redex =
  let
    val ctxt = Simplifier.the_context ss
    val thy = Proof_Context.theory_of ctxt
    val set_Nil_I = @{thm trans} OF [@{thm set.simps(1)}, @{thm empty_def}]
    val set_singleton = @{lemma "set [a] = {x. x = a}" by simp}
    val inst_Collect_mem_eq = @{lemma "set A = {x. x : set A}" by simp}
    val del_refl_eq = @{lemma "(t = t & P) == P" by simp}
    fun mk_set T = Const (@{const_name List.set}, HOLogic.listT T --> HOLogic.mk_setT T)
    fun dest_set (Const (@{const_name List.set}, _) $ xs) = xs
    fun dest_singleton_list (Const (@{const_name List.Cons}, _)
          $ t $ (Const (@{const_name List.Nil}, _))) = t
      | dest_singleton_list t = raise TERM ("dest_singleton_list", [t])
    (* We check that one case returns a singleton list and all other cases
       return [], and return the index of the one singleton list case *)
    fun possible_index_of_singleton_case cases =
      let
        fun check (i, case_t) s =
          (case strip_abs_body case_t of
            (Const (@{const_name List.Nil}, _)) => s
          | _ => (case s of NONE => SOME i | SOME _ => NONE))
      in
        fold_index check cases NONE
      end
    (* returns (case_expr type index chosen_case) option  *)
    fun dest_case case_term =
      let
        val (case_const, args) = strip_comb case_term
      in
        (case try dest_Const case_const of
          SOME (c, T) =>
            (case Datatype.info_of_case thy c of
              SOME _ =>
                (case possible_index_of_singleton_case (fst (split_last args)) of
                  SOME i =>
                    let
                      val (Ts, _) = strip_type T
                      val T' = List.last Ts
                    in SOME (List.last args, T', i, nth args i) end
                | NONE => NONE)
            | NONE => NONE)
        | NONE => NONE)
      end
    (* returns condition continuing term option *)
    fun dest_if (Const (@{const_name If}, _) $ cond $ then_t $ Const (@{const_name Nil}, _)) =
          SOME (cond, then_t)
      | dest_if _ = NONE
    fun tac _ [] = rtac set_singleton 1 ORELSE rtac inst_Collect_mem_eq 1
      | tac ctxt (If :: cont) =
          Splitter.split_tac [@{thm split_if}] 1
          THEN rtac @{thm conjI} 1
          THEN rtac @{thm impI} 1
          THEN Subgoal.FOCUS (fn {prems, context, ...} =>
            CONVERSION (right_hand_set_comprehension_conv (K
              (conj_conv (Conv.rewr_conv (List.last prems RS @{thm Eq_TrueI})) Conv.all_conv
               then_conv
               rewr_conv' @{lemma "(True & P) = P" by simp})) context) 1) ctxt 1
          THEN tac ctxt cont
          THEN rtac @{thm impI} 1
          THEN Subgoal.FOCUS (fn {prems, context, ...} =>
              CONVERSION (right_hand_set_comprehension_conv (K
                (conj_conv (Conv.rewr_conv (List.last prems RS @{thm Eq_FalseI})) Conv.all_conv
                 then_conv rewr_conv' @{lemma "(False & P) = False" by simp})) context) 1) ctxt 1
          THEN rtac set_Nil_I 1
      | tac ctxt (Case (T, i) :: cont) =
          let
            val info = Datatype.the_info thy (fst (dest_Type T))
          in
            (* do case distinction *)
            Splitter.split_tac [#split info] 1
            THEN EVERY (map_index (fn (i', _) =>
              (if i' < length (#case_rewrites info) - 1 then rtac @{thm conjI} 1 else all_tac)
              THEN REPEAT_DETERM (rtac @{thm allI} 1)
              THEN rtac @{thm impI} 1
              THEN (if i' = i then
                (* continue recursively *)
                Subgoal.FOCUS (fn {prems, context, ...} =>
                  CONVERSION (Thm.eta_conversion then_conv right_hand_set_comprehension_conv (K
                      ((conj_conv
                        (eq_conv Conv.all_conv (rewr_conv' (List.last prems)) then_conv
                          (Conv.try_conv (Conv.rewrs_conv (map mk_meta_eq (#inject info)))))
                        Conv.all_conv)
                        then_conv (Conv.try_conv (Conv.rewr_conv del_refl_eq))
                        then_conv conjunct_assoc_conv)) context
                    then_conv (Trueprop_conv (eq_conv Conv.all_conv (Collect_conv (fn (_, ctxt) =>
                      Conv.repeat_conv
                        (all_but_last_exists_conv
                          (K (rewr_conv'
                            @{lemma "(EX x. x = t & P x) = P t" by simp})) ctxt)) context)))) 1) ctxt 1
                THEN tac ctxt cont
              else
                Subgoal.FOCUS (fn {prems, context, ...} =>
                  CONVERSION
                    (right_hand_set_comprehension_conv (K
                      (conj_conv
                        ((eq_conv Conv.all_conv
                          (rewr_conv' (List.last prems))) then_conv
                          (Conv.rewrs_conv (map (fn th => th RS @{thm Eq_FalseI}) (#distinct info))))
                        Conv.all_conv then_conv
                        (rewr_conv' @{lemma "(False & P) = False" by simp}))) context then_conv
                      Trueprop_conv
                        (eq_conv Conv.all_conv
                          (Collect_conv (fn (_, ctxt) =>
                            Conv.repeat_conv
                              (Conv.bottom_conv
                                (K (rewr_conv'
                                  @{lemma "(EX x. P) = P" by simp})) ctxt)) context))) 1) ctxt 1
                THEN rtac set_Nil_I 1)) (#case_rewrites info))
          end
    fun make_inner_eqs bound_vs Tis eqs t =
      (case dest_case t of
        SOME (x, T, i, cont) =>
          let
            val (vs, body) = strip_abs (Pattern.eta_long (map snd bound_vs) cont)
            val x' = incr_boundvars (length vs) x
            val eqs' = map (incr_boundvars (length vs)) eqs
            val (constr_name, _) = nth (the (Datatype.get_constrs thy (fst (dest_Type T)))) i
            val constr_t =
              list_comb
                (Const (constr_name, map snd vs ---> T), map Bound (((length vs) - 1) downto 0))
            val constr_eq = Const (@{const_name HOL.eq}, T --> T --> @{typ bool}) $ constr_t $ x'
          in
            make_inner_eqs (rev vs @ bound_vs) (Case (T, i) :: Tis) (constr_eq :: eqs') body
          end
      | NONE =>
          (case dest_if t of
            SOME (condition, cont) => make_inner_eqs bound_vs (If :: Tis) (condition :: eqs) cont
          | NONE =>
            if eqs = [] then NONE (* no rewriting, nothing to be done *)
            else
              let
                val Type (@{type_name List.list}, [rT]) = fastype_of1 (map snd bound_vs, t)
                val pat_eq =
                  (case try dest_singleton_list t of
                    SOME t' =>
                      Const (@{const_name HOL.eq}, rT --> rT --> @{typ bool}) $
                        Bound (length bound_vs) $ t'
                  | NONE =>
                      Const (@{const_name Set.member}, rT --> HOLogic.mk_setT rT --> @{typ bool}) $
                        Bound (length bound_vs) $ (mk_set rT $ t))
                val reverse_bounds = curry subst_bounds
                  ((map Bound ((length bound_vs - 1) downto 0)) @ [Bound (length bound_vs)])
                val eqs' = map reverse_bounds eqs
                val pat_eq' = reverse_bounds pat_eq
                val inner_t =
                  fold (fn (_, T) => fn t => HOLogic.exists_const T $ absdummy T t)
                    (rev bound_vs) (fold (curry HOLogic.mk_conj) eqs' pat_eq')
                val lhs = term_of redex
                val rhs = HOLogic.mk_Collect ("x", rT, inner_t)
                val rewrite_rule_t = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
              in
                SOME
                  ((Goal.prove ctxt [] [] rewrite_rule_t
                    (fn {context, ...} => tac context (rev Tis))) RS @{thm eq_reflection})
              end))
  in
    make_inner_eqs [] [] [] (dest_set (term_of redex))
  end

end
