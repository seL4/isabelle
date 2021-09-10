(*  Title:      HOL/Decision_Procs/approximation.ML
    Author:     Johannes Hoelzl, TU Muenchen
*)

signature APPROXIMATION =
sig
  val reify_form: Proof.context -> term -> term
  val approx: int -> Proof.context -> term -> term
  val approximate: Proof.context -> term -> term
  val approximation_tac : int -> (string * int) list -> int option -> Proof.context -> int -> tactic
end

structure Approximation =
struct

fun reorder_bounds_tac ctxt prems i =
  let
    fun variable_of_bound (Const (\<^const_name>\<open>Trueprop\<close>, _) $
                           (Const (\<^const_name>\<open>Set.member\<close>, _) $
                            Free (name, _) $ _)) = name
      | variable_of_bound (Const (\<^const_name>\<open>Trueprop\<close>, _) $
                           (Const (\<^const_name>\<open>HOL.eq\<close>, _) $
                            Free (name, _) $ _)) = name
      | variable_of_bound t = raise TERM ("variable_of_bound", [t])

    val variable_bounds
      = map (`(variable_of_bound o Thm.prop_of)) prems

    fun add_deps (name, bnds)
      = Graph.add_deps_acyclic (name,
          remove (op =) name (Term.add_free_names (Thm.prop_of bnds) []))

    val order = Graph.empty
                |> fold Graph.new_node variable_bounds
                |> fold add_deps variable_bounds
                |> Graph.strong_conn |> map the_single |> rev
                |> map_filter (AList.lookup (op =) variable_bounds)

    fun prepend_prem th tac =
      tac THEN resolve_tac ctxt [th RSN (2, @{thm mp})] i
  in
    fold prepend_prem order all_tac
  end

fun approximate ctxt t = case fastype_of t
   of \<^typ>\<open>bool\<close> =>
        Approximation_Computation.approx_bool ctxt t
    | \<^typ>\<open>(float interval) option\<close> =>
        Approximation_Computation.approx_arith ctxt t
    | \<^typ>\<open>(float interval) option list\<close> =>
        Approximation_Computation.approx_form_eval ctxt t
    | _ => error ("Bad term: " ^ Syntax.string_of_term ctxt t);

fun rewrite_interpret_form_tac ctxt prec splitting taylor i st = let
    fun lookup_splitting (Free (name, _)) =
        (case AList.lookup (op =) splitting name
          of SOME s => HOLogic.mk_number \<^typ>\<open>nat\<close> s
           | NONE => \<^term>\<open>0 :: nat\<close>)
      | lookup_splitting t = raise TERM ("lookup_splitting", [t])
    val vs = nth (Thm.prems_of st) (i - 1)
             |> Logic.strip_imp_concl
             |> HOLogic.dest_Trueprop
             |> Term.strip_comb |> snd |> List.last
             |> HOLogic.dest_list
    val p = prec
            |> HOLogic.mk_number \<^typ>\<open>nat\<close>
            |> Thm.cterm_of ctxt
  in case taylor
  of NONE => let
       val n = vs |> length
               |> HOLogic.mk_number \<^typ>\<open>nat\<close>
               |> Thm.cterm_of ctxt
       val s = vs
               |> map lookup_splitting
               |> HOLogic.mk_list \<^typ>\<open>nat\<close>
               |> Thm.cterm_of ctxt
     in
       (resolve_tac ctxt [Thm.instantiate (TVars.empty,
           Vars.make [((("n", 0), \<^typ>\<open>nat\<close>), n),
                      ((("prec", 0), \<^typ>\<open>nat\<close>), p),
                      ((("ss", 0), \<^typ>\<open>nat list\<close>), s)])
            @{thm approx_form}] i
        THEN simp_tac (put_simpset (simpset_of \<^context>) ctxt) i) st
     end

   | SOME t =>
     if length vs <> 1
     then raise (TERM ("More than one variable used for taylor series expansion", [Thm.prop_of st]))
     else let
       val t = t
            |> HOLogic.mk_number \<^typ>\<open>nat\<close>
            |> Thm.cterm_of ctxt
       val s = vs |> map lookup_splitting |> hd
            |> Thm.cterm_of ctxt
     in
       resolve_tac ctxt [Thm.instantiate (TVars.empty,
            Vars.make [((("s", 0), \<^typ>\<open>nat\<close>), s),
                       ((("t", 0), \<^typ>\<open>nat\<close>), t),
                       ((("prec", 0), \<^typ>\<open>nat\<close>), p)])
            @{thm approx_tse_form}] i st
     end
  end

fun calculated_subterms (\<^const>\<open>Trueprop\<close> $ t) = calculated_subterms t
  | calculated_subterms (\<^const>\<open>HOL.implies\<close> $ _ $ t) = calculated_subterms t
  | calculated_subterms (\<^term>\<open>(\<le>) :: real \<Rightarrow> real \<Rightarrow> bool\<close> $ t1 $ t2) = [t1, t2]
  | calculated_subterms (\<^term>\<open>(<) :: real \<Rightarrow> real \<Rightarrow> bool\<close> $ t1 $ t2) = [t1, t2]
  | calculated_subterms (\<^term>\<open>(\<in>) :: real \<Rightarrow> real set \<Rightarrow> bool\<close> $ t1 $
                         (\<^term>\<open>atLeastAtMost :: real \<Rightarrow> real \<Rightarrow> real set\<close> $ t2 $ t3)) = [t1, t2, t3]
  | calculated_subterms t = raise TERM ("calculated_subterms", [t])

fun dest_interpret_form (\<^const>\<open>interpret_form\<close> $ b $ xs) = (b, xs)
  | dest_interpret_form t = raise TERM ("dest_interpret_form", [t])

fun dest_interpret (\<^const>\<open>interpret_floatarith\<close> $ b $ xs) = (b, xs)
  | dest_interpret t = raise TERM ("dest_interpret", [t])

fun dest_interpret_env (\<^const>\<open>interpret_form\<close> $ _ $ xs) = xs
  | dest_interpret_env (\<^const>\<open>interpret_floatarith\<close> $ _ $ xs) = xs
  | dest_interpret_env t = raise TERM ("dest_interpret_env", [t])

fun dest_float (\<^const>\<open>Float\<close> $ m $ e) = (snd (HOLogic.dest_number m), snd (HOLogic.dest_number e))
  | dest_float t = raise TERM ("dest_float", [t])


fun dest_ivl
  (Const (\<^const_name>\<open>Some\<close>, _) $
    (Const (\<^const_name>\<open>Interval\<close>, _) $ ((Const (\<^const_name>\<open>Pair\<close>, _) $ u $ l)))) =
      SOME (dest_float u, dest_float l)
  | dest_ivl (Const (\<^const_name>\<open>None\<close>, _)) = NONE
  | dest_ivl t = raise TERM ("dest_result", [t])

fun mk_approx' prec t = (\<^const>\<open>approx'\<close>
                       $ HOLogic.mk_number \<^typ>\<open>nat\<close> prec
                       $ t $ \<^term>\<open>[] :: (float interval) option list\<close>)

fun mk_approx_form_eval prec t xs = (\<^const>\<open>approx_form_eval\<close>
                       $ HOLogic.mk_number \<^typ>\<open>nat\<close> prec
                       $ t $ xs)

fun float2_float10 prec round_down (m, e) = (
  let
    val (m, e) = (if e < 0 then (m,e) else (m * Integer.pow e 2, 0))

    fun frac _ _ 0 digits cnt = (digits, cnt, 0)
      | frac _ 0 r digits cnt = (digits, cnt, r)
      | frac c p r digits cnt = (let
        val (d, r) = Integer.div_mod (r * 10) (Integer.pow (~e) 2)
      in frac (c orelse d <> 0) (if d <> 0 orelse c then p - 1 else p) r
              (digits * 10 + d) (cnt + 1)
      end)

    val sgn = Int.sign m
    val m = abs m

    val round_down = (sgn = 1 andalso round_down) orelse
                     (sgn = ~1 andalso not round_down)

    val (x, r) = Integer.div_mod m (Integer.pow (~e) 2)

    val p = ((if x = 0 then prec else prec - (Integer.log2 x + 1)) * 3) div 10 + 1

    val (digits, e10, r) = if p > 0 then frac (x <> 0) p r 0 0 else (0,0,0)

    val digits = if round_down orelse r = 0 then digits else digits + 1

  in (sgn * (digits + x * (Integer.pow e10 10)), ~e10)
  end)

fun mk_result prec (SOME (l, u)) =
  (let
    fun mk_float10 rnd x = (let val (m, e) = float2_float10 prec rnd x
                       in if e = 0 then HOLogic.mk_number \<^typ>\<open>real\<close> m
                     else if e = 1 then \<^term>\<open>divide :: real \<Rightarrow> real \<Rightarrow> real\<close> $
                                        HOLogic.mk_number \<^typ>\<open>real\<close> m $
                                        \<^term>\<open>10\<close>
                                   else \<^term>\<open>divide :: real \<Rightarrow> real \<Rightarrow> real\<close> $
                                        HOLogic.mk_number \<^typ>\<open>real\<close> m $
                                        (\<^term>\<open>power 10 :: nat \<Rightarrow> real\<close> $
                                         HOLogic.mk_number \<^typ>\<open>nat\<close> (~e)) end)
    in \<^term>\<open>atLeastAtMost :: real \<Rightarrow> real \<Rightarrow> real set\<close> $ mk_float10 true l $ mk_float10 false u end)
  | mk_result _ NONE = \<^term>\<open>UNIV :: real set\<close>

fun realify t =
  let
    val t = Logic.varify_global t
    val m = map (fn (name, _) => (name, \<^typ>\<open>real\<close>)) (Term.add_tvars t [])
    val t = Term.subst_TVars m t
  in t end

fun apply_tactic ctxt term tactic =
  Thm.cterm_of ctxt term
  |> Goal.init
  |> SINGLE tactic
  |> the |> Thm.prems_of |> hd

fun preproc_form_conv ctxt =
  Simplifier.rewrite
   (put_simpset HOL_basic_ss ctxt addsimps
     (Named_Theorems.get ctxt \<^named_theorems>\<open>approximation_preproc\<close>))

fun reify_form_conv ctxt ct =
  let
    val thm =
       Reification.conv ctxt @{thms interpret_form.simps interpret_floatarith.simps} ct
       handle ERROR msg =>
        cat_error ("Reification failed: " ^ msg)
          ("Approximation does not support " ^
            quote (Syntax.string_of_term ctxt (Thm.term_of ct)))
    fun check_env (Free _) = ()
      | check_env (Var _) = ()
      | check_env t =
          cat_error "Term not supported by approximation:" (Syntax.string_of_term ctxt t)
    val _ = Thm.rhs_of thm |> Thm.term_of |> dest_interpret_env |> HOLogic.dest_list |> map check_env
  in thm end


fun reify_form_tac ctxt i = CONVERSION (Conv.arg_conv (reify_form_conv ctxt)) i

fun prepare_form_tac ctxt i =
  REPEAT (FIRST' [eresolve_tac ctxt @{thms intervalE},
    eresolve_tac ctxt @{thms meta_eqE},
    resolve_tac ctxt @{thms impI}] i)
  THEN Subgoal.FOCUS (fn {prems, context = ctxt', ...} => reorder_bounds_tac ctxt' prems i) ctxt i
  THEN DETERM (TRY (filter_prems_tac ctxt (K false) i))
  THEN CONVERSION (Conv.arg_conv (preproc_form_conv ctxt)) i

fun prepare_form ctxt term = apply_tactic ctxt term (prepare_form_tac ctxt 1)

fun apply_reify_form ctxt t = apply_tactic ctxt t (reify_form_tac ctxt 1)

fun reify_form ctxt t = HOLogic.mk_Trueprop t
  |> prepare_form ctxt
  |> apply_reify_form ctxt
  |> HOLogic.dest_Trueprop

fun approx_form prec ctxt t =
        realify t
     |> prepare_form ctxt
     |> (fn arith_term => apply_reify_form ctxt arith_term
         |> HOLogic.dest_Trueprop
         |> dest_interpret_form
         |> (fn (data, xs) =>
            mk_approx_form_eval prec data (HOLogic.mk_list \<^typ>\<open>(float interval) option\<close>
              (map (fn _ => \<^term>\<open>None :: (float interval) option\<close>) (HOLogic.dest_list xs)))
         |> approximate ctxt
         |> HOLogic.dest_list
         |> curry ListPair.zip (HOLogic.dest_list xs @ calculated_subterms arith_term)
         |> map (fn (elem, s) => \<^term>\<open>(\<in>) :: real \<Rightarrow> real set \<Rightarrow> bool\<close> $ elem $ mk_result prec (dest_ivl s))
         |> foldr1 HOLogic.mk_conj))

fun approx_arith prec ctxt t = realify t
     |> Thm.cterm_of ctxt
     |> (preproc_form_conv ctxt then_conv reify_form_conv ctxt)
     |> Thm.prop_of
     |> Logic.dest_equals |> snd
     |> dest_interpret |> fst
     |> mk_approx' prec
     |> approximate ctxt
     |> dest_ivl
     |> mk_result prec

fun approx prec ctxt t =
  if type_of t = \<^typ>\<open>prop\<close> then approx_form prec ctxt t
  else if type_of t = \<^typ>\<open>bool\<close> then approx_form prec ctxt (\<^const>\<open>Trueprop\<close> $ t)
  else approx_arith prec ctxt t

fun approximate_cmd modes raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val t = Syntax.read_term ctxt raw_t;
    val t' = approx 30 ctxt t;
    val ty' = Term.type_of t';
    val ctxt' = Proof_Context.augment t' ctxt;
  in
    Print_Mode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ()
  end |> Pretty.writeln;

val opt_modes =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) [];

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>approximate\<close> "print approximation of term"
    (opt_modes -- Parse.term
      >> (fn (modes, t) => Toplevel.keep (approximate_cmd modes t)));

fun approximation_tac prec splitting taylor ctxt =
  prepare_form_tac ctxt
  THEN' reify_form_tac ctxt
  THEN' rewrite_interpret_form_tac ctxt prec splitting taylor
  THEN' CONVERSION (Approximation_Computation.approx_conv ctxt)
  THEN' resolve_tac ctxt [TrueI]

end;
