(*  Title:      HOL/Decision_Procs/approximation.ML
    Author:     Johannes Hoelzl, TU Muenchen
*)

signature APPROXIMATION =
sig
  val approx: int -> Proof.context -> term -> term
  val approximate: Proof.context -> term -> term
  val approximation_tac : int -> (string * int) list -> int option -> Proof.context -> int -> tactic
end

structure Approximation: APPROXIMATION =
struct

fun reorder_bounds_tac prems i =
  let
    fun variable_of_bound (Const (@{const_name Trueprop}, _) $
                           (Const (@{const_name Set.member}, _) $
                            Free (name, _) $ _)) = name
      | variable_of_bound (Const (@{const_name Trueprop}, _) $
                           (Const (@{const_name HOL.eq}, _) $
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

    fun prepend_prem th tac
      = tac THEN rtac (th RSN (2, @{thm mp})) i
  in
    fold prepend_prem order all_tac
  end

fun approximation_conv ctxt ct =
  approximation_oracle (Proof_Context.theory_of ctxt, Thm.term_of ct |> tap (tracing o Syntax.string_of_term ctxt));

fun approximate ctxt t =
  approximation_oracle (Proof_Context.theory_of ctxt, t)
  |> Thm.prop_of |> Logic.dest_equals |> snd;

(* Should be in HOL.thy ? *)
fun gen_eval_tac conv ctxt = CONVERSION
  (Object_Logic.judgment_conv (Conv.params_conv (~1) (K (Conv.concl_conv (~1) conv)) ctxt))
  THEN' rtac TrueI

val form_equations = @{thms interpret_form_equations};

fun rewrite_interpret_form_tac ctxt prec splitting taylor i st = let
    fun lookup_splitting (Free (name, _))
      = case AList.lookup (op =) splitting name
        of SOME s => HOLogic.mk_number @{typ nat} s
         | NONE => @{term "0 :: nat"}
    val vs = nth (Thm.prems_of st) (i - 1)
             |> Logic.strip_imp_concl
             |> HOLogic.dest_Trueprop
             |> Term.strip_comb |> snd |> List.last
             |> HOLogic.dest_list
    val p = prec
            |> HOLogic.mk_number @{typ nat}
            |> Thm.cterm_of ctxt
  in case taylor
  of NONE => let
       val n = vs |> length
               |> HOLogic.mk_number @{typ nat}
               |> Thm.cterm_of ctxt
       val s = vs
               |> map lookup_splitting
               |> HOLogic.mk_list @{typ nat}
               |> Thm.cterm_of ctxt
     in
       (rtac (Thm.instantiate ([], [(@{cpat "?n::nat"}, n),
                                   (@{cpat "?prec::nat"}, p),
                                   (@{cpat "?ss::nat list"}, s)])
            @{thm "approx_form"}) i
        THEN simp_tac (put_simpset (simpset_of @{context}) ctxt) i) st
     end

   | SOME t =>
     if length vs <> 1
     then raise (TERM ("More than one variable used for taylor series expansion", [Thm.prop_of st]))
     else let
       val t = t
            |> HOLogic.mk_number @{typ nat}
            |> Thm.cterm_of ctxt
       val s = vs |> map lookup_splitting |> hd
            |> Thm.cterm_of ctxt
     in
       rtac (Thm.instantiate ([], [(@{cpat "?s::nat"}, s),
                                   (@{cpat "?t::nat"}, t),
                                   (@{cpat "?prec::nat"}, p)])
            @{thm "approx_tse_form"}) i st
     end
  end

fun calculated_subterms (@{const Trueprop} $ t) = calculated_subterms t
  | calculated_subterms (@{const HOL.implies} $ _ $ t) = calculated_subterms t
  | calculated_subterms (@{term "op <= :: real \<Rightarrow> real \<Rightarrow> bool"} $ t1 $ t2) = [t1, t2]
  | calculated_subterms (@{term "op < :: real \<Rightarrow> real \<Rightarrow> bool"} $ t1 $ t2) = [t1, t2]
  | calculated_subterms (@{term "op : :: real \<Rightarrow> real set \<Rightarrow> bool"} $ t1 $
                         (@{term "atLeastAtMost :: real \<Rightarrow> real \<Rightarrow> real set"} $ t2 $ t3)) = [t1, t2, t3]
  | calculated_subterms t = raise TERM ("calculated_subterms", [t])

fun dest_interpret_form (@{const "interpret_form"} $ b $ xs) = (b, xs)
  | dest_interpret_form t = raise TERM ("dest_interpret_form", [t])

fun dest_interpret (@{const "interpret_floatarith"} $ b $ xs) = (b, xs)
  | dest_interpret t = raise TERM ("dest_interpret", [t])


fun dest_float (@{const "Float"} $ m $ e) =
  (snd (HOLogic.dest_number m), snd (HOLogic.dest_number e))

fun dest_ivl (Const (@{const_name "Some"}, _) $
              (Const (@{const_name Pair}, _) $ u $ l)) = SOME (dest_float u, dest_float l)
  | dest_ivl (Const (@{const_name "None"}, _)) = NONE
  | dest_ivl t = raise TERM ("dest_result", [t])

fun mk_approx' prec t = (@{const "approx'"}
                       $ HOLogic.mk_number @{typ nat} prec
                       $ t $ @{term "[] :: (float * float) option list"})

fun mk_approx_form_eval prec t xs = (@{const "approx_form_eval"}
                       $ HOLogic.mk_number @{typ nat} prec
                       $ t $ xs)

fun float2_float10 prec round_down (m, e) = (
  let
    val (m, e) = (if e < 0 then (m,e) else (m * Integer.pow e 2, 0))

    fun frac c p 0 digits cnt = (digits, cnt, 0)
      | frac c 0 r digits cnt = (digits, cnt, r)
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

    val p = ((if x = 0 then prec else prec - (IntInf.log2 x + 1)) * 3) div 10 + 1

    val (digits, e10, r) = if p > 0 then frac (x <> 0) p r 0 0 else (0,0,0)

    val digits = if round_down orelse r = 0 then digits else digits + 1

  in (sgn * (digits + x * (Integer.pow e10 10)), ~e10)
  end)

fun mk_result prec (SOME (l, u)) =
  (let
    fun mk_float10 rnd x = (let val (m, e) = float2_float10 prec rnd x
                       in if e = 0 then HOLogic.mk_number @{typ real} m
                     else if e = 1 then @{term "divide :: real \<Rightarrow> real \<Rightarrow> real"} $
                                        HOLogic.mk_number @{typ real} m $
                                        @{term "10"}
                                   else @{term "divide :: real \<Rightarrow> real \<Rightarrow> real"} $
                                        HOLogic.mk_number @{typ real} m $
                                        (@{term "power 10 :: nat \<Rightarrow> real"} $
                                         HOLogic.mk_number @{typ nat} (~e)) end)
    in @{term "atLeastAtMost :: real \<Rightarrow> real \<Rightarrow> real set"} $ mk_float10 true l $ mk_float10 false u end)
  | mk_result _ NONE = @{term "UNIV :: real set"}

fun realify t =
  let
    val t = Logic.varify_global t
    val m = map (fn (name, _) => (name, @{typ real})) (Term.add_tvars t [])
    val t = Term.subst_TVars m t
  in t end

fun apply_tactic ctxt term tactic =
  Thm.cterm_of ctxt term
  |> Goal.init
  |> SINGLE tactic
  |> the |> Thm.prems_of |> hd

fun prepare_form ctxt term = apply_tactic ctxt term (
    REPEAT (FIRST' [etac @{thm intervalE}, etac @{thm meta_eqE}, rtac @{thm impI}] 1)
    THEN Subgoal.FOCUS (fn {prems, ...} => reorder_bounds_tac prems 1) ctxt 1
    THEN DETERM (TRY (filter_prems_tac ctxt (K false) 1)))

fun reify_form ctxt term = apply_tactic ctxt term
   (Reification.tac ctxt form_equations NONE 1)

fun approx_form prec ctxt t =
        realify t
     |> prepare_form ctxt
     |> (fn arith_term => reify_form ctxt arith_term
         |> HOLogic.dest_Trueprop |> dest_interpret_form
         |> (fn (data, xs) =>
            mk_approx_form_eval prec data (HOLogic.mk_list @{typ "(float * float) option"}
              (map (fn _ => @{term "None :: (float * float) option"}) (HOLogic.dest_list xs)))
         |> approximate ctxt
         |> HOLogic.dest_list
         |> curry ListPair.zip (HOLogic.dest_list xs @ calculated_subterms arith_term)
         |> map (fn (elem, s) => @{term "op : :: real \<Rightarrow> real set \<Rightarrow> bool"} $ elem $ mk_result prec (dest_ivl s))
         |> foldr1 HOLogic.mk_conj))

fun approx_arith prec ctxt t = realify t
     |> Thm.cterm_of ctxt
     |> Reification.conv ctxt form_equations
     |> Thm.prop_of
     |> Logic.dest_equals |> snd
     |> dest_interpret |> fst
     |> mk_approx' prec
     |> approximate ctxt
     |> dest_ivl
     |> mk_result prec

fun approx prec ctxt t =
  if type_of t = @{typ prop} then approx_form prec ctxt t
  else if type_of t = @{typ bool} then approx_form prec ctxt (@{const Trueprop} $ t)
  else approx_arith prec ctxt t

fun approximate_cmd modes raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val t = Syntax.read_term ctxt raw_t;
    val t' = approx 30 ctxt t;
    val ty' = Term.type_of t';
    val ctxt' = Variable.auto_fixes t' ctxt;
  in
    Print_Mode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ()
  end |> Pretty.writeln;

val opt_modes =
  Scan.optional (@{keyword "("} |-- Parse.!!! (Scan.repeat1 Parse.xname --| @{keyword ")"})) [];

val _ =
  Outer_Syntax.command @{command_spec "approximate"} "print approximation of term"
    (opt_modes -- Parse.term
      >> (fn (modes, t) => Toplevel.keep (approximate_cmd modes t)));

fun approximation_tac prec splitting taylor ctxt i =
  REPEAT (FIRST' [etac @{thm intervalE},
                  etac @{thm meta_eqE},
                  rtac @{thm impI}] i)
  THEN Subgoal.FOCUS (fn {prems, ...} => reorder_bounds_tac prems i) ctxt i
  THEN DETERM (TRY (filter_prems_tac ctxt (K false) i))
  THEN DETERM (Reification.tac ctxt form_equations NONE i)
  THEN rewrite_interpret_form_tac ctxt prec splitting taylor i
  THEN gen_eval_tac (approximation_conv ctxt) ctxt i
    
end;