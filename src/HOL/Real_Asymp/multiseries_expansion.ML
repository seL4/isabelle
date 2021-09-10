signature MULTISERIES_EXPANSION = sig

type expansion_thm = thm
type trimmed_thm = thm
type expr = Exp_Log_Expression.expr
type basis = Asymptotic_Basis.basis

datatype trim_mode = Simple_Trim | Pos_Trim | Neg_Trim | Sgn_Trim

datatype zeroness = IsZero | IsNonZero | IsPos | IsNeg

datatype intyness = Nat of thm | Neg_Nat of thm | No_Nat
datatype parity = Even of thm | Odd of thm | Unknown_Parity

datatype limit =
   Zero_Limit of bool option
 | Finite_Limit of term
 | Infinite_Limit of bool option

datatype trim_result =
    Trimmed of zeroness * trimmed_thm option
  | Aborted of order

val get_intyness : Proof.context -> cterm -> intyness
val get_parity : cterm -> parity

val get_expansion : thm -> term
val get_coeff : term -> term
val get_exponent : term -> term
val get_expanded_fun : thm -> term
val get_eval : term -> term
val expands_to_hd : thm -> thm

val mk_eval_ctxt : Proof.context -> Lazy_Eval.eval_ctxt
val expand : Lazy_Eval.eval_ctxt -> expr -> basis -> expansion_thm * basis
val expand_term : Lazy_Eval.eval_ctxt -> term -> basis -> expansion_thm * basis
val expand_terms : Lazy_Eval.eval_ctxt -> term list -> basis -> expansion_thm list * basis

val limit_of_expansion : bool * bool -> Lazy_Eval.eval_ctxt -> thm * basis -> limit * thm
val compute_limit : Lazy_Eval.eval_ctxt -> term -> limit * thm
val compare_expansions : 
  Lazy_Eval.eval_ctxt -> expansion_thm * expansion_thm * basis -> 
    order * thm * expansion_thm * expansion_thm

(* TODO DEBUG *)
datatype comparison_result =
  Cmp_Dominated of order * thm list * zeroness * trimmed_thm * expansion_thm * expansion_thm 
| Cmp_Asymp_Equiv of thm * thm
val compare_expansions' :
  Lazy_Eval.eval_ctxt ->
      thm * thm * Asymptotic_Basis.basis ->
        comparison_result

val prove_at_infinity : Lazy_Eval.eval_ctxt -> thm * basis -> thm
val prove_at_top : Lazy_Eval.eval_ctxt -> thm * basis -> thm
val prove_at_bot : Lazy_Eval.eval_ctxt -> thm * basis -> thm
val prove_nhds : Lazy_Eval.eval_ctxt -> thm * basis -> thm
val prove_at_0 : Lazy_Eval.eval_ctxt -> thm * basis -> thm
val prove_at_left_0 : Lazy_Eval.eval_ctxt -> thm * basis -> thm
val prove_at_right_0 : Lazy_Eval.eval_ctxt -> thm * basis -> thm

val prove_smallo : Lazy_Eval.eval_ctxt -> thm * thm * basis -> thm
val prove_bigo : Lazy_Eval.eval_ctxt -> thm * thm * basis -> thm
val prove_bigtheta : Lazy_Eval.eval_ctxt -> thm * thm * basis -> thm
val prove_asymp_equiv : Lazy_Eval.eval_ctxt -> thm * thm * basis -> thm

val prove_asymptotic_relation : Lazy_Eval.eval_ctxt -> thm * thm * basis -> order * thm
val prove_eventually_less : Lazy_Eval.eval_ctxt -> thm * thm * basis -> thm
val prove_eventually_greater : Lazy_Eval.eval_ctxt -> thm * thm * basis -> thm
val prove_eventually_nonzero : Lazy_Eval.eval_ctxt -> thm * basis -> thm

val extract_terms : int * bool -> Lazy_Eval.eval_ctxt -> basis -> term -> term * term option

(* Internal functions *)
val check_expansion : Exp_Log_Expression.expr -> expansion_thm -> expansion_thm

val zero_expansion : basis -> expansion_thm
val const_expansion : Lazy_Eval.eval_ctxt -> basis -> term -> expansion_thm
val ln_expansion :
  Lazy_Eval.eval_ctxt -> trimmed_thm -> expansion_thm -> basis -> expansion_thm * basis
val exp_expansion : Lazy_Eval.eval_ctxt -> expansion_thm -> basis -> expansion_thm * basis
val powr_expansion :
  Lazy_Eval.eval_ctxt -> expansion_thm * expansion_thm * basis -> expansion_thm * basis
val powr_const_expansion :
  Lazy_Eval.eval_ctxt -> expansion_thm * term * basis -> expansion_thm
val powr_nat_expansion :
  Lazy_Eval.eval_ctxt -> expansion_thm * expansion_thm * basis -> expansion_thm * basis
val power_expansion : Lazy_Eval.eval_ctxt -> expansion_thm * term * basis -> expansion_thm
val root_expansion : Lazy_Eval.eval_ctxt -> expansion_thm * term * basis -> expansion_thm

val sgn_expansion : Lazy_Eval.eval_ctxt -> expansion_thm * basis -> expansion_thm
val min_expansion : Lazy_Eval.eval_ctxt -> expansion_thm * expansion_thm * basis -> expansion_thm
val max_expansion : Lazy_Eval.eval_ctxt -> expansion_thm * expansion_thm * basis -> expansion_thm
val arctan_expansion : Lazy_Eval.eval_ctxt -> basis -> expansion_thm -> expansion_thm

val ev_zeroness_oracle : Lazy_Eval.eval_ctxt -> term -> thm option
val zeroness_oracle : bool -> trim_mode option -> Lazy_Eval.eval_ctxt -> term -> zeroness * thm option

val whnf_expansion : Lazy_Eval.eval_ctxt -> expansion_thm -> term option * expansion_thm * thm
val simplify_expansion : Lazy_Eval.eval_ctxt -> expansion_thm -> expansion_thm 
val simplify_term : Lazy_Eval.eval_ctxt -> term -> term

val trim_expansion_while_greater :
  bool -> term list option -> bool -> trim_mode option -> Lazy_Eval.eval_ctxt ->
    thm * Asymptotic_Basis.basis -> thm * trim_result * (zeroness * thm) list
val trim_expansion : bool -> trim_mode option -> Lazy_Eval.eval_ctxt -> expansion_thm * basis -> 
  expansion_thm * zeroness * trimmed_thm option
val try_drop_leading_term_ex : bool -> Lazy_Eval.eval_ctxt -> expansion_thm -> expansion_thm option

val try_prove_real_eq : bool -> Lazy_Eval.eval_ctxt -> term * term -> thm option
val try_prove_ev_eq : Lazy_Eval.eval_ctxt -> term * term -> thm option
val prove_compare_expansions : order -> thm list -> thm

val simplify_trimmed_expansion : Lazy_Eval.eval_ctxt -> expansion_thm * trimmed_thm -> 
  expansion_thm * trimmed_thm
val retrim_expansion : Lazy_Eval.eval_ctxt -> expansion_thm * basis -> expansion_thm * thm
val retrim_pos_expansion : Lazy_Eval.eval_ctxt -> expansion_thm * basis * trimmed_thm ->
  expansion_thm * thm * trimmed_thm

val register_sign_oracle : 
  binding * (Proof.context -> int -> tactic) -> Context.generic -> Context.generic
val get_sign_oracles :
  Context.generic -> (string * (Proof.context -> int -> tactic)) list

val solve_eval_eq : thm -> thm

end

structure Multiseries_Expansion : MULTISERIES_EXPANSION = struct

open Asymptotic_Basis
open Exp_Log_Expression
open Lazy_Eval

structure Data = Generic_Data
(
  type T = (Proof.context -> int -> tactic) Name_Space.table;
  val empty : T = Name_Space.empty_table "sign_oracle_tactic";
  val extend = I;
  fun merge (tactics1, tactics2) : T = Name_Space.merge_tables (tactics1, tactics2);
);

fun register_sign_oracle (s, tac) ctxt =
  Data.map (Name_Space.define ctxt false (s, tac) #> snd) ctxt

fun get_sign_oracles ctxt = Name_Space.fold_table cons (Data.get ctxt) []

fun apply_sign_oracles ctxt tac =
  let
    val oracles = get_sign_oracles (Context.Proof ctxt)
    fun tac' {context = ctxt, concl, ...} =
      if Thm.term_of concl = \<^term>\<open>HOL.Trueprop HOL.False\<close> then
        no_tac
      else
        FIRST (map (fn tac => HEADGOAL (snd tac ctxt)) oracles)
  in
    tac THEN_ALL_NEW (Subgoal.FOCUS_PREMS tac' ctxt)
  end
    

type expansion_thm = thm
type trimmed_thm = thm

val dest_fun = dest_comb #> fst
val dest_arg = dest_comb #> snd
val concl_of' = Thm.concl_of #> HOLogic.dest_Trueprop

fun get_expansion thm =
  thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> Term.dest_comb |> fst |> Term.dest_comb |> snd

fun get_expanded_fun thm = thm |> concl_of' |> dest_fun |> dest_fun |> dest_arg

(*
  The following function is useful in order to detect whether a given real constant is
  an integer, which allows us to use the "f(x) ^ n" operation instead of "f(x) powr n".
  This usually leads to nicer results.
*)
datatype intyness = Nat of thm | Neg_Nat of thm | No_Nat

fun get_intyness ctxt ct =
  if Thm.typ_of_cterm ct = \<^typ>\<open>Real.real\<close> then
    let
      val ctxt' = put_simpset HOL_basic_ss ctxt addsimps @{thms intyness_simps}
      val conv = 
        Simplifier.rewrite ctxt then_conv Simplifier.rewrite ctxt'
      fun flip (Nat thm) = Neg_Nat (thm RS @{thm intyness_uminus})
        | flip _ = No_Nat
      fun get_intyness' ct =
        case Thm.term_of ct of
          \<^term>\<open>0::real\<close> => Nat @{thm intyness_0}
        | \<^term>\<open>1::real\<close> => Nat @{thm intyness_1}
        | Const (\<^const_name>\<open>numeral\<close>, _) $ _ => 
            Nat (Thm.reflexive (Thm.dest_arg ct) RS @{thm intyness_numeral})
        | Const (\<^const_name>\<open>uminus\<close>, _) $ _ => flip (get_intyness' (Thm.dest_arg ct))
        | Const (\<^const_name>\<open>of_nat\<close>, _) $ _ => 
            Nat (Thm.reflexive (Thm.dest_arg ct) RS @{thm intyness_of_nat})
        | _ => No_Nat
      val thm = conv ct
      val ct' = thm |> Thm.cprop_of |> Thm.dest_equals_rhs
    in
      case get_intyness' ct' of
        Nat thm' => Nat (Thm.transitive thm thm' RS @{thm HOL.meta_eq_to_obj_eq})
      | Neg_Nat thm' => Neg_Nat (Thm.transitive thm thm' RS @{thm HOL.meta_eq_to_obj_eq})
      | No_Nat => No_Nat
    end
      handle CTERM _ => No_Nat
  else
    No_Nat

datatype parity = Even of thm | Odd of thm | Unknown_Parity

(* TODO: powers *)
fun get_parity ct =
  let
    fun inst thm cts =
      let
        val tvs = Term.add_tvars (Thm.concl_of thm) []
      in
        case tvs of
          [v] =>
            let
              val thm' = Thm.instantiate (TVars.make [(v, Thm.ctyp_of_cterm ct)], Vars.empty) thm
              val vs = take (length cts) (rev (Term.add_vars (Thm.concl_of thm') []))
            in
              Thm.instantiate (TVars.empty, Vars.make (vs ~~ cts)) thm'
            end
        | _ => raise THM ("get_parity", 0, [thm])
      end
    val get_num = Thm.dest_arg o Thm.dest_arg
  in
    case Thm.term_of ct of
      Const (\<^const_name>\<open>Groups.zero\<close>, _) => Even (inst @{thm even_zero} [])
    | Const (\<^const_name>\<open>Groups.one\<close>, _) => Odd (inst @{thm odd_one} [])
    | Const (\<^const_name>\<open>Num.numeral_class.numeral\<close>, _) $ \<^term>\<open>Num.One\<close> =>
        Odd (inst @{thm odd_Numeral1} [])
    | Const (\<^const_name>\<open>Num.numeral_class.numeral\<close>, _) $ (\<^term>\<open>Num.Bit0\<close> $ _) =>
        Even (inst @{thm even_numeral} [get_num ct])
    | Const (\<^const_name>\<open>Num.numeral_class.numeral\<close>, _) $ (\<^term>\<open>Num.Bit1\<close> $ _) =>
        Odd (inst @{thm odd_numeral} [get_num ct])
    | Const (\<^const_name>\<open>Groups.uminus\<close>, _) $ _ => (
        case get_parity (Thm.dest_arg ct) of
          Even thm => Even (@{thm even_uminusI} OF [thm])
        | Odd thm => Odd (@{thm odd_uminusI} OF [thm])
        | _ => Unknown_Parity)
    | Const (\<^const_name>\<open>Groups.plus\<close>, _) $ _ $ _ => (
        case apply2 get_parity (Thm.dest_binop ct) of
          (Even thm1, Even thm2) => Even (@{thm even_addI(1)} OF [thm1, thm2])
        | (Odd thm1, Odd thm2) => Even (@{thm even_addI(2)} OF [thm1, thm2])
        | (Even thm1, Odd thm2) => Odd (@{thm odd_addI(1)} OF [thm1, thm2])
        | (Odd thm1, Even thm2) => Odd (@{thm odd_addI(2)} OF [thm1, thm2])
        | _ => Unknown_Parity)
    | Const (\<^const_name>\<open>Groups.minus\<close>, _) $ _ $ _ => (
        case apply2 get_parity (Thm.dest_binop ct) of
          (Even thm1, Even thm2) => Even (@{thm even_diffI(1)} OF [thm1, thm2])
        | (Odd thm1, Odd thm2) => Even (@{thm even_diffI(2)} OF [thm1, thm2])
        | (Even thm1, Odd thm2) => Odd (@{thm odd_diffI(1)} OF [thm1, thm2])
        | (Odd thm1, Even thm2) => Odd (@{thm odd_diffI(2)} OF [thm1, thm2])
        | _ => Unknown_Parity)
    | Const (\<^const_name>\<open>Groups.times\<close>, _) $ _ $ _ => (
        case apply2 get_parity (Thm.dest_binop ct) of
          (Even thm1, _) => Even (@{thm even_multI(1)} OF [thm1])
        | (_, Even thm2) => Even (@{thm even_multI(2)} OF [thm2])
        | (Odd thm1, Odd thm2) => Odd (@{thm odd_multI} OF [thm1, thm2])
        | _ => Unknown_Parity)
    | Const (\<^const_name>\<open>Power.power\<close>, _) $ _ $ _ =>
        let
          val (a, n) = Thm.dest_binop ct
        in
          case get_parity a of
            Odd thm => Odd (inst @{thm odd_powerI} [a, n] OF [thm])
          | _ => Unknown_Parity
        end
    | _ => Unknown_Parity
  end

fun simplify_term' facts ctxt =
  let
    val ctxt = Simplifier.add_prems facts ctxt
  in
    Thm.cterm_of ctxt #> Simplifier.rewrite ctxt #> 
    Thm.concl_of #> Logic.dest_equals #> snd
  end

fun simplify_term ectxt = simplify_term' (get_facts ectxt) (get_ctxt ectxt)

fun simplify_eval ctxt =
  simplify_term' [] (put_simpset HOL_basic_ss ctxt addsimps @{thms eval_simps})

datatype zeroness = IsZero | IsNonZero | IsPos | IsNeg


(* Caution: The following functions assume that the given expansion is in normal form already
   as far as needed. *)

(* Returns the leading coefficient of the given expansion. This coefficient is a multiseries. *)
fun try_get_coeff expr =
  case expr of
    Const (\<^const_name>\<open>MS\<close>, _) $ (
      Const (\<^const_name>\<open>MSLCons\<close>, _) $ (
        Const (\<^const_name>\<open>Pair\<close>, _) $ c $ _) $ _) $ _ =>
      SOME c
  | _ => NONE

fun get_coeff expr = 
  expr |> dest_comb |> fst |> dest_comb |> snd |> dest_comb |> fst |> dest_comb |> snd
    |> dest_comb |> fst |> dest_comb |> snd

(* Returns the coefficient of the leading term in the expansion (i.e. a real number) *)
fun get_lead_coeff expr =
  case try_get_coeff expr of
    NONE => expr
  | SOME c => get_lead_coeff c

(* Returns the exponent (w.r.t. the fastest-growing basis element) of the leading term *)
fun get_exponent expr = 
  expr |> dest_comb |> fst |> dest_comb |> snd |> dest_comb |> fst |> dest_comb |> snd
    |> dest_comb |> snd

(* Returns the list of exponents of the leading term *)
fun get_exponents exp =
  if fastype_of exp = \<^typ>\<open>real\<close> then
    []
  else
    get_exponent exp :: get_exponents (get_coeff exp)

(* Returns the function that the expansion corresponds to *)
fun get_eval expr =
  if fastype_of expr = \<^typ>\<open>real\<close> then
    Abs ("x", \<^typ>\<open>real\<close>, expr)
  else
    expr |> dest_comb |> snd

val eval_simps = @{thms eval_simps [THEN eq_reflection]}

(* Tries to prove that the given function is eventually zero *)
fun ev_zeroness_oracle ectxt t = 
  let
    val ctxt = Lazy_Eval.get_ctxt ectxt
    val goal = 
      betapply (\<^term>\<open>\<lambda>f::real \<Rightarrow> real. eventually (\<lambda>x. f x = 0) at_top\<close>, t)
      |> HOLogic.mk_Trueprop
    fun tac {context = ctxt, ...} =
      HEADGOAL (Method.insert_tac ctxt (get_facts ectxt))
      THEN Local_Defs.unfold_tac ctxt eval_simps
      THEN HEADGOAL (Simplifier.asm_full_simp_tac ctxt)
  in
    try (Goal.prove ctxt [] [] goal) tac
  end

(* 
  Encodes the kind of trimming/zeroness checking operation to be performed.
  Simple_Trim only checks for zeroness/non-zeroness. Pos_Trim/Neg_Trim try to prove either
  zeroness or positivity (resp. negativity). Sgn_Trim tries all three possibilities (positive,
  negative, zero). *)
datatype trim_mode = Simple_Trim | Pos_Trim | Neg_Trim | Sgn_Trim

(*
  Checks (and proves) whether the given term (assumed to be a real number) is zero, positive,
  or negative, depending on given flags. The "fail" flag determines whether an exception is
  thrown if this fails.
*)
fun zeroness_oracle fail mode ectxt exp = 
  let
    val ctxt = Lazy_Eval.get_ctxt ectxt
    val eq = (exp, \<^term>\<open>0::real\<close>) |> HOLogic.mk_eq
    val goal1 = (IsZero, eq |> HOLogic.mk_Trueprop)
    val goal2 = 
      case mode of
        SOME Pos_Trim => 
          (IsPos, \<^term>\<open>(<) (0::real)\<close> $ exp |> HOLogic.mk_Trueprop)
      | SOME Sgn_Trim => 
          (IsPos, \<^term>\<open>(<) (0::real)\<close> $ exp |> HOLogic.mk_Trueprop)
      | SOME Neg_Trim => 
          (IsNeg, betapply (\<^term>\<open>\<lambda>x. x < (0::real)\<close>, exp) |> HOLogic.mk_Trueprop)
      | _ =>
          (IsNonZero, eq |> HOLogic.mk_not |> HOLogic.mk_Trueprop)
    val goals =
      (if mode = SOME Sgn_Trim then 
         [(IsNeg, betapply (\<^term>\<open>\<lambda>x. x < (0::real)\<close>, exp) |> HOLogic.mk_Trueprop)] 
       else 
         [])
    val goals = goal2 :: goals
    fun tac {context = ctxt, ...} =
      HEADGOAL (Method.insert_tac ctxt (get_facts ectxt))
      THEN Local_Defs.unfold_tac ctxt eval_simps
      THEN HEADGOAL (apply_sign_oracles ctxt (Simplifier.asm_full_simp_tac ctxt))
    fun prove (res, goal) = try (fn goal => (res, SOME (Goal.prove ctxt [] [] goal tac))) goal
    fun err () =
      let
        val mode_msg =
          case mode of
            SOME Simple_Trim => "whether the following constant is zero"
          | SOME Pos_Trim => "whether the following constant is zero or positive"
          | SOME Neg_Trim => "whether the following constant is zero or negative"
          | SOME Sgn_Trim => "the sign of the following constant"
          | _ => raise Match
        val t = simplify_term' (get_facts ectxt) ctxt exp
        val _ =
          if #verbose (#ctxt ectxt) then
            let
              val p = Pretty.str ("real_asymp failed to determine " ^ mode_msg ^ ":")
              val p = Pretty.chunks [p, Pretty.indent 2 (Syntax.pretty_term ctxt t)]
            in
              Pretty.writeln p
            end else ()
      in
        raise TERM ("zeroness_oracle", [t])
      end
  in
    case prove goal1 of
      SOME res => res
    | NONE => 
        if mode = NONE then 
          (IsNonZero, NONE)
        else
          case get_first prove (goal2 :: goals) of
            NONE => if fail then err () else (IsNonZero, NONE)
          | SOME res => res
  end

(* Tries to prove a given equality of real numbers. *)
fun try_prove_real_eq fail ectxt (lhs, rhs) =
  case zeroness_oracle false NONE ectxt (\<^term>\<open>(-) :: real => _\<close> $ lhs $ rhs) of
    (IsZero, SOME thm) => SOME (thm RS @{thm real_eqI})
  | _ => 
    if not fail then NONE else
      let
        val ctxt = get_ctxt ectxt
        val ts = map (simplify_term' (get_facts ectxt) ctxt) [lhs, rhs]
        val _ =
          if #verbose (#ctxt ectxt) then
            let
              val p = 
                Pretty.str ("real_asymp failed to prove that the following two numbers are equal:")
              val p = Pretty.chunks (p :: map (Pretty.indent 2 o Syntax.pretty_term ctxt) ts)
            in
              Pretty.writeln p
            end else ()
      in
        raise TERM ("try_prove_real_eq", [lhs, rhs])
      end

(* Tries to prove a given eventual equality of real functions. *)
fun try_prove_ev_eq ectxt (f, g) =
  let
    val t = Envir.beta_eta_contract (\<^term>\<open>\<lambda>(f::real=>real) g x. f x - g x\<close> $ f $ g)
  in
    Option.map (fn thm => thm RS @{thm eventually_diff_zero_imp_eq}) (ev_zeroness_oracle ectxt t)
  end

fun real_less a b = \<^term>\<open>(<) :: real \<Rightarrow> real \<Rightarrow> bool\<close> $ a $ b
fun real_eq a b = \<^term>\<open>(=) :: real \<Rightarrow> real \<Rightarrow> bool\<close> $ a $ b
fun real_neq a b = \<^term>\<open>(\<noteq>) :: real \<Rightarrow> real \<Rightarrow> bool\<close> $ a $ b

(* The hook that is called by the Lazy_Eval module whenever two real numbers have to be compared *)
fun real_sgn_hook ({pctxt = ctxt, facts, verbose, ...}) t =
  let
    val get_rhs = Thm.concl_of #> Logic.dest_equals #> snd
    fun tac {context = ctxt, ...} = 
      HEADGOAL (Method.insert_tac ctxt (Net.content facts) 
        THEN' (apply_sign_oracles ctxt (Simplifier.asm_full_simp_tac ctxt)))
    fun prove_first err [] [] =
          if not verbose then raise TERM ("real_sgn_hook", [t])
            else let val _ = err () in raise TERM ("real_sgn_hook", [t]) end
      | prove_first err (goal :: goals) (thm :: thms) =
          (case try (Goal.prove ctxt [] [] goal) tac of
             SOME thm' => 
               let val thm'' = thm' RS thm in SOME (get_rhs thm'', Conv.rewr_conv thm'') end
           | NONE => prove_first err goals thms)
      | prove_first _ _ _ = raise Match
  in
    case t of
      \<^term>\<open>(=) :: real => _\<close> $ a $ \<^term>\<open>0 :: real\<close> =>
        let
          val goals =
            map (fn c => HOLogic.mk_Trueprop (c a \<^term>\<open>0 :: real\<close>)) [real_neq, real_eq]
          fun err () = 
            let
              val facts' = Net.content facts
              val a' = simplify_term' facts' ctxt a
              val p = Pretty.str ("real_asymp failed to determine whether the following " ^
                                    "constant is zero: ")
              val p = Pretty.chunks [p, Pretty.indent 2 (Syntax.pretty_term ctxt a')]
            in
              Pretty.writeln p
            end
        in
          prove_first err goals @{thms Eq_FalseI Eq_TrueI}
        end
    | Const (\<^const_name>\<open>COMPARE\<close>, _) $ a $ b =>
        let
          val goals = map HOLogic.mk_Trueprop [real_less a b, real_less b a, real_eq a b]
          fun err () = 
            let
              val facts' = Net.content facts
              val (a', b') = apply2 (simplify_term' facts' ctxt) (a, b)
              val p = Pretty.str ("real_asymp failed to compare" ^
                        "the following two constants: ")
              val p = Pretty.chunks (p :: map (Pretty.indent 2 o Syntax.pretty_term ctxt) [a', b'])
            in
              Pretty.writeln p
            end
        in
          prove_first err goals @{thms COMPARE_intros}
        end
    | _ => NONE
  end

(* 
  Returns the datatype constructors registered for use with the Lazy_Eval package.
  All constructors on which pattern matching is performed need to be registered for evaluation
  to work. It should be rare for users to add additional ones.
*)
fun get_constructors ctxt =
  let
    val thms = Named_Theorems.get ctxt \<^named_theorems>\<open>exp_log_eval_constructor\<close>
    fun go _ [] acc = rev acc
      | go f (x :: xs) acc =
          case f x of
            NONE => go f xs acc
          | SOME y => go f xs (y :: acc)
    fun map_option f xs = go f xs []
    fun dest_constructor thm =
      case Thm.concl_of thm of
        Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $
            (Const (\<^const_name>\<open>REAL_ASYMP_EVAL_CONSTRUCTOR\<close>, _) $ Const (c, T)) =>
          SOME (c, length (fst (strip_type T)))
     | _ => NONE
  in
    thms |> map_option dest_constructor
  end

(*
  Creates an evaluation context with the correct setup of constructors,  equations, and hooks.
*)
fun mk_eval_ctxt ctxt =
  let
    val eval_eqs = (Named_Theorems.get ctxt \<^named_theorems>\<open>real_asymp_eval_eqs\<close>)
    val constructors = get_constructors ctxt
  in
    Lazy_Eval.mk_eval_ctxt ctxt constructors eval_eqs
    |> add_hook real_sgn_hook
  end

(* A pattern for determining the leading coefficient of a multiseries *)
val exp_pat = 
  let
    val anypat = AnyPat ("_", 0)
  in
    ConsPat (\<^const_name>\<open>MS\<close>, 
      [ConsPat (\<^const_name>\<open>MSLCons\<close>, 
         [ConsPat (\<^const_name>\<open>Pair\<close>, [anypat, anypat]), anypat]), anypat])
  end

(*
  Evaluates an expansion to (weak) head normal form, so that the leading coefficient and
  exponent can be read off.
*)
fun whnf_expansion ectxt thm =
  let
    val ctxt = get_ctxt ectxt
    val exp = get_expansion thm
    val (_, _, conv) = match ectxt exp_pat exp (SOME [])
    val eq_thm = conv (Thm.cterm_of ctxt exp)
    val exp' = eq_thm |> Thm.concl_of |> Logic.dest_equals |> snd
  in
    case exp' of
      Const (\<^const_name>\<open>MS\<close>, _) $ (Const (\<^const_name>\<open>MSLCons\<close>, _) $ 
        (Const (\<^const_name>\<open>Pair\<close>, _) $ c $ _) $ _) $ _ =>
          (SOME c, @{thm expands_to_meta_eq_cong} OF [thm, eq_thm], eq_thm)
    | Const (\<^const_name>\<open>MS\<close>, _) $ Const (\<^const_name>\<open>MSLNil\<close>, _) $ _ =>
        (NONE, @{thm expands_to_meta_eq_cong} OF [thm, eq_thm], eq_thm)
    | _ => raise TERM ("whnf_expansion", [exp'])
  end

fun try_lift_function ectxt (thm, SEmpty) _ = (NONE, thm)
  | try_lift_function ectxt (thm, basis) cont =
  case whnf_expansion ectxt thm of
    (SOME c, thm, _) =>
      let
        val f = get_expanded_fun thm
        val T = fastype_of c
        val t = Const (\<^const_name>\<open>eval\<close>, T --> \<^typ>\<open>real \<Rightarrow> real\<close>) $ c
        val t = Term.betapply (Term.betapply (\<^term>\<open>\<lambda>(f::real\<Rightarrow>real) g x. f x - g x\<close>, f), t)
      in
        case ev_zeroness_oracle ectxt t of
          NONE => (NONE, thm)
        | SOME zero_thm =>
            let
              val thm' = cont ectxt (thm RS @{thm expands_to_hd''}, tl_basis basis)
              val thm'' = @{thm expands_to_lift_function} OF [zero_thm, thm']
            in
              (SOME (lift basis thm''), thm)
            end
      end
  | _ => (NONE, thm)

(* Turns an expansion theorem into an expansion theorem for the leading coefficient. *)
fun expands_to_hd thm = thm RS
  (if fastype_of (get_expansion thm) = \<^typ>\<open>real ms\<close> then 
     @{thm expands_to_hd'}
   else 
     @{thm expands_to_hd})

fun simplify_expansion ectxt thm =
  let
    val exp = get_expansion thm
    val ctxt = get_ctxt ectxt
    val eq_thm = Simplifier.rewrite ctxt (Thm.cterm_of ctxt exp)
  in
    @{thm expands_to_meta_eq_cong} OF [thm, eq_thm]
  end

(*
  Simplifies a trimmed expansion and returns the simplified expansion theorem and
  the trimming theorem for that simplified expansion.
*)
fun simplify_trimmed_expansion ectxt (thm, trimmed_thm) =
  let
    val exp = get_expansion thm
    val ctxt = get_ctxt ectxt
    val eq_thm = Simplifier.rewrite ctxt (Thm.cterm_of ctxt exp)
    val trimmed_cong_thm =
      case trimmed_thm |> concl_of' |> dest_fun of
        Const (\<^const_name>\<open>trimmed\<close>, _) => @{thm trimmed_eq_cong}
      | Const (\<^const_name>\<open>trimmed_pos\<close>, _) => @{thm trimmed_pos_eq_cong}
      | Const (\<^const_name>\<open>trimmed_neg\<close>, _) => @{thm trimmed_neg_eq_cong}
      | _ => raise THM ("simplify_trimmed_expansion", 2, [thm, trimmed_thm])
  in
    (@{thm expands_to_meta_eq_cong} OF [thm, eq_thm], 
      trimmed_cong_thm OF [trimmed_thm, eq_thm])     
  end

(*
  Re-normalises a trimmed expansion (so that the leading term with its (real) coefficient and
  all exponents can be read off. This may be necessary after lifting a trimmed expansion to
  a larger basis.
*)
fun retrim_expansion ectxt (thm, basis) =
  let
    val (c, thm, eq_thm) = whnf_expansion ectxt thm
  in
    case c of
      NONE => (thm, eq_thm)
    | SOME c =>
      if fastype_of c = \<^typ>\<open>real\<close> then 
        (thm, eq_thm) 
      else
        let
          val c_thm = thm RS @{thm expands_to_hd''}
          val (c_thm', eq_thm') = retrim_expansion ectxt (c_thm, tl_basis basis)
          val thm = @{thm expands_to_trim_cong} OF [thm, c_thm']
        in
          (thm, @{thm trim_lift_eq} OF [eq_thm, eq_thm'])
        end
  end

fun retrim_pos_expansion ectxt (thm, basis, trimmed_thm) =
  let
    val (thm', eq_thm) = retrim_expansion ectxt (thm, basis)
  in
    (thm', eq_thm, @{thm trimmed_pos_eq_cong} OF [trimmed_thm, eq_thm])
  end

(*
  Tries to determine whether the leading term is (identically) zero and drops it if it is.
  If "fail" is set, an exception is thrown when that term is a real number and zeroness cannot
  be determined. (Which typically indicates missing facts or case distinctions)
*)
fun try_drop_leading_term_ex fail ectxt thm =
  let
    val exp = get_expansion thm
  in
    if fastype_of exp = \<^typ>\<open>real\<close> then
      NONE
    else if fastype_of (get_coeff exp) = \<^typ>\<open>real\<close> then
      case zeroness_oracle fail (SOME Simple_Trim) ectxt (get_coeff exp) of
        (IsZero, SOME zero_thm) => SOME (@{thm drop_zero_ms'} OF [zero_thm, thm])
      | _ => NONE
    else
      let
        val c = get_coeff exp
        val T = fastype_of c
        val t = Const (\<^const_name>\<open>eval\<close>, T --> \<^typ>\<open>real \<Rightarrow> real\<close>) $ c
      in
        case ev_zeroness_oracle ectxt t of
          SOME zero_thm => SOME (@{thm expands_to_drop_zero} OF [zero_thm, thm])
        | _ => NONE
      end
  end

(*
  Tries to drop the leading term of an expansion. If this is not possible, an exception 
  is thrown and an informative error message is printed.
*)
fun try_drop_leading_term ectxt thm =
  let
    fun err () =
      let
        val ctxt = get_ctxt ectxt
        val exp = get_expansion thm
        val c = get_coeff exp
        val t = 
          if fastype_of c = \<^typ>\<open>real\<close> then c else c |> dest_arg
        val t = simplify_term' (get_facts ectxt) ctxt t
        val _ =
          if #verbose (#ctxt ectxt) then
            let
              val p = Pretty.str ("real_asymp failed to prove that the following term is zero: ")
              val p = Pretty.chunks [p, Pretty.indent 2 (Syntax.pretty_term ctxt t)]
            in
              Pretty.writeln p
            end else ()
      in
        raise TERM ("try_drop_leading_term", [t])
      end
  in
    case try_drop_leading_term_ex true ectxt thm of
      NONE => err ()
    | SOME thm => thm
  end


datatype trim_result =
    Trimmed of zeroness * trimmed_thm option
  | Aborted of order

fun cstrip_assms ct =
  case Thm.term_of ct of
    \<^term>\<open>(==>)\<close> $ _ $ _ => cstrip_assms (snd (Thm.dest_implies ct))
  | _ => ct

(*
  Trims an expansion (i.e. drops leading zero terms) and provides a trimmedness theorem.
  Optionally, a list of exponents can be given to instruct the function to only trim until
  the exponents of the leading term are lexicographically less than (or less than or equal) than
  the given ones. This is useful to avoid unnecessary trimming.

  The "strict" flag indicates whether the trimming should already be aborted when the 
  exponents are lexicographically equal or not.

  The "fail" flag is passed on to the zeroness oracle and determines whether a failure to determine
  the sign of a real number leads to an exception.

  "mode" indicates what kind of trimmedness theorem will be returned: Simple_Trim only gives the
  default trimmedness theorem, whereas Pos_Trim/Neg_Trim/Sgn_Trim will give trimmed_pos or
  trimmed_neg. Giving "None" as mode will produce no trimmedness theorem; it will only drop 
  leading zero terms until zeroness cannot be proven anymore, upon which it will stop.

  The main result of the function is the trimmed expansion theorem.

  The function returns whether the trimming has been aborted or not. If was aborted, either
  LESS or EQUAL will be returned, indicating whether the exponents of the leading term are
  now lexicographically smaller or equal to the given ones. In the other case, the zeroness
  of the leading coefficient is returned (zero, non-zero, positive, negative) together with a
  trimmedness theorem.

  Lastly, a list of the exponent comparison results and associated theorems is also returned, so
  that the caller can reconstruct the result of the lexicographic ordering without doing the
  exponent comparisons again.
*)
fun trim_expansion_while_greater strict es fail mode ectxt (thm, basis) = 
  let
    val (_, thm, _) = whnf_expansion ectxt thm
    val thm = simplify_expansion ectxt thm
    val cexp = thm |> Thm.cprop_of |> cstrip_assms |> Thm.dest_arg |> Thm.dest_fun |> Thm.dest_arg
    val c = try_get_coeff (get_expansion thm)
    fun lift_trimmed_thm nz thm =
      let
        val cexp = thm |> Thm.cprop_of |> cstrip_assms |> Thm.dest_arg |> Thm.dest_fun |> Thm.dest_arg
        val lift_thm =
          case nz of
            IsNonZero => @{thm trimmed_eq_cong[rotated, OF _ lift_trimmed]}
          | IsPos => @{thm trimmed_pos_eq_cong[rotated, OF _ lift_trimmed_pos]}
          | IsNeg => @{thm trimmed_neg_eq_cong[rotated, OF _ lift_trimmed_neg]}
          | _ => raise TERM ("Unexpected zeroness result in trim_expansion", [])
      in 
        Thm.reflexive cexp RS lift_thm
      end        
    fun trimmed_real_thm nz = Thm.reflexive cexp RS (
      case nz of
        IsNonZero => @{thm trimmed_eq_cong[rotated, OF _ lift_trimmed[OF trimmed_realI]]}
      | IsPos => @{thm trimmed_pos_eq_cong[rotated, OF _ lift_trimmed_pos[OF trimmed_pos_realI]]}
      | IsNeg => @{thm trimmed_neg_eq_cong[rotated, OF _ lift_trimmed_neg[OF trimmed_neg_realI]]}
      | _ => raise TERM ("Unexpected zeroness result in trim_expansion", []))
    fun do_trim es =
      let
        val c = the c
        val T = fastype_of c
        val t = Const (\<^const_name>\<open>eval\<close>, T --> \<^typ>\<open>real \<Rightarrow> real\<close>) $ c
      in
        if T = \<^typ>\<open>real\<close> then (
          case zeroness_oracle fail mode ectxt c of
            (IsZero, SOME zero_thm) => 
              trim_expansion_while_greater strict es fail mode ectxt
                (@{thm drop_zero_ms'} OF [zero_thm, thm], basis)
          | (nz, SOME nz_thm) => (thm, Trimmed (nz, SOME (nz_thm RS trimmed_real_thm nz)), [])
          | (nz, NONE) => (thm, Trimmed (nz, NONE), []))
        else
          case trim_expansion_while_greater strict (Option.map tl es) fail mode ectxt
                 (thm RS @{thm expands_to_hd''}, tl_basis basis) of
            (c_thm', Aborted ord, thms) =>
              (@{thm expands_to_trim_cong} OF [thm, c_thm'], Aborted ord, thms)
          | (c_thm', Trimmed (nz, trimmed_thm), thms) =>
              let
                val thm = (@{thm expands_to_trim_cong} OF [thm, c_thm'])
                fun err () =
                  raise TERM ("trim_expansion: zero coefficient should have been trimmed", [c])
              in
                case (nz, trimmed_thm) of
                  (IsZero, _) => 
                    if #verbose (#ctxt ectxt) then
                      let
                        val ctxt = get_ctxt ectxt
                        val t' = t |> simplify_eval ctxt |> simplify_term' (get_facts ectxt) ctxt
                        val p = Pretty.str ("trim_expansion failed to recognise zeroness of " ^
                          "the following term:")
                        val p = Pretty.chunks [p, Pretty.indent 2 (Syntax.pretty_term ctxt t')]
                        val _ = Pretty.writeln p
                      in
                        err ()
                      end
                    else err ()
                | (_, SOME trimmed_thm) =>
                      (thm, Trimmed (nz, SOME (trimmed_thm RS lift_trimmed_thm nz thm)), thms)
                | (_, NONE) => (thm, Trimmed (nz, NONE), thms)
              end
      end
    val minus = \<^term>\<open>(-) :: real => real => real\<close>
  in
    case (c, es) of
      (NONE, _) => (thm, Trimmed (IsZero, NONE), [])
    | (SOME c, SOME (e' :: _)) =>
        let
          val e = get_exponent (get_expansion thm)
        in
          case zeroness_oracle true (SOME Sgn_Trim) ectxt (minus $ e $ e') of
            (IsPos, SOME pos_thm) => (
              case try_drop_leading_term_ex false ectxt thm of
                SOME thm =>
                  trim_expansion_while_greater strict es fail mode ectxt (thm, basis)
              | NONE => do_trim NONE |> @{apply 3(3)} (fn thms => (IsPos, pos_thm) :: thms))
          | (IsNeg, SOME neg_thm) => (thm, Aborted LESS, [(IsNeg, neg_thm)])
          | (IsZero, SOME zero_thm) =>
              if not strict andalso fastype_of c = \<^typ>\<open>real\<close> then
                (thm, Aborted EQUAL, [(IsZero, zero_thm)])
              else (
                case try_drop_leading_term_ex false ectxt thm of
                  SOME thm => trim_expansion_while_greater strict es fail mode ectxt (thm, basis)
                | NONE => (do_trim es |> @{apply 3(3)} (fn thms => (IsZero, zero_thm) :: thms)))
          | _ => do_trim NONE
        end
    | _ => (
      case try_drop_leading_term_ex false ectxt thm of
          SOME thm => trim_expansion_while_greater strict es fail mode ectxt (thm, basis)
        | NONE => do_trim NONE)
  end

(*
  Trims an expansion without any stopping criterion.
*)
fun trim_expansion fail mode ectxt (thm, basis) = 
  case trim_expansion_while_greater false NONE fail mode ectxt (thm, basis) of
    (thm, Trimmed (zeroness, trimmed_thm), _) => (thm, zeroness, trimmed_thm)
  | _ => raise Match

(*
  Determines the sign of an expansion that has already been trimmed.
*)
fun determine_trimmed_sgn ectxt exp =
  if fastype_of exp = \<^typ>\<open>real\<close> then
    (case zeroness_oracle true (SOME Sgn_Trim) ectxt exp of
       (IsPos, SOME thm) => (IsPos, thm RS @{thm trimmed_pos_realI})
     | (IsNeg, SOME thm) => (IsNeg, thm RS @{thm trimmed_neg_realI})
     | _ => raise TERM ("determine_trimmed_sgn", []))
  else
    let
      val ct = Thm.cterm_of (get_ctxt ectxt) exp
    in
      (case determine_trimmed_sgn ectxt (get_coeff exp) of
         (IsPos, thm) => (IsPos, @{thm lift_trimmed_pos'} OF [thm, Thm.reflexive ct])
       | (IsNeg, thm) => (IsNeg, @{thm lift_trimmed_neg'} OF [thm, Thm.reflexive ct])
       | _ => raise TERM ("determine_trimmed_sgn", []))
    end

fun mk_compare_expansions_const T =
      Const (\<^const_name>\<open>compare_expansions\<close>, 
        T --> T --> \<^typ>\<open>cmp_result \<times> real \<times> real\<close>)

datatype comparison_result =
  Cmp_Dominated of order * thm list * zeroness * trimmed_thm * expansion_thm * expansion_thm 
| Cmp_Asymp_Equiv of thm * thm

fun compare_expansions' _ (thm1, thm2, SEmpty) = Cmp_Asymp_Equiv (thm1, thm2)
  | compare_expansions' ectxt (thm1, thm2, basis) =
  let
    fun lift_trimmed_thm nz =
      case nz of
        IsPos => @{thm lift_trimmed_pos}
      | IsNeg => @{thm lift_trimmed_neg}
      | _ => raise TERM ("Unexpected zeroness result in compare_expansions'", [])
    val (e1, e2) = apply2 (get_expansion #> get_exponent) (thm1, thm2)
    val e = \<^term>\<open>(-) :: real => _\<close> $ e1 $ e2
    fun trim thm = trim_expansion true (SOME Sgn_Trim) ectxt (thm, basis)
    val try_drop = Option.map (whnf_expansion ectxt #> #2) o try_drop_leading_term_ex false ectxt
    fun handle_result ord zeroness trimmed_thm thm1 thm2 =
      let
        val (e1, e2) = apply2 (get_expansion #> get_exponent) (thm1, thm2)
        val e = \<^term>\<open>(-) :: real => _\<close> $ e1 $ e2
        val mode = if ord = LESS then Neg_Trim else Pos_Trim
      in
        case zeroness_oracle true (SOME mode) ectxt e of
          (_, SOME e_thm) => Cmp_Dominated (ord, [e_thm], zeroness, trimmed_thm, thm1, thm2)
        | _ => raise Match
      end
    fun recurse e_zero_thm =
      case basis of
        SNE (SSng _) => Cmp_Asymp_Equiv (thm1, thm2)
      | _ =>
        let
          val (thm1', thm2') = apply2 (fn thm => thm RS @{thm expands_to_hd''}) (thm1, thm2)
          val (thm1', thm2') = apply2 (whnf_expansion ectxt #> #2) (thm1', thm2')
        in
          case compare_expansions' ectxt (thm1', thm2', tl_basis basis) of
            Cmp_Dominated (order, e_thms, zeroness, trimmed_thm, thm1', thm2') =>
              Cmp_Dominated (order, e_zero_thm :: e_thms, zeroness,
                trimmed_thm RS lift_trimmed_thm zeroness,
                @{thm expands_to_trim_cong} OF [thm1, thm1'],
                @{thm expands_to_trim_cong} OF [thm2, thm2'])
          | Cmp_Asymp_Equiv (thm1', thm2') => Cmp_Asymp_Equiv
              (@{thm expands_to_trim_cong} OF [thm1, thm1'],
                @{thm expands_to_trim_cong} OF [thm2, thm2'])
        end
  in
    case zeroness_oracle false (SOME Sgn_Trim) ectxt e of
      (IsPos, SOME _) => (
        case try_drop thm1 of
          SOME thm1 => compare_expansions' ectxt (thm1, thm2, basis)
        | NONE => (
            case trim thm1 of
              (thm1, zeroness, SOME trimmed_thm) =>
                handle_result GREATER zeroness trimmed_thm thm1 thm2
            | _ => raise TERM ("compare_expansions", map get_expansion [thm1, thm2])))
    | (IsNeg, SOME _) => (
        case try_drop thm2 of
          SOME thm2 => compare_expansions' ectxt (thm1, thm2, basis)
        | NONE => (
            case trim thm2 of
              (thm2, zeroness, SOME trimmed_thm) =>
                handle_result LESS zeroness trimmed_thm thm1 thm2
            | _ => raise TERM ("compare_expansions", map get_expansion [thm1, thm2])))
    | (IsZero, SOME e_zero_thm) => (
        case try_drop thm1 of
          SOME thm1 => compare_expansions' ectxt (thm1, thm2, basis)
        | NONE => (
            case try_drop thm2 of
              SOME thm2 => compare_expansions' ectxt (thm1, thm2, basis)
            | NONE => recurse e_zero_thm))
    | _ =>
        case try_drop thm1 of
          SOME thm1 => compare_expansions' ectxt (thm1, thm2, basis)
        | NONE => (
            case try_drop thm2 of
              SOME thm2 => compare_expansions' ectxt (thm1, thm2, basis)
            | NONE => raise TERM ("compare_expansions", [e1, e2]))
  end

(* Uses a list of exponent comparison results to show that compare_expansions has a given result.*)
fun prove_compare_expansions ord [thm] = (
      case ord of
        LESS => @{thm compare_expansions_LT_I} OF [thm]
      | GREATER => @{thm compare_expansions_GT_I} OF [thm]
      | EQUAL => @{thm compare_expansions_same_exp[OF _ compare_expansions_real]} OF [thm])
  | prove_compare_expansions ord (thm :: thms) =
      @{thm compare_expansions_same_exp} OF [thm, prove_compare_expansions ord thms]
  | prove_compare_expansions _ [] = raise Match

val ev_zero_pos_thm = Eventuallize.eventuallize \<^context>
  @{lemma "\<forall>x::real. f x = 0 \<longrightarrow> g x > 0 \<longrightarrow> f x < g x" by auto} NONE
  OF @{thms _ expands_to_imp_eventually_pos}

val ev_zero_neg_thm = Eventuallize.eventuallize \<^context>
  @{lemma "\<forall>x::real. f x = 0 \<longrightarrow> g x < 0 \<longrightarrow> f x > g x" by auto} NONE
  OF @{thms _ expands_to_imp_eventually_neg}

val ev_zero_zero_thm = Eventuallize.eventuallize \<^context>
  @{lemma "\<forall>x::real. f x = 0 \<longrightarrow> g x = 0 \<longrightarrow> f x = g x" by auto} NONE

fun compare_expansions_trivial ectxt (thm1, thm2, basis) =
  case try_prove_ev_eq ectxt (apply2 get_expanded_fun (thm1, thm2)) of
    SOME thm => SOME (EQUAL, thm, thm1, thm2)
  | NONE =>
      case apply2 (ev_zeroness_oracle ectxt o get_expanded_fun) (thm1, thm2) of
        (NONE, NONE) => NONE
      | (SOME zero1_thm, NONE) => (
          case trim_expansion true (SOME Sgn_Trim) ectxt (thm2, basis) of
            (thm2, IsPos, SOME trimmed2_thm) =>
              SOME (LESS, ev_zero_pos_thm OF
                [zero1_thm, get_basis_wf_thm basis, thm2, trimmed2_thm], thm1, thm2)
          | (thm2, IsNeg, SOME trimmed2_thm) =>
              SOME (GREATER, ev_zero_neg_thm OF
                [zero1_thm, get_basis_wf_thm basis, thm2, trimmed2_thm], thm1, thm2)
          | _ => raise TERM ("Unexpected zeroness result in compare_expansions", []))
      | (NONE, SOME zero2_thm) => (
          case trim_expansion true (SOME Sgn_Trim) ectxt (thm1, basis) of
            (thm1, IsPos, SOME trimmed1_thm) =>
              SOME (GREATER, ev_zero_pos_thm OF
                [zero2_thm, get_basis_wf_thm basis, thm1, trimmed1_thm], thm1, thm2)
          | (thm1, IsNeg, SOME trimmed1_thm) =>
              SOME (LESS, ev_zero_neg_thm OF
                [zero2_thm, get_basis_wf_thm basis, thm1, trimmed1_thm], thm1, thm2)
          | _ => raise TERM ("Unexpected zeroness result in compare_expansions", []))
      | (SOME zero1_thm, SOME zero2_thm) =>
          SOME (EQUAL, ev_zero_zero_thm OF [zero1_thm, zero2_thm] , thm1, thm2)

fun compare_expansions ectxt (thm1, thm2, basis) =
  case compare_expansions_trivial ectxt (thm1, thm2, basis) of
    SOME res => res
  | NONE =>
    let
      val (_, thm1, _) = whnf_expansion ectxt thm1
      val (_, thm2, _) = whnf_expansion ectxt thm2
    in
      case compare_expansions' ectxt (thm1, thm2, basis) of
        Cmp_Dominated (order, e_thms, zeroness, trimmed_thm, thm1, thm2) =>
          let
            val wf_thm = get_basis_wf_thm basis
            val cmp_thm = prove_compare_expansions order e_thms
            val trimmed_thm' = trimmed_thm RS
              (if zeroness = IsPos then @{thm trimmed_pos_imp_trimmed}
                 else @{thm trimmed_neg_imp_trimmed})
            val smallo_thm = 
              (if order = LESS then @{thm compare_expansions_LT} else @{thm compare_expansions_GT}) OF
                [cmp_thm, trimmed_thm', thm1, thm2, wf_thm]
            val thm' = 
              if zeroness = IsPos then @{thm smallo_trimmed_imp_eventually_less} 
              else @{thm smallo_trimmed_imp_eventually_greater}
            val result_thm =
              thm' OF [smallo_thm, if order = LESS then thm2 else thm1, wf_thm, trimmed_thm]
          in
            (order, result_thm, thm1, thm2)
          end
       | Cmp_Asymp_Equiv (thm1, thm2) =>
          let
            val thm = @{thm expands_to_minus} OF [get_basis_wf_thm basis, thm1, thm2]
            val (order, result_thm) =
              case trim_expansion true (SOME Sgn_Trim) ectxt (thm, basis) of
                (thm, IsPos, SOME pos_thm) => (GREATER,
                  @{thm expands_to_imp_eventually_gt} OF [get_basis_wf_thm basis, thm, pos_thm])
              | (thm, IsNeg, SOME neg_thm) => (LESS,
                  @{thm expands_to_imp_eventually_lt} OF [get_basis_wf_thm basis, thm, neg_thm])
              | _ => raise TERM ("Unexpected zeroness result in prove_eventually_less", [])
          in
            (order, result_thm, thm1, thm2)
          end
    end



(*
  Throws an exception and prints an error message indicating that the leading term could 
  not be determined to be either zero or non-zero.
*)
fun raise_trimming_error ectxt thm =
  let
    val ctxt = get_ctxt ectxt
    fun lead_coeff exp =
      if fastype_of exp = \<^typ>\<open>real\<close> then exp else lead_coeff (get_coeff exp)
    val c = lead_coeff (get_expansion thm)
    fun err () =
      let
        val t = simplify_term' (get_facts ectxt) ctxt c
        val _ =
          if #verbose (#ctxt ectxt) then
            let
              val p = Pretty.str 
                ("real_asymp failed to determine whether the following constant is zero:")
              val p = Pretty.chunks [p, Pretty.indent 2 (Syntax.pretty_term ctxt t)]
            in
              Pretty.writeln p
            end else ()
      in
        raise TERM ("zeroness_oracle", [t])
      end
  in
    err ()
  end
    

(* TODO Here be dragons *)
fun solve_eval_eq thm =
  case try (fn _ => @{thm refl} RS thm) () of
    SOME thm' => thm'
  | NONE => 
      case try (fn _ => @{thm eval_real_def} RS thm) () of
        SOME thm' => thm'
      | NONE => @{thm eval_ms.simps} RS thm

(*
  Returns an expansion theorem for the logarithm of the given expansion.
  May add one additional element to the basis at the end.
*)
fun ln_expansion _ _ _ SEmpty = raise TERM ("ln_expansion: empty basis", [])
  | ln_expansion ectxt trimmed_thm thm (SNE basis) =
  let
    fun trailing_exponent expr (SSng _) = get_exponent expr
      | trailing_exponent expr (SCons (_, _, tl)) = trailing_exponent (get_coeff expr) tl
    val e = trailing_exponent (get_expansion thm) basis
    fun ln_expansion_aux trimmed_thm zero_thm thm basis =
      let
        val t = betapply (\<^term>\<open>\<lambda>(f::real \<Rightarrow> real) x. f x - 1 :: real\<close>, get_expanded_fun thm)
      in
        case ev_zeroness_oracle ectxt t of
          NONE => ln_expansion_aux' trimmed_thm zero_thm thm basis
        | SOME zero_thm =>
            @{thm expands_to_ln_eventually_1} OF 
              [get_basis_wf_thm' basis, mk_expansion_level_eq_thm' basis, zero_thm]
      end
    and ln_expansion_aux' trimmed_thm zero_thm thm (SSng {wf_thm, ...}) =
          ( @{thm expands_to_ln} OF
            [trimmed_thm, wf_thm, thm, 
              @{thm expands_to_ln_aux_0} OF [zero_thm, @{thm expands_to_ln_const}]])
          |> solve_eval_eq
      | ln_expansion_aux' trimmed_thm zero_thm thm (SCons ({wf_thm, ...}, {ln_thm, ...}, basis')) =
          let
            val c_thm = 
              ln_expansion_aux (trimmed_thm RS @{thm trimmed_pos_hd_coeff}) zero_thm 
                (expands_to_hd thm) basis'
            val e = get_exponent (get_expansion thm)
            val c_thm' =
              case zeroness_oracle true NONE ectxt e of
                (IsZero, SOME thm) =>
                  @{thm expands_to_ln_to_expands_to_ln_eval [OF expands_to_ln_aux_0]} OF [thm,c_thm]
              | _ => 
                case try_prove_real_eq false ectxt (e, \<^term>\<open>1::real\<close>) of
                  SOME thm => 
                    @{thm expands_to_ln_to_expands_to_ln_eval [OF expands_to_ln_aux_1]}
                      OF [thm, wf_thm, c_thm, ln_thm]
                | NONE => 
                    @{thm expands_to_ln_to_expands_to_ln_eval [OF expands_to_ln_aux]} 
                      OF [wf_thm, c_thm, ln_thm]
          in
            (@{thm expands_to_ln} OF [trimmed_thm, wf_thm, thm, c_thm'])
            |> solve_eval_eq
          end
  in
    case zeroness_oracle true NONE ectxt e of
      (IsZero, SOME zero_thm) => (ln_expansion_aux trimmed_thm zero_thm thm basis, SNE basis)
    | _ => 
        let
          val basis' = insert_ln (SNE basis)
          val lifting = mk_lifting (get_basis_list' basis) basis'
          val thm' = lift_expands_to_thm lifting thm
          val trimmed_thm' = lift_trimmed_pos_thm lifting trimmed_thm
          val (thm'', eq_thm) = retrim_expansion ectxt (thm', basis')
          val trimmed_thm'' = @{thm trimmed_pos_eq_cong} OF [trimmed_thm', eq_thm]
        in
          ln_expansion ectxt trimmed_thm'' thm'' basis'
        end
  end

(*
  Handles a possible basis change after expanding exp(c(x)) for an expansion of the form
  f(x) = c(x) + g(x). Expanding exp(c(x)) may have inserted an additional basis element. If the 
  old basis was b :: bs (i.e. c is an expansion w.r.t. bs) and the updated one is bs' (which
  agrees with bs except for one additional element b'), we need to argue that b :: bs' is still
  well-formed. This may require us to show that ln(b') is o(ln(b)), which the function takes
  as an argument.
*)
fun adjust_exp_basis basis basis' ln_smallo_thm =
  if length (get_basis_list basis) = length (get_basis_list basis') + 1 then
    basis
  else
    let
      val SNE (SCons (info, ln_info, tail)) = basis
      val SNE tail' = basis'
      val wf_thms = map get_basis_wf_thm [basis, basis']
      val wf_thm' = 
        case
          get_first (fn f => try f ())
            [fn _ => @{thm basis_wf_lift_modification} OF wf_thms,
             fn _ => @{thm basis_wf_insert_exp_near} OF (wf_thms @ [ln_smallo_thm]),
             fn _ => @{thm basis_wf_insert_exp_near} OF (wf_thms @ 
               [ln_smallo_thm RS @{thm basis_wf_insert_exp_uminus'}])] of
          SOME wf_thm => wf_thm
        | _ => raise TERM ("Lifting basis modification in exp_expansion failed.", map Thm.concl_of (wf_thms @ [ln_smallo_thm]))
      val info' = {wf_thm = wf_thm', head = #head info}
      val lifting = mk_lifting (get_basis_list' tail) basis'
      val ln_info' = 
        {trimmed_thm = lift_trimmed_pos_thm lifting (#trimmed_thm ln_info),
         ln_thm = lift_expands_to_thm lifting (#ln_thm ln_info)}
    in
      SNE (SCons (info', ln_info', tail'))
    end

(* inserts the exponential of a given function at the beginning of the given basis *)
fun insert_exp _ _ _ _ _ SEmpty = raise TERM ("insert_exp", [])
  | insert_exp t ln_thm ln_smallo_thm ln_trimmed_thm lim_thm (SNE basis) =
      let
        val head = Envir.beta_eta_contract (\<^term>\<open>\<lambda>(f::real\<Rightarrow>real) x. exp (f x)\<close> $ t)
        val ln_smallo_thm = ln_smallo_thm RS @{thm ln_smallo_ln_exp}
        val wf_thm = @{thm basis_wf_manyI} OF [lim_thm, ln_smallo_thm, get_basis_wf_thm' basis]
        val basis' = SNE (SCons ({wf_thm = wf_thm, head = head}, 
          {ln_thm = ln_thm, trimmed_thm = ln_trimmed_thm} , basis))
      in
        check_basis basis'
      end 

(* 
  Returns an expansion of the exponential of the given expansion. This may add several
  new basis elements at any position of the basis (except at the very end
*)
fun exp_expansion _ thm SEmpty = (thm RS @{thm expands_to_exp_real}, SEmpty)
  | exp_expansion ectxt thm basis =
    let
      val (_, thm, _) = whnf_expansion ectxt thm
    in
      case ev_zeroness_oracle ectxt (get_eval (get_expansion thm)) of
        SOME zero_thm => 
          (@{thm expands_to_exp_zero} OF 
             [thm, zero_thm, get_basis_wf_thm basis, mk_expansion_level_eq_thm basis], basis)
      | NONE =>
          let
            val ln =
              Option.map (fn x => (#ln_thm x, #trimmed_thm x)) (get_ln_info basis)
            val ln = Option.map (fn (x, y) => retrim_pos_expansion ectxt (x, basis, y)) ln
            val es' = \<^term>\<open>0::real\<close> :: (
              case ln of
                NONE => []
              | SOME (ln_thm, _, _) => get_exponents (get_expansion ln_thm))
            val trim_result =
              trim_expansion_while_greater true (SOME es') false (SOME Simple_Trim) ectxt (thm, basis)
          in
            exp_expansion' ectxt trim_result ln basis
          end
    end
and exp_expansion' _ (thm, _, _) _ SEmpty = (thm RS @{thm expands_to_exp_real}, SEmpty)
  | exp_expansion' ectxt (thm, trim_result, e_thms) ln basis =
  let
    val exp = get_expansion thm
    val wf_thm = get_basis_wf_thm basis
    val f = get_expanded_fun thm
    fun exp_expansion_insert ln_smallo_thm = (
      case determine_trimmed_sgn ectxt exp of
        (IsPos, trimmed_thm) =>
          let
            val [lim_thm, ln_thm', thm'] =
              @{thms expands_to_exp_insert_pos}
              |> map (fn thm' => thm' OF [thm, wf_thm, trimmed_thm, ln_smallo_thm])
            val basis' = insert_exp f ln_thm' ln_smallo_thm trimmed_thm lim_thm basis
          in
            (thm', basis')
          end
      | (IsNeg, trimmed_thm) =>
          let
            val [lim_thm, ln_thm', ln_trimmed_thm, thm'] = 
              @{thms expands_to_exp_insert_neg}
              |> map (fn thm' => thm' OF [thm, wf_thm, trimmed_thm, ln_smallo_thm])
            val ln_smallo_thm = ln_smallo_thm RS @{thm basis_wf_insert_exp_uminus}
            val f' = Envir.beta_eta_contract (\<^term>\<open>\<lambda>(f::real\<Rightarrow>real) x. -f x\<close> $ f)
            val basis' = insert_exp f' ln_thm' ln_smallo_thm ln_trimmed_thm lim_thm basis
          in
            (thm', basis')
          end
      | _ => raise TERM ("Unexpected zeroness result in exp_expansion", []))
    fun lexord (IsNeg :: _) = LESS
      | lexord (IsPos :: _) = GREATER
      | lexord (IsZero :: xs) = lexord xs
      | lexord [] = EQUAL
      | lexord _ = raise Match
    val compare_result = lexord (map fst e_thms)
  in
    case (trim_result, e_thms, compare_result) of
      (Aborted _, (IsNeg, e_neg_thm) :: _, _) =>
        (* leading exponent is negative; we can simply Taylor-expand exp(x) around 0 *)
        (@{thm expands_to_exp_neg} OF [thm, get_basis_wf_thm basis, e_neg_thm], basis)
    | (Trimmed (_, SOME trimmed_thm), (IsPos, e_pos_thm) :: _, GREATER) =>
        (* leading exponent is positive; exp(f(x)) or exp(-f(x)) is new basis element *)
        let
          val ln_smallo_thm =
            @{thm basis_wf_insert_exp_pos} OF [thm, get_basis_wf_thm basis, trimmed_thm, e_pos_thm]
        in
          exp_expansion_insert ln_smallo_thm
        end
    | (Trimmed (_, SOME trimmed_thm), _, GREATER) =>
        (* leading exponent is zero, but f(x) grows faster than ln(b(x)), so 
           exp(f(x)) or exp(-f(x)) must still be new basis elements *)
        let
          val ln_thm =
            case ln of
              SOME (ln_thm, _, _) => ln_thm
            | NONE => raise TERM ("TODO blubb", [])
          val ln_thm = @{thm expands_to_lift''} OF [get_basis_wf_thm basis, ln_thm]
          val ln_smallo_thm = 
             @{thm compare_expansions_GT} OF [prove_compare_expansions GREATER (map snd e_thms),
               trimmed_thm, thm, ln_thm, get_basis_wf_thm basis]
        in
          exp_expansion_insert ln_smallo_thm
        end
    | (Aborted LESS, (IsZero, e_zero_thm) :: e_thms', _) =>
        (* leading exponent is zero and f(x) grows more slowly than ln(b(x)), so 
           we can write f(x) = c(x) + g(x) and therefore exp(f(x)) = exp(c(x)) * exp(g(x)).
           The former is treated by a recursive call; the latter by Taylor expansion. *)
        let
          val (ln_thm, trimmed_thm) =
            case ln of
              SOME (ln_thm, _, trimmed_thm) =>
                (ln_thm, trimmed_thm RS @{thm trimmed_pos_imp_trimmed})
            | NONE => raise TERM ("TODO foo", [])
          val c_thm = expands_to_hd thm
          val ln_smallo_thm =
            @{thm compare_expansions_LT} OF [prove_compare_expansions LESS (map snd e_thms'),
              trimmed_thm, c_thm, ln_thm, get_basis_wf_thm (tl_basis basis)]
          val (c_thm, c_basis) = exp_expansion ectxt c_thm (tl_basis basis)
          val basis' = adjust_exp_basis basis c_basis ln_smallo_thm
          val wf_thm = get_basis_wf_thm basis'
          val thm' = lift basis' thm
          val (thm'', _) = retrim_expansion ectxt (thm', basis')
        in
          (@{thm expands_to_exp_0} OF [thm'', wf_thm, e_zero_thm, c_thm], basis')
        end
    | (Trimmed _, [(IsZero, e_zero_thm)], EQUAL) =>
        (* f(x) can be written as c + g(x) where c is just a real constant.
           We can therefore write exp(f(x)) = exp(c) * exp(g(x)), where the latter is
           a simple Taylor expansion. *)
        (@{thm expands_to_exp_0_real} OF [thm, wf_thm, e_zero_thm], basis)
    | (Trimmed _, (_, e_zero_thm) :: _, EQUAL) =>
        (* f(x) is asymptotically equivalent to c * ln(b(x)), so we can write f(x) as
           c * ln(b(x)) + g(x) and therefore exp(f(x)) = b(x)^c * exp(g(x)). The second
           factor is handled by a recursive call *)
        let
          val ln_thm =
            case ln of
              SOME (ln_thm, _, _) => ln_thm
            | NONE => raise TERM ("TODO blargh", [])
          val c =
            case (thm, ln_thm) |> apply2 (get_expansion #> get_lead_coeff) of
              (c1, c2) => \<^term>\<open>(/) :: real => _\<close> $ c1 $ c2
          val c = Thm.cterm_of (get_ctxt ectxt) c
          
          val thm' = 
            @{thm expands_to_exp_0_pull_out1} 
                OF [thm, ln_thm, wf_thm, e_zero_thm, Thm.reflexive c]
          val (thm'', basis') = exp_expansion ectxt thm' basis
          val pat = ConsPat ("MS", [AnyPat ("_", 0), AnyPat ("_", 0)])
          val (_, _, conv) = match ectxt pat (get_expansion thm'') (SOME [])
          val eq_thm = conv (Thm.cterm_of (get_ctxt ectxt) (get_expansion thm''))
          val thm''' = @{thm expands_to_meta_eq_cong} OF [thm'', eq_thm]
          val thm'''' = 
            case get_intyness (get_ctxt ectxt) c of
              No_Nat =>
                @{thm expands_to_exp_0_pull_out2} OF [thm''', get_basis_wf_thm basis']
             | Nat nat_thm =>
                @{thm expands_to_exp_0_pull_out2_nat} OF 
                  [thm''', get_basis_wf_thm basis', nat_thm]
             | Neg_Nat nat_thm =>
                @{thm expands_to_exp_0_pull_out2_neg_nat} OF 
                  [thm''', get_basis_wf_thm basis', nat_thm]
        in
          (thm'''', basis')
        end
    | (Trimmed (IsZero, _), [], _) =>
        (* Expansion is empty, i.e. f(x) is identically zero *)
        (@{thm expands_to_exp_MSLNil} OF [thm, get_basis_wf_thm basis], basis)
    | (Trimmed (_, NONE), _, GREATER) =>
        (* We could not determine whether f(x) grows faster than ln(b(x)) or not. *)
        raise_trimming_error ectxt thm
    | _ => raise Match
  end

fun powr_expansion ectxt (thm1, thm2, basis) =
      case ev_zeroness_oracle ectxt (get_expanded_fun thm1) of
        SOME zero_thm =>
          (@{thm expands_to_powr_0} OF
             [zero_thm, Thm.reflexive (Thm.cterm_of (get_ctxt ectxt) (get_expanded_fun thm2)),
              get_basis_wf_thm basis, mk_expansion_level_eq_thm basis],
           basis)
      | NONE =>
          let
            val (thm1, _, SOME trimmed_thm) =
              trim_expansion true (SOME Pos_Trim) ectxt (thm1, basis)
            val (ln_thm, basis') = ln_expansion ectxt trimmed_thm thm1 basis
            val thm2' = lift basis' thm2 |> simplify_expansion ectxt
            val mult_thm = @{thm expands_to_mult} OF [get_basis_wf_thm basis', ln_thm, thm2']
            val (exp_thm, basis'') = exp_expansion ectxt mult_thm basis'
            val thm = @{thm expands_to_powr} OF 
              [trimmed_thm, get_basis_wf_thm basis, thm1, exp_thm]
          in  
            (thm, basis'')
          end

fun powr_nat_expansion ectxt (thm1, thm2, basis) =
      case ev_zeroness_oracle ectxt (get_expanded_fun thm1) of
        SOME zero_thm => (
          case ev_zeroness_oracle ectxt (get_expanded_fun thm2) of
            SOME zero'_thm => (@{thm expands_to_powr_nat_0_0} OF
             [zero_thm, zero'_thm, get_basis_wf_thm basis, mk_expansion_level_eq_thm basis], basis)
          | NONE => (
              case trim_expansion true (SOME Simple_Trim) ectxt (thm2, basis) of
                (thm2, _, SOME trimmed_thm) =>
                  (@{thm expands_to_powr_nat_0} OF [zero_thm, thm2, trimmed_thm, 
                     get_basis_wf_thm basis, mk_expansion_level_eq_thm basis], basis)))
      | NONE =>
          let
            val (thm1, _, SOME trimmed_thm) =
              trim_expansion true (SOME Pos_Trim) ectxt (thm1, basis)
            val (ln_thm, basis') = ln_expansion ectxt trimmed_thm thm1 basis
            val thm2' = lift basis' thm2 |> simplify_expansion ectxt
            val mult_thm = @{thm expands_to_mult} OF [get_basis_wf_thm basis', ln_thm, thm2']
            val (exp_thm, basis'') = exp_expansion ectxt mult_thm basis'
            val thm = @{thm expands_to_powr_nat} OF 
              [trimmed_thm, get_basis_wf_thm basis, thm1, exp_thm]
          in  
            (thm, basis'')
          end

fun is_numeral t =
  let
    val _ = HOLogic.dest_number t
  in
    true
  end
    handle TERM _ => false

fun power_expansion ectxt (thm, n, basis) =
      case ev_zeroness_oracle ectxt (get_expanded_fun thm) of
        SOME zero_thm => @{thm expands_to_power_0} OF
          [zero_thm, get_basis_wf_thm basis, mk_expansion_level_eq_thm basis,
             Thm.reflexive (Thm.cterm_of (get_ctxt ectxt) n)]
      | NONE => (
          case trim_expansion true (SOME Simple_Trim) ectxt (thm, basis) of
            (thm', _, SOME trimmed_thm) =>
              let
                val ctxt = get_ctxt ectxt
                val thm =
                  if is_numeral n then @{thm expands_to_power[where abort = True]}
                    else @{thm expands_to_power[where abort = False]}
                val thm = 
                  Drule.infer_instantiate' ctxt [NONE, NONE, NONE, SOME (Thm.cterm_of ctxt n)] thm
              in                
                thm OF [trimmed_thm, get_basis_wf_thm basis, thm']
              end
          | _ => raise TERM ("Unexpected zeroness result in power_expansion", []))

fun powr_const_expansion ectxt (thm, p, basis) =
  let
    val pthm = Thm.reflexive (Thm.cterm_of (get_ctxt ectxt) p)
  in
    case ev_zeroness_oracle ectxt (get_expanded_fun thm) of
      SOME zero_thm => @{thm expands_to_powr_const_0} OF 
        [zero_thm, get_basis_wf_thm basis, mk_expansion_level_eq_thm basis, pthm]
    | NONE =>
        case trim_expansion true (SOME Pos_Trim) ectxt (thm, basis) of
          (_, _, NONE) => raise TERM ("Unexpected zeroness result for powr", [])
        | (thm, _, SOME trimmed_thm) =>
            (if is_numeral p then @{thm expands_to_powr_const[where abort = True]}
                 else @{thm expands_to_powr_const[where abort = False]})
               OF [trimmed_thm, get_basis_wf_thm basis, thm, pthm]
  end

fun sgn_expansion ectxt (thm, basis) =
  let
    val thms = [get_basis_wf_thm basis, mk_expansion_level_eq_thm basis]
  in
    case ev_zeroness_oracle ectxt (get_expanded_fun thm) of
      SOME zero_thm => @{thm expands_to_sgn_zero} OF (zero_thm :: thms)
    | NONE =>
        case trim_expansion true (SOME Sgn_Trim) ectxt (thm, basis) of
          (thm, IsPos, SOME trimmed_thm) =>
            @{thm expands_to_sgn_pos} OF ([trimmed_thm, thm] @ thms)
        | (thm, IsNeg, SOME trimmed_thm) =>
            @{thm expands_to_sgn_neg} OF ([trimmed_thm, thm] @ thms)
        | _ => raise TERM ("Unexpected zeroness result in sgn_expansion", [])
  end

(*
  Returns an expansion of the sine and cosine of the given expansion. Fails if that function
  goes to infinity.
*)
fun sin_cos_expansion _ thm SEmpty =
      (thm RS @{thm expands_to_sin_real}, thm RS @{thm expands_to_cos_real})
  | sin_cos_expansion ectxt thm basis =
      let
        val exp = get_expansion thm
        val e = get_exponent exp
      in
        case zeroness_oracle true (SOME Sgn_Trim) ectxt e of
          (IsPos, _) => raise THM ("sin_cos_expansion", 0, [thm])
        | (IsNeg, SOME e_thm) =>
            let
              val [thm1, thm2] = 
                map (fn thm' => thm' OF [e_thm, get_basis_wf_thm basis, thm]) 
                  @{thms expands_to_sin_ms_neg_exp expands_to_cos_ms_neg_exp}
            in
              (thm1, thm2)
            end
        | (IsZero, SOME e_thm) =>
            let
              val (sin_thm, cos_thm) = (sin_cos_expansion ectxt (expands_to_hd thm) (tl_basis basis))
              fun mk_thm thm' = 
                (thm' OF [e_thm, get_basis_wf_thm basis, thm, sin_thm, cos_thm]) |> solve_eval_eq
              val [thm1, thm2] = 
                map mk_thm @{thms expands_to_sin_ms_zero_exp expands_to_cos_ms_zero_exp}
            in
              (thm1, thm2)
            end
        | _ => raise TERM ("Unexpected zeroness result in sin_exp_expansion", [])
      end

fun abconv (t, t') = Envir.beta_eta_contract t aconv Envir.beta_eta_contract t'

(*
  Makes sure that an expansion theorem really talks about the right function.
  This is basically a sanity check to make things fail early and in the right place.
*)
fun check_expansion e thm =
  if abconv (expr_to_term e, get_expanded_fun thm) then 
    thm 
  else
(* TODO Remove Debugging stuff *)
let val _ = \<^print> e
val _ = \<^print> (get_expanded_fun thm)
in
    raise TERM ("check_expansion", [Thm.concl_of thm, expr_to_term e])
end

fun minmax_expansion max [less_thm, eq_thm, gt_thm] ectxt (thm1, thm2, basis) = (
      case compare_expansions ectxt (thm1, thm2, basis) of
        (LESS, less_thm', thm1, thm2) => less_thm OF [if max then thm2 else thm1, less_thm']
      | (GREATER, gt_thm', thm1, thm2) => gt_thm OF [if max then thm1 else thm2, gt_thm']
      | (EQUAL, eq_thm', thm1, _) => eq_thm OF [thm1, eq_thm'])
  | minmax_expansion _ _ _ _ = raise Match

val min_expansion =
  minmax_expansion false @{thms expands_to_min_lt expands_to_min_eq expands_to_min_gt}
val max_expansion =
  minmax_expansion true @{thms expands_to_max_lt expands_to_max_eq expands_to_max_gt}

fun zero_expansion basis =
  @{thm expands_to_zero} OF [get_basis_wf_thm basis, mk_expansion_level_eq_thm basis]

fun const_expansion _ basis \<^term>\<open>0 :: real\<close> = zero_expansion basis
  | const_expansion ectxt basis t =
  let
    val ctxt = get_ctxt ectxt
    val thm = Drule.infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt t)] 
                @{thm expands_to_const}
  in
    thm OF [get_basis_wf_thm basis, mk_expansion_level_eq_thm basis]
  end

fun root_expansion ectxt (thm, n, basis) =
  let
    val ctxt = get_ctxt ectxt
    fun tac {context = ctxt, ...} =
      HEADGOAL (Method.insert_tac ctxt (get_facts ectxt))
      THEN Local_Defs.unfold_tac ctxt eval_simps
      THEN HEADGOAL (Simplifier.asm_full_simp_tac ctxt)
    fun prove goal =
      try (Goal.prove ctxt [] [] (HOLogic.mk_Trueprop (Term.betapply (goal, n)))) tac
    fun err () =
      let
        val t = simplify_term' (get_facts ectxt) ctxt n
        val _ =
          if #verbose (#ctxt ectxt) then
            let
              val p = Pretty.str ("real_asymp failed to determine whether the following constant " ^
                "is zero or not:")
              val p = Pretty.chunks [p, Pretty.indent 2 (Syntax.pretty_term ctxt t)]
            in
              Pretty.writeln p
            end else ()
      in
        raise TERM ("zeroness_oracle", [n])
      end
    fun aux nz_thm =
      case trim_expansion true (SOME Sgn_Trim) ectxt (thm, basis) of
        (thm, IsPos, SOME trimmed_thm) =>
          @{thm expands_to_root} OF [nz_thm, trimmed_thm, get_basis_wf_thm basis, thm]
      | (thm, IsNeg, SOME trimmed_thm) =>
          @{thm expands_to_root_neg} OF [nz_thm, trimmed_thm, get_basis_wf_thm basis, thm]
      | _ => raise TERM ("Unexpected zeroness result in root_expansion", [])
  in
    case prove \<^term>\<open>\<lambda>n::nat. n = 0\<close> of
      SOME zero_thm =>
        @{thm expands_to_0th_root} OF
          [zero_thm, get_basis_wf_thm basis, mk_expansion_level_eq_thm basis, 
             Thm.reflexive (Thm.cterm_of ctxt (get_expanded_fun thm))]
    | NONE =>
        case prove \<^term>\<open>\<lambda>n::nat. n > 0\<close> of
          NONE => err ()
        | SOME nz_thm =>
            case ev_zeroness_oracle ectxt (get_expanded_fun thm) of
              SOME zero_thm => @{thm expands_to_root_0} OF
                [nz_thm, zero_thm, get_basis_wf_thm basis, mk_expansion_level_eq_thm basis]
            | NONE => aux nz_thm
  end


fun arctan_expansion _ SEmpty thm =
      @{thm expands_to_real_compose[where g = arctan]} OF [thm]
  | arctan_expansion ectxt basis thm =
      case ev_zeroness_oracle ectxt (get_expanded_fun thm) of
        SOME zero_thm => @{thm expands_to_arctan_zero} OF [zero_expansion basis, zero_thm]
      | NONE =>
          let
            val (thm, _, _) = trim_expansion true (SOME Simple_Trim) ectxt (thm, basis)
            val e = get_exponent (get_expansion thm)
            fun cont ectxt (thm, basis) = arctan_expansion ectxt basis thm
          in
            case zeroness_oracle true (SOME Sgn_Trim) ectxt e of
                (IsNeg, SOME neg_thm) =>
                  @{thm expands_to_arctan_ms_neg_exp} OF [neg_thm, get_basis_wf_thm basis, thm]
              | (IsPos, SOME e_pos_thm) => (
                  case determine_trimmed_sgn ectxt (get_expansion thm) of
                    (IsPos, trimmed_thm) =>
                      @{thm expands_to_arctan_ms_pos_exp_pos} OF 
                        [e_pos_thm, trimmed_thm, get_basis_wf_thm basis, thm]
                  | (IsNeg, trimmed_thm) =>
                      @{thm expands_to_arctan_ms_pos_exp_neg} OF 
                        [e_pos_thm, trimmed_thm, get_basis_wf_thm basis, thm]
                  | _ => raise TERM ("Unexpected trim result during expansion of arctan", []))
              | (IsZero, _) => (
                  case try_lift_function ectxt (thm, basis) cont of
                    (SOME thm', _) => thm'
                  | _ =>
                      let
                        val _ = if get_verbose ectxt then 
                          writeln "Unsupported occurrence of arctan" else ()
                      in
                        raise TERM ("Unsupported occurence of arctan", [])
                      end)
              | _ => raise TERM ("Unexpected trim result during expansion of arctan", [])
          end

(* Returns an expansion theorem for a function that is already a basis element *)
fun expand_basic _ t SEmpty = raise TERM ("expand_basic", [t])
  | expand_basic thm t basis =
      if abconv (get_basis_head basis, t) then
        thm (get_basis_wf_thm basis) (mk_expansion_level_eq_thm (tl_basis basis))
      else
        @{thm expands_to_lift'} OF [get_basis_wf_thm basis, expand_basic thm t (tl_basis basis)]
  
fun expand_unary ectxt thm e basis =
      let
        val (thm', basis') = expand' ectxt e basis |> apfst (simplify_expansion ectxt)
      in
        (thm OF [get_basis_wf_thm basis', thm'], basis')
      end
and expand_binary ectxt thm (e1, e2) basis =
      let
        val (thm1, basis') = expand' ectxt e1 basis |> apfst (simplify_expansion ectxt)
        val (thm2, basis'') = expand' ectxt e2 basis' |> apfst (simplify_expansion ectxt)
        val thm1 = lift basis'' thm1 |> simplify_expansion ectxt
      in
        (thm OF [get_basis_wf_thm basis'', thm1, thm2], basis'')
      end
and trim_nz mode ectxt e basis =
      let
        val (thm, basis') = expand' ectxt e basis |> apfst (simplify_expansion ectxt)
        val (thm', nz, trimmed_thm) = trim_expansion true (SOME mode) ectxt (thm, basis')
      in
        case trimmed_thm of
          NONE => raise TERM ("expand: zero denominator", [get_expansion thm])
        | SOME trimmed_thm => (thm', basis', nz, trimmed_thm)
      end
and expand'' ectxt (ConstExpr c) basis = (const_expansion ectxt basis c, basis)
  | expand'' _ X basis = (lift basis @{thm expands_to_X}, basis)
  | expand'' ectxt (Uminus e) basis = expand_unary ectxt @{thm expands_to_uminus} e basis
  | expand'' ectxt (Add e12) basis = expand_binary ectxt @{thm expands_to_add} e12 basis
  | expand'' ectxt (Minus e12) basis = expand_binary ectxt @{thm expands_to_minus} e12 basis
  | expand'' ectxt (Mult e12) basis = expand_binary ectxt @{thm expands_to_mult} e12 basis
  | expand'' ectxt (Powr' (e, p)) basis = (* TODO zero basis *)
      let
        val (thm, basis') = expand' ectxt e basis |> apfst (simplify_expansion ectxt)
      in
        (powr_const_expansion ectxt (thm, p, basis'), basis')
      end
  | expand'' ectxt (Powr (e1, e2)) basis =
      let
        val (thm2, basis1) = expand' ectxt e2 basis |> apfst (simplify_expansion ectxt)
        val (thm1, basis2) = expand' ectxt e1 basis1 |> apfst (simplify_expansion ectxt)
      in
        powr_expansion ectxt (thm1, thm2, basis2)
      end
  | expand'' ectxt (Powr_Nat (e1, e2)) basis =
      let
        val (thm2, basis1) = expand' ectxt e2 basis |> apfst (simplify_expansion ectxt)
        val (thm1, basis2) = expand' ectxt e1 basis1 |> apfst (simplify_expansion ectxt)
      in
        powr_nat_expansion ectxt (thm1, thm2, basis2)
      end
  | expand'' ectxt (LnPowr (e1, e2)) basis =
      let (* TODO zero base *)
        val (thm2, basis1) = expand' ectxt e2 basis |> apfst (simplify_expansion ectxt)
        val (thm1, basis2, _, trimmed_thm) = trim_nz Pos_Trim ectxt e1 basis1
        val (ln_thm, basis3) = ln_expansion ectxt trimmed_thm thm1 basis2
        val thm2' = lift basis3 thm2 |> simplify_expansion ectxt
        val mult_thm = @{thm expands_to_mult} OF [get_basis_wf_thm basis3, ln_thm, thm2']
        val thm = @{thm expands_to_ln_powr} OF 
          [trimmed_thm, get_basis_wf_thm basis2, thm1, mult_thm]
      in  
        (thm, basis3)
      end
  | expand'' ectxt (ExpLn e) basis =
      let
        val (thm, basis', _, trimmed_thm) = trim_nz Pos_Trim ectxt e basis
        val thm = @{thm expands_to_exp_ln} OF [trimmed_thm, get_basis_wf_thm basis', thm]
      in  
        (thm, basis')
      end
  | expand'' ectxt (Power (e, n)) basis =
      let
        val (thm, basis') = expand' ectxt e basis |> apfst (simplify_expansion ectxt)
      in
        (power_expansion ectxt (thm, n, basis'), basis')
      end
  | expand'' ectxt (Root (e, n)) basis =
      let
        val (thm, basis') = expand' ectxt e basis |> apfst (simplify_expansion ectxt)
      in
        (root_expansion ectxt (thm, n, basis'), basis')
      end
  | expand'' ectxt (Inverse e) basis = 
      (case trim_nz Simple_Trim ectxt e basis of
         (thm, basis', _, trimmed_thm) => 
           (@{thm expands_to_inverse} OF [trimmed_thm, get_basis_wf_thm basis', thm], basis'))
  | expand'' ectxt (Div (e1, e2)) basis =
      let
        val (thm1, basis') = expand' ectxt e1 basis
        val (thm2, basis'', _, trimmed_thm) = trim_nz Simple_Trim ectxt e2 basis'
        val thm1 = lift basis'' thm1
      in
        (@{thm expands_to_divide} OF [trimmed_thm, get_basis_wf_thm basis'', thm1, thm2], basis'')
      end
  | expand'' ectxt (Ln e) basis =
      let
        val (thm, basis', _, trimmed_thm) = trim_nz Pos_Trim ectxt e basis
      in
        ln_expansion ectxt trimmed_thm thm basis'
      end
  | expand'' ectxt (Exp e) basis =
      let
        val (thm, basis') = expand' ectxt e basis
      in
        exp_expansion ectxt thm basis'
      end
  | expand'' ectxt (Absolute e) basis =
      let
        val (thm, basis', nz, trimmed_thm) = trim_nz Sgn_Trim ectxt e basis
        val thm' =
          case nz of 
            IsPos => @{thm expands_to_abs_pos} 
          | IsNeg => @{thm expands_to_abs_neg}
          | _ => raise TERM ("Unexpected trim result during expansion of abs", [])
      in
        (thm' OF [trimmed_thm, get_basis_wf_thm basis', thm], basis')
      end
  | expand'' ectxt (Sgn e) basis =
      let
        val (thm, basis') = expand' ectxt e basis
      in
        (sgn_expansion ectxt (thm, basis'), basis')
      end
  | expand'' ectxt (Min (e1, e2)) basis = (
      case try_prove_ev_eq ectxt (apply2 expr_to_term (e1, e2)) of
        SOME eq_thm =>
          expand' ectxt e1 basis
          |> apfst (fn thm => @{thm expands_to_min_eq} OF [thm, eq_thm])
      | NONE =>
          let
            val (thm1, basis') = expand' ectxt e1 basis
            val (thm2, basis'') = expand' ectxt e2 basis'
            val thm1' = lift basis'' thm1
          in
            (min_expansion ectxt (thm1', thm2, basis''), basis'')
          end)
  | expand'' ectxt (Max (e1, e2)) basis = (
      case try_prove_ev_eq ectxt (apply2 expr_to_term (e1, e2)) of
        SOME eq_thm =>
          expand' ectxt e1 basis
          |> apfst (fn thm => @{thm expands_to_max_eq} OF [thm, eq_thm])
      | NONE =>
          let
            val (thm1, basis') = expand' ectxt e1 basis
            val (thm2, basis'') = expand' ectxt e2 basis'
            val thm1' = lift basis'' thm1
          in
            (max_expansion ectxt (thm1', thm2, basis''), basis'')
          end)
  | expand'' ectxt (Sin e) basis =
      let
        val (thm, basis', _, _) = trim_nz Simple_Trim ectxt e basis (* TODO could be relaxed *)
      in
        (sin_cos_expansion ectxt thm basis' |> fst, basis')
      end
  | expand'' ectxt (Cos e) basis =
      let
        val (thm, basis', _, _) = trim_nz Simple_Trim ectxt e basis (* TODO could be relaxed *)
      in
        (sin_cos_expansion ectxt thm basis' |> snd, basis')
      end
  | expand'' _ (Floor _) _ =
      raise TERM ("floor not supported.", [])
  | expand'' _ (Ceiling _) _ =
      raise TERM ("ceiling not supported.", [])
  | expand'' _ (Frac _) _ =
      raise TERM ("frac not supported.", [])
  | expand'' _ (NatMod _) _ =
      raise TERM ("mod not supported.", [])
  | expand'' ectxt (ArcTan e) basis =
      let
        (* TODO: what if it's zero *)
        val (thm, basis') = expand' ectxt e basis
      in
        (arctan_expansion ectxt basis' thm, basis')
      end
  | expand'' ectxt (Custom (name, t, args)) basis =
      let
        fun expand_args acc basis [] = (rev acc, basis)
          | expand_args acc basis (arg :: args) =
              case expand' ectxt arg basis of
                (thm, basis') => expand_args (thm :: acc) basis' args          
      in
        case expand_custom (get_ctxt ectxt) name of
          NONE => raise TERM ("Unsupported custom function: " ^ name, [t])
        | SOME e => e ectxt t (expand_args [] basis args)
      end

and expand' ectxt (e' as (Inverse e)) basis =
      let
        val t = expr_to_term e
        fun thm wf_thm len_thm =
          @{thm expands_to_basic_inverse} OF [wf_thm, len_thm]
      in
        if member abconv (get_basis_list basis) t then
          (expand_basic thm t basis, basis) |> apfst (check_expansion e')
        else
          expand'' ectxt e' basis |> apfst (check_expansion e')
      end
  | expand' ectxt (Div (e1, e2)) basis =
      let
        val (thm1, basis') = expand' ectxt e1 basis
        val t = expr_to_term e2
        fun thm wf_thm len_thm =
          @{thm expands_to_basic_inverse} OF [wf_thm, len_thm]
      in
        if member abconv (get_basis_list basis') t then
          (@{thm expands_to_div'} OF [get_basis_wf_thm basis', thm1, expand_basic thm t basis'], 
             basis')
        else
          let
            val (thm2, basis'', _, trimmed_thm) = trim_nz Simple_Trim ectxt e2 basis'
            val thm1 = lift basis'' thm1
          in
            (@{thm expands_to_divide} OF [trimmed_thm, get_basis_wf_thm basis'', thm1, thm2], 
               basis'')
          end
      end
  | expand' ectxt (e' as (Powr' (e, p))) basis =
      let
        val t = expr_to_term e
        val ctxt = get_ctxt ectxt
        fun thm wf_thm len_thm =
          (Drule.infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt p)]
            @{thm expands_to_basic_powr}) OF [wf_thm, len_thm]
      in
        if member abconv (get_basis_list basis) t then
          (expand_basic thm t basis, basis) |> apfst (check_expansion e')
        else
          expand'' ectxt e' basis |> apfst (check_expansion e')
      end
  | expand' ectxt e basis =
      let
        val t = expr_to_term e
        fun thm wf_thm len_thm = @{thm expands_to_basic} OF [wf_thm, len_thm]
      in
        if member abconv (get_basis_list basis) t then
          (expand_basic thm t basis, basis) |> apfst (check_expansion e)
        else
          expand'' ectxt e basis |> apfst (check_expansion e)
      end

fun expand ectxt e basis = 
  expand' ectxt e basis
  |> apfst (simplify_expansion ectxt) 
  |> apfst (check_expansion e)

fun expand_term ectxt t basis =
  let
    val ctxt = get_ctxt ectxt
    val (e, eq_thm) = reify ctxt t
    val (thm,  basis) = expand ectxt e basis
  in
    (@{thm expands_to_meta_eq_cong'} OF [thm, eq_thm], basis)
  end

fun expand_terms ectxt ts basis =
  let
    val ctxt = get_ctxt ectxt
    val e_eq_thms = map (reify ctxt) ts
    fun step (e, eq_thm) (thms, basis) =
      let
        val (thm, basis) = expand' ectxt e basis
        val thm = @{thm expands_to_meta_eq_cong'} OF [simplify_expansion ectxt thm, eq_thm]
      in
        (thm :: thms, basis)
      end
    val (thms, basis) = fold step e_eq_thms ([], basis)
    fun lift thm = lift_expands_to_thm (mk_lifting (extract_basis_list thm) basis) thm
  in
    (map lift (rev thms), basis)
  end

datatype limit =
   Zero_Limit of bool option
 | Finite_Limit of term
 | Infinite_Limit of bool option

fun is_empty_expansion (Const (\<^const_name>\<open>MS\<close>, _) $ Const (\<^const_name>\<open>MSLNil\<close>, _) $ _) = true
  | is_empty_expansion _ = false

fun limit_of_expansion_aux ectxt basis thm =
  let
    val n = length (get_basis_list basis)
    val (thm, res, e_thms) =
      trim_expansion_while_greater false (SOME (replicate n \<^term>\<open>0::real\<close>)) true
        (SOME Simple_Trim) ectxt (thm, basis)
    val trimmed_thm = case res of Trimmed (_, trimmed_thm) => trimmed_thm | _ => NONE
    val res = case res of Trimmed _ => GREATER | Aborted res => res
    val exp = get_expansion thm
    val _ = if res = GREATER andalso is_none trimmed_thm andalso not (is_empty_expansion exp) then
              raise TERM ("limit_of_expansion", [get_expansion thm]) else ()
    fun go thm _ _ [] = (
          case zeroness_oracle false (SOME Simple_Trim) ectxt (get_expansion thm) of
            (IsZero, _) => (Zero_Limit NONE, @{thm expands_to_real_imp_filterlim} OF [thm])
          | _ => (Finite_Limit \<^term>\<open>0::real\<close>, @{thm expands_to_real_imp_filterlim} OF [thm]))
      | go thm _ basis ((IsNeg, neg_thm) :: _) = (Zero_Limit NONE,
          @{thm expands_to_neg_exponent_imp_filterlim} OF
            [thm, get_basis_wf_thm basis, neg_thm RS @{thm compare_reals_diff_sgnD(1)}])
      | go thm trimmed_thm basis ((IsPos, pos_thm) :: _) = (Infinite_Limit NONE,
          @{thm expands_to_pos_exponent_imp_filterlim} OF
            [thm, the trimmed_thm, get_basis_wf_thm basis,
             pos_thm RS @{thm compare_reals_diff_sgnD(3)}])
      | go thm trimmed_thm basis ((IsZero, zero_thm) :: e_thms) =
          let
             val thm' = thm RS @{thm expands_to_hd''}
             val trimmed_thm' = Option.map (fn thm => thm RS @{thm trimmed_hd}) trimmed_thm
             val (lim, lim_thm) = go thm' trimmed_thm' (tl_basis basis) e_thms
             val lim_lift_thm =
                case lim of
                  Infinite_Limit _ => @{thm expands_to_zero_exponent_imp_filterlim(1)}
                | _ => @{thm expands_to_zero_exponent_imp_filterlim(2)}
             val lim_thm' = 
               lim_lift_thm OF [thm, get_basis_wf_thm basis, 
                 zero_thm RS @{thm compare_reals_diff_sgnD(2)}, lim_thm]
          in
              (lim, lim_thm')
          end
      | go _ _ _ _ = raise Match
  in
    if is_empty_expansion exp then
      (Zero_Limit NONE, thm RS @{thm expands_to_MSLNil_imp_filterlim}, thm)
    else
      case go thm trimmed_thm basis e_thms of
        (lim, lim_thm) => (lim, lim_thm, thm)
  end

(* 
  Determines the limit of a function from its expansion. The two flags control whether the
  the sign of the approach should be determined for the infinite case (i.e. at_top/at_bot instead
  of just at_infinity) and the zero case (i.e. at_right 0/at_left 0 instead of just nhds 0)
*)
fun limit_of_expansion (sgn_zero, sgn_inf) ectxt (thm, basis) =
  let
    val (lim, lim_thm, thm) = limit_of_expansion_aux ectxt basis thm
  in
    case lim of
      Zero_Limit _ => (
        if sgn_zero then
          case trim_expansion false (SOME Sgn_Trim) ectxt (thm, basis) of
            (thm, IsPos, SOME pos_thm) => (Zero_Limit (SOME true),
              @{thm tendsto_imp_filterlim_at_right[OF _ expands_to_imp_eventually_pos]} OF
                [lim_thm, get_basis_wf_thm basis, thm, pos_thm])
          | (thm, IsNeg, SOME neg_thm) => (Zero_Limit (SOME false),
              @{thm tendsto_imp_filterlim_at_left[OF _ expands_to_imp_eventually_neg]} OF
                [lim_thm, get_basis_wf_thm basis, thm, neg_thm])
          | _ => (Zero_Limit NONE, lim_thm)
        else (Zero_Limit NONE, lim_thm))
    | Infinite_Limit _ => (
        if sgn_inf then
          case trim_expansion false (SOME Sgn_Trim) ectxt (thm, basis) of
            (thm, IsPos, SOME pos_thm) => (Infinite_Limit (SOME true),
              (@{thm filterlim_at_infinity_imp_filterlim_at_top[OF _ expands_to_imp_eventually_pos]} OF
                 [lim_thm, get_basis_wf_thm basis, thm, pos_thm]))
          | (thm, IsNeg, SOME neg_thm) => (Infinite_Limit (SOME false),
              @{thm filterlim_at_infinity_imp_filterlim_at_bot[OF _ expands_to_imp_eventually_neg]} OF
                [lim_thm, get_basis_wf_thm basis, thm, neg_thm])
          | _ => (Infinite_Limit NONE, lim_thm)
        else (Infinite_Limit NONE, lim_thm))
    | Finite_Limit c => (Finite_Limit c, lim_thm)
  end

fun compute_limit ectxt t =
  case expand_term ectxt t default_basis of
    (thm, basis) => limit_of_expansion (true, true) ectxt (thm, basis)

fun prove_at_infinity ectxt (thm, basis) =
  let
    fun err () = raise TERM ("prove_at_infinity", [get_expanded_fun thm])
    val (thm, _, SOME trimmed_thm) = trim_expansion true (SOME Simple_Trim) ectxt (thm, basis)
    fun go basis thm trimmed_thm =
      if fastype_of (get_expansion thm) = \<^typ>\<open>real\<close> then
        err ()
      else
        case zeroness_oracle true (SOME Pos_Trim) ectxt (get_exponent (get_expansion thm)) of
          (IsPos, SOME pos_thm) =>
            @{thm expands_to_pos_exponent_imp_filterlim} OF
              [thm, trimmed_thm, get_basis_wf_thm basis, pos_thm]
        | (IsZero, SOME zero_thm) =>
            @{thm expands_to_zero_exponent_imp_filterlim(1)} OF
              [thm, get_basis_wf_thm basis, zero_thm,
                 go (tl_basis basis) (thm RS @{thm expands_to_hd''})
                   (trimmed_thm RS @{thm trimmed_hd})]
        | _ => err ()
  in
    go basis thm trimmed_thm
  end

fun prove_at_top_at_bot mode ectxt (thm, basis) =
  let
    val s = if mode = Pos_Trim then "prove_at_top" else "prove_at_bot"
    fun err () = raise TERM (s, [get_expanded_fun thm])
    val (thm, _, SOME trimmed_thm) = trim_expansion true (SOME mode) ectxt (thm, basis)
    val trimmed_thm' = trimmed_thm RS
      (if mode = Pos_Trim then @{thm trimmed_pos_imp_trimmed} else @{thm trimmed_neg_imp_trimmed})
    fun go basis thm trimmed_thm =
      if fastype_of (get_expansion thm) = \<^typ>\<open>real\<close> then
        err ()
      else
        case zeroness_oracle true (SOME Pos_Trim) ectxt (get_exponent (get_expansion thm)) of
          (IsPos, SOME pos_thm) =>
            @{thm expands_to_pos_exponent_imp_filterlim} OF
              [thm, trimmed_thm, get_basis_wf_thm basis, pos_thm]
        | (IsZero, SOME zero_thm) =>
            @{thm expands_to_zero_exponent_imp_filterlim(1)} OF
              [thm, get_basis_wf_thm basis, zero_thm,
                 go (tl_basis basis) (thm RS @{thm expands_to_hd''})
                   (trimmed_thm RS @{thm trimmed_hd})]
        | _ => err ()
    val lim_thm = go basis thm trimmed_thm'
    val add_sign_thm =
      if mode = Pos_Trim then
        @{thm filterlim_at_infinity_imp_filterlim_at_top[OF _ expands_to_imp_eventually_pos]}
      else
        @{thm filterlim_at_infinity_imp_filterlim_at_bot[OF _ expands_to_imp_eventually_neg]}
  in
    add_sign_thm OF [lim_thm, get_basis_wf_thm basis, thm, trimmed_thm]
  end

val prove_at_top = prove_at_top_at_bot Pos_Trim
val prove_at_bot = prove_at_top_at_bot Neg_Trim


fun prove_at_aux mode ectxt (thm, basis) =
  let
    val (s, add_sign_thm) =
      case mode of
        Simple_Trim =>
          ("prove_at_0", @{thm Topological_Spaces.filterlim_atI[OF _ expands_to_imp_eventually_nz]})
      | Pos_Trim =>
          ("prove_at_right_0",
             @{thm tendsto_imp_filterlim_at_right[OF _ expands_to_imp_eventually_pos]})
      | Neg_Trim =>
          ("prove_at_left_0",
             @{thm tendsto_imp_filterlim_at_left[OF _ expands_to_imp_eventually_neg]})
    fun err () = raise TERM (s, [get_expanded_fun thm])
    val (thm, _, SOME trimmed_thm) = trim_expansion true (SOME mode) ectxt (thm, basis)
    fun go basis thm =
      if fastype_of (get_expansion thm) = \<^typ>\<open>real\<close> then
        err ()
      else
        case zeroness_oracle true (SOME Neg_Trim) ectxt (get_exponent (get_expansion thm)) of
          (IsNeg, SOME neg_thm) =>
            @{thm expands_to_neg_exponent_imp_filterlim} OF
              [thm, get_basis_wf_thm basis, neg_thm]
        | (IsZero, SOME zero_thm) =>
            @{thm expands_to_zero_exponent_imp_filterlim(2)} OF
              [thm, get_basis_wf_thm basis, zero_thm,
                 go (tl_basis basis) (thm RS @{thm expands_to_hd''})]
        | _ => err ()
    val lim_thm = go basis thm
  in
    add_sign_thm OF [lim_thm, get_basis_wf_thm basis, thm, trimmed_thm]
  end

val prove_at_0 = prove_at_aux Simple_Trim
val prove_at_left_0 = prove_at_aux Neg_Trim
val prove_at_right_0 = prove_at_aux Pos_Trim


fun prove_nhds ectxt (thm, basis) =
  let
    fun simplify (a, b, c) = (a, simplify_expansion ectxt b, c)
    fun go thm basis =
      if fastype_of (get_expansion thm) = \<^typ>\<open>real\<close> then
        @{thm expands_to_real_imp_filterlim} OF [thm]
      else
        case whnf_expansion ectxt thm |> simplify of
          (NONE, thm, _) => @{thm expands_to_MSLNil_imp_filterlim} OF [thm]
        | (SOME _, thm, _) => (
            case zeroness_oracle true (SOME Sgn_Trim) ectxt (get_exponent (get_expansion thm)) of
              (IsZero, SOME zero_thm) =>
                @{thm expands_to_zero_exponent_imp_filterlim(2)} OF
                  [thm, get_basis_wf_thm basis, zero_thm,
                    go (thm RS @{thm expands_to_hd''}) (tl_basis basis)]
            | (IsNeg, SOME neg_thm) =>
                @{thm expands_to_neg_exponent_imp_filterlim} OF
                  [thm, get_basis_wf_thm basis, neg_thm]
            | (IsPos, _) =>
                go (try_drop_leading_term ectxt thm) basis
            | _ => raise TERM ("Unexpected zeroness result in prove_nhds",
                     [get_exponent (get_expansion thm)]))
  in
    go thm basis
  end

fun prove_equivalent theta ectxt (thm1, thm2, basis) =
  let
    val ((thm1, _, SOME trimmed_thm1), (thm2, _, SOME trimmed_thm2)) =
      apply2 (trim_expansion true (SOME Simple_Trim) ectxt) ((thm1, basis), (thm2, basis))
    val pat = ConsPat (\<^const_name>\<open>Pair\<close>, [ConsPat (\<^const_name>\<open>Lazy_Eval.cmp_result.EQ\<close>, []), 
                ConsPat (\<^const_name>\<open>Pair\<close>, [AnyPat ("_", 0), AnyPat ("_", 0)])])
    val (exp1, exp2) = apply2 get_expansion (thm1, thm2)
    val T = fastype_of exp1
    val t = mk_compare_expansions_const T $ exp1 $ exp2
    fun eq_thm conv = HOLogic.mk_obj_eq (conv (Thm.cterm_of (get_ctxt ectxt) t))
    val imp_thm =
      if theta then @{thm compare_expansions_EQ_imp_bigtheta}
      else @{thm compare_expansions_EQ_same}
  in
    case match ectxt pat t (SOME []) of
      (SOME _, t, conv) =>
        let
          val [_, c1, c2] = HOLogic.strip_tuple t
          val c12_thm = if theta then [] else [the (try_prove_real_eq true ectxt (c1, c2))]
        in
          imp_thm OF ([eq_thm conv, trimmed_thm1, trimmed_thm2, thm1, thm2, get_basis_wf_thm basis] 
            @ c12_thm)
        end
    | _ => raise TERM ("prove_equivalent", map get_expanded_fun [thm1, thm2])
  end

val prove_bigtheta = prove_equivalent true
val prove_asymp_equiv = prove_equivalent false

fun print_trimming_error s ectxt exp =
  let
    val c = get_coeff exp
    val t = if fastype_of c = \<^typ>\<open>real\<close> then c else get_eval c
  in
    if #verbose (#ctxt ectxt) then
      let
        val ctxt = get_ctxt ectxt
        val p = Pretty.str "real_asymp failed to show zeroness of the following expression:"
        val p = Pretty.chunks [p, Pretty.indent 2 (Syntax.pretty_term ctxt t)]
        val _ = Pretty.writeln p
      in
        raise TERM (s, [t])
      end
    else
      raise TERM (s, [t])
  end

fun prove_smallo ectxt (thm1, thm2, basis) =
  let
    val (thm2, _, SOME trimmed_thm) = trim_expansion true (SOME Simple_Trim) ectxt (thm2, basis)
    val es = get_exponents (get_expansion thm2)
  in
    case trim_expansion_while_greater true (SOME es) false NONE ectxt (thm1, basis) of
      (thm1, Aborted LESS, thms) =>
        @{thm compare_expansions_LT} OF [prove_compare_expansions LESS (map snd thms),
          trimmed_thm, thm1, thm2, get_basis_wf_thm basis]
    | (thm1, Aborted _, _) =>
        print_trimming_error "prove_smallo" ectxt (get_expansion thm1)
    | (thm1, Trimmed _, _) =>
        print_trimming_error "prove_smallo" ectxt (get_expansion thm1)
  end

fun prove_bigo ectxt (thm1, thm2, basis) =
  let
    val (thm2, _, SOME trimmed_thm) = trim_expansion true (SOME Simple_Trim) ectxt (thm2, basis)
    val es = get_exponents (get_expansion thm2)
  in
    case trim_expansion_while_greater false (SOME es) false NONE ectxt (thm1, basis) of
      (thm1, Aborted LESS, thms) =>
        @{thm landau_o.small_imp_big[OF compare_expansions_LT]} OF
          [prove_compare_expansions LESS (map snd thms), trimmed_thm, thm1, thm2,
           get_basis_wf_thm basis]
    | (thm1, Aborted EQ, thms) =>
        @{thm compare_expansions_EQ_imp_bigo} OF [prove_compare_expansions EQ (map snd thms),
          trimmed_thm, thm1, thm2, get_basis_wf_thm basis]
    | (thm1, Trimmed _, _) =>
        print_trimming_error "prove_bigo" ectxt (get_expansion thm1)
  end


fun prove_asymptotic_relation_aux mode f ectxt (thm1, thm2, basis) = f (
  let
    val thm = @{thm expands_to_minus} OF [get_basis_wf_thm basis, thm1, thm2]
  in
    case ev_zeroness_oracle ectxt (get_expanded_fun thm) of
      SOME zero_thm => (EQUAL, zero_thm RS @{thm eventually_diff_zero_imp_eq})
    | _ => (
      case trim_expansion true (SOME mode) ectxt (thm, basis) of
        (thm, IsPos, SOME pos_thm) =>
          (GREATER, @{thm expands_to_imp_eventually_gt} OF [get_basis_wf_thm basis, thm, pos_thm])
      | (thm, IsNeg, SOME neg_thm) =>
          (LESS, @{thm expands_to_imp_eventually_lt} OF [get_basis_wf_thm basis, thm, neg_thm])
      | _ => raise TERM ("Unexpected zeroness result in prove_asymptotic_relation", []))
  end)

val prove_eventually_greater = prove_asymptotic_relation_aux Pos_Trim snd
val prove_eventually_less = prove_asymptotic_relation_aux Neg_Trim snd
val prove_asymptotic_relation = prove_asymptotic_relation_aux Sgn_Trim I

fun prove_eventually_nonzero ectxt (thm, basis) =
  case trim_expansion true (SOME Simple_Trim) ectxt (thm, basis) of
    (thm, _, SOME trimmed_thm) =>
      @{thm expands_to_imp_eventually_nz} OF [get_basis_wf_thm basis, thm, trimmed_thm]
  | _ => raise TERM ("prove_eventually_nonzero", [get_expanded_fun thm])

fun extract_terms (n, strict) ectxt basis t =
  let
    val bs = get_basis_list basis
    fun mk_constfun c = (Abs ("x", \<^typ>\<open>real\<close>, c))
    val const_0 = mk_constfun \<^term>\<open>0 :: real\<close>
    val const_1 = mk_constfun \<^term>\<open>1 :: real\<close>
    fun uminus t = Term.betapply (\<^term>\<open>\<lambda>(f::real\<Rightarrow>real) x. -f x\<close>, t)
    fun betapply2 a b c = Term.betapply (Term.betapply (a, b), c)

    fun mk_sum' [] acc = acc
      | mk_sum' ((t, sgn) :: ts) acc = mk_sum' ts (
          if sgn then
            betapply2 \<^term>\<open>%(f::real=>real) g x. f x - g x\<close> acc t
          else
            betapply2 \<^term>\<open>%(f::real=>real) g x. f x + g x\<close> acc t)
    fun mk_sum [] = const_0
      | mk_sum ((t, sgn) :: ts) = mk_sum' ts (if sgn then uminus t else t) 

    fun mk_mult a b =
      if a aconv const_0 then
        const_0
      else if b aconv const_0 then
        const_0
      else if a aconv \<^term>\<open>\<lambda>_::real. 1 :: real\<close> then
        b
      else if b aconv \<^term>\<open>\<lambda>_::real. 1 :: real\<close> then
        a
      else if a aconv \<^term>\<open>\<lambda>_::real. -1 :: real\<close> then
        Term.betapply (\<^term>\<open>\<lambda>(f::real\<Rightarrow>real) x. -f x\<close>, b)
      else if b aconv \<^term>\<open>\<lambda>_::real. -1 :: real\<close> then
        Term.betapply (\<^term>\<open>\<lambda>(f::real\<Rightarrow>real) x. -f x\<close>, a)
      else
        Abs ("x", \<^typ>\<open>real\<close>, \<^term>\<open>(*) :: real => _\<close> $
          (Term.betapply (a, Bound 0)) $ (Term.betapply (b, Bound 0)))

    fun mk_powr b e =
      if e = \<^term>\<open>0 :: real\<close> then
        const_1
      else
        let
          val n = HOLogic.dest_number e |> snd
        in
          if n >= 0 then
            Term.betapply (Term.betapply (\<^term>\<open>%(b::real=>real) e x. b x ^ e\<close>, b),
              HOLogic.mk_number \<^typ>\<open>nat\<close> n)
          else
            Term.betapply (Term.betapply (\<^term>\<open>%(b::real=>real) e x. b x powr e\<close>, b), e)
        end
      handle TERM _ =>
        Term.betapply (Term.betapply (\<^term>\<open>%(b::real=>real) e x. b x powr e\<close>, b), e)

    fun mk_scale_elem b e acc =
      let
        val e = simplify_term ectxt e
      in
        if e = \<^term>\<open>0 :: real\<close> then
          acc
        else if e = \<^term>\<open>1 :: real\<close> then
          mk_mult acc b
        else
          mk_mult acc (mk_powr b e)
      end

    fun mk_scale_elems [] _ acc = acc
      | mk_scale_elems (b :: bs) (e :: es) acc =
          mk_scale_elems bs es (mk_scale_elem b e acc)
      | mk_scale_elems _ _ _ = raise Match

    fun mk_summand c es =
      let
        val es = mk_scale_elems bs es \<^term>\<open>\<lambda>_::real. 1 :: real\<close>
      in
        case c of
          Const (\<^const_name>\<open>uminus\<close>, _) $ c => ((c, true), es)
        | _ => ((c, false), es)
      end

    fun go _ _ _ acc 0 = (acc, 0)
      | go 0 es t acc n =
          let
            val c = simplify_term ectxt t
          in
            if strict andalso c = \<^term>\<open>0 :: real\<close> then
              (acc, n)
            else
              (mk_summand c (rev es) :: acc, n - 1)
          end
      | go m es t acc n =
          case Lazy_Eval.whnf ectxt t |> fst of
            Const (\<^const_name>\<open>MS\<close>, _) $ cs $ _ =>
              go' m es (simplify_term ectxt cs) acc n
          | _ => raise TERM("extract_terms", [t])
    and go' _ _ _ acc 0 = (acc, 0)
      | go' m es cs acc n =
          case Lazy_Eval.whnf ectxt cs |> fst of
            Const (\<^const_name>\<open>MSLNil\<close>, _) => (acc, n)
          | Const (\<^const_name>\<open>MSLCons\<close>, _) $ c $ cs => (
              case Lazy_Eval.whnf ectxt c |> fst |> HOLogic.dest_prod of
                (c, e) =>
                  case go (m - 1) (e :: es) c acc n of
                   (acc, n) => go' m es (simplify_term ectxt cs) acc n)
          | _ => raise TERM("extract_terms", [t])
    val (summands, remaining) = go (basis_size basis) [] t [] (n + 1)
    val (summands, error) =
      if remaining = 0 then (rev (tl summands), SOME (snd (hd summands))) else (rev summands, NONE)
    val summands = map (fn ((c, sgn), es) => (mk_mult (mk_constfun c) es, sgn)) summands
    val error = Option.map (fn err => Term.betapply (\<^term>\<open>\<lambda>f::real\<Rightarrow>real. O(f)\<close>, err)) error
    val expansion = mk_sum summands 
  in
    (expansion, error)
  end

end


structure Multiseries_Expansion_Basic : EXPANSION_INTERFACE =
struct
open Multiseries_Expansion;

type T = expansion_thm

val expand_term = expand_term
val expand_terms = expand_terms

val prove_nhds = prove_nhds
val prove_at_infinity = prove_at_infinity
val prove_at_top = prove_at_top
val prove_at_bot = prove_at_bot
val prove_at_0 = prove_at_0
val prove_at_right_0 = prove_at_right_0
val prove_at_left_0 = prove_at_left_0
val prove_eventually_nonzero = prove_eventually_nonzero

val prove_eventually_less = prove_eventually_less
val prove_eventually_greater = prove_eventually_greater

val prove_smallo = prove_smallo
val prove_bigo = prove_bigo
val prove_bigtheta = prove_bigtheta
val prove_asymp_equiv = prove_asymp_equiv

end
