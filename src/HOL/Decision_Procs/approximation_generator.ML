(*  Title:      HOL/Decision_Procs/approximation_generator.ML
    Author:     Fabian Immler, TU Muenchen
*)

signature APPROXIMATION_GENERATOR =
sig
  val custom_seed: int Config.T
  val precision: int Config.T
  val epsilon: real Config.T
  val approximation_generator:
    Proof.context ->
    (term * term list) list ->
    bool -> int list -> (bool * term list) option * Quickcheck.report option
  val setup: theory -> theory
end;

structure Approximation_Generator : APPROXIMATION_GENERATOR =
struct

val custom_seed = Attrib.setup_config_int @{binding quickcheck_approximation_custom_seed} (K ~1)

val precision = Attrib.setup_config_int @{binding quickcheck_approximation_precision} (K 30)

val epsilon = Attrib.setup_config_real @{binding quickcheck_approximation_epsilon} (K 0.0)

val random_float = @{code "random_class.random::_ \<Rightarrow> _ \<Rightarrow> (float \<times> (unit \<Rightarrow> term)) \<times> _"}

fun nat_of_term t =
  (HOLogic.dest_nat t handle TERM _ => snd (HOLogic.dest_number t)
    handle TERM _ => raise TERM ("nat_of_term", [t]));

fun int_of_term t = snd (HOLogic.dest_number t) handle TERM _ => raise TERM ("int_of_term", [t]);

fun real_of_man_exp m e = Real.fromManExp {man = Real.fromInt m, exp = e}

fun mapprox_float (@{term Float} $ m $ e) = real_of_man_exp (int_of_term m) (int_of_term e)
  | mapprox_float t = Real.fromInt (snd (HOLogic.dest_number t))
      handle TERM _ => raise TERM ("mapprox_float", [t]);

(* TODO: define using compiled terms? *)
fun mapprox_floatarith (@{term Add} $ a $ b) xs = mapprox_floatarith a xs + mapprox_floatarith b xs
  | mapprox_floatarith (@{term Minus} $ a) xs = ~ (mapprox_floatarith a xs)
  | mapprox_floatarith (@{term Mult} $ a $ b) xs = mapprox_floatarith a xs * mapprox_floatarith b xs
  | mapprox_floatarith (@{term Inverse} $ a) xs = 1.0 / mapprox_floatarith a xs
  | mapprox_floatarith (@{term Cos} $ a) xs = Math.cos (mapprox_floatarith a xs)
  | mapprox_floatarith (@{term Arctan} $ a) xs = Math.atan (mapprox_floatarith a xs)
  | mapprox_floatarith (@{term Abs} $ a) xs = abs (mapprox_floatarith a xs)
  | mapprox_floatarith (@{term Max} $ a $ b) xs =
      Real.max (mapprox_floatarith a xs, mapprox_floatarith b xs)
  | mapprox_floatarith (@{term Min} $ a $ b) xs =
      Real.min (mapprox_floatarith a xs, mapprox_floatarith b xs)
  | mapprox_floatarith @{term Pi} _ = Math.pi
  | mapprox_floatarith (@{term Sqrt} $ a) xs = Math.sqrt (mapprox_floatarith a xs)
  | mapprox_floatarith (@{term Exp} $ a) xs = Math.exp (mapprox_floatarith a xs)
  | mapprox_floatarith (@{term Ln} $ a) xs = Math.ln (mapprox_floatarith a xs)
  | mapprox_floatarith (@{term Power} $ a $ n) xs =
      Math.pow (mapprox_floatarith a xs, Real.fromInt (nat_of_term n))
  | mapprox_floatarith (@{term Var} $ n) xs = nth xs (nat_of_term n)
  | mapprox_floatarith (@{term Num} $ m) _ = mapprox_float m
  | mapprox_floatarith t _ = raise TERM ("mapprox_floatarith", [t])

fun mapprox_atLeastAtMost eps x a b xs =
    let
      val x' = mapprox_floatarith x xs
    in
      mapprox_floatarith a xs + eps <= x' andalso x' + eps <= mapprox_floatarith b xs
    end

fun mapprox_form eps (@{term Bound} $ x $ a $ b $ f) xs =
    (not (mapprox_atLeastAtMost eps x a b xs)) orelse mapprox_form eps f xs
| mapprox_form eps (@{term Assign} $ x $ a $ f) xs =
    (Real.!= (mapprox_floatarith x xs, mapprox_floatarith a xs)) orelse mapprox_form eps f xs
| mapprox_form eps (@{term Less} $ a $ b) xs = mapprox_floatarith a xs + eps < mapprox_floatarith b xs
| mapprox_form eps (@{term LessEqual} $ a $ b) xs = mapprox_floatarith a xs + eps <= mapprox_floatarith b xs
| mapprox_form eps (@{term AtLeastAtMost} $ x $ a $ b) xs = mapprox_atLeastAtMost eps x a b xs
| mapprox_form eps (@{term Conj} $ f $ g) xs = mapprox_form eps f xs andalso mapprox_form eps g xs
| mapprox_form eps (@{term Disj} $ f $ g) xs = mapprox_form eps f xs orelse mapprox_form eps g xs
| mapprox_form _ t _ = raise TERM ("mapprox_form", [t])

fun dest_interpret_form (@{const "interpret_form"} $ b $ xs) = (b, xs)
  | dest_interpret_form t = raise TERM ("dest_interpret_form", [t])

fun optionT t = Type (@{type_name "option"}, [t])
fun mk_Some t = Const (@{const_name "Some"}, t --> optionT t)

fun random_float_list size xs seed =
  fold (K (apsnd (random_float size) #-> (fn c => apfst (fn b => b::c)))) xs ([],seed)

fun real_of_Float (@{code Float} (m, e)) =
    real_of_man_exp (@{code integer_of_int} m) (@{code integer_of_int} e)

fun is_True @{term True} = true
  | is_True _ = false

val postproc_form_eqs =
  @{lemma
    "real (Float 0 a) = 0"
    "real (Float (numeral m) 0) = numeral m"
    "real (Float 1 0) = 1"
    "real (Float (- 1) 0) = - 1"
    "real (Float 1 (numeral e)) = 2 ^ numeral e"
    "real (Float 1 (- numeral e)) = 1 / 2 ^ numeral e"
    "real (Float a 1) = a * 2"
    "real (Float a (-1)) = a / 2"
    "real (Float (- a) b) = - real (Float a b)"
    "real (Float (numeral m) (numeral e)) = numeral m * 2 ^ (numeral e)"
    "real (Float (numeral m) (- numeral e)) = numeral m / 2 ^ (numeral e)"
    "- (c * d::real) = -c * d"
    "- (c / d::real) = -c / d"
    "- (0::real) = 0"
    "int_of_integer (numeral k) = numeral k"
    "int_of_integer (- numeral k) = - numeral k"
    "int_of_integer 0 = 0"
    "int_of_integer 1 = 1"
    "int_of_integer (- 1) = - 1"
    by auto
  }

fun rewrite_with ctxt thms = Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps thms)
fun conv_term ctxt conv r = Thm.cterm_of ctxt r |> conv |> Thm.prop_of |> Logic.dest_equals |> snd

fun approx_random ctxt prec eps frees e xs genuine_only size seed =
  let
    val (rs, seed') = random_float_list size xs seed
    fun mk_approx_form e ts =
      @{const "approx_form"} $
        HOLogic.mk_number @{typ nat} prec $
        e $
        (HOLogic.mk_list @{typ "(float * float) option"}
          (map (fn t => mk_Some @{typ "float * float"} $ HOLogic.mk_prod (t, t)) ts)) $
        @{term "[] :: nat list"}
  in
    (if mapprox_form eps e (map (real_of_Float o fst) rs)
    then
      let
        val ts = map (fn x => snd x ()) rs
        val ts' = map
          (AList.lookup op = (map dest_Free xs ~~ ts)
            #> the_default Term.dummy
            #> curry op $ @{term "real::float\<Rightarrow>_"}
            #> conv_term ctxt (rewrite_with ctxt postproc_form_eqs))
          frees
      in
        if Approximation.approximate ctxt (mk_approx_form e ts) |> is_True
        then SOME (true, ts')
        else (if genuine_only then NONE else SOME (false, ts'))
      end
    else NONE, seed')
  end

val preproc_form_eqs =
  @{lemma
    "(a::real) \<in> {b .. c} \<longleftrightarrow> b \<le> a \<and> a \<le> c"
    "a = b \<longleftrightarrow> a \<le> b \<and> b \<le> a"
    "(p \<longrightarrow> q) \<longleftrightarrow> \<not>p \<or> q"
    "(p \<longleftrightarrow> q) \<longleftrightarrow> (p \<longrightarrow> q) \<and> (q \<longrightarrow> p)"
    "\<not> (a < b) \<longleftrightarrow> b \<le> a"
    "\<not> (a \<le> b) \<longleftrightarrow> b < a"
    "\<not> (p \<and> q) \<longleftrightarrow> \<not> p \<or> \<not> q"
    "\<not> (p \<or> q) \<longleftrightarrow> \<not> p \<and> \<not> q"
    "\<not> \<not> q \<longleftrightarrow> q"
    by auto}

val form_equations = @{thms interpret_form_equations};

fun reify_goal ctxt t =
  HOLogic.mk_not t
    |> conv_term ctxt (rewrite_with ctxt preproc_form_eqs)
    |> conv_term ctxt (Reification.conv ctxt form_equations)
    |> dest_interpret_form
    ||> HOLogic.dest_list

fun approximation_generator_raw ctxt t =
  let
    val iterations = Config.get ctxt Quickcheck.iterations
    val prec = Config.get ctxt precision
    val eps = Config.get ctxt epsilon
    val cs = Config.get ctxt custom_seed
    val seed = (Code_Numeral.natural_of_integer (cs + 1), Code_Numeral.natural_of_integer 1)
    val run = if cs < 0
      then (fn f => fn seed => (Random_Engine.run f, seed))
      else (fn f => fn seed => f seed)
    val frees = Term.add_frees t []
    val (e, xs) = reify_goal ctxt t
    fun single_tester b s =
      approx_random ctxt prec eps frees e xs b s |> run
    fun iterate _ _ 0 _ = NONE
      | iterate genuine_only size j seed =
        case single_tester genuine_only size seed of
          (NONE, seed') => iterate genuine_only size (j - 1) seed'
        | (SOME q, _) => SOME q
  in
    fn genuine_only => fn size => (iterate genuine_only size iterations seed, NONE)
  end

fun approximation_generator ctxt [(t, _)] =
  (fn genuine_only =>
    fn [_, size] =>
      approximation_generator_raw ctxt t genuine_only
        (Code_Numeral.natural_of_integer size))
  | approximation_generator _ _ =
      error "Quickcheck-approximation does not support type variables (or finite instantiations)"

val test_goals =
  Quickcheck_Common.generator_test_goal_terms
    ("approximation", (fn _ => fn _ => false, approximation_generator))

val active = Attrib.setup_config_bool @{binding quickcheck_approximation_active} (K false)

val setup = Context.theory_map (Quickcheck.add_tester ("approximation", (active, test_goals)))

end
