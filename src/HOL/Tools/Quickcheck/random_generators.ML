(*  Title:      HOL/Tools/Quickcheck/random_generators.ML
    Author:     Florian Haftmann, TU Muenchen

Random generators for various types.
*)

signature RANDOM_GENERATORS =
sig
  type seed = Random_Engine.seed
  val random_fun: typ -> typ -> ('a -> 'a -> bool) -> ('a -> term) ->
    (seed -> ('b * (unit -> term)) * seed) -> (seed -> seed * seed) ->
    seed -> (('a -> 'b) * (unit -> term)) * seed
  val compile_generator_expr: Proof.context -> (term * term list) list -> bool -> int list ->
    (bool * term list) option * Quickcheck.report option
  val put_counterexample: (unit -> Code_Numeral.natural -> bool -> Code_Numeral.natural ->
    seed -> (bool * term list) option * seed) -> Proof.context -> Proof.context
  val put_counterexample_report: (unit -> Code_Numeral.natural -> bool ->
    Code_Numeral.natural -> seed -> ((bool * term list) option * (bool list * bool)) * seed) ->
    Proof.context -> Proof.context
  val instantiate_random_datatype : Old_Datatype_Aux.config -> Old_Datatype_Aux.descr ->
    (string * sort) list -> string list -> string -> string list * string list ->
    typ list * typ list -> theory -> theory
end;

structure Random_Generators : RANDOM_GENERATORS =
struct

(** abstract syntax **)

fun termifyT T = HOLogic.mk_prodT (T, \<^typ>\<open>unit \<Rightarrow> term\<close>)
val size = \<^term>\<open>i::natural\<close>;
val size_pred = \<^term>\<open>(i::natural) - 1\<close>;
val size' = \<^term>\<open>j::natural\<close>;
val seed = \<^term>\<open>s::Random.seed\<close>;

val resultT =  \<^typ>\<open>(bool \<times> term list) option\<close>;


(** typ "'a \<Rightarrow> 'b" **)

type seed = Random_Engine.seed;

fun random_fun T1 T2 eq term_of random random_split seed =
  let
    val fun_upd = Const (\<^const_name>\<open>fun_upd\<close>, (T1 --> T2) --> T1 --> T2 --> T1 --> T2);
    val ((_, t2), seed') = random seed;
    val (seed'', seed''') = random_split seed';

    val state = Unsynchronized.ref (seed'', [], fn () => Abs ("x", T1, t2 ()));
    fun random_fun' x =
      let
        val (seed, fun_map, f_t) = ! state;
      in case AList.lookup (uncurry eq) fun_map x
       of SOME y => y
        | NONE => let
              val t1 = term_of x;
              val ((y, t2), seed') = random seed;
              val fun_map' = (x, y) :: fun_map;
              val f_t' = fn () => fun_upd $ f_t () $ t1 $ t2 ();
              val _ = state := (seed', fun_map', f_t');
            in y end
      end;
    fun term_fun' () = #3 (! state) ();
  in ((random_fun', term_fun'), seed''') end;

  
(** datatypes **)

(* definitional scheme for random instances on datatypes *)

local

val eq = Thm.cprop_of @{thm random_aux_rec} |> Thm.dest_arg |> Thm.dest_arg |> Thm.dest_arg;
val lhs = eq |> Thm.dest_arg1;
val pt_random_aux = lhs |> Thm.dest_fun;
val pt_rhs = eq |> Thm.dest_arg |> Thm.dest_fun;
val a_v =
  pt_random_aux |> Thm.ctyp_of_cterm |> Thm.dest_ctyp1
  |> Thm.typ_of |> dest_TVar;

val rew_thms = map mk_meta_eq [@{thm natural_zero_minus_one},
  @{thm Suc_natural_minus_one}, @{thm select_weight_cons_zero}, @{thm beyond_zero}];
val rew_ts = map (Logic.dest_equals o Thm.prop_of) rew_thms;
val rew_ss = simpset_of (put_simpset HOL_ss \<^context> addsimps rew_thms);

in

fun random_aux_primrec eq lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val ((t_random_aux as Free (random_aux, T)) $ (t_k as Free (v, _)), proto_t_rhs) =
      (HOLogic.dest_eq o HOLogic.dest_Trueprop) eq;
    val Type (_, [_, iT]) = T;
    val icT = Thm.ctyp_of lthy iT;
    val inst = Thm.instantiate_cterm (TVars.make [(a_v, icT)], Vars.empty);
    fun subst_v t' = map_aterms (fn t as Free (w, _) => if v = w then t' else t | t => t);
    val t_rhs = lambda t_k proto_t_rhs;
    val eqs0 = [subst_v \<^term>\<open>0::natural\<close> eq,
      subst_v \<^Const>\<open>Code_Numeral.Suc for t_k\<close> eq];
    val eqs1 = map (Pattern.rewrite_term thy rew_ts []) eqs0;
    val ((_, (_, eqs2)), lthy') = lthy
      |> BNF_LFP_Compat.primrec_simple
        [((Binding.concealed (Binding.name random_aux), T), NoSyn)] eqs1;
    val cT_random_aux = inst pt_random_aux |> Thm.term_of |> dest_Var;
    val cT_rhs = inst pt_rhs |> Thm.term_of |> dest_Var;
    val rule = @{thm random_aux_rec}
      |> Drule.instantiate_normalize
        (TVars.make [(a_v, icT)],
          Vars.make [(cT_random_aux, Thm.cterm_of lthy' t_random_aux),
           (cT_rhs, Thm.cterm_of lthy' t_rhs)]);
    fun tac ctxt =
      ALLGOALS (resolve_tac ctxt [rule])
      THEN ALLGOALS (simp_tac (put_simpset rew_ss ctxt))
      THEN (ALLGOALS (Proof_Context.fact_tac ctxt eqs2));
    val simp = Goal.prove_sorry lthy' [v] [] eq (tac o #context);
  in (simp, lthy') end;

end;

fun random_aux_primrec_multi auxname [eq] lthy =
      lthy
      |> random_aux_primrec eq
      |>> single
  | random_aux_primrec_multi auxname (eqs as _ :: _ :: _) lthy =
      let
        val thy = Proof_Context.theory_of lthy;
        val (lhss, rhss) = map_split (HOLogic.dest_eq o HOLogic.dest_Trueprop) eqs;
        val (vs, (arg as Free (v, _)) :: _) = map_split (fn (t1 $ t2) => (t1, t2)) lhss;
        val Ts = map fastype_of lhss;
        val tupleT = foldr1 HOLogic.mk_prodT Ts;
        val aux_lhs = Free ("mutual_" ^ auxname, fastype_of arg --> tupleT) $ arg;
        val aux_eq = (HOLogic.mk_Trueprop o HOLogic.mk_eq)
          (aux_lhs, foldr1 HOLogic.mk_prod rhss);
        fun mk_proj t [T] = [t]
          | mk_proj t (Ts as T :: (Ts' as _ :: _)) =
              Const (\<^const_name>\<open>fst\<close>, foldr1 HOLogic.mk_prodT Ts --> T) $ t
                :: mk_proj (Const (\<^const_name>\<open>snd\<close>,
                  foldr1 HOLogic.mk_prodT Ts --> foldr1 HOLogic.mk_prodT Ts') $ t) Ts';
        val projs = mk_proj (aux_lhs) Ts;
        val proj_eqs = map2 (fn v => fn proj => (v, lambda arg proj)) vs projs;
        val proj_defs = map2 (fn Free (name, _) => fn (_, rhs) =>
          ((Binding.concealed (Binding.name name), NoSyn),
            (apfst Binding.concealed Binding.empty_atts, rhs))) vs proj_eqs;
        val aux_eq' = Pattern.rewrite_term thy proj_eqs [] aux_eq;
        fun prove_eqs aux_simp proj_defs lthy = 
          let
            val proj_simps = map (snd o snd) proj_defs;
            fun tac { context = ctxt, prems = _ } =
              ALLGOALS (simp_tac (put_simpset HOL_ss ctxt addsimps proj_simps))
              THEN ALLGOALS (EqSubst.eqsubst_tac ctxt [0] [aux_simp])
              THEN ALLGOALS (simp_tac (put_simpset HOL_ss ctxt addsimps @{thms fst_conv snd_conv}));
          in (map (fn prop => Goal.prove_sorry lthy [v] [] prop tac) eqs, lthy) end;
      in
        lthy
        |> random_aux_primrec aux_eq'
        ||>> fold_map Local_Theory.define proj_defs
        |-> uncurry prove_eqs
      end;

fun random_aux_specification prfx name eqs lthy =
  let
    val vs = fold Term.add_free_names ((snd o strip_comb o fst o HOLogic.dest_eq
      o HOLogic.dest_Trueprop o hd) eqs) [];
    fun mk_proto_eq eq =
      let
        val (head $ t $ u, rhs) = (HOLogic.dest_eq o HOLogic.dest_Trueprop) eq;
      in ((HOLogic.mk_Trueprop o HOLogic.mk_eq) (head, lambda t (lambda u rhs))) end;
    val proto_eqs = map mk_proto_eq eqs;
    fun prove_simps proto_simps lthy =
      let
        val ext_simps = map (fn thm => fun_cong OF [fun_cong OF [thm]]) proto_simps;
        val tac = ALLGOALS (Proof_Context.fact_tac lthy ext_simps);
      in (map (fn prop => Goal.prove_sorry lthy vs [] prop (K tac)) eqs, lthy) end;
    val b = Binding.concealed (Binding.qualify true prfx
      (Binding.qualify true name (Binding.name "simps")));
  in
    lthy
    |> random_aux_primrec_multi (name ^ prfx) proto_eqs
    |-> prove_simps
    |-> (fn simps => Local_Theory.note
          ((b, @{attributes [simp, nitpick_simp]}), simps))
    |-> (fn (_, thms) => Code.declare_default_eqns (map (rpair true) thms))
  end


(* constructing random instances on datatypes *)

val random_auxN = "random_aux";

fun mk_random_aux_eqs thy descr vs (names, auxnames) (Ts, Us) =
  let
    val mk_const = curry (Sign.mk_const thy);
    val random_auxsN = map (prefix (random_auxN ^ "_")) (names @ auxnames);
    val rTs = Ts @ Us;
    fun random_resultT T = \<^typ>\<open>Random.seed\<close>
      --> HOLogic.mk_prodT (termifyT T,\<^typ>\<open>Random.seed\<close>);
    fun sizeT T = \<^typ>\<open>natural\<close> --> \<^typ>\<open>natural\<close> --> T;
    val random_auxT = sizeT o random_resultT;
    val random_auxs = map2 (fn s => fn rT => Free (s, random_auxT rT))
      random_auxsN rTs;
    fun mk_random_call T = (NONE, (HOLogic.mk_random T size', T));
    fun mk_random_aux_call fTs (k, _) (tyco, Ts) =
      let
        val T = Type (tyco, Ts);
        fun mk_random_fun_lift [] t = t
          | mk_random_fun_lift (fT :: fTs) t =
              mk_const \<^const_name>\<open>random_fun_lift\<close> [fTs ---> T, fT] $
                mk_random_fun_lift fTs t;
        val t = mk_random_fun_lift fTs (nth random_auxs k $ size_pred $ size');
        val size = Option.map snd (Old_Datatype_Aux.find_shortest_path descr k)
          |> the_default 0;
      in (SOME size, (t, fTs ---> T)) end;
    val tss = Old_Datatype_Aux.interpret_construction descr vs
      { atyp = mk_random_call, dtyp = mk_random_aux_call };
    fun mk_consexpr simpleT (c, xs) =
      let
        val (ks, simple_tTs) = split_list xs;
        val T = termifyT simpleT;
        val tTs = (map o apsnd) termifyT simple_tTs;
        val is_rec = exists is_some ks;
        val k = fold (fn NONE => I | SOME k => Integer.max k) ks 0;
        val vs = Name.invent_names Name.context "x" (map snd simple_tTs);
        val tc = HOLogic.mk_return T \<^typ>\<open>Random.seed\<close>
          (HOLogic.mk_valtermify_app c vs simpleT);
        val t = HOLogic.mk_ST
          (map2 (fn (t, _) => fn (v, T') => ((t, \<^typ>\<open>Random.seed\<close>), SOME ((v, termifyT T')))) tTs vs)
            tc \<^typ>\<open>Random.seed\<close> (SOME T, \<^typ>\<open>Random.seed\<close>);
        val tk = if is_rec
          then if k = 0 then size
            else \<^term>\<open>Quickcheck_Random.beyond :: natural \<Rightarrow> natural \<Rightarrow> natural\<close>
             $ HOLogic.mk_number \<^typ>\<open>natural\<close> k $ size
          else \<^term>\<open>1::natural\<close>
      in (is_rec, HOLogic.mk_prod (tk, t)) end;
    fun sort_rec xs =
      map_filter (fn (true, t) => SOME t | _ =>  NONE) xs
      @ map_filter (fn (false, t) => SOME t | _ =>  NONE) xs;
    val gen_exprss = tss
      |> (map o apfst) Type
      |> map (fn (T, cs) => (T, (sort_rec o map (mk_consexpr T)) cs));
    fun mk_select (rT, xs) =
      mk_const \<^const_name>\<open>Quickcheck_Random.collapse\<close> [\<^typ>\<open>Random.seed\<close>, termifyT rT]
      $ (mk_const \<^const_name>\<open>Random.select_weight\<close> [random_resultT rT]
        $ HOLogic.mk_list (HOLogic.mk_prodT (\<^typ>\<open>natural\<close>, random_resultT rT)) xs)
          $ seed;
    val auxs_lhss = map (fn t => t $ size $ size' $ seed) random_auxs;
    val auxs_rhss = map mk_select gen_exprss;
  in (random_auxs, auxs_lhss ~~ auxs_rhss) end;

fun instantiate_random_datatype config descr vs tycos prfx (names, auxnames) (Ts, Us) thy =
  let
    val _ = Old_Datatype_Aux.message config "Creating quickcheck generators ...";
    val mk_prop_eq = HOLogic.mk_Trueprop o HOLogic.mk_eq;
    fun mk_size_arg k = case Old_Datatype_Aux.find_shortest_path descr k
     of SOME (_, l) => if l = 0 then size
          else \<^term>\<open>max :: natural \<Rightarrow> natural \<Rightarrow> natural\<close>
            $ HOLogic.mk_number \<^typ>\<open>natural\<close> l $ size
      | NONE => size;
    val (random_auxs, auxs_eqs) = (apsnd o map) mk_prop_eq
      (mk_random_aux_eqs thy descr vs (names, auxnames) (Ts, Us));
    val random_defs = map_index (fn (k, T) => mk_prop_eq
      (HOLogic.mk_random T size, nth random_auxs k $ mk_size_arg k $ size)) Ts;
  in
    thy
    |> Class.instantiation (tycos, vs, \<^sort>\<open>random\<close>)
    |> random_aux_specification prfx random_auxN auxs_eqs
    |> `(fn lthy => map (Syntax.check_term lthy) random_defs)
    |-> (fn random_defs' => fold_map (fn random_def =>
          Specification.definition NONE [] []
            ((Binding.concealed Binding.empty, []), random_def)) random_defs')
    |> snd
    |> Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac ctxt [])
  end;


(** building and compiling generator expressions **)

structure Data = Proof_Data
(
  type T =
    (unit -> Code_Numeral.natural -> bool -> Code_Numeral.natural -> seed ->
      (bool * term list) option * seed) *
    (unit -> Code_Numeral.natural -> bool -> Code_Numeral.natural -> seed ->
      ((bool * term list) option * (bool list * bool)) * seed);
  val empty: T =
   (fn () => raise Fail "counterexample",
    fn () => raise Fail "counterexample_report");
  fun init _ = empty;
);

val get_counterexample = #1 o Data.get;
val get_counterexample_report = #2 o Data.get;

val put_counterexample = Data.map o @{apply 2(1)} o K;
val put_counterexample_report = Data.map o @{apply 2(2)} o K;

val target = "Quickcheck";

fun mk_generator_expr ctxt (t, _) =
  let  
    val thy = Proof_Context.theory_of ctxt
    val prop = fold_rev absfree (Term.add_frees t []) t
    val Ts = (map snd o fst o strip_abs) prop
    val bound_max = length Ts - 1;
    val bounds = map_index (fn (i, ty) =>
      (2 * (bound_max - i) + 1, 2 * (bound_max - i), 2 * i, ty)) Ts;
    val result = list_comb (prop, map (fn (i, _, _, _) => Bound i) bounds);
    val terms = HOLogic.mk_list \<^typ>\<open>term\<close> (map (fn (_, i, _, _) => Bound i $ \<^term>\<open>()\<close>) bounds);
    val ([genuine_only_name], _) = Variable.variant_fixes ["genuine_only"] ctxt
    val genuine_only = Free (genuine_only_name, \<^typ>\<open>bool\<close>)
    val none_t = Const (\<^const_name>\<open>None\<close>, resultT)
    val check = Quickcheck_Common.mk_safe_if genuine_only none_t (result, none_t,
      fn genuine => \<^term>\<open>Some :: bool \<times> term list => (bool \<times> term list) option\<close> $
        HOLogic.mk_prod (Quickcheck_Common.reflect_bool genuine, terms))
    val return = HOLogic.pair_const resultT \<^typ>\<open>Random.seed\<close>;
    fun liftT T sT = sT --> HOLogic.mk_prodT (T, sT);
    fun mk_termtyp T = HOLogic.mk_prodT (T, \<^typ>\<open>unit \<Rightarrow> term\<close>);
    fun mk_scomp T1 T2 sT f g = Const (\<^const_name>\<open>scomp\<close>,
      liftT T1 sT --> (T1 --> liftT T2 sT) --> liftT T2 sT) $ f $ g;
    fun mk_case_prod T = Sign.mk_const thy
      (\<^const_name>\<open>case_prod\<close>, [T, \<^typ>\<open>unit \<Rightarrow> term\<close>, liftT resultT \<^typ>\<open>Random.seed\<close>]);
    fun mk_scomp_split T t t' =
      mk_scomp (mk_termtyp T) resultT \<^typ>\<open>Random.seed\<close> t
        (mk_case_prod T $ Abs ("", T, Abs ("", \<^typ>\<open>unit => term\<close>, t')));
    fun mk_bindclause (_, _, i, T) = mk_scomp_split T
      (Sign.mk_const thy (\<^const_name>\<open>Quickcheck_Random.random\<close>, [T]) $ Bound i);
  in
    lambda genuine_only
      (Abs ("n", \<^typ>\<open>natural\<close>, fold_rev mk_bindclause bounds (return $ check true)))
  end;

fun mk_reporting_generator_expr ctxt (t, _) =
  let
    val thy = Proof_Context.theory_of ctxt
    val resultT = \<^typ>\<open>(bool \<times> term list) option \<times> (bool list \<times> bool)\<close>
    val prop = fold_rev absfree (Term.add_frees t []) t
    val Ts = (map snd o fst o strip_abs) prop
    val bound_max = length Ts - 1
    val bounds = map_index (fn (i, ty) =>
      (2 * (bound_max - i) + 1, 2 * (bound_max - i), 2 * i, ty)) Ts;
    val prop' = betapplys (prop, map (fn (i, _, _, _) => Bound i) bounds);
    val terms = HOLogic.mk_list \<^typ>\<open>term\<close> (map (fn (_, i, _, _) => Bound i $ \<^term>\<open>()\<close>) bounds)
    val (assms, concl) = Quickcheck_Common.strip_imp prop'
    val return = HOLogic.pair_const resultT \<^typ>\<open>Random.seed\<close>;
    fun mk_assms_report i =
      HOLogic.mk_prod (\<^term>\<open>None :: (bool \<times> term list) option\<close>,
        HOLogic.mk_prod (HOLogic.mk_list HOLogic.boolT
          (replicate i \<^term>\<open>True\<close> @ replicate (length assms - i) \<^term>\<open>False\<close>),
        \<^term>\<open>False\<close>))
    fun mk_concl_report b =
      HOLogic.mk_prod (HOLogic.mk_list HOLogic.boolT (replicate (length assms) \<^term>\<open>True\<close>),
        Quickcheck_Common.reflect_bool b)
    val ([genuine_only_name], _) = Variable.variant_fixes ["genuine_only"] ctxt
    val genuine_only = Free (genuine_only_name, \<^typ>\<open>bool\<close>)
    val none_t = HOLogic.mk_prod (\<^term>\<open>None :: (bool \<times> term list) option\<close>, mk_concl_report true)
    val concl_check = Quickcheck_Common.mk_safe_if genuine_only none_t (concl, none_t,
      fn genuine => HOLogic.mk_prod (\<^term>\<open>Some :: bool \<times> term list => (bool \<times> term list) option\<close> $
        HOLogic.mk_prod (Quickcheck_Common.reflect_bool genuine, terms), mk_concl_report false))
    val check = fold_rev (fn (i, assm) => fn t => Quickcheck_Common.mk_safe_if genuine_only
      (mk_assms_report i) (HOLogic.mk_not assm, mk_assms_report i, t))
      (map_index I assms) concl_check
    fun liftT T sT = sT --> HOLogic.mk_prodT (T, sT);
    fun mk_termtyp T = HOLogic.mk_prodT (T, \<^typ>\<open>unit \<Rightarrow> term\<close>);
    fun mk_scomp T1 T2 sT f g = Const (\<^const_name>\<open>scomp\<close>,
      liftT T1 sT --> (T1 --> liftT T2 sT) --> liftT T2 sT) $ f $ g;
    fun mk_case_prod T = Sign.mk_const thy
      (\<^const_name>\<open>case_prod\<close>, [T, \<^typ>\<open>unit \<Rightarrow> term\<close>, liftT resultT \<^typ>\<open>Random.seed\<close>]);
    fun mk_scomp_split T t t' =
      mk_scomp (mk_termtyp T) resultT \<^typ>\<open>Random.seed\<close> t
        (mk_case_prod T $ Abs ("", T, Abs ("", \<^typ>\<open>unit \<Rightarrow> term\<close>, t')));
    fun mk_bindclause (_, _, i, T) = mk_scomp_split T
      (Sign.mk_const thy (\<^const_name>\<open>Quickcheck_Random.random\<close>, [T]) $ Bound i);
  in
    lambda genuine_only
      (Abs ("n", \<^typ>\<open>natural\<close>, fold_rev mk_bindclause bounds (return $ check true)))
  end

val mk_parametric_generator_expr = Quickcheck_Common.gen_mk_parametric_generator_expr 
  ((mk_generator_expr, 
    absdummy \<^typ>\<open>bool\<close> (absdummy \<^typ>\<open>natural\<close>
      \<^term>\<open>Pair None :: Random.seed \<Rightarrow> (bool \<times> term list) option \<times> Random.seed\<close>)),
    \<^typ>\<open>bool \<Rightarrow> natural \<Rightarrow> Random.seed \<Rightarrow> (bool \<times> term list) option \<times> Random.seed\<close>)

val mk_parametric_reporting_generator_expr = Quickcheck_Common.gen_mk_parametric_generator_expr 
  ((mk_reporting_generator_expr,
    absdummy \<^typ>\<open>bool\<close> (absdummy \<^typ>\<open>natural\<close>
      \<^term>\<open>Pair (None, ([], False)) :: Random.seed \<Rightarrow>
        ((bool \<times> term list) option \<times> (bool list \<times> bool)) \<times> Random.seed\<close>)),
    \<^typ>\<open>bool \<Rightarrow> natural \<Rightarrow> Random.seed \<Rightarrow> ((bool \<times> term list) option \<times> (bool list \<times> bool)) \<times> Random.seed\<close>)
    
    
(* single quickcheck report *)

datatype single_report = Run of bool list * bool | MatchExc

fun collect_single_report single_report
    (Quickcheck.Report {iterations = iterations, raised_match_errors = raised_match_errors,
    satisfied_assms = satisfied_assms, positive_concl_tests = positive_concl_tests}) =
  case single_report
  of MatchExc =>
    Quickcheck.Report {iterations = iterations + 1, raised_match_errors = raised_match_errors + 1,
      satisfied_assms = satisfied_assms, positive_concl_tests = positive_concl_tests}
   | Run (assms, concl) =>
    Quickcheck.Report {iterations = iterations + 1, raised_match_errors = raised_match_errors,
      satisfied_assms =
        map2 (fn b => fn s => if b then s + 1 else s) assms
         (if null satisfied_assms then replicate (length assms) 0 else satisfied_assms),
      positive_concl_tests = if concl then positive_concl_tests + 1 else positive_concl_tests}

val empty_report = Quickcheck.Report { iterations = 0, raised_match_errors = 0,
  satisfied_assms = [], positive_concl_tests = 0 }
    
fun compile_generator_expr_raw ctxt ts =
  let
    val iterations = Config.get ctxt Quickcheck.iterations
  in
    if Config.get ctxt Quickcheck.report then
      let
        val t' = mk_parametric_reporting_generator_expr ctxt ts;
        val compile =
          Code_Runtime.dynamic_value_strict
            (get_counterexample_report, put_counterexample_report,
              "Random_Generators.put_counterexample_report")
            ctxt (SOME target)
            (fn proc => fn g => fn c => fn b => fn s =>
              g c b s #>> (apfst o Option.map o apsnd o map) proc)
            t' [];
        fun single_tester c b s = compile c b s |> Random_Engine.run
        fun iterate_and_collect _ _ 0 report = (NONE, report)
          | iterate_and_collect genuine_only (card, size) j report =
            let
              val (test_result, single_report) = apsnd Run (single_tester card genuine_only size)
              val report = collect_single_report single_report report
            in
              case test_result of NONE => iterate_and_collect genuine_only (card, size) (j - 1) report
                | SOME q => (SOME q, report)
            end
      in
        fn genuine_only => fn [card, size] =>
          apsnd SOME (iterate_and_collect genuine_only (card, size) iterations empty_report)
      end
    else
      let
        val t' = mk_parametric_generator_expr ctxt ts;
        val compile =
          Code_Runtime.dynamic_value_strict
            (get_counterexample, put_counterexample, "Random_Generators.put_counterexample")
            ctxt (SOME target)
            (fn proc => fn g => fn c => fn b => fn s =>
              g c b s #>> (Option.map o apsnd o map) proc)
            t' [];
        fun single_tester c b s = compile c b s |> Random_Engine.run
        fun iterate _ _ 0 = NONE
          | iterate genuine_only (card, size) j =
            case single_tester card genuine_only size of
              NONE => iterate genuine_only (card, size) (j - 1)
            | SOME q => SOME q
      in
        fn genuine_only => fn [card, size] =>
          (rpair NONE (iterate genuine_only (card, size) iterations))
      end
  end;

fun compile_generator_expr ctxt ts =
  let
    val compiled = compile_generator_expr_raw ctxt ts
  in fn genuine_only => fn [card, size] =>
    compiled genuine_only [Code_Numeral.natural_of_integer card, Code_Numeral.natural_of_integer size]
  end;

val size_types = [\<^type_name>\<open>Enum.finite_1\<close>, \<^type_name>\<open>Enum.finite_2\<close>,
  \<^type_name>\<open>Enum.finite_3\<close>, \<^type_name>\<open>Enum.finite_4\<close>, \<^type_name>\<open>Enum.finite_5\<close>];

fun size_matters_for _ Ts =
  not (forall (fn Type (tyco, []) => member (op =) size_types tyco | _ => false) Ts);

val test_goals =
  Quickcheck_Common.generator_test_goal_terms ("random", (size_matters_for, compile_generator_expr));

  
(** setup **)

val active = Attrib.setup_config_bool \<^binding>\<open>quickcheck_random_active\<close> (K false);

val _ =
  Theory.setup
   (Quickcheck_Common.datatype_interpretation \<^plugin>\<open>quickcheck_random\<close>
      (\<^sort>\<open>random\<close>, instantiate_random_datatype) #>
    Context.theory_map (Quickcheck.add_tester ("random", (active, test_goals))));

end;
