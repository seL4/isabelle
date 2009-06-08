(* Author: Florian Haftmann, TU Muenchen

Quickcheck generators for various types.
*)

signature QUICKCHECK_GENERATORS =
sig
  val compile_generator_expr: theory -> term -> int -> term list option
  type seed = Random_Engine.seed
  val random_fun: typ -> typ -> ('a -> 'a -> bool) -> ('a -> term)
    -> (seed -> ('b * (unit -> term)) * seed) -> (seed -> seed * seed)
    -> seed -> (('a -> 'b) * (unit -> Term.term)) * seed
  val ensure_random_typecopy: string -> theory -> theory
  val random_aux_specification: string -> term list -> local_theory -> local_theory
  val eval_ref: (unit -> int -> int * int -> term list option * (int * int)) option ref
  val setup: theory -> theory
end;

structure Quickcheck_Generators : QUICKCHECK_GENERATORS =
struct

(** building and compiling generator expressions **)

val eval_ref : (unit -> int -> int * int -> term list option * (int * int)) option ref = ref NONE;

val target = "Quickcheck";

fun mk_generator_expr thy prop tys =
  let
    val bound_max = length tys - 1;
    val bounds = map_index (fn (i, ty) =>
      (2 * (bound_max - i) + 1, 2 * (bound_max - i), 2 * i, ty)) tys;
    val result = list_comb (prop, map (fn (i, _, _, _) => Bound i) bounds);
    val terms = HOLogic.mk_list @{typ term} (map (fn (_, i, _, _) => Bound i $ @{term "()"}) bounds);
    val check = @{term "If :: bool => term list option => term list option => term list option"}
      $ result $ @{term "None :: term list option"} $ (@{term "Some :: term list => term list option "} $ terms);
    val return = @{term "Pair :: term list option => Random.seed => term list option * Random.seed"};
    fun liftT T sT = sT --> HOLogic.mk_prodT (T, sT);
    fun mk_termtyp ty = HOLogic.mk_prodT (ty, @{typ "unit => term"});
    fun mk_scomp T1 T2 sT f g = Const (@{const_name scomp},
      liftT T1 sT --> (T1 --> liftT T2 sT) --> liftT T2 sT) $ f $ g;
    fun mk_split ty = Sign.mk_const thy
      (@{const_name split}, [ty, @{typ "unit => term"}, liftT @{typ "term list option"} @{typ Random.seed}]);
    fun mk_scomp_split ty t t' =
      mk_scomp (mk_termtyp ty) @{typ "term list option"} @{typ Random.seed} t
        (mk_split ty $ Abs ("", ty, Abs ("", @{typ "unit => term"}, t')));
    fun mk_bindclause (_, _, i, ty) = mk_scomp_split ty
      (Sign.mk_const thy (@{const_name random}, [ty]) $ Bound i);
  in Abs ("n", @{typ code_numeral}, fold_rev mk_bindclause bounds (return $ check)) end;

fun compile_generator_expr thy t =
  let
    val tys = (map snd o fst o strip_abs) t;
    val t' = mk_generator_expr thy t tys;
    val f = Code_ML.eval (SOME target) ("Quickcheck_Generators.eval_ref", eval_ref)
      (fn proc => fn g => fn s => g s #>> (Option.map o map) proc) thy t' [];
  in f #> Random_Engine.run end;


(** typ "'a => 'b" **)

type seed = Random_Engine.seed;

fun random_fun (T1 : typ) (T2 : typ) (eq : 'a -> 'a -> bool) (term_of : 'a -> term)
    (random : seed -> ('b * (unit -> term)) * seed)
    (random_split : seed -> seed * seed)
    (seed : seed) =
  let
    val (seed', seed'') = random_split seed;
    val state = ref (seed', [], Const (@{const_name undefined}, T1 --> T2));
    val fun_upd = Const (@{const_name fun_upd},
      (T1 --> T2) --> T1 --> T2 --> T1 --> T2);
    fun random_fun' x =
      let
        val (seed, fun_map, f_t) = ! state;
      in case AList.lookup (uncurry eq) fun_map x
       of SOME y => y
        | NONE => let
              val t1 = term_of x;
              val ((y, t2), seed') = random seed;
              val fun_map' = (x, y) :: fun_map;
              val f_t' = fun_upd $ f_t $ t1 $ t2 ();
              val _ = state := (seed', fun_map', f_t');
            in y end
      end;
    fun term_fun' () = #3 (! state);
  in ((random_fun', term_fun'), seed'') end;


(** type copies **)

fun mk_random_typecopy tyco vs constr typ thy =
  let
    val Ts = map TFree vs;  
    val T = Type (tyco, Ts);
    fun mk_termifyT T = HOLogic.mk_prodT (T, @{typ "unit => term"})
    val Ttm = mk_termifyT T;
    val typtm = mk_termifyT typ;
    fun mk_const c Ts = Const (c, Sign.const_instance thy (c, Ts));
    fun mk_random T = mk_const @{const_name random} [T];
    val size = @{term "j::code_numeral"};
    val v = "x";
    val t_v = Free (v, typtm);
    val t_constr = mk_const constr Ts;
    val lhs = mk_random T $ size;
    val rhs = HOLogic.mk_ST [(((mk_random typ) $ size, @{typ Random.seed}), SOME (v, typtm))]
      (HOLogic.mk_return Ttm @{typ Random.seed}
      (mk_const "Code_Eval.valapp" [typ, T]
        $ HOLogic.mk_prod (t_constr, Abs ("u", @{typ unit}, HOLogic.reflect_term t_constr)) $ t_v))
      @{typ Random.seed} (SOME Ttm, @{typ Random.seed});
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in   
    thy
    |> TheoryTarget.instantiation ([tyco], vs, @{sort random})
    |> `(fn lthy => Syntax.check_term lthy eq)
    |-> (fn eq => Specification.definition (NONE, (Attrib.empty_binding, eq)))
    |> snd
    |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
  end;

fun ensure_random_typecopy tyco thy =
  let
    val SOME { vs = raw_vs, constr, typ = raw_typ, ... } =
      TypecopyPackage.get_info thy tyco;
    val constrain = curry (Sorts.inter_sort (Sign.classes_of thy));
    val typ = map_atyps (fn TFree (v, sort) =>
      TFree (v, constrain sort @{sort random})) raw_typ;
    val vs' = Term.add_tfreesT typ [];
    val vs = map (fn (v, sort) =>
      (v, the_default (constrain sort @{sort typerep}) (AList.lookup (op =) vs' v))) raw_vs;
    val do_inst = Sign.of_sort thy (typ, @{sort random});
  in if do_inst then mk_random_typecopy tyco vs constr typ thy else thy end;


(** datatypes **)

(* definitional scheme for random instances on datatypes *)

(*FIXME avoid this low-level proving*)
val rct = Thm.cprop_of @{thm random_aux_rec} |> Thm.dest_arg |> Thm.dest_arg
  |> Thm.dest_arg |> Thm.dest_arg1 |> Thm.dest_fun;
fun dest_ctyp_nth k cT = nth (Thm.dest_ctyp cT) k;
val aT = rct |> Thm.ctyp_of_term |> dest_ctyp_nth 1;

fun random_aux_primrec eq lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val rews = map mk_meta_eq [@{thm code_numeral_zero_minus_one},
      @{thm Suc_code_numeral_minus_one}, @{thm select_weight_cons_zero}, @{thm beyond_zero}];
    val (rt as Free (random_aux, T)) $ (vt as Free (v, _)) =
      (fst o HOLogic.dest_eq o HOLogic.dest_Trueprop) eq;
    val Type (_, [_, iT]) = T;
    val icT = Thm.ctyp_of thy iT;
    fun subst_v t' = map_aterms (fn t as Free (w, _) => if v = w then t' else t | t => t);
    val eqs0 = [subst_v @{term "0::code_numeral"} eq, subst_v (@{term "Suc_code_numeral"} $ vt) eq];
    val eqs1 = map (Pattern.rewrite_term thy (map (Logic.dest_equals o Thm.prop_of) rews) []) eqs0
    val ((_, eqs2), lthy') = PrimrecPackage.add_primrec_simple
      [((Binding.name random_aux, T), NoSyn)] eqs1 lthy;
    val eq_tac = ALLGOALS Goal.conjunction_tac THEN ALLGOALS (simp_tac (HOL_ss addsimps rews))
      THEN (ALLGOALS (ProofContext.fact_tac (flat eqs2)));
    val eqs3 = Goal.prove_multi lthy' [v] [] eqs0 (K eq_tac);
    val rct' = Thm.instantiate_cterm ([(aT, icT)], []) rct
    val rule = @{thm random_aux_rec}
      |> Drule.instantiate ([(aT, icT)], [(rct', Thm.cterm_of thy rt)])
      |> (fn thm => thm OF eqs3)
    val tac = ALLGOALS (rtac rule);
    val simp = Goal.prove lthy' [v] [] eq (K tac);
  in (simp, lthy') end;

fun random_aux_primrec_multi prefix [eq] lthy =
      lthy
      |> random_aux_primrec eq
      |>> (fn simp => [simp])
  | random_aux_primrec_multi prefix (eqs as _ :: _ :: _) lthy =
      let
        val thy = ProofContext.theory_of lthy;
        val (lhss, rhss) = map_split (HOLogic.dest_eq o HOLogic.dest_Trueprop) eqs;
        val (vs, (arg as Free (v, _)) :: _) = map_split (fn (t1 $ t2) => (t1, t2)) lhss;
        val Ts = map fastype_of lhss;
        val tupleT = foldr1 HOLogic.mk_prodT Ts;
        val aux_lhs = Free ("mutual_" ^ prefix, fastype_of arg --> tupleT) $ arg;
        val aux_eq = (HOLogic.mk_Trueprop o HOLogic.mk_eq)
          (aux_lhs, foldr1 HOLogic.mk_prod rhss);
        fun mk_proj t [T] = [t]
          | mk_proj t (Ts as T :: (Ts' as _ :: _)) =
              Const (@{const_name fst}, foldr1 HOLogic.mk_prodT Ts --> T) $ t
                :: mk_proj (Const (@{const_name snd},
                  foldr1 HOLogic.mk_prodT Ts --> foldr1 HOLogic.mk_prodT Ts') $ t) Ts';
        val projs = mk_proj (aux_lhs) Ts;
        val proj_eqs = map2 (fn v => fn proj => (v, lambda arg proj)) vs projs;
        val proj_defs = map2 (fn Free (name, _) => fn (_, rhs) =>
          ((Binding.name name, NoSyn), (Attrib.empty_binding, rhs))) vs proj_eqs;
        val aux_eq' = Pattern.rewrite_term thy proj_eqs [] aux_eq;
        fun prove_eqs aux_simp proj_defs lthy = 
          let
            val proj_simps = map (snd o snd) proj_defs;
            fun tac { context = ctxt, ... } = ALLGOALS Goal.conjunction_tac
              THEN ALLGOALS (simp_tac (HOL_ss addsimps proj_simps))
              THEN ALLGOALS (EqSubst.eqsubst_tac ctxt [0] [aux_simp])
              THEN ALLGOALS (simp_tac (HOL_ss addsimps [fst_conv, snd_conv]));
          in (Goal.prove_multi lthy [v] [] eqs tac, lthy) end;
      in
        lthy
        |> random_aux_primrec aux_eq'
        ||>> fold_map (LocalTheory.define Thm.definitionK) proj_defs
        |-> (fn (aux_simp, proj_defs) => prove_eqs aux_simp proj_defs)
      end;

fun random_aux_specification prefix eqs lthy =
  let
    val _ $ Free (v, _) $ Free (w, _) =
      (fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o hd) eqs;
    fun mk_proto_eq eq =
      let
        val (head $ arg, rhs) = (HOLogic.dest_eq o HOLogic.dest_Trueprop) eq;
      in ((HOLogic.mk_Trueprop o HOLogic.mk_eq) (head, lambda arg rhs)) end;
    val proto_eqs = map mk_proto_eq eqs;
    fun prove_simps proto_simps lthy =
      let
        val ext_simps = map (fn thm => fun_cong OF [thm]) proto_simps;
        val tac = ALLGOALS Goal.conjunction_tac
          THEN ALLGOALS (ProofContext.fact_tac ext_simps);
      in (Goal.prove_multi lthy [v, w] [] eqs (K tac), lthy) end;
    val b = Binding.qualify true prefix (Binding.name "simps");
  in
    lthy
    |> random_aux_primrec_multi prefix proto_eqs
    |-> (fn proto_simps => prove_simps proto_simps)
    |-> (fn simps => LocalTheory.note Thm.generatedK ((b,
           Code.add_default_eqn_attrib :: map (Attrib.internal o K)
          [Simplifier.simp_add, Nitpick_Const_Simp_Thms.add, Quickcheck_RecFun_Simp_Thms.add]),
            simps))
    |> snd
  end


(* constructing random instances on datatypes *)

(*still under construction*)


(** setup **)

val setup = Code_Target.extend_target (target, (Code_ML.target_Eval, K I))
  #> Quickcheck.add_generator ("code", compile_generator_expr o ProofContext.theory_of)
  #> TypecopyPackage.interpretation ensure_random_typecopy;

end;
