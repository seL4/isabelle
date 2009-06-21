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
  val mk_random_aux_eqs: theory -> Datatype.descr -> (string * sort) list
    -> string list -> string list * string list -> typ list * typ list
    -> string * (term list * (term * term) list)
  val ensure_random_datatype: Datatype.config -> string list -> theory -> theory
  val eval_ref: (unit -> int -> seed -> term list option * seed) option ref
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
      (Sign.mk_const thy (@{const_name Quickcheck.random}, [ty]) $ Bound i);
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

fun random_fun T1 T2 eq term_of random random_split seed =
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
    fun mk_random T = mk_const @{const_name Quickcheck.random} [T];
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
      Typecopy.get_info thy tyco;
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
local

fun dest_ctyp_nth k cT = nth (Thm.dest_ctyp cT) k;
val eq = Thm.cprop_of @{thm random_aux_rec} |> Thm.dest_arg |> Thm.dest_arg |> Thm.dest_arg;
val lhs = eq |> Thm.dest_arg1;
val pt_random_aux = lhs |> Thm.dest_fun;
val ct_k = lhs |> Thm.dest_arg;
val pt_rhs = eq |> Thm.dest_arg |> Thm.dest_fun;
val aT = pt_random_aux |> Thm.ctyp_of_term |> dest_ctyp_nth 1;

val rew_thms = map mk_meta_eq [@{thm code_numeral_zero_minus_one},
  @{thm Suc_code_numeral_minus_one}, @{thm select_weight_cons_zero}, @{thm beyond_zero}];
val rew_ts = map (Logic.dest_equals o Thm.prop_of) rew_thms;
val rew_ss = HOL_ss addsimps rew_thms;

in

fun random_aux_primrec eq lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val ((t_random_aux as Free (random_aux, T)) $ (t_k as Free (v, _)), proto_t_rhs) =
      (HOLogic.dest_eq o HOLogic.dest_Trueprop) eq;
    val Type (_, [_, iT]) = T;
    val icT = Thm.ctyp_of thy iT;
    val cert = Thm.cterm_of thy;
    val inst = Thm.instantiate_cterm ([(aT, icT)], []);
    fun subst_v t' = map_aterms (fn t as Free (w, _) => if v = w then t' else t | t => t);
    val t_rhs = lambda t_k proto_t_rhs;
    val eqs0 = [subst_v @{term "0::code_numeral"} eq, subst_v (@{term "Suc_code_numeral"} $ t_k) eq];
    val eqs1 = map (Pattern.rewrite_term thy rew_ts []) eqs0;
    val ((_, eqs2), lthy') = Primrec.add_primrec_simple
      [((Binding.name random_aux, T), NoSyn)] eqs1 lthy;
    val eq_tac = ALLGOALS (simp_tac rew_ss)
      THEN (ALLGOALS (ProofContext.fact_tac (flat eqs2)));
    val eqs3 = map (fn prop => SkipProof.prove lthy' [v] [] prop (K eq_tac)) eqs0;
    val cT_random_aux = inst pt_random_aux;
    val cT_rhs = inst pt_rhs;
    val rule = @{thm random_aux_rec}
      |> Drule.instantiate ([(aT, icT)],
           [(cT_random_aux, cert t_random_aux), (cT_rhs, cert t_rhs)])
      |> (fn thm => thm OF eqs3);
    val tac = ALLGOALS (rtac rule);
    val simp = SkipProof.prove lthy' [v] [] eq (K tac);
  in (simp, lthy') end;

end;

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
            fun tac { context = ctxt, prems = _ } =
              ALLGOALS (simp_tac (HOL_ss addsimps proj_simps))
              THEN ALLGOALS (EqSubst.eqsubst_tac ctxt [0] [aux_simp])
              THEN ALLGOALS (simp_tac (HOL_ss addsimps [fst_conv, snd_conv]));
          in (map (fn prop => SkipProof.prove lthy [v] [] prop tac) eqs, lthy) end;
      in
        lthy
        |> random_aux_primrec aux_eq'
        ||>> fold_map (LocalTheory.define Thm.definitionK) proj_defs
        |-> (fn (aux_simp, proj_defs) => prove_eqs aux_simp proj_defs)
      end;

fun random_aux_specification prefix eqs lthy =
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
        val tac = ALLGOALS (ProofContext.fact_tac ext_simps);
      in (map (fn prop => SkipProof.prove lthy vs [] prop (K tac)) eqs, lthy) end;
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

fun mk_random_aux_eqs thy descr vs tycos (names, auxnames) (Ts, Us) =
  let
    val mk_const = curry (Sign.mk_const thy);
    val i = @{term "i\<Colon>code_numeral"};
    val i1 = @{term "(i\<Colon>code_numeral) - 1"};
    val j = @{term "j\<Colon>code_numeral"};
    val seed = @{term "s\<Colon>Random.seed"};
    val random_auxN = "random_aux";
    val random_auxsN = map (prefix (random_auxN ^ "_")) (names @ auxnames);
    fun termifyT T = HOLogic.mk_prodT (T, @{typ "unit \<Rightarrow> term"});
    val rTs = Ts @ Us;
    fun random_resultT T = @{typ Random.seed}
      --> HOLogic.mk_prodT (termifyT T,@{typ Random.seed});
    val pTs = map random_resultT rTs;
    fun sizeT T = @{typ code_numeral} --> @{typ code_numeral} --> T;
    val random_auxT = sizeT o random_resultT;
    val random_auxs = map2 (fn s => fn rT => Free (s, random_auxT rT))
      random_auxsN rTs;
    fun mk_random_call T = (NONE, (HOLogic.mk_random T j, T));
    fun mk_random_aux_call fTs (k, _) (tyco, Ts) =
      let
        val T = Type (tyco, Ts);
        fun mk_random_fun_lift [] t = t
          | mk_random_fun_lift (fT :: fTs) t =
              mk_const @{const_name random_fun_lift} [fTs ---> T, fT] $
                mk_random_fun_lift fTs t;
        val t = mk_random_fun_lift fTs (nth random_auxs k $ i1 $ j);
        val size = Option.map snd (DatatypeCodegen.find_shortest_path descr k)
          |> the_default 0;
      in (SOME size, (t, fTs ---> T)) end;
    val tss = DatatypeAux.interpret_construction descr vs
      { atyp = mk_random_call, dtyp = mk_random_aux_call };
    fun mk_consexpr simpleT (c, xs) =
      let
        val (ks, simple_tTs) = split_list xs;
        val T = termifyT simpleT;
        val tTs = (map o apsnd) termifyT simple_tTs;
        val is_rec = exists is_some ks;
        val k = fold (fn NONE => I | SOME k => curry Int.max k) ks 0;
        val vs = Name.names Name.context "x" (map snd simple_tTs);
        val vs' = (map o apsnd) termifyT vs;
        val tc = HOLogic.mk_return T @{typ Random.seed}
          (HOLogic.mk_valtermify_app c vs simpleT);
        val t = HOLogic.mk_ST (map (fn (t, _) => (t, @{typ Random.seed})) tTs ~~ map SOME vs')
          tc @{typ Random.seed} (SOME T, @{typ Random.seed});
        val tk = if is_rec
          then if k = 0 then i
            else @{term "Quickcheck.beyond :: code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral"}
             $ HOLogic.mk_number @{typ code_numeral} k $ i
          else @{term "1::code_numeral"}
      in (is_rec, HOLogic.mk_prod (tk, t)) end;
    fun sort_rec xs =
      map_filter (fn (true, t) => SOME t | _ =>  NONE) xs
      @ map_filter (fn (false, t) => SOME t | _ =>  NONE) xs;
    val gen_exprss = tss
      |> (map o apfst) Type
      |> map (fn (T, cs) => (T, (sort_rec o map (mk_consexpr T)) cs));
    fun mk_select (rT, xs) =
      mk_const @{const_name Quickcheck.collapse} [@{typ "Random.seed"}, termifyT rT]
      $ (mk_const @{const_name Random.select_weight} [random_resultT rT]
        $ HOLogic.mk_list (HOLogic.mk_prodT (@{typ code_numeral}, random_resultT rT)) xs)
          $ seed;
    val auxs_lhss = map (fn t => t $ i $ j $ seed) random_auxs;
    val auxs_rhss = map mk_select gen_exprss;
    val prefix = space_implode "_" (random_auxN :: names);
  in (prefix, (random_auxs, auxs_lhss ~~ auxs_rhss)) end;

fun mk_random_datatype config descr vs tycos (names, auxnames) (Ts, Us) thy =
  let
    val _ = DatatypeAux.message config "Creating quickcheck generators ...";
    val i = @{term "i\<Colon>code_numeral"};
    val mk_prop_eq = HOLogic.mk_Trueprop o HOLogic.mk_eq;
    fun mk_size_arg k = case DatatypeCodegen.find_shortest_path descr k
     of SOME (_, l) => if l = 0 then i
          else @{term "max :: code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral"}
            $ HOLogic.mk_number @{typ code_numeral} l $ i
      | NONE => i;
    val (prefix, (random_auxs, auxs_eqs)) = (apsnd o apsnd o map) mk_prop_eq
      (mk_random_aux_eqs thy descr vs tycos (names, auxnames) (Ts, Us));
    val random_defs = map_index (fn (k, T) => mk_prop_eq
      (HOLogic.mk_random T i, nth random_auxs k $ mk_size_arg k $ i)) Ts;
  in
    thy
    |> TheoryTarget.instantiation (tycos, vs, @{sort random})
    |> random_aux_specification prefix auxs_eqs
    |> `(fn lthy => map (Syntax.check_term lthy) random_defs)
    |-> (fn random_defs' => fold_map (fn random_def =>
          Specification.definition (NONE, (Attrib.empty_binding,
            random_def))) random_defs')
    |> snd
    |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
  end;

fun perhaps_constrain thy insts raw_vs =
  let
    fun meet_random (T, sort) = Sorts.meet_sort (Sign.classes_of thy) 
      (Logic.varifyT T, sort);
    val vtab = Vartab.empty
      |> fold (fn (v, sort) => Vartab.update ((v, 0), sort)) raw_vs
      |> fold meet_random insts;
  in SOME (fn (v, _) => (v, (the o Vartab.lookup vtab) (v, 0)))
  end handle CLASS_ERROR => NONE;

fun ensure_random_datatype config raw_tycos thy =
  let
    val pp = Syntax.pp_global thy;
    val algebra = Sign.classes_of thy;
    val (descr, raw_vs, tycos, (names, auxnames), raw_TUs) =
      Datatype.the_datatype_descr thy raw_tycos;
    val random_insts = (map (rpair @{sort random}) o flat o maps snd o maps snd)
      (DatatypeAux.interpret_construction descr raw_vs { atyp = single, dtyp = (K o K o K) [] });
    val term_of_insts = (map (rpair @{sort term_of}) o flat o maps snd o maps snd)
      (DatatypeAux.interpret_construction descr raw_vs { atyp = K [], dtyp = K o K });
    val has_inst = exists (fn tyco =>
      can (Sorts.mg_domain algebra tyco) @{sort random}) tycos;
  in if has_inst then thy
    else case perhaps_constrain thy (random_insts @ term_of_insts) raw_vs
     of SOME constrain => mk_random_datatype config descr
          (map constrain raw_vs) tycos (names, auxnames)
            ((pairself o map o map_atyps) (fn TFree v => TFree (constrain v)) raw_TUs) thy
      | NONE => thy
  end;


(** setup **)

val setup = Code_Target.extend_target (target, (Code_ML.target_Eval, K I))
  #> Quickcheck.add_generator ("code", compile_generator_expr o ProofContext.theory_of)
  #> Typecopy.interpretation ensure_random_typecopy
  #> Datatype.interpretation ensure_random_datatype;

end;
