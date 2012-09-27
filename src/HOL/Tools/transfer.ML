(*  Title:      HOL/Tools/transfer.ML
    Author:     Brian Huffman, TU Muenchen

Generic theorem transfer method.
*)

signature TRANSFER =
sig
  val prep_conv: conv
  val get_relator_eq: Proof.context -> thm list
  val get_sym_relator_eq: Proof.context -> thm list
  val transfer_add: attribute
  val transfer_del: attribute
  val transfer_rule_of_term: Proof.context -> term -> thm
  val transfer_tac: bool -> Proof.context -> int -> tactic
  val transfer_prover_tac: Proof.context -> int -> tactic
  val setup: theory -> theory
end

structure Transfer : TRANSFER =
struct

(** Theory Data **)

structure Data = Generic_Data
(
  type T =
    { transfer_raw : thm Item_Net.T,
      known_frees : (string * typ) list,
      compound_rhs : unit Net.net,
      relator_eq : thm Item_Net.T }
  val empty =
    { transfer_raw = Thm.full_rules,
      known_frees = [],
      compound_rhs = Net.empty,
      relator_eq = Thm.full_rules }
  val extend = I
  fun merge
    ( { transfer_raw = t1, known_frees = k1,
        compound_rhs = c1, relator_eq = r1},
      { transfer_raw = t2, known_frees = k2,
        compound_rhs = c2, relator_eq = r2}) =
    { transfer_raw = Item_Net.merge (t1, t2),
      known_frees = Library.merge (op =) (k1, k2),
      compound_rhs = Net.merge (K true) (c1, c2),
      relator_eq = Item_Net.merge (r1, r2) }
)

fun get_relator_eq ctxt = ctxt
  |> (Item_Net.content o #relator_eq o Data.get o Context.Proof)
  |> map safe_mk_meta_eq

fun get_sym_relator_eq ctxt = ctxt
  |> (Item_Net.content o #relator_eq o Data.get o Context.Proof)
  |> map (Thm.symmetric o safe_mk_meta_eq)

fun get_transfer_raw ctxt = ctxt
  |> (Item_Net.content o #transfer_raw o Data.get o Context.Proof)

fun get_known_frees ctxt = ctxt
  |> (#known_frees o Data.get o Context.Proof)

fun get_compound_rhs ctxt = ctxt
  |> (#compound_rhs o Data.get o Context.Proof)

fun map_data f1 f2 f3 f4
  { transfer_raw, known_frees, compound_rhs, relator_eq } =
  { transfer_raw = f1 transfer_raw,
    known_frees = f2 known_frees,
    compound_rhs = f3 compound_rhs,
    relator_eq = f4 relator_eq }

fun map_transfer_raw f = map_data f I I I
fun map_known_frees f = map_data I f I I
fun map_compound_rhs f = map_data I I f I
fun map_relator_eq f = map_data I I I f

fun add_transfer_thm thm = Data.map
  (map_transfer_raw (Item_Net.update thm) o
   map_compound_rhs
     (case HOLogic.dest_Trueprop (Thm.concl_of thm) of
        _ $ _ $ (rhs as (_ $ _)) => Net.insert_term (K true) (rhs, ())
      | _ => I) o
   map_known_frees (Term.add_frees (Thm.concl_of thm)))

fun del_transfer_thm thm = Data.map (map_transfer_raw (Item_Net.remove thm))

val relator_eq_setup =
  let
    val name = @{binding relator_eq}
    fun add_thm thm = Data.map (map_relator_eq (Item_Net.update thm))
    fun del_thm thm = Data.map (map_relator_eq (Item_Net.remove thm))
    val add = Thm.declaration_attribute add_thm
    val del = Thm.declaration_attribute del_thm
    val text = "declaration of relator equality rule (used by transfer method)"
    val content = Item_Net.content o #relator_eq o Data.get
  in
    Attrib.setup name (Attrib.add_del add del) text
    #> Global_Theory.add_thms_dynamic (name, content)
  end

(** Conversions **)

val Rel_rule = Thm.symmetric @{thm Rel_def}

fun dest_funcT cT =
  (case Thm.dest_ctyp cT of [T, U] => (T, U)
    | _ => raise TYPE ("dest_funcT", [Thm.typ_of cT], []))

fun Rel_conv ct =
  let val (cT, cT') = dest_funcT (Thm.ctyp_of_term ct)
      val (cU, _) = dest_funcT cT'
  in Drule.instantiate' [SOME cT, SOME cU] [SOME ct] Rel_rule end

fun Trueprop_conv cv ct =
  (case Thm.term_of ct of
    Const (@{const_name Trueprop}, _) $ _ => Conv.arg_conv cv ct
  | _ => raise CTERM ("Trueprop_conv", [ct]))

(* Conversion to preprocess a transfer rule *)
fun prep_conv ct = (
      Conv.implies_conv Conv.all_conv prep_conv
      else_conv
      Trueprop_conv (Conv.fun_conv (Conv.fun_conv Rel_conv))
      else_conv
      Conv.all_conv) ct

(** Transfer proof method **)

fun RelT (Const (@{const_name Rel}, _) $ _ $ _ $ y) = fastype_of y
  | RelT t = raise TERM ("RelT", [t])

(* Tactic to correspond a value to itself *)
fun eq_tac ctxt = SUBGOAL (fn (t, i) =>
  let
    val T = RelT (HOLogic.dest_Trueprop (Logic.strip_assums_concl t))
    val cT = ctyp_of (Proof_Context.theory_of ctxt) T
    val rews = get_sym_relator_eq ctxt
    val thm1 = Drule.instantiate' [SOME cT] [] @{thm Rel_eq_refl}
    val thm2 = Raw_Simplifier.rewrite_rule rews thm1
  in
    rtac thm2 i
  end handle Match => no_tac | TERM _ => no_tac)

val post_simps =
  @{thms transfer_forall_eq [symmetric]
    transfer_implies_eq [symmetric] transfer_bforall_unfold}

fun gen_frees_tac keepers ctxt = SUBGOAL (fn (t, i) =>
  let
    val keepers = keepers @ get_known_frees ctxt
    val vs = rev (Term.add_frees t [])
    val vs' = filter_out (member (op =) keepers) vs
  in
    Induct.arbitrary_tac ctxt 0 vs' i
  end)

fun mk_relT (T, U) = T --> U --> HOLogic.boolT

fun mk_Rel t =
  let val T = fastype_of t
  in Const (@{const_name Transfer.Rel}, T --> T) $ t end

fun transfer_rule_of_terms ctxt tab t u =
  let
    val thy = Proof_Context.theory_of ctxt
    (* precondition: T must consist of only TFrees and function space *)
    fun rel (T as TFree (a, _)) U =
          Free (the (AList.lookup (op =) tab a), mk_relT (T, U))
      | rel (T as Type ("fun", [T1, T2])) (U as Type ("fun", [U1, U2])) =
        let
          val r1 = rel T1 U1
          val r2 = rel T2 U2
          val rT = fastype_of r1 --> fastype_of r2 --> mk_relT (T, U)
        in
          Const (@{const_name fun_rel}, rT) $ r1 $ r2
        end
      | rel T U = raise TYPE ("rel", [T, U], [])
    fun zip _ thms (Bound i) (Bound _) = (nth thms i, [])
      | zip ctxt thms (Abs (x, T, t)) (Abs (y, U, u)) =
        let
          val ([x', y'], ctxt') = Variable.variant_fixes [x, y] ctxt
          val prop = mk_Rel (rel T U) $ Free (x', T) $ Free (y', U)
          val cprop = Thm.cterm_of thy (HOLogic.mk_Trueprop prop)
          val thm0 = Thm.assume cprop
          val (thm1, hyps) = zip ctxt' (thm0 :: thms) t u
          val ((r1, x), y) = apfst Thm.dest_comb (Thm.dest_comb (Thm.dest_arg cprop))
          val r2 = Thm.dest_fun2 (Thm.dest_arg (cprop_of thm1))
          val (a1, (b1, _)) = apsnd dest_funcT (dest_funcT (ctyp_of_term r1))
          val (a2, (b2, _)) = apsnd dest_funcT (dest_funcT (ctyp_of_term r2))
          val tinsts = [SOME a1, SOME b1, SOME a2, SOME b2]
          val insts = [SOME (Thm.dest_arg r1), SOME (Thm.dest_arg r2)]
          val rule = Drule.instantiate' tinsts insts @{thm Rel_abs}
          val thm2 = Thm.forall_intr x (Thm.forall_intr y (Thm.implies_intr cprop thm1))
        in
          (thm2 COMP rule, hyps)
        end
      | zip ctxt thms (f $ t) (g $ u) =
        let
          val (thm1, hyps1) = zip ctxt thms f g
          val (thm2, hyps2) = zip ctxt thms t u
        in
          (thm2 RS (thm1 RS @{thm Rel_app}), hyps1 @ hyps2)
        end
      | zip _ _ (t as Free (_, T)) u =
        let
          val U = fastype_of u
          val prop = mk_Rel (rel T U) $ t $ u
          val cprop = Thm.cterm_of thy (HOLogic.mk_Trueprop prop)
        in
          (Thm.assume cprop, [cprop])
        end
      | zip _ _ t u = raise TERM ("zip_relterm", [t, u])
    val r = mk_Rel (rel (fastype_of t) (fastype_of u))
    val goal = HOLogic.mk_Trueprop (r $ t $ u)
    val rename = Thm.trivial (cterm_of thy goal)
    val (thm, hyps) = zip ctxt [] t u
  in
    Drule.implies_intr_list hyps (thm RS rename)
  end

fun transfer_rule_of_term ctxt t =
  let
    val compound_rhs = get_compound_rhs ctxt
    val is_rhs = not o null o Net.unify_term compound_rhs
    fun dummy ctxt =
      let
        val (c, ctxt) = yield_singleton Variable.variant_fixes "a" ctxt
      in
        (Free (c, dummyT), ctxt)
      end
    (* create a lambda term of the same shape as the given term *)
    fun skeleton (Bound i) ctxt = (Bound i, ctxt)
      | skeleton (Abs (x, _, t)) ctxt =
        let
          val (t', ctxt) = skeleton t ctxt
        in
          (Abs (x, dummyT, t'), ctxt)
        end
      | skeleton (tu as (t $ u)) ctxt =
        if is_rhs tu then dummy ctxt else
        let
          val (t', ctxt) = skeleton t ctxt
          val (u', ctxt) = skeleton u ctxt
        in
          (t' $ u', ctxt)
        end
      | skeleton _ ctxt = dummy ctxt
    val s = skeleton t ctxt |> fst |> Syntax.check_term ctxt |>
      map_types (map_type_tfree (fn (a, _) => TFree (a, HOLogic.typeS)))
    val frees = map fst (Term.add_frees s [])
    val tfrees = map fst (Term.add_tfrees s [])
    fun prep a = "R" ^ Library.unprefix "'" a
    val (rnames, ctxt') = Variable.variant_fixes (map prep tfrees) ctxt
    val thm = transfer_rule_of_terms ctxt' (tfrees ~~ rnames) s t
  in
    Thm.generalize (tfrees, rnames @ frees) (Thm.maxidx_of thm + 1) thm
  end

fun transfer_tac equiv ctxt i =
  let
    val pre_simps = @{thms transfer_forall_eq transfer_implies_eq}
    val start_rule = 
      if equiv then @{thm transfer_start} else @{thm transfer_start'}
    val rules = get_transfer_raw ctxt
    (* allow unsolved subgoals only for standard transfer method, not for transfer' *)
    val end_tac = if equiv then K all_tac else K no_tac
  in
    EVERY
      [rewrite_goal_tac pre_simps i THEN
       SUBGOAL (fn (t, i) =>
         rtac start_rule i THEN
         (rtac (transfer_rule_of_term ctxt (HOLogic.dest_Trueprop t))
           THEN_ALL_NEW
             (SOLVED' (REPEAT_ALL_NEW (resolve_tac rules))
               ORELSE' eq_tac ctxt ORELSE' end_tac)) (i + 1)) i,
       (* FIXME: rewrite_goal_tac does unwanted eta-contraction *)
       rewrite_goal_tac post_simps i,
       rtac @{thm _} i]
  end

fun transfer_prover_tac ctxt = SUBGOAL (fn (t, i) =>
  let
    val rhs = (snd o Term.dest_comb o HOLogic.dest_Trueprop) t
    val rule1 = transfer_rule_of_term ctxt rhs
    val rules = get_transfer_raw ctxt
  in
    EVERY
      [CONVERSION prep_conv i,
       rtac @{thm transfer_prover_start} i,
       (rtac rule1 THEN_ALL_NEW
         REPEAT_ALL_NEW
           (resolve_tac rules ORELSE' eq_tac ctxt)) (i+1),
       rtac @{thm refl} i]
  end)

(** Methods and attributes **)

val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ Syntax.string_of_term ctxt t))

val fixing = Scan.optional (Scan.lift (Args.$$$ "fixing" -- Args.colon)
  |-- Scan.repeat free) []

fun transfer_method equiv : (Proof.context -> Method.method) context_parser =
  fixing >> (fn vs => fn ctxt =>
    SIMPLE_METHOD' (gen_frees_tac vs ctxt THEN' transfer_tac equiv ctxt))

val transfer_prover_method : (Proof.context -> Method.method) context_parser =
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (transfer_prover_tac ctxt))

(* Attribute for transfer rules *)

val prep_rule = Conv.fconv_rule prep_conv

val transfer_add =
  Thm.declaration_attribute (add_transfer_thm o prep_rule)

val transfer_del =
  Thm.declaration_attribute (del_transfer_thm o prep_rule)

val transfer_attribute =
  Attrib.add_del transfer_add transfer_del

(* Theory setup *)

val setup =
  relator_eq_setup
  #> Attrib.setup @{binding transfer_rule} transfer_attribute
     "transfer rule for transfer method"
  #> Global_Theory.add_thms_dynamic
     (@{binding transfer_raw}, Item_Net.content o #transfer_raw o Data.get)
  #> Method.setup @{binding transfer} (transfer_method true)
     "generic theorem transfer method"
  #> Method.setup @{binding transfer'} (transfer_method false)
     "generic theorem transfer method"
  #> Method.setup @{binding transfer_prover} transfer_prover_method
     "for proving transfer rules"

end
