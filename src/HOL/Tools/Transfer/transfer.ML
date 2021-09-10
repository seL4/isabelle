(*  Title:      HOL/Tools/Transfer/transfer.ML
    Author:     Brian Huffman, TU Muenchen
    Author:     Ondrej Kuncar, TU Muenchen

Generic theorem transfer method.
*)

signature TRANSFER =
sig
  type pred_data
  val mk_pred_data: thm -> thm -> thm list -> pred_data
  val rel_eq_onp: pred_data -> thm
  val pred_def: pred_data -> thm
  val pred_simps: pred_data -> thm list
  val update_pred_simps: thm list -> pred_data -> pred_data

  val bottom_rewr_conv: thm list -> conv
  val top_rewr_conv: thm list -> conv
  val top_sweep_rewr_conv: thm list -> conv

  val prep_conv: conv
  val fold_relator_eqs_conv: Proof.context -> conv
  val unfold_relator_eqs_conv: Proof.context -> conv
  val get_transfer_raw: Proof.context -> thm list
  val get_relator_eq: Proof.context -> thm list
  val retrieve_relator_eq: Proof.context -> term -> thm list
  val get_sym_relator_eq: Proof.context -> thm list
  val get_relator_eq_raw: Proof.context -> thm list
  val get_relator_domain: Proof.context -> thm list
  val morph_pred_data: morphism -> pred_data -> pred_data
  val lookup_pred_data: Proof.context -> string -> pred_data option
  val update_pred_data: string -> pred_data -> Context.generic -> Context.generic
  val is_compound_lhs: Proof.context -> term -> bool
  val is_compound_rhs: Proof.context -> term -> bool
  val transfer_add: attribute
  val transfer_del: attribute
  val transfer_raw_add: thm -> Context.generic -> Context.generic
  val transfer_raw_del: thm -> Context.generic -> Context.generic
  val transferred_attribute: thm list -> attribute
  val untransferred_attribute: thm list -> attribute
  val prep_transfer_domain_thm: Proof.context -> thm -> thm
  val transfer_domain_add: attribute
  val transfer_domain_del: attribute
  val transfer_rule_of_term: Proof.context -> bool -> term -> thm
  val transfer_rule_of_lhs: Proof.context -> term -> thm
  val eq_tac: Proof.context -> int -> tactic
  val transfer_start_tac: bool -> Proof.context -> int -> tactic
  val transfer_prover_start_tac: Proof.context -> int -> tactic
  val transfer_step_tac: Proof.context -> int -> tactic
  val transfer_end_tac: Proof.context -> int -> tactic
  val transfer_prover_end_tac: Proof.context -> int -> tactic
  val transfer_tac: bool -> Proof.context -> int -> tactic
  val transfer_prover_tac: Proof.context -> int -> tactic
  val gen_frees_tac: (string * typ) list -> Proof.context -> int -> tactic
end

structure Transfer : TRANSFER =
struct

fun bottom_rewr_conv rewrs = Conv.bottom_conv (K (Conv.try_conv (Conv.rewrs_conv rewrs))) \<^context>
fun top_rewr_conv rewrs = Conv.top_conv (K (Conv.try_conv (Conv.rewrs_conv rewrs))) \<^context>
fun top_sweep_rewr_conv rewrs = Conv.top_sweep_conv (K (Conv.rewrs_conv rewrs)) \<^context>

(** Theory Data **)

val compound_xhs_empty_net = Item_Net.init (Thm.eq_thm_prop o apply2 snd) (single o fst);
val rewr_rules = Item_Net.init Thm.eq_thm_prop (single o fst o HOLogic.dest_eq
  o HOLogic.dest_Trueprop o Thm.concl_of);

datatype pred_data = PRED_DATA of {pred_def: thm, rel_eq_onp: thm, pred_simps: thm list}

fun mk_pred_data pred_def rel_eq_onp pred_simps = PRED_DATA {pred_def = pred_def, 
  rel_eq_onp = rel_eq_onp, pred_simps = pred_simps}

fun map_pred_data' f1 f2 f3 (PRED_DATA {pred_def, rel_eq_onp, pred_simps}) =
  PRED_DATA {pred_def = f1 pred_def, rel_eq_onp = f2 rel_eq_onp, pred_simps = f3 pred_simps}

fun rep_pred_data (PRED_DATA p) = p
val rel_eq_onp = #rel_eq_onp o rep_pred_data
val pred_def = #pred_def o rep_pred_data
val pred_simps = #pred_simps o rep_pred_data
fun update_pred_simps new_pred_data = map_pred_data' I I (K new_pred_data)


structure Data = Generic_Data
(
  type T =
    { transfer_raw : thm Item_Net.T,
      known_frees : (string * typ) list,
      compound_lhs : (term * thm) Item_Net.T,
      compound_rhs : (term * thm) Item_Net.T,
      relator_eq : thm Item_Net.T,
      relator_eq_raw : thm Item_Net.T,
      relator_domain : thm Item_Net.T,
      pred_data : pred_data Symtab.table }
  val empty =
    { transfer_raw = Thm.item_net_intro,
      known_frees = [],
      compound_lhs = compound_xhs_empty_net,
      compound_rhs = compound_xhs_empty_net,
      relator_eq = rewr_rules,
      relator_eq_raw = Thm.item_net,
      relator_domain = Thm.item_net,
      pred_data = Symtab.empty }
  val extend = I
  fun merge
    ( { transfer_raw = t1, known_frees = k1,
        compound_lhs = l1,
        compound_rhs = c1, relator_eq = r1,
        relator_eq_raw = rw1, relator_domain = rd1,
        pred_data = pd1 },
      { transfer_raw = t2, known_frees = k2,
        compound_lhs = l2,
        compound_rhs = c2, relator_eq = r2,
        relator_eq_raw = rw2, relator_domain = rd2,
        pred_data = pd2 } ) =
    { transfer_raw = Item_Net.merge (t1, t2),
      known_frees = Library.merge (op =) (k1, k2),
      compound_lhs = Item_Net.merge (l1, l2),
      compound_rhs = Item_Net.merge (c1, c2),
      relator_eq = Item_Net.merge (r1, r2),
      relator_eq_raw = Item_Net.merge (rw1, rw2),
      relator_domain = Item_Net.merge (rd1, rd2),
      pred_data = Symtab.merge (K true) (pd1, pd2) }
)

fun get_net_content f ctxt =
  Item_Net.content (f (Data.get (Context.Proof ctxt)))
  |> map (Thm.transfer' ctxt)

val get_transfer_raw = get_net_content #transfer_raw

val get_known_frees = #known_frees o Data.get o Context.Proof

fun is_compound f ctxt t =
  Item_Net.retrieve (f (Data.get (Context.Proof ctxt))) t
  |> exists (fn (pat, _) => Pattern.matches (Proof_Context.theory_of ctxt) (pat, t));

val is_compound_lhs = is_compound #compound_lhs
val is_compound_rhs = is_compound #compound_rhs

val get_relator_eq = get_net_content #relator_eq #> map safe_mk_meta_eq

fun retrieve_relator_eq ctxt t =
  Item_Net.retrieve (#relator_eq (Data.get (Context.Proof ctxt))) t
  |> map (Thm.transfer' ctxt)

val get_sym_relator_eq = get_net_content #relator_eq #> map (safe_mk_meta_eq #> Thm.symmetric)

val get_relator_eq_raw = get_net_content #relator_eq_raw

val get_relator_domain = get_net_content #relator_domain

val get_pred_data = #pred_data o Data.get o Context.Proof

fun map_data f1 f2 f3 f4 f5 f6 f7 f8
  { transfer_raw, known_frees, compound_lhs, compound_rhs,
    relator_eq, relator_eq_raw, relator_domain, pred_data } =
  { transfer_raw = f1 transfer_raw,
    known_frees = f2 known_frees,
    compound_lhs = f3 compound_lhs,
    compound_rhs = f4 compound_rhs,
    relator_eq = f5 relator_eq,
    relator_eq_raw = f6 relator_eq_raw,
    relator_domain = f7 relator_domain,
    pred_data = f8 pred_data }

fun map_transfer_raw   f = map_data f I I I I I I I
fun map_known_frees    f = map_data I f I I I I I I
fun map_compound_lhs   f = map_data I I f I I I I I
fun map_compound_rhs   f = map_data I I I f I I I I
fun map_relator_eq     f = map_data I I I I f I I I
fun map_relator_eq_raw f = map_data I I I I I f I I
fun map_relator_domain f = map_data I I I I I I f I
fun map_pred_data      f = map_data I I I I I I I f

val add_transfer_thm =
  Thm.trim_context #> (fn thm => Data.map
    (map_transfer_raw (Item_Net.update thm) o
     map_compound_lhs
       (case HOLogic.dest_Trueprop (Thm.concl_of thm) of
          Const (\<^const_name>\<open>Rel\<close>, _) $ _ $ (lhs as (_ $ _)) $ _ =>
            Item_Net.update (lhs, thm)
        | _ => I) o
     map_compound_rhs
       (case HOLogic.dest_Trueprop (Thm.concl_of thm) of
          Const (\<^const_name>\<open>Rel\<close>, _) $ _ $ _ $ (rhs as (_ $ _)) =>
            Item_Net.update (rhs, thm)
        | _ => I) o
     map_known_frees (Term.add_frees (Thm.concl_of thm))))

fun del_transfer_thm thm = Data.map
  (map_transfer_raw (Item_Net.remove thm) o
   map_compound_lhs
     (case HOLogic.dest_Trueprop (Thm.concl_of thm) of
        Const (\<^const_name>\<open>Rel\<close>, _) $ _ $ (lhs as (_ $ _)) $ _ =>
          Item_Net.remove (lhs, thm)
      | _ => I) o
   map_compound_rhs
     (case HOLogic.dest_Trueprop (Thm.concl_of thm) of
        Const (\<^const_name>\<open>Rel\<close>, _) $ _ $ _ $ (rhs as (_ $ _)) =>
          Item_Net.remove (rhs, thm)
      | _ => I))

fun transfer_raw_add thm ctxt = add_transfer_thm thm ctxt
fun transfer_raw_del thm ctxt = del_transfer_thm thm ctxt

(** Conversions **)

fun transfer_rel_conv conv =
  Conv.concl_conv ~1 (HOLogic.Trueprop_conv (Conv.fun2_conv (Conv.arg_conv conv)))

val Rel_rule = Thm.symmetric @{thm Rel_def}

fun Rel_conv ct =
  let val (cT, cT') = Thm.dest_funT (Thm.ctyp_of_cterm ct)
      val (cU, _) = Thm.dest_funT cT'
  in Thm.instantiate' [SOME cT, SOME cU] [SOME ct] Rel_rule end

(* Conversion to preprocess a transfer rule *)
fun safe_Rel_conv ct =
  Conv.try_conv (HOLogic.Trueprop_conv (Conv.fun_conv (Conv.fun_conv Rel_conv))) ct

fun prep_conv ct = (
      Conv.implies_conv safe_Rel_conv prep_conv
      else_conv
      safe_Rel_conv
      else_conv
      Conv.all_conv) ct

fun fold_relator_eqs_conv ctxt ct = (bottom_rewr_conv (get_relator_eq ctxt)) ct;
fun unfold_relator_eqs_conv ctxt ct = (top_rewr_conv (get_sym_relator_eq ctxt)) ct;


(** Replacing explicit equalities with is_equality premises **)

fun mk_is_equality t =
  Const (\<^const_name>\<open>is_equality\<close>, Term.fastype_of t --> HOLogic.boolT) $ t

fun gen_abstract_equalities ctxt (dest : term -> term * (term -> term)) thm =
  let
    val prop = Thm.prop_of thm
    val (t, mk_prop') = dest prop
    (* Only consider "(=)" at non-base types *)
    fun is_eq (Const (\<^const_name>\<open>HOL.eq\<close>, Type ("fun", [T, _]))) =
        (case T of Type (_, []) => false | _ => true)
      | is_eq _ = false
    val add_eqs = Term.fold_aterms (fn t => if is_eq t then insert (op =) t else I)
    val eq_consts = rev (add_eqs t [])
    val eqTs = map (snd o dest_Const) eq_consts
    val used = Term.add_free_names prop []
    val names = map (K "") eqTs |> Name.variant_list used
    val frees = map Free (names ~~ eqTs)
    val prems = map (HOLogic.mk_Trueprop o mk_is_equality) frees
    val prop1 = mk_prop' (Term.subst_atomic (eq_consts ~~ frees) t)
    val prop2 = fold Logic.all frees (Logic.list_implies (prems, prop1))
    val cprop = Thm.cterm_of ctxt prop2
    val equal_thm = Raw_Simplifier.rewrite ctxt false @{thms is_equality_lemma} cprop
    fun forall_elim thm = Thm.forall_elim_vars (Thm.maxidx_of thm + 1) thm
  in
    forall_elim (thm COMP (equal_thm COMP @{thm equal_elim_rule2}))
  end
    handle TERM _ => thm

fun abstract_equalities_transfer ctxt thm =
  let
    fun dest prop =
      let
        val prems = Logic.strip_imp_prems prop
        val concl = HOLogic.dest_Trueprop (Logic.strip_imp_concl prop)
        val ((rel, x), y) = apfst Term.dest_comb (Term.dest_comb concl)
      in
        (rel, fn rel' =>
          Logic.list_implies (prems, HOLogic.mk_Trueprop (rel' $ x $ y)))
      end
    val contracted_eq_thm =
      Conv.fconv_rule (transfer_rel_conv (fold_relator_eqs_conv ctxt)) thm
      handle CTERM _ => thm
  in
    gen_abstract_equalities ctxt dest contracted_eq_thm
  end

fun abstract_equalities_relator_eq ctxt rel_eq_thm =
  gen_abstract_equalities ctxt (fn x => (x, I))
    (rel_eq_thm RS @{thm is_equality_def [THEN iffD2]})

fun abstract_equalities_domain ctxt thm =
  let
    fun dest prop =
      let
        val prems = Logic.strip_imp_prems prop
        val concl = HOLogic.dest_Trueprop (Logic.strip_imp_concl prop)
        val ((eq, dom), y) = apfst Term.dest_comb (Term.dest_comb concl)
      in
        (dom, fn dom' => Logic.list_implies (prems, HOLogic.mk_Trueprop (eq $ dom' $ y)))
      end
    fun transfer_rel_conv conv =
      Conv.concl_conv ~1 (HOLogic.Trueprop_conv (Conv.arg1_conv (Conv.arg_conv conv)))
    val contracted_eq_thm =
      Conv.fconv_rule (transfer_rel_conv (fold_relator_eqs_conv ctxt)) thm
  in
    gen_abstract_equalities ctxt dest contracted_eq_thm
  end


(** Replacing explicit Domainp predicates with Domainp assumptions **)

fun mk_Domainp_assm (T, R) =
  HOLogic.mk_eq ((Const (\<^const_name>\<open>Domainp\<close>, Term.fastype_of T --> Term.fastype_of R) $ T), R)

fun fold_Domainp f (t as Const (\<^const_name>\<open>Domainp\<close>,_) $ (Var (_,_))) = f t
  | fold_Domainp f (t $ u) = fold_Domainp f t #> fold_Domainp f u
  | fold_Domainp f (Abs (_, _, t)) = fold_Domainp f t
  | fold_Domainp _ _ = I

fun subst_terms tab t =
  let
    val t' = Termtab.lookup tab t
  in
    case t' of
      SOME t' => t'
      | NONE =>
        (case t of
          u $ v => (subst_terms tab u) $ (subst_terms tab v)
          | Abs (a, T, t) => Abs (a, T, subst_terms tab t)
          | t => t)
  end

fun gen_abstract_domains ctxt (dest : term -> term * (term -> term)) thm =
  let
    val prop = Thm.prop_of thm
    val (t, mk_prop') = dest prop
    val Domainp_tms = rev (fold_Domainp (fn t => insert op= t) t [])
    val Domainp_Ts = map (snd o dest_funT o snd o dest_Const o fst o dest_comb) Domainp_tms
    val used = Term.add_free_names t []
    val rels = map (snd o dest_comb) Domainp_tms
    val rel_names = map (fst o fst o dest_Var) rels
    val names = map (fn name => ("D" ^ name)) rel_names |> Name.variant_list used
    val frees = map Free (names ~~ Domainp_Ts)
    val prems = map (HOLogic.mk_Trueprop o mk_Domainp_assm) (rels ~~ frees);
    val t' = subst_terms (fold Termtab.update (Domainp_tms ~~ frees) Termtab.empty) t
    val prop1 = fold Logic.all frees (Logic.list_implies (prems, mk_prop' t'))
    val prop2 = Logic.list_rename_params (rev names) prop1
    val cprop = Thm.cterm_of ctxt prop2
    val equal_thm = Raw_Simplifier.rewrite ctxt false @{thms Domainp_lemma} cprop
    fun forall_elim thm = Thm.forall_elim_vars (Thm.maxidx_of thm + 1) thm;
  in
    forall_elim (thm COMP (equal_thm COMP @{thm equal_elim_rule2}))
  end
  handle TERM _ => thm

fun abstract_domains_transfer ctxt thm =
  let
    fun dest prop =
      let
        val prems = Logic.strip_imp_prems prop
        val concl = HOLogic.dest_Trueprop (Logic.strip_imp_concl prop)
        val ((rel, x), y) = apfst Term.dest_comb (Term.dest_comb concl)
      in
        (x, fn x' =>
          Logic.list_implies (prems, HOLogic.mk_Trueprop (rel $ x' $ y)))
      end
  in
    gen_abstract_domains ctxt dest thm
  end

fun abstract_domains_relator_domain ctxt thm =
  let
    fun dest prop =
      let
        val prems = Logic.strip_imp_prems prop
        val concl = HOLogic.dest_Trueprop (Logic.strip_imp_concl prop)
        val ((rel, x), y) = apfst Term.dest_comb (Term.dest_comb concl)
      in
        (y, fn y' =>
          Logic.list_implies (prems, HOLogic.mk_Trueprop (rel $ x $ y')))
      end
  in
    gen_abstract_domains ctxt dest thm
  end

fun detect_transfer_rules thm =
  let
    fun is_transfer_rule tm = case (HOLogic.dest_Trueprop tm) of
      (Const (\<^const_name>\<open>HOL.eq\<close>, _)) $ ((Const (\<^const_name>\<open>Domainp\<close>, _)) $ _) $ _ => false
      | _ $ _ $ _ => true
      | _ => false
    fun safe_transfer_rule_conv ctm =
      if is_transfer_rule (Thm.term_of ctm) then safe_Rel_conv ctm else Conv.all_conv ctm
  in
    Conv.fconv_rule (Conv.prems_conv ~1 safe_transfer_rule_conv) thm
  end

(** Adding transfer domain rules **)

fun prep_transfer_domain_thm ctxt =
  abstract_equalities_domain ctxt o detect_transfer_rules

fun add_transfer_domain_thm thm ctxt =
  (add_transfer_thm o prep_transfer_domain_thm (Context.proof_of ctxt)) thm ctxt

fun del_transfer_domain_thm thm ctxt =
  (del_transfer_thm o prep_transfer_domain_thm (Context.proof_of ctxt)) thm ctxt

(** Transfer proof method **)

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
  in Const (\<^const_name>\<open>Transfer.Rel\<close>, T --> T) $ t end

fun transfer_rule_of_terms (prj : typ * typ -> typ) ctxt tab t u =
  let
    (* precondition: prj(T,U) must consist of only TFrees and type "fun" *)
    fun rel (T as Type ("fun", [T1, T2])) (U as Type ("fun", [U1, U2])) =
          let
            val r1 = rel T1 U1
            val r2 = rel T2 U2
            val rT = fastype_of r1 --> fastype_of r2 --> mk_relT (T, U)
          in
            Const (\<^const_name>\<open>rel_fun\<close>, rT) $ r1 $ r2
          end
      | rel T U =
          let
            val (a, _) = dest_TFree (prj (T, U))
          in
            Free (the (AList.lookup (op =) tab a), mk_relT (T, U))
          end
    fun zip _ thms (Bound i) (Bound _) = (nth thms i, [])
      | zip ctxt thms (Abs (x, T, t)) (Abs (y, U, u)) =
          let
            val ([x', y'], ctxt') = Variable.variant_fixes [x, y] ctxt
            val prop = mk_Rel (rel T U) $ Free (x', T) $ Free (y', U)
            val cprop = Thm.cterm_of ctxt' (HOLogic.mk_Trueprop prop)
            val thm0 = Thm.assume cprop
            val (thm1, hyps) = zip ctxt' (thm0 :: thms) t u
            val ((r1, x), y) = apfst Thm.dest_comb (Thm.dest_comb (Thm.dest_arg cprop))
            val r2 = Thm.dest_fun2 (Thm.dest_arg (Thm.cprop_of thm1))
            val (a1, (b1, _)) = apsnd Thm.dest_funT (Thm.dest_funT (Thm.ctyp_of_cterm r1))
            val (a2, (b2, _)) = apsnd Thm.dest_funT (Thm.dest_funT (Thm.ctyp_of_cterm r2))
            val tinsts = [SOME a1, SOME b1, SOME a2, SOME b2]
            val insts = [SOME (Thm.dest_arg r1), SOME (Thm.dest_arg r2)]
            val rule = Thm.instantiate' tinsts insts @{thm Rel_abs}
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
      | zip _ _ t u =
          let
            val T = fastype_of t
            val U = fastype_of u
            val prop = mk_Rel (rel T U) $ t $ u
            val cprop = Thm.cterm_of ctxt (HOLogic.mk_Trueprop prop)
          in
            (Thm.assume cprop, [cprop])
          end
    val r = mk_Rel (rel (fastype_of t) (fastype_of u))
    val goal = HOLogic.mk_Trueprop (r $ t $ u)
    val rename = Thm.trivial (Thm.cterm_of ctxt goal)
    val (thm, hyps) = zip ctxt [] t u
  in
    Drule.implies_intr_list hyps (thm RS rename)
  end

(* create a lambda term of the same shape as the given term *)
fun skeleton is_atom =
  let
    fun dummy ctxt =
      let val (c, ctxt') = yield_singleton Variable.variant_fixes "a" ctxt
      in (Free (c, dummyT), ctxt') end
    fun skel (Bound i) ctxt = (Bound i, ctxt)
      | skel (Abs (x, _, t)) ctxt =
          let val (t', ctxt) = skel t ctxt
          in (Abs (x, dummyT, t'), ctxt) end
      | skel (tu as t $ u) ctxt =
          if is_atom tu andalso not (Term.is_open tu) then dummy ctxt
          else
            let
              val (t', ctxt) = skel t ctxt
              val (u', ctxt) = skel u ctxt
            in (t' $ u', ctxt) end
      | skel _ ctxt = dummy ctxt
  in
    fn ctxt => fn t =>
      fst (skel t ctxt) |> Syntax.check_term ctxt  (* FIXME avoid syntax operation!? *)
  end

(** Monotonicity analysis **)

(* TODO: Put extensible table in theory data *)
val monotab =
  Symtab.make
    [(\<^const_name>\<open>transfer_implies\<close>, [~1, 1]),
     (\<^const_name>\<open>transfer_forall\<close>, [1])(*,
     (@{const_name implies}, [~1, 1]),
     (@{const_name All}, [1])*)]

(*
Function bool_insts determines the set of boolean-relation variables
that can be instantiated to implies, rev_implies, or iff.

Invariants: bool_insts p (t, u) requires that
  u :: _ => _ => ... => bool, and
  t is a skeleton of u
*)
fun bool_insts p (t, u) =
  let
    fun strip2 (t1 $ t2, u1 $ u2, tus) =
        strip2 (t1, u1, (t2, u2) :: tus)
      | strip2 x = x
    fun or3 ((a, b, c), (x, y, z)) = (a orelse x, b orelse y, c orelse z)
    fun go Ts p (Abs (_, T, t), Abs (_, _, u)) tab = go (T :: Ts) p (t, u) tab
      | go Ts p (t, u) tab =
        let
          val (a, _) = dest_TFree (Term.body_type (Term.fastype_of1 (Ts, t)))
          val (_, tf, tus) = strip2 (t, u, [])
          val ps_opt = case tf of Const (c, _) => Symtab.lookup monotab c | _ => NONE
          val tab1 =
            case ps_opt of
              SOME ps =>
              let
                val ps' = map (fn x => p * x) (take (length tus) ps)
              in
                fold I (map2 (go Ts) ps' tus) tab
              end
            | NONE => tab
          val tab2 = Symtab.make [(a, (p >= 0, p <= 0, is_none ps_opt))]
        in
          Symtab.join (K or3) (tab1, tab2)
        end
    val tab = go [] p (t, u) Symtab.empty
    fun f (a, (true, false, false)) = SOME (a, \<^const>\<open>implies\<close>)
      | f (a, (false, true, false)) = SOME (a, \<^const>\<open>rev_implies\<close>)
      | f (a, (true, true, _))      = SOME (a, HOLogic.eq_const HOLogic.boolT)
      | f _                         = NONE
  in
    map_filter f (Symtab.dest tab)
  end

fun transfer_rule_of_term ctxt equiv t =
  let
    val s = skeleton (is_compound_rhs ctxt) ctxt t
    val frees = map fst (Term.add_frees s [])
    val tfrees = map fst (Term.add_tfrees s [])
    fun prep a = "R" ^ Library.unprefix "'" a
    val (rnames, ctxt') = Variable.variant_fixes (map prep tfrees) ctxt
    val tab = tfrees ~~ rnames
    fun prep a = the (AList.lookup (op =) tab a)
    val thm = transfer_rule_of_terms fst ctxt' tab s t
    val binsts = bool_insts (if equiv then 0 else 1) (s, t)
    val idx = Thm.maxidx_of thm + 1
    fun tinst (a, _) = (((a, idx), \<^sort>\<open>type\<close>), \<^ctyp>\<open>bool\<close>)
    fun inst (a, t) =
      ((Name.clean_index (prep a, idx), \<^typ>\<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close>), Thm.cterm_of ctxt' t)
  in
    thm
    |> Thm.generalize (Names.make_set tfrees, Names.make_set (rnames @ frees)) idx
    |> Thm.instantiate (TVars.make (map tinst binsts), Vars.make (map inst binsts))
  end

fun transfer_rule_of_lhs ctxt t =
  let
    val s = skeleton (is_compound_lhs ctxt) ctxt t
    val frees = map fst (Term.add_frees s [])
    val tfrees = map fst (Term.add_tfrees s [])
    fun prep a = "R" ^ Library.unprefix "'" a
    val (rnames, ctxt') = Variable.variant_fixes (map prep tfrees) ctxt
    val tab = tfrees ~~ rnames
    fun prep a = the (AList.lookup (op =) tab a)
    val thm = transfer_rule_of_terms snd ctxt' tab t s
    val binsts = bool_insts 1 (s, t)
    val idx = Thm.maxidx_of thm + 1
    fun tinst (a, _) = (((a, idx), \<^sort>\<open>type\<close>), \<^ctyp>\<open>bool\<close>)
    fun inst (a, t) =
      ((Name.clean_index (prep a, idx), \<^typ>\<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close>), Thm.cterm_of ctxt' t)
  in
    thm
    |> Thm.generalize (Names.make_set tfrees, Names.make_set (rnames @ frees)) idx
    |> Thm.instantiate (TVars.make (map tinst binsts), Vars.make (map inst binsts))
  end

fun eq_rules_tac ctxt eq_rules =
  TRY o REPEAT_ALL_NEW (resolve_tac ctxt eq_rules)
  THEN_ALL_NEW resolve_tac ctxt @{thms is_equality_eq}

fun eq_tac ctxt = eq_rules_tac ctxt (get_relator_eq_raw ctxt)

fun transfer_step_tac ctxt =
  REPEAT_ALL_NEW (resolve_tac ctxt (get_transfer_raw ctxt))
  THEN_ALL_NEW (DETERM o eq_rules_tac ctxt (get_relator_eq_raw ctxt))

fun transfer_start_tac equiv ctxt i =
    let
      val pre_simps = @{thms transfer_forall_eq transfer_implies_eq}
      val start_rule =
        if equiv then @{thm transfer_start} else @{thm transfer_start'}
      val err_msg = "Transfer failed to convert goal to an object-logic formula"
      fun main_tac (t, i) =
        resolve_tac ctxt [start_rule] i THEN
        (resolve_tac ctxt [transfer_rule_of_term ctxt equiv (HOLogic.dest_Trueprop t)]) (i + 1)
          handle TERM (_, ts) => raise TERM (err_msg, ts)
    in
      EVERY
        [rewrite_goal_tac ctxt pre_simps i THEN
         SUBGOAL main_tac i]
    end;

fun transfer_prover_start_tac ctxt = SUBGOAL (fn (t, i) =>
  let
    val rhs = (snd o Term.dest_comb o HOLogic.dest_Trueprop) t
    val rule1 = transfer_rule_of_term ctxt false rhs
    val expand_eqs_in_rel_conv = transfer_rel_conv (unfold_relator_eqs_conv ctxt)
  in
    EVERY
      [CONVERSION prep_conv i,
       CONVERSION expand_eqs_in_rel_conv i,
       resolve_tac ctxt @{thms transfer_prover_start} i,
       resolve_tac ctxt [rule1] (i + 1)]
  end);

fun transfer_end_tac ctxt i =
  let
    val post_simps = @{thms transfer_forall_eq [symmetric]
      transfer_implies_eq [symmetric] transfer_bforall_unfold}
  in
    EVERY [rewrite_goal_tac ctxt post_simps i,
           Goal.norm_hhf_tac ctxt i]
  end;

fun transfer_prover_end_tac ctxt i = resolve_tac ctxt @{thms refl} i

local 
  infix 1 THEN_ALL_BUT_FIRST_NEW
  fun (tac1 THEN_ALL_BUT_FIRST_NEW tac2) i st =
    st |> (tac1 i THEN (fn st' =>
      Seq.INTERVAL tac2 (i + 1) (i + Thm.nprems_of st' - Thm.nprems_of st) st'));
in
  fun transfer_tac equiv ctxt i =
    let
      val rules = get_transfer_raw ctxt
      val eq_rules = get_relator_eq_raw ctxt
      (* allow unsolved subgoals only for standard transfer method, not for transfer' *)
      val end_tac = if equiv then K all_tac else K no_tac
  
      fun transfer_search_tac i =
        (SOLVED'
          (REPEAT_ALL_NEW (resolve_tac ctxt rules) THEN_ALL_NEW
            (DETERM o eq_rules_tac ctxt eq_rules))
          ORELSE' end_tac) i
     in
       (transfer_start_tac equiv ctxt 
        THEN_ALL_BUT_FIRST_NEW transfer_search_tac
        THEN' transfer_end_tac ctxt) i
     end

  fun transfer_prover_tac ctxt i = 
    let
      val rules = get_transfer_raw ctxt
      val eq_rules = get_relator_eq_raw ctxt
  
      fun transfer_prover_search_tac i = 
        (REPEAT_ALL_NEW (resolve_tac ctxt rules) THEN_ALL_NEW
          (DETERM o eq_rules_tac ctxt eq_rules)) i
    in
      (transfer_prover_start_tac ctxt 
       THEN_ALL_BUT_FIRST_NEW transfer_prover_search_tac
       THEN' transfer_prover_end_tac ctxt) i
    end
end;

(** Transfer attribute **)

fun transferred ctxt extra_rules thm =
  let
    val rules = extra_rules @ get_transfer_raw ctxt
    val eq_rules = get_relator_eq_raw ctxt
    val pre_simps = @{thms transfer_forall_eq transfer_implies_eq}
    val thm1 = Thm.forall_intr_vars thm
    val instT =
      rev (Term.add_tvars (Thm.full_prop_of thm1) [])
      |> map (fn v as ((a, _), S) => (v, Thm.ctyp_of ctxt (TFree (a, S))))
    val thm2 = thm1
      |> Thm.instantiate (TVars.make instT, Vars.empty)
      |> Raw_Simplifier.rewrite_rule ctxt pre_simps
    val ctxt' = Variable.declare_names (Thm.full_prop_of thm2) ctxt
    val rule = transfer_rule_of_lhs ctxt' (HOLogic.dest_Trueprop (Thm.concl_of thm2))
  in
    Goal.prove_internal ctxt' []
      (Thm.cterm_of ctxt' (HOLogic.mk_Trueprop (Var (("P", 0), \<^typ>\<open>bool\<close>))))
      (fn _ =>
        resolve_tac ctxt' [thm2 RS @{thm transfer_start'}, thm2 RS @{thm transfer_start}] 1 THEN
        (resolve_tac ctxt' [rule]
          THEN_ALL_NEW
            (SOLVED' (REPEAT_ALL_NEW (resolve_tac ctxt' rules)
              THEN_ALL_NEW (DETERM o eq_rules_tac ctxt' eq_rules)))) 1
          handle TERM (_, ts) =>
            raise TERM ("Transfer failed to convert goal to an object-logic formula", ts))
    |> Raw_Simplifier.rewrite_rule ctxt' post_simps
    |> Simplifier.norm_hhf ctxt'
    |> Drule.generalize
        (Names.make_set (map (fst o dest_TFree o Thm.typ_of o snd) instT), Names.empty)
    |> Drule.zero_var_indexes
  end
(*
    handle THM _ => thm
*)

fun untransferred ctxt extra_rules thm =
  let
    val rules = extra_rules @ get_transfer_raw ctxt
    val eq_rules = get_relator_eq_raw ctxt
    val pre_simps = @{thms transfer_forall_eq transfer_implies_eq}
    val thm1 = Thm.forall_intr_vars thm
    val instT =
      rev (Term.add_tvars (Thm.full_prop_of thm1) [])
      |> map (fn v as ((a, _), S) => (v, Thm.ctyp_of ctxt (TFree (a, S))))
    val thm2 = thm1
      |> Thm.instantiate (TVars.make instT, Vars.empty)
      |> Raw_Simplifier.rewrite_rule ctxt pre_simps
    val ctxt' = Variable.declare_names (Thm.full_prop_of thm2) ctxt
    val t = HOLogic.dest_Trueprop (Thm.concl_of thm2)
    val rule = transfer_rule_of_term ctxt' true t
  in
    Goal.prove_internal ctxt' []
      (Thm.cterm_of ctxt' (HOLogic.mk_Trueprop (Var (("P", 0), \<^typ>\<open>bool\<close>))))
      (fn _ =>
        resolve_tac ctxt' [thm2 RS @{thm untransfer_start}] 1 THEN
        (resolve_tac ctxt' [rule]
          THEN_ALL_NEW
            (SOLVED' (REPEAT_ALL_NEW (resolve_tac ctxt' rules)
              THEN_ALL_NEW (DETERM o eq_rules_tac ctxt' eq_rules)))) 1
          handle TERM (_, ts) =>
            raise TERM ("Transfer failed to convert goal to an object-logic formula", ts))
    |> Raw_Simplifier.rewrite_rule ctxt' post_simps
    |> Simplifier.norm_hhf ctxt'
    |> Drule.generalize
        (Names.make_set (map (fst o dest_TFree o Thm.typ_of o snd) instT), Names.empty)
    |> Drule.zero_var_indexes
  end

(** Methods and attributes **)

val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ Syntax.string_of_term ctxt t))

val fixing = Scan.optional (Scan.lift (Args.$$$ "fixing" -- Args.colon)
  |-- Scan.repeat free) []

val reverse_prems = fn _ => PRIMITIVE (fn thm => fold_rev (fn i => Thm.permute_prems i 1) 
    (0 upto Thm.nprems_of thm - 1) thm);
  
fun transfer_start_method equiv : (Proof.context -> Proof.method) context_parser =
  fixing >> (fn vs => fn ctxt =>
    SIMPLE_METHOD' (gen_frees_tac vs ctxt THEN' transfer_start_tac equiv ctxt
    THEN' reverse_prems));

fun transfer_method equiv : (Proof.context -> Proof.method) context_parser =
  fixing >> (fn vs => fn ctxt =>
    SIMPLE_METHOD' (gen_frees_tac vs ctxt THEN' transfer_tac equiv ctxt))

val transfer_prover_start_method : (Proof.context -> Proof.method) context_parser =
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (transfer_prover_start_tac ctxt THEN' reverse_prems))

val transfer_prover_method : (Proof.context -> Proof.method) context_parser =
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (transfer_prover_tac ctxt))

(* Attribute for transfer rules *)

fun prep_rule ctxt =
  abstract_domains_transfer ctxt o abstract_equalities_transfer ctxt o Conv.fconv_rule prep_conv

val transfer_add =
  Thm.declaration_attribute (fn thm => fn ctxt =>
    (add_transfer_thm o prep_rule (Context.proof_of ctxt)) thm ctxt)

val transfer_del =
  Thm.declaration_attribute (fn thm => fn ctxt =>
    (del_transfer_thm o prep_rule (Context.proof_of ctxt)) thm ctxt)

val transfer_attribute =
  Attrib.add_del transfer_add transfer_del

(* Attributes for transfer domain rules *)

val transfer_domain_add = Thm.declaration_attribute add_transfer_domain_thm

val transfer_domain_del = Thm.declaration_attribute del_transfer_domain_thm

val transfer_domain_attribute =
  Attrib.add_del transfer_domain_add transfer_domain_del

(* Attributes for transferred rules *)

fun transferred_attribute thms =
  Thm.rule_attribute thms (fn context => transferred (Context.proof_of context) thms)

fun untransferred_attribute thms =
  Thm.rule_attribute thms (fn context => untransferred (Context.proof_of context) thms)

val transferred_attribute_parser =
  Attrib.thms >> transferred_attribute

val untransferred_attribute_parser =
  Attrib.thms >> untransferred_attribute

fun morph_pred_data phi = 
  let
    val morph_thm = Morphism.thm phi
  in
    map_pred_data' morph_thm morph_thm (map morph_thm)
  end

fun lookup_pred_data ctxt type_name =
  Symtab.lookup (get_pred_data ctxt) type_name
  |> Option.map (morph_pred_data (Morphism.transfer_morphism' ctxt))

fun update_pred_data type_name qinfo ctxt =
  Data.map (map_pred_data (Symtab.update (type_name, qinfo))) ctxt

(* Theory setup *)

val _ =
  Theory.setup
    let
      val name = \<^binding>\<open>relator_eq\<close>
      fun add_thm thm context =
        context
        |> Data.map (map_relator_eq (Item_Net.update (Thm.trim_context thm)))
        |> Data.map (map_relator_eq_raw
            (Item_Net.update
              (Thm.trim_context (abstract_equalities_relator_eq (Context.proof_of context) thm))))
      fun del_thm thm context = context
        |> Data.map (map_relator_eq (Item_Net.remove thm))
        |> Data.map (map_relator_eq_raw
            (Item_Net.remove (abstract_equalities_relator_eq (Context.proof_of context) thm)))
      val add = Thm.declaration_attribute add_thm
      val del = Thm.declaration_attribute del_thm
      val text = "declaration of relator equality rule (used by transfer method)"
      val content = Item_Net.content o #relator_eq o Data.get
    in
      Attrib.setup name (Attrib.add_del add del) text
      #> Global_Theory.add_thms_dynamic (name, content)
    end

val _ =
  Theory.setup
    let
      val name = \<^binding>\<open>relator_domain\<close>
      fun add_thm thm context =
        let
          val thm' = thm
            |> abstract_domains_relator_domain (Context.proof_of context)
            |> Thm.trim_context
        in
          context
          |> Data.map (map_relator_domain (Item_Net.update thm'))
          |> add_transfer_domain_thm thm'
        end
      fun del_thm thm context =
        let
          val thm' = abstract_domains_relator_domain (Context.proof_of context) thm
        in
          context
          |> Data.map (map_relator_domain (Item_Net.remove thm'))
          |> del_transfer_domain_thm thm'
        end
      val add = Thm.declaration_attribute add_thm
      val del = Thm.declaration_attribute del_thm
      val text = "declaration of relator domain rule (used by transfer method)"
      val content = Item_Net.content o #relator_domain o Data.get
    in
      Attrib.setup name (Attrib.add_del add del) text
      #> Global_Theory.add_thms_dynamic (name, content)
    end

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>transfer_rule\<close> transfer_attribute
       "transfer rule for transfer method"
    #> Global_Theory.add_thms_dynamic
       (\<^binding>\<open>transfer_raw\<close>, Item_Net.content o #transfer_raw o Data.get)
    #> Attrib.setup \<^binding>\<open>transfer_domain_rule\<close> transfer_domain_attribute
       "transfer domain rule for transfer method"
    #> Attrib.setup \<^binding>\<open>transferred\<close> transferred_attribute_parser
       "raw theorem transferred to abstract theorem using transfer rules"
    #> Attrib.setup \<^binding>\<open>untransferred\<close> untransferred_attribute_parser
       "abstract theorem transferred to raw theorem using transfer rules"
    #> Global_Theory.add_thms_dynamic
       (\<^binding>\<open>relator_eq_raw\<close>, Item_Net.content o #relator_eq_raw o Data.get)
    #> Method.setup \<^binding>\<open>transfer_start\<close> (transfer_start_method true)
       "firtst step in the transfer algorithm (for debugging transfer)"
    #> Method.setup \<^binding>\<open>transfer_start'\<close> (transfer_start_method false)
       "firtst step in the transfer algorithm (for debugging transfer)"
    #> Method.setup \<^binding>\<open>transfer_prover_start\<close> transfer_prover_start_method
       "firtst step in the transfer_prover algorithm (for debugging transfer_prover)"
    #> Method.setup \<^binding>\<open>transfer_step\<close>
       (Scan.succeed (fn ctxt => SIMPLE_METHOD' (transfer_step_tac ctxt)))
       "step in the search for transfer rules (for debugging transfer and transfer_prover)"
    #> Method.setup \<^binding>\<open>transfer_end\<close>
       (Scan.succeed (fn ctxt => SIMPLE_METHOD' (transfer_end_tac ctxt)))
       "last step in the transfer algorithm (for debugging transfer)"
    #> Method.setup \<^binding>\<open>transfer_prover_end\<close>
       (Scan.succeed (fn ctxt => SIMPLE_METHOD' (transfer_prover_end_tac ctxt)))
       "last step in the transfer_prover algorithm (for debugging transfer_prover)"
    #> Method.setup \<^binding>\<open>transfer\<close> (transfer_method true)
       "generic theorem transfer method"
    #> Method.setup \<^binding>\<open>transfer'\<close> (transfer_method false)
       "generic theorem transfer method"
    #> Method.setup \<^binding>\<open>transfer_prover\<close> transfer_prover_method
       "for proving transfer rules")
end
