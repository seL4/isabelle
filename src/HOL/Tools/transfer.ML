(*  Title:      HOL/Tools/transfer.ML
    Author:     Brian Huffman, TU Muenchen
    Author:     Ondrej Kuncar, TU Muenchen

Generic theorem transfer method.
*)

signature TRANSFER =
sig
  val bottom_rewr_conv: thm list -> conv
  val top_rewr_conv: thm list -> conv

  val prep_conv: conv
  val get_transfer_raw: Proof.context -> thm list
  val get_relator_eq_item_net: Proof.context -> thm Item_Net.T
  val get_relator_eq: Proof.context -> thm list
  val get_sym_relator_eq: Proof.context -> thm list
  val get_relator_eq_raw: Proof.context -> thm list
  val get_relator_domain: Proof.context -> thm list
  val get_compound_lhs: Proof.context -> (term * thm) Item_Net.T
  val get_compound_rhs: Proof.context -> (term * thm) Item_Net.T
  val transfer_add: attribute
  val transfer_del: attribute
  val transfer_raw_add: thm -> Context.generic -> Context.generic
  val transfer_raw_del: thm -> Context.generic -> Context.generic
  val transferred_attribute: thm list -> attribute
  val untransferred_attribute: thm list -> attribute
  val transfer_domain_add: attribute
  val transfer_domain_del: attribute
  val transfer_rule_of_term: Proof.context -> bool -> term -> thm
  val transfer_rule_of_lhs: Proof.context -> term -> thm
  val transfer_tac: bool -> Proof.context -> int -> tactic
  val transfer_prover_tac: Proof.context -> int -> tactic
  val gen_frees_tac: (string * typ) list -> Proof.context -> int -> tactic
  val setup: theory -> theory
end

structure Transfer : TRANSFER =
struct

(** Theory Data **)

val compound_xhs_empty_net = Item_Net.init (Thm.eq_thm_prop o pairself snd) (single o fst);
val rewr_rules = Item_Net.init Thm.eq_thm_prop (single o fst o HOLogic.dest_eq 
  o HOLogic.dest_Trueprop o Thm.concl_of);

structure Data = Generic_Data
(
  type T =
    { transfer_raw : thm Item_Net.T,
      known_frees : (string * typ) list,
      compound_lhs : (term * thm) Item_Net.T,
      compound_rhs : (term * thm) Item_Net.T,
      relator_eq : thm Item_Net.T,
      relator_eq_raw : thm Item_Net.T,
      relator_domain : thm Item_Net.T }
  val empty =
    { transfer_raw = Thm.intro_rules,
      known_frees = [],
      compound_lhs = compound_xhs_empty_net,
      compound_rhs = compound_xhs_empty_net,
      relator_eq = rewr_rules,
      relator_eq_raw = Thm.full_rules,
      relator_domain = Thm.full_rules }
  val extend = I
  fun merge
    ( { transfer_raw = t1, known_frees = k1,
        compound_lhs = l1,
        compound_rhs = c1, relator_eq = r1,
        relator_eq_raw = rw1, relator_domain = rd1 },
      { transfer_raw = t2, known_frees = k2,
        compound_lhs = l2,
        compound_rhs = c2, relator_eq = r2,
        relator_eq_raw = rw2, relator_domain = rd2 } ) =
    { transfer_raw = Item_Net.merge (t1, t2),
      known_frees = Library.merge (op =) (k1, k2),
      compound_lhs = Item_Net.merge (l1, l2),
      compound_rhs = Item_Net.merge (c1, c2),
      relator_eq = Item_Net.merge (r1, r2),
      relator_eq_raw = Item_Net.merge (rw1, rw2),
      relator_domain = Item_Net.merge (rd1, rd2) }
)

fun get_transfer_raw ctxt = ctxt
  |> (Item_Net.content o #transfer_raw o Data.get o Context.Proof)

fun get_known_frees ctxt = ctxt
  |> (#known_frees o Data.get o Context.Proof)

fun get_compound_lhs ctxt = ctxt
  |> (#compound_lhs o Data.get o Context.Proof)

fun get_compound_rhs ctxt = ctxt
  |> (#compound_rhs o Data.get o Context.Proof)

fun get_relator_eq_item_net ctxt = (#relator_eq o Data.get o Context.Proof) ctxt

fun get_relator_eq ctxt = ctxt
  |> (Item_Net.content o #relator_eq o Data.get o Context.Proof)
  |> map safe_mk_meta_eq

fun get_sym_relator_eq ctxt = ctxt
  |> (Item_Net.content o #relator_eq o Data.get o Context.Proof)
  |> map (Thm.symmetric o safe_mk_meta_eq)

fun get_relator_eq_raw ctxt = ctxt
  |> (Item_Net.content o #relator_eq_raw o Data.get o Context.Proof)

fun get_relator_domain ctxt = ctxt
  |> (Item_Net.content o #relator_domain o Data.get o Context.Proof)

fun map_data f1 f2 f3 f4 f5 f6 f7
  { transfer_raw, known_frees, compound_lhs, compound_rhs,
    relator_eq, relator_eq_raw, relator_domain } =
  { transfer_raw = f1 transfer_raw,
    known_frees = f2 known_frees,
    compound_lhs = f3 compound_lhs,
    compound_rhs = f4 compound_rhs,
    relator_eq = f5 relator_eq,
    relator_eq_raw = f6 relator_eq_raw,
    relator_domain = f7 relator_domain }

fun map_transfer_raw   f = map_data f I I I I I I
fun map_known_frees    f = map_data I f I I I I I
fun map_compound_lhs   f = map_data I I f I I I I
fun map_compound_rhs   f = map_data I I I f I I I
fun map_relator_eq     f = map_data I I I I f I I
fun map_relator_eq_raw f = map_data I I I I I f I
fun map_relator_domain f = map_data I I I I I I f

fun add_transfer_thm thm = Data.map
  (map_transfer_raw (Item_Net.update thm) o
   map_compound_lhs
     (case HOLogic.dest_Trueprop (Thm.concl_of thm) of
        Const (@{const_name Rel}, _) $ _ $ (lhs as (_ $ _)) $ _ =>
          Item_Net.update (lhs, thm)
      | _ => I) o
   map_compound_rhs
     (case HOLogic.dest_Trueprop (Thm.concl_of thm) of
        Const (@{const_name Rel}, _) $ _ $ _ $ (rhs as (_ $ _)) =>
          Item_Net.update (rhs, thm)
      | _ => I) o
   map_known_frees (Term.add_frees (Thm.concl_of thm)))

fun del_transfer_thm thm = Data.map 
  (map_transfer_raw (Item_Net.remove thm) o
   map_compound_lhs
     (case HOLogic.dest_Trueprop (Thm.concl_of thm) of
        Const (@{const_name Rel}, _) $ _ $ (lhs as (_ $ _)) $ _ =>
          Item_Net.remove (lhs, thm)
      | _ => I) o
   map_compound_rhs
     (case HOLogic.dest_Trueprop (Thm.concl_of thm) of
        Const (@{const_name Rel}, _) $ _ $ _ $ (rhs as (_ $ _)) =>
          Item_Net.remove (rhs, thm)
      | _ => I))

fun transfer_raw_add thm ctxt = add_transfer_thm thm ctxt
fun transfer_raw_del thm ctxt = del_transfer_thm thm ctxt

(** Conversions **)

fun bottom_rewr_conv rewrs = Conv.bottom_conv (K (Conv.try_conv (Conv.rewrs_conv rewrs))) @{context}
fun top_rewr_conv rewrs = Conv.top_conv (K (Conv.try_conv (Conv.rewrs_conv rewrs))) @{context}

fun transfer_rel_conv conv = 
  Conv.concl_conv ~1 (HOLogic.Trueprop_conv (Conv.fun2_conv (Conv.arg_conv conv)))

val Rel_rule = Thm.symmetric @{thm Rel_def}

fun dest_funcT cT =
  (case Thm.dest_ctyp cT of [T, U] => (T, U)
    | _ => raise TYPE ("dest_funcT", [Thm.typ_of cT], []))

fun Rel_conv ct =
  let val (cT, cT') = dest_funcT (Thm.ctyp_of_term ct)
      val (cU, _) = dest_funcT cT'
  in Drule.instantiate' [SOME cT, SOME cU] [SOME ct] Rel_rule end

(* Conversion to preprocess a transfer rule *)
fun safe_Rel_conv ct =
  Conv.try_conv (HOLogic.Trueprop_conv (Conv.fun_conv (Conv.fun_conv Rel_conv))) ct

fun prep_conv ct = (
      Conv.implies_conv safe_Rel_conv prep_conv
      else_conv
      safe_Rel_conv
      else_conv
      Conv.all_conv) ct

(** Replacing explicit equalities with is_equality premises **)

fun mk_is_equality t =
  Const (@{const_name is_equality}, Term.fastype_of t --> HOLogic.boolT) $ t

val is_equality_lemma =
  @{lemma "(!!R. is_equality R ==> PROP (P R)) == PROP (P (op =))"
    by (unfold is_equality_def, rule, drule meta_spec,
      erule meta_mp, rule refl, simp)}

fun gen_abstract_equalities ctxt (dest : term -> term * (term -> term)) thm =
  let
    val thy = Thm.theory_of_thm thm
    val prop = Thm.prop_of thm
    val (t, mk_prop') = dest prop
    (* Only consider "op =" at non-base types *)
    fun is_eq (Const (@{const_name HOL.eq}, Type ("fun", [T, _]))) =
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
    val cprop = Thm.cterm_of thy prop2
    val equal_thm = Raw_Simplifier.rewrite ctxt false [is_equality_lemma] cprop
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
      Conv.fconv_rule (transfer_rel_conv (bottom_rewr_conv (get_relator_eq ctxt))) thm
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
      Conv.fconv_rule (transfer_rel_conv (bottom_rewr_conv (get_relator_eq ctxt))) thm
  in
    gen_abstract_equalities ctxt dest contracted_eq_thm
  end 


(** Replacing explicit Domainp predicates with Domainp assumptions **)

fun mk_Domainp_assm (T, R) =
  HOLogic.mk_eq ((Const (@{const_name Domainp}, Term.fastype_of T --> Term.fastype_of R) $ T), R)

val Domainp_lemma =
  @{lemma "(!!R. Domainp T = R ==> PROP (P R)) == PROP (P (Domainp T))"
    by (rule, drule meta_spec,
      erule meta_mp, rule refl, simp)}

fun fold_Domainp f (t as Const (@{const_name Domainp},_) $ (Var (_,_))) = f t
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
    val thy = Thm.theory_of_thm thm
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
    val cprop = Thm.cterm_of thy prop2
    val equal_thm = Raw_Simplifier.rewrite ctxt false [Domainp_lemma] cprop
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

fun detect_transfer_rules thm =
  let
    fun is_transfer_rule tm = case (HOLogic.dest_Trueprop tm) of
      (Const (@{const_name HOL.eq}, _)) $ ((Const (@{const_name Domainp}, _)) $ _) $ _ => false
      | _ $ _ $ _ => true
      | _ => false
    fun safe_transfer_rule_conv ctm =
      if is_transfer_rule (term_of ctm) then safe_Rel_conv ctm else Conv.all_conv ctm
  in
    Conv.fconv_rule (Conv.prems_conv ~1 safe_transfer_rule_conv) thm
  end

(** Adding transfer domain rules **)

fun add_transfer_domain_thm thm ctxt = 
  (add_transfer_thm o abstract_equalities_domain (Context.proof_of ctxt) o detect_transfer_rules) thm ctxt

fun del_transfer_domain_thm thm ctxt = 
  (del_transfer_thm o abstract_equalities_domain (Context.proof_of ctxt) o detect_transfer_rules) thm ctxt

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
  in Const (@{const_name Transfer.Rel}, T --> T) $ t end

fun transfer_rule_of_terms (prj : typ * typ -> typ) ctxt tab t u =
  let
    val thy = Proof_Context.theory_of ctxt
    (* precondition: prj(T,U) must consist of only TFrees and type "fun" *)
    fun rel (T as Type ("fun", [T1, T2])) (U as Type ("fun", [U1, U2])) =
        let
          val r1 = rel T1 U1
          val r2 = rel T2 U2
          val rT = fastype_of r1 --> fastype_of r2 --> mk_relT (T, U)
        in
          Const (@{const_name fun_rel}, rT) $ r1 $ r2
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
      | zip _ _ t u =
        let
          val T = fastype_of t
          val U = fastype_of u
          val prop = mk_Rel (rel T U) $ t $ u
          val cprop = Thm.cterm_of thy (HOLogic.mk_Trueprop prop)
        in
          (Thm.assume cprop, [cprop])
        end
    val r = mk_Rel (rel (fastype_of t) (fastype_of u))
    val goal = HOLogic.mk_Trueprop (r $ t $ u)
    val rename = Thm.trivial (cterm_of thy goal)
    val (thm, hyps) = zip ctxt [] t u
  in
    Drule.implies_intr_list hyps (thm RS rename)
  end

(* create a lambda term of the same shape as the given term *)
fun skeleton (is_atom : term -> bool) ctxt t =
  let
    fun dummy ctxt =
      let
        val (c, ctxt) = yield_singleton Variable.variant_fixes "a" ctxt
      in
        (Free (c, dummyT), ctxt)
      end
    fun go (Bound i) ctxt = (Bound i, ctxt)
      | go (Abs (x, _, t)) ctxt =
        let
          val (t', ctxt) = go t ctxt
        in
          (Abs (x, dummyT, t'), ctxt)
        end
      | go (tu as (t $ u)) ctxt =
        if is_atom tu andalso not (Term.is_open tu) then dummy ctxt else
        let
          val (t', ctxt) = go t ctxt
          val (u', ctxt) = go u ctxt
        in
          (t' $ u', ctxt)
        end
      | go _ ctxt = dummy ctxt
  in
    go t ctxt |> fst |> Syntax.check_term ctxt |>
      map_types (map_type_tfree (fn (a, _) => TFree (a, HOLogic.typeS)))
  end

(** Monotonicity analysis **)

(* TODO: Put extensible table in theory data *)
val monotab =
  Symtab.make
    [(@{const_name transfer_implies}, [~1, 1]),
     (@{const_name transfer_forall}, [1])(*,
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
    fun f (a, (true, false, false)) = SOME (a, @{const implies})
      | f (a, (false, true, false)) = SOME (a, @{const rev_implies})
      | f (a, (true, true, _))      = SOME (a, HOLogic.eq_const HOLogic.boolT)
      | f _                         = NONE
  in
    map_filter f (Symtab.dest tab)
  end

fun retrieve_terms t net = map fst (Item_Net.retrieve net t)
  
fun matches_list ctxt term = 
  is_some o find_first (fn pat => Pattern.matches (Proof_Context.theory_of ctxt) (pat, term))

fun transfer_rule_of_term ctxt equiv t : thm =
  let
    val compound_rhs = get_compound_rhs ctxt
    fun is_rhs t = compound_rhs |> retrieve_terms t |> matches_list ctxt t
    val s = skeleton is_rhs ctxt t
    val frees = map fst (Term.add_frees s [])
    val tfrees = map fst (Term.add_tfrees s [])
    fun prep a = "R" ^ Library.unprefix "'" a
    val (rnames, ctxt') = Variable.variant_fixes (map prep tfrees) ctxt
    val tab = tfrees ~~ rnames
    fun prep a = the (AList.lookup (op =) tab a)
    val thm = transfer_rule_of_terms fst ctxt' tab s t
    val binsts = bool_insts (if equiv then 0 else 1) (s, t)
    val cbool = @{ctyp bool}
    val relT = @{typ "bool => bool => bool"}
    val idx = Thm.maxidx_of thm + 1
    val thy = Proof_Context.theory_of ctxt
    fun tinst (a, _) = (ctyp_of thy (TVar ((a, idx), HOLogic.typeS)), cbool)
    fun inst (a, t) = (cterm_of thy (Var (Name.clean_index (prep a, idx), relT)), cterm_of thy t)
  in
    thm
      |> Thm.generalize (tfrees, rnames @ frees) idx
      |> Thm.instantiate (map tinst binsts, map inst binsts)
  end

fun transfer_rule_of_lhs ctxt t : thm =
  let
    val compound_lhs = get_compound_lhs ctxt
    fun is_lhs t = compound_lhs |> retrieve_terms t |> matches_list ctxt t
    val s = skeleton is_lhs ctxt t
    val frees = map fst (Term.add_frees s [])
    val tfrees = map fst (Term.add_tfrees s [])
    fun prep a = "R" ^ Library.unprefix "'" a
    val (rnames, ctxt') = Variable.variant_fixes (map prep tfrees) ctxt
    val tab = tfrees ~~ rnames
    fun prep a = the (AList.lookup (op =) tab a)
    val thm = transfer_rule_of_terms snd ctxt' tab t s
    val binsts = bool_insts 1 (s, t)
    val cbool = @{ctyp bool}
    val relT = @{typ "bool => bool => bool"}
    val idx = Thm.maxidx_of thm + 1
    val thy = Proof_Context.theory_of ctxt
    fun tinst (a, _) = (ctyp_of thy (TVar ((a, idx), HOLogic.typeS)), cbool)
    fun inst (a, t) = (cterm_of thy (Var (Name.clean_index (prep a, idx), relT)), cterm_of thy t)
  in
    thm
      |> Thm.generalize (tfrees, rnames @ frees) idx
      |> Thm.instantiate (map tinst binsts, map inst binsts)
  end

fun eq_tac eq_rules = TRY o REPEAT_ALL_NEW (resolve_tac eq_rules) THEN_ALL_NEW rtac @{thm is_equality_eq}

fun transfer_tac equiv ctxt i =
  let
    val pre_simps = @{thms transfer_forall_eq transfer_implies_eq}
    val start_rule =
      if equiv then @{thm transfer_start} else @{thm transfer_start'}
    val rules = get_transfer_raw ctxt
    val eq_rules = get_relator_eq_raw ctxt
    (* allow unsolved subgoals only for standard transfer method, not for transfer' *)
    val end_tac = if equiv then K all_tac else K no_tac
    val err_msg = "Transfer failed to convert goal to an object-logic formula"
    fun main_tac (t, i) =
      rtac start_rule i THEN
      (rtac (transfer_rule_of_term ctxt equiv (HOLogic.dest_Trueprop t))
        THEN_ALL_NEW
          (SOLVED' (REPEAT_ALL_NEW (resolve_tac rules) THEN_ALL_NEW (DETERM o eq_tac eq_rules))
            ORELSE' end_tac)) (i + 1)
        handle TERM (_, ts) => raise TERM (err_msg, ts)
  in
    EVERY
      [rewrite_goal_tac ctxt pre_simps i THEN
       SUBGOAL main_tac i,
       (* FIXME: rewrite_goal_tac does unwanted eta-contraction *)
       rewrite_goal_tac ctxt post_simps i,
       Goal.norm_hhf_tac ctxt i]
  end

fun transfer_prover_tac ctxt = SUBGOAL (fn (t, i) =>
  let
    val rhs = (snd o Term.dest_comb o HOLogic.dest_Trueprop) t
    val rule1 = transfer_rule_of_term ctxt false rhs
    val rules = get_transfer_raw ctxt
    val eq_rules = get_relator_eq_raw ctxt
    val expand_eq_in_rel = transfer_rel_conv (top_rewr_conv [@{thm fun_rel_eq[symmetric,THEN eq_reflection]}])
  in
    EVERY
      [CONVERSION prep_conv i,
       rtac @{thm transfer_prover_start} i,
       ((rtac rule1 ORELSE' (CONVERSION expand_eq_in_rel THEN' rtac rule1))
        THEN_ALL_NEW
         (REPEAT_ALL_NEW (resolve_tac rules) THEN_ALL_NEW (DETERM o eq_tac eq_rules))) (i+1),
       rtac @{thm refl} i]
  end)

(** Transfer attribute **)

fun transferred ctxt extra_rules thm =
  let
    val start_rule = @{thm transfer_start}
    val start_rule' = @{thm transfer_start'}
    val rules = extra_rules @ get_transfer_raw ctxt
    val eq_rules = get_relator_eq_raw ctxt
    val err_msg = "Transfer failed to convert goal to an object-logic formula"
    val pre_simps = @{thms transfer_forall_eq transfer_implies_eq}
    val thm1 = Drule.forall_intr_vars thm
    val instT = rev (Term.add_tvars (Thm.full_prop_of thm1) [])
                |> map (fn v as ((a, _), S) => (v, TFree (a, S)))
    val thm2 = thm1
      |> Thm.certify_instantiate (instT, [])
      |> Raw_Simplifier.rewrite_rule ctxt pre_simps
    val ctxt' = Variable.declare_names (Thm.full_prop_of thm2) ctxt
    val t = HOLogic.dest_Trueprop (Thm.concl_of thm2)
    val rule = transfer_rule_of_lhs ctxt' t
    val tac =
      resolve_tac [thm2 RS start_rule', thm2 RS start_rule] 1 THEN
      (rtac rule
        THEN_ALL_NEW
          (SOLVED' (REPEAT_ALL_NEW (resolve_tac rules)
            THEN_ALL_NEW (DETERM o eq_tac eq_rules)))) 1
        handle TERM (_, ts) => raise TERM (err_msg, ts)
    val thm3 = Goal.prove_internal ctxt' [] @{cpat "Trueprop ?P"} (K tac)
    val tnames = map (fst o dest_TFree o snd) instT
  in
    thm3
      |> Raw_Simplifier.rewrite_rule ctxt' post_simps
      |> Simplifier.norm_hhf ctxt'
      |> Drule.generalize (tnames, [])
      |> Drule.zero_var_indexes
  end
(*
    handle THM _ => thm
*)

fun untransferred ctxt extra_rules thm =
  let
    val start_rule = @{thm untransfer_start}
    val rules = extra_rules @ get_transfer_raw ctxt
    val eq_rules = get_relator_eq_raw ctxt
    val err_msg = "Transfer failed to convert goal to an object-logic formula"
    val pre_simps = @{thms transfer_forall_eq transfer_implies_eq}
    val thm1 = Drule.forall_intr_vars thm
    val instT = rev (Term.add_tvars (Thm.full_prop_of thm1) [])
                |> map (fn v as ((a, _), S) => (v, TFree (a, S)))
    val thm2 = thm1
      |> Thm.certify_instantiate (instT, [])
      |> Raw_Simplifier.rewrite_rule ctxt pre_simps
    val ctxt' = Variable.declare_names (Thm.full_prop_of thm2) ctxt
    val t = HOLogic.dest_Trueprop (Thm.concl_of thm2)
    val rule = transfer_rule_of_term ctxt' true t
    val tac =
      rtac (thm2 RS start_rule) 1 THEN
      (rtac rule
        THEN_ALL_NEW
          (SOLVED' (REPEAT_ALL_NEW (resolve_tac rules)
            THEN_ALL_NEW (DETERM o eq_tac eq_rules)))) 1
        handle TERM (_, ts) => raise TERM (err_msg, ts)
    val thm3 = Goal.prove_internal ctxt' [] @{cpat "Trueprop ?P"} (K tac)
    val tnames = map (fst o dest_TFree o snd) instT
  in
    thm3
      |> Raw_Simplifier.rewrite_rule ctxt' post_simps
      |> Simplifier.norm_hhf ctxt'
      |> Drule.generalize (tnames, [])
      |> Drule.zero_var_indexes
  end

(** Methods and attributes **)

val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ Syntax.string_of_term ctxt t))

val fixing = Scan.optional (Scan.lift (Args.$$$ "fixing" -- Args.colon)
  |-- Scan.repeat free) []

fun transfer_method equiv : (Proof.context -> Proof.method) context_parser =
  fixing >> (fn vs => fn ctxt =>
    SIMPLE_METHOD' (gen_frees_tac vs ctxt THEN' transfer_tac equiv ctxt))

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

fun transferred_attribute thms = Thm.rule_attribute
  (fn context => transferred (Context.proof_of context) thms)

fun untransferred_attribute thms = Thm.rule_attribute
  (fn context => untransferred (Context.proof_of context) thms)

val transferred_attribute_parser =
  Attrib.thms >> transferred_attribute

val untransferred_attribute_parser =
  Attrib.thms >> untransferred_attribute

(* Theory setup *)

val relator_eq_setup =
  let
    val name = @{binding relator_eq}
    fun add_thm thm context = context
      |> Data.map (map_relator_eq (Item_Net.update thm))
      |> Data.map (map_relator_eq_raw
          (Item_Net.update (abstract_equalities_relator_eq (Context.proof_of context) thm)))
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

val relator_domain_setup =
  let
    val name = @{binding relator_domain}
    fun add_thm thm = Data.map (map_relator_domain (Item_Net.update thm))
      #> add_transfer_domain_thm thm
    fun del_thm thm = Data.map (map_relator_domain (Item_Net.remove thm))
      #> del_transfer_domain_thm thm
    val add = Thm.declaration_attribute add_thm
    val del = Thm.declaration_attribute del_thm
    val text = "declaration of relator domain rule (used by transfer method)"
    val content = Item_Net.content o #relator_domain o Data.get
  in
    Attrib.setup name (Attrib.add_del add del) text
    #> Global_Theory.add_thms_dynamic (name, content)
  end


val setup =
  relator_eq_setup
  #> relator_domain_setup
  #> Attrib.setup @{binding transfer_rule} transfer_attribute
     "transfer rule for transfer method"
  #> Global_Theory.add_thms_dynamic
     (@{binding transfer_raw}, Item_Net.content o #transfer_raw o Data.get)
  #> Attrib.setup @{binding transfer_domain_rule} transfer_domain_attribute
     "transfer domain rule for transfer method"
  #> Attrib.setup @{binding transferred} transferred_attribute_parser
     "raw theorem transferred to abstract theorem using transfer rules"
  #> Attrib.setup @{binding untransferred} untransferred_attribute_parser
     "abstract theorem transferred to raw theorem using transfer rules"
  #> Global_Theory.add_thms_dynamic
     (@{binding relator_eq_raw}, Item_Net.content o #relator_eq_raw o Data.get)
  #> Method.setup @{binding transfer} (transfer_method true)
     "generic theorem transfer method"
  #> Method.setup @{binding transfer'} (transfer_method false)
     "generic theorem transfer method"
  #> Method.setup @{binding transfer_prover} transfer_prover_method
     "for proving transfer rules"

end
