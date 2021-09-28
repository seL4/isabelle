(*  Title:      HOL/Tools/Nunchaku/nunchaku_collect.ML
    Author:     Jasmin Blanchette, VU Amsterdam
    Copyright   2015, 2016, 2017

Collecting of Isabelle/HOL definitions etc. for Nunchaku.
*)

signature NUNCHAKU_COLLECT =
sig
  val dest_co_datatype_case: Proof.context -> string * typ -> (string * typ) list

  type isa_type_spec =
    {abs_typ: typ,
     rep_typ: typ,
     wrt: term,
     abs: term,
     rep: term}

  type isa_co_data_spec =
    {typ: typ,
     ctrs: term list}

  type isa_const_spec =
    {const: term,
     props: term list}

  type isa_rec_spec =
    {const: term,
     props: term list,
     pat_complete: bool}

  type isa_consts_spec =
    {consts: term list,
     props: term list}

  datatype isa_command =
    ITVal of typ * (int option * int option)
  | ITypedef of isa_type_spec
  | IQuotient of isa_type_spec
  | ICoData of BNF_Util.fp_kind * isa_co_data_spec list
  | IVal of term
  | ICoPred of BNF_Util.fp_kind * bool * isa_const_spec list
  | IRec of isa_rec_spec list
  | ISpec of isa_consts_spec
  | IAxiom of term
  | IGoal of term
  | IEval of term

  type isa_problem =
    {commandss: isa_command list list,
     sound: bool,
     complete: bool}

  exception CYCLIC_DEPS of unit
  exception TOO_DEEP_DEPS of unit
  exception TOO_META of term
  exception UNEXPECTED_POLYMORPHISM of term
  exception UNEXPECTED_VAR of term
  exception UNSUPPORTED_FUNC of term

  val isa_problem_of_subgoal: Proof.context -> bool -> ((string * typ) option * bool option) list ->
    (term option * bool) list -> (typ option * (int option * int option)) list -> bool ->
    Time.time -> term list -> term list -> term -> term list * isa_problem
  val pat_completes_of_isa_problem: isa_problem -> term list
  val str_of_isa_problem: Proof.context -> isa_problem -> string
end;

structure Nunchaku_Collect : NUNCHAKU_COLLECT =
struct

open Nunchaku_Util;

type isa_type_spec =
  {abs_typ: typ,
   rep_typ: typ,
   wrt: term,
   abs: term,
   rep: term};

type isa_co_data_spec =
  {typ: typ,
   ctrs: term list};

type isa_const_spec =
  {const: term,
   props: term list};

type isa_rec_spec =
  {const: term,
   props: term list,
   pat_complete: bool};

type isa_consts_spec =
  {consts: term list,
   props: term list};

datatype isa_command =
  ITVal of typ * (int option * int option)
| ITypedef of isa_type_spec
| IQuotient of isa_type_spec
| ICoData of BNF_Util.fp_kind * isa_co_data_spec list
| IVal of term
| ICoPred of BNF_Util.fp_kind * bool * isa_const_spec list
| IRec of isa_rec_spec list
| ISpec of isa_consts_spec
| IAxiom of term
| IGoal of term
| IEval of term;

type isa_problem =
  {commandss: isa_command list list,
   sound: bool,
   complete: bool};

exception CYCLIC_DEPS of unit;
exception TOO_DEEP_DEPS of unit;
exception TOO_META of term;
exception UNEXPECTED_POLYMORPHISM of term;
exception UNEXPECTED_VAR of term;
exception UNSUPPORTED_FUNC of term;

fun str_of_and_list str_of_elem =
  map str_of_elem #> space_implode ("\nand ");

val key_of_typ =
  let
    fun key_of (Type (s, [])) = s
      | key_of (Type (s, Ts)) = s ^ "(" ^ commas (map key_of Ts) ^ ")"
      | key_of (TFree (s, _)) = s;
  in
    prefix "y" o key_of
  end;

fun key_of_const ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun key_of (Const (x as (s, _))) =
        (case Sign.const_typargs thy x of
          [] => s
        | Ts => s ^ "(" ^ commas (map key_of_typ Ts) ^ ")")
      | key_of (Free (s, _)) = s;
  in
    prefix "t" o key_of
  end;

val add_type_keys = fold_subtypes (insert (op =) o key_of_typ);

fun add_aterm_keys ctxt t =
  if is_Const t orelse is_Free t then insert (op =) (key_of_const ctxt t) else I;

fun add_keys ctxt t =
  fold_aterms (add_aterm_keys ctxt) t
  #> fold_types add_type_keys t;

fun close_form except t =
  fold (fn ((s, i), T) => fn t' =>
      HOLogic.all_const T $ Abs (s, T, abstract_over (Var ((s, i), T), t')))
    (Term.add_vars t [] |> subtract (op =) except) t;

(* "imp_conjL[symmetric]" is important for inductive predicates with multiple assumptions. *)
val basic_defs =
  @{thms Ball_def[abs_def] Bex_def[abs_def] case_bool_if Ex1_def[abs_def]
    imp_conjL[symmetric, abs_def] Let_def[abs_def] rmember_def[symmetric, abs_def]};

fun unfold_basic_def ctxt =
  let val thy = Proof_Context.theory_of ctxt in
    Pattern.rewrite_term thy (map (Logic.dest_equals o Thm.prop_of) basic_defs) []
  end;

val has_polymorphism = exists_type (exists_subtype is_TVar);

fun whack_term thy whacks =
  let
    fun whk t =
      if triple_lookup (term_match thy o swap) whacks t = SOME true then
        Const (\<^const_name>\<open>unreachable\<close>, fastype_of t)
      else
        (case t of
          u $ v => whk u $ whk v
        | Abs (s, T, u) => Abs (s, T, whk u)
        | _ => t);
  in
    whk
  end;

fun preprocess_term_basic falsify ctxt whacks t =
  let val thy = Proof_Context.theory_of ctxt in
    if has_polymorphism t then
      raise UNEXPECTED_POLYMORPHISM t
    else
      t
      |> attach_typeS
      |> whack_term thy whacks
      |> Object_Logic.atomize_term ctxt
      |> tap (fn t' => fastype_of t' <> \<^typ>\<open>prop\<close> orelse raise TOO_META t)
      |> falsify ? HOLogic.mk_not
      |> unfold_basic_def ctxt
  end;

val check_closed = tap (fn t => null (Term.add_vars t []) orelse raise UNEXPECTED_VAR t);

val preprocess_prop = close_form [] oooo preprocess_term_basic;
val preprocess_closed_term = check_closed ooo preprocess_term_basic false;

val is_type_builtin = member (op =) [\<^type_name>\<open>bool\<close>, \<^type_name>\<open>fun\<close>];

val is_const_builtin =
  member (op =) [\<^const_name>\<open>All\<close>, \<^const_name>\<open>conj\<close>, \<^const_name>\<open>disj\<close>, \<^const_name>\<open>Eps\<close>,
    \<^const_name>\<open>HOL.eq\<close>, \<^const_name>\<open>Ex\<close>, \<^const_name>\<open>False\<close>, \<^const_name>\<open>If\<close>,
    \<^const_name>\<open>implies\<close>, \<^const_name>\<open>Not\<close>, \<^const_name>\<open>The\<close>, \<^const_name>\<open>The_unsafe\<close>,
    \<^const_name>\<open>True\<close>];

datatype type_classification = Builtin | TVal | Typedef | Quotient | Co_Datatype;

fun classify_type_name ctxt T_name =
  if is_type_builtin T_name then
    Builtin
  else if T_name = \<^type_name>\<open>itself\<close> then
    Co_Datatype
  else
    (case BNF_FP_Def_Sugar.fp_sugar_of ctxt T_name of
      SOME _ => Co_Datatype
    | NONE =>
      (case Ctr_Sugar.ctr_sugar_of ctxt T_name of
        SOME _ => Co_Datatype
      | NONE =>
        (case Quotient_Info.lookup_quotients ctxt T_name of
          SOME _ => Quotient
        | NONE =>
          if T_name = \<^type_name>\<open>set\<close> then
            Typedef
          else
            (case Typedef.get_info ctxt T_name of
              _ :: _ => Typedef
            | [] => TVal))));

fun fp_kind_of_ctr_sugar_kind Ctr_Sugar.Codatatype = BNF_Util.Greatest_FP
  | fp_kind_of_ctr_sugar_kind _ = BNF_Util.Least_FP;

fun mutual_co_datatypes_of ctxt (T_name, Ts) =
  (if T_name = \<^type_name>\<open>itself\<close> then
     (BNF_Util.Least_FP, [\<^typ>\<open>'a itself\<close>], [[\<^Const>\<open>Pure.type \<^typ>\<open>'a\<close>\<close>]])
   else
     let
       val (fp, ctr_sugars) =
         (case BNF_FP_Def_Sugar.fp_sugar_of ctxt T_name of
           SOME (fp_sugar as {fp, fp_res = {Ts, ...}, ...}) =>
           (fp,
            (case Ts of
              [_] => [fp_sugar]
            | _ => map (the o BNF_FP_Def_Sugar.fp_sugar_of ctxt o fst o dest_Type) Ts)
            |> map (#ctr_sugar o #fp_ctr_sugar))
         | NONE =>
           (case Ctr_Sugar.ctr_sugar_of ctxt T_name of
             SOME (ctr_sugar as {kind, ...}) =>
             (* Any freely constructed type that is not a codatatype is considered a datatype. This
                is sound (but incomplete) for model finding. *)
             (fp_kind_of_ctr_sugar_kind kind, [ctr_sugar])));
     in
       (fp, map #T ctr_sugars, map #ctrs ctr_sugars)
     end)
  |> @{apply 3(2)} (map ((fn Type (s, _) => Type (s, Ts))))
  |> @{apply 3(3)} (map (map (Ctr_Sugar.mk_ctr Ts)));

fun typedef_of ctxt T_name =
  if T_name = \<^type_name>\<open>set\<close> then
    let
      val A = Logic.varifyT_global \<^typ>\<open>'a\<close>;
      val absT = Type (\<^type_name>\<open>set\<close>, [A]);
      val repT = A --> HOLogic.boolT;
      val pred = Abs (Name.uu, repT, \<^Const>\<open>True\<close>);
      val abs = Const (\<^const_name>\<open>Collect\<close>, repT --> absT);
      val rep = Const (\<^const_name>\<open>rmember\<close>, absT --> repT);
    in
      (absT, repT, pred, abs, rep)
    end
  else
    (case Typedef.get_info ctxt T_name of
      (* When several entries are returned, it shouldn't matter much which one we take (according to
         Florian Haftmann). The "Logic.varifyT_global" calls are a workaround because these types'
         variables sometimes clash with locally fixed type variables. *)
      ({abs_type, rep_type, Abs_name, Rep_name, ...}, {Rep, ...}) :: _ =>
      let
        val absT = Logic.varifyT_global abs_type;
        val repT = Logic.varifyT_global rep_type;
        val set = Thm.prop_of Rep
          |> HOLogic.dest_Trueprop
          |> HOLogic.dest_mem
          |> snd;
        val pred = Abs (Name.uu, repT, HOLogic.mk_mem (Bound 0, set));
        val abs = Const (Abs_name, repT --> absT);
        val rep = Const (Rep_name, absT --> repT);
      in
        (absT, repT, pred, abs, rep)
      end);

fun quotient_of ctxt T_name =
  (case Quotient_Info.lookup_quotients ctxt T_name of
    SOME {equiv_rel, qtyp, rtyp, quot_thm, ...} =>
    let val _ $ (_ $ _ $ abs $ rep) = Thm.prop_of quot_thm in
      (qtyp, rtyp, equiv_rel, abs, rep)
    end);

fun is_co_datatype_ctr ctxt (s, T) =
  (case body_type T of
    Type (fpT_name, Ts) =>
    classify_type_name ctxt fpT_name = Co_Datatype andalso
    let
      val ctrs =
        if fpT_name = \<^type_name>\<open>itself\<close> then
          [Const (\<^const_name>\<open>Pure.type\<close>, \<^typ>\<open>'a itself\<close>)]
        else
          (case BNF_FP_Def_Sugar.fp_sugar_of ctxt fpT_name of
            SOME {fp_ctr_sugar = {ctr_sugar = {ctrs, ...}, ...}, ...} => ctrs
          | NONE =>
            (case Ctr_Sugar.ctr_sugar_of ctxt fpT_name of
              SOME {ctrs, ...} => ctrs
            | _ => []));

      fun is_right_ctr (t' as Const (s', _)) =
        s = s' andalso fastype_of (Ctr_Sugar.mk_ctr Ts t') = T;
    in
      exists is_right_ctr ctrs
    end
  | _  => false);

fun dest_co_datatype_case ctxt (s, T) =
  let val thy = Proof_Context.theory_of ctxt in
    (case strip_fun_type (Sign.the_const_type thy s) of
      (gen_branch_Ts, gen_body_fun_T) =>
      (case gen_body_fun_T of
        Type (\<^type_name>\<open>fun\<close>, [Type (fpT_name, _), _]) =>
        if classify_type_name ctxt fpT_name = Co_Datatype then
          let
            val Type (_, fpTs) = domain_type (funpow (length gen_branch_Ts) range_type T);
            val (ctrs0, Const (case_name, _)) =
              (case BNF_FP_Def_Sugar.fp_sugar_of ctxt fpT_name of
                SOME {fp_ctr_sugar = {ctr_sugar = {ctrs, casex, ...}, ...}, ...} => (ctrs, casex)
              | NONE =>
                (case Ctr_Sugar.ctr_sugar_of ctxt fpT_name of
                  SOME {ctrs, casex, ...} => (ctrs, casex)));
          in
            if s = case_name then map (dest_Const o Ctr_Sugar.mk_ctr fpTs) ctrs0
            else raise Fail "non-case"
          end
        else
          raise Fail "non-case"))
  end;

val is_co_datatype_case = can o dest_co_datatype_case;

fun is_quotient_abs ctxt (s, T) =
  (case T of
    Type (\<^type_name>\<open>fun\<close>, [_, Type (absT_name, _)]) =>
    classify_type_name ctxt absT_name = Quotient andalso
    (case quotient_of ctxt absT_name of
      (_, _, _, Const (s', _), _) => s' = s)
  | _ => false);

fun is_quotient_rep ctxt (s, T) =
  (case T of
    Type (\<^type_name>\<open>fun\<close>, [Type (absT_name, _), _]) =>
    classify_type_name ctxt absT_name = Quotient andalso
    (case quotient_of ctxt absT_name of
      (_, _, _, _, Const (s', _)) => s' = s)
  | _ => false);

fun is_maybe_typedef_abs ctxt absT_name s =
  if absT_name = \<^type_name>\<open>set\<close> then
    s = \<^const_name>\<open>Collect\<close>
  else
    (case try (typedef_of ctxt) absT_name of
      SOME (_, _, _, Const (s', _), _) => s' = s
    | NONE => false);

fun is_maybe_typedef_rep ctxt absT_name s =
  if absT_name = \<^type_name>\<open>set\<close> then
    s = \<^const_name>\<open>rmember\<close>
  else
    (case try (typedef_of ctxt) absT_name of
      SOME (_, _, _, _, Const (s', _)) => s' = s
    | NONE => false);

fun is_typedef_abs ctxt (s, T) =
  (case T of
    Type (\<^type_name>\<open>fun\<close>, [_, Type (absT_name, _)]) =>
    classify_type_name ctxt absT_name = Typedef andalso is_maybe_typedef_abs ctxt absT_name s
  | _ => false);

fun is_typedef_rep ctxt (s, T) =
  (case T of
    Type (\<^type_name>\<open>fun\<close>, [Type (absT_name, _), _]) =>
    classify_type_name ctxt absT_name = Typedef andalso is_maybe_typedef_rep ctxt absT_name s
  | _ => false);

fun is_stale_typedef_abs ctxt (s, T) =
  (case T of
    Type (\<^type_name>\<open>fun\<close>, [_, Type (absT_name, _)]) =>
    classify_type_name ctxt absT_name <> Typedef andalso is_maybe_typedef_abs ctxt absT_name s
  | _ => false);

fun is_stale_typedef_rep ctxt (s, T) =
  (case T of
    Type (\<^type_name>\<open>fun\<close>, [Type (absT_name, _), _]) =>
    classify_type_name ctxt absT_name <> Typedef andalso is_maybe_typedef_rep ctxt absT_name s
  | _ => false);

fun instantiate_constant_types_in_term ctxt csts target =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun try_const _ _ (res as SOME _) = res
      | try_const (s', T') cst NONE =
        (case cst of
          Const (s, T) =>
          if s = s' then
            SOME (Sign.typ_match thy (T', T) Vartab.empty)
            handle Type.TYPE_MATCH => NONE
          else
            NONE
        | _ => NONE);

    fun subst_for (Const x) = fold (try_const x) csts NONE
      | subst_for (t as Free _) = if member (op aconv) csts t then SOME Vartab.empty else NONE
      | subst_for (t1 $ t2) = (case subst_for t1 of SOME subst => SOME subst | NONE => subst_for t2)
      | subst_for (Abs (_, _, t')) = subst_for t'
      | subst_for _ = NONE;
  in
    (case subst_for target of
      SOME subst => Envir.subst_term_types subst target
    | NONE => raise Type.TYPE_MATCH)
  end;

datatype card = One | Fin | Fin_or_Inf | Inf

(* Similar to "ATP_Util.tiny_card_of_type". *)
fun card_of_type ctxt =
  let
    fun max_card Inf _ = Inf
      | max_card _ Inf = Inf
      | max_card Fin_or_Inf _ = Fin_or_Inf
      | max_card _ Fin_or_Inf = Fin_or_Inf
      | max_card Fin _ = Fin
      | max_card _ Fin = Fin
      | max_card One One = One;

    fun card_of avoid T =
      if member (op =) avoid T then
        Inf
      else
        (case T of
          TFree _ => Fin_or_Inf
        | TVar _ => Inf
        | Type (\<^type_name>\<open>fun\<close>, [T1, T2]) =>
          (case (card_of avoid T1, card_of avoid T2) of
            (_, One) => One
          | (k1, k2) => max_card k1 k2)
        | Type (\<^type_name>\<open>prod\<close>, [T1, T2]) =>
          (case (card_of avoid T1, card_of avoid T2) of
            (k1, k2) => max_card k1 k2)
        | Type (\<^type_name>\<open>set\<close>, [T']) => card_of avoid (T' --> HOLogic.boolT)
        | Type (T_name, Ts) =>
          (case try (mutual_co_datatypes_of ctxt) (T_name, Ts) of
            NONE => Inf
          | SOME (_, fpTs, ctrss) =>
            (case ctrss of [[_]] => One | _ => Fin)
            |> fold (fold (fold (max_card o card_of (fpTs @ avoid)) o binder_types o fastype_of))
              ctrss));
  in
    card_of []
  end;

fun spec_rules_of ctxt (x as (s, T)) =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun subst_of t0 =
      try (Sign.typ_match thy (fastype_of t0, T)) Vartab.empty;

    fun process_spec _ (res as SOME _) = res
      | process_spec {rough_classification = classif, terms = ts0, rules = ths as _ :: _, ...} NONE =
        (case get_first subst_of ts0 of
          SOME subst =>
          (let
             val ts = map (Envir.subst_term_types subst) ts0;
             val poly_props = map Thm.prop_of ths;
             val props = map (instantiate_constant_types_in_term ctxt ts) poly_props;
           in
             if exists (exists (exists_type (exists_subtype is_TVar))) [ts, props] then NONE
             else SOME (classif, ts, props, poly_props)
           end
           handle Type.TYPE_MATCH => NONE)
        | NONE => NONE)
      | process_spec _ NONE = NONE;

    fun spec_rules () =
      Spec_Rules.retrieve ctxt (Const x)
      |> sort (Spec_Rules.rough_classification_ord o apply2 #rough_classification);

    val specs =
      if s = \<^const_name>\<open>The\<close> then
        [{pos = Position.none, name = "", rough_classification = Spec_Rules.Unknown,
          terms = [Logic.varify_global \<^term>\<open>The\<close>],
          rules = [@{thm theI_unique}]}]
      else if s = \<^const_name>\<open>finite\<close> then
        let val card = card_of_type ctxt T in
          if card = Inf orelse card = Fin_or_Inf then
            spec_rules ()
          else
            [{pos = Position.none, name = "", rough_classification = Spec_Rules.equational,
              terms = [Logic.varify_global \<^term>\<open>finite\<close>],
              rules = [Skip_Proof.make_thm thy (Logic.varify_global \<^prop>\<open>finite A = True\<close>)]}]
        end
      else
        spec_rules ();
  in
    fold process_spec specs NONE
  end;

fun lhs_of_equation \<^Const_>\<open>Pure.eq _ for t _\<close> = t
  | lhs_of_equation \<^Const_>\<open>Trueprop for \<^Const_>\<open>HOL.eq _ for t _\<close>\<close> = t;

fun specialize_definition_type thy x def0 =
  let
    val def = specialize_type thy x def0;
    val lhs = lhs_of_equation def;
  in
    if exists_Const (curry (op =) x) lhs then def else raise Fail "cannot specialize"
  end;

fun definition_of thy (x as (s, _)) =
  Defs.specifications_of (Theory.defs_of thy) (Defs.Const, s)
  |> map_filter #def
  |> map_filter (try (specialize_definition_type thy x o Thm.prop_of o Thm.axiom thy))
  |> try hd;

fun is_builtin_theory thy_id =
  Context.subthy_id (thy_id, Context.theory_id \<^theory>\<open>Hilbert_Choice\<close>);

val orphan_axioms_of =
  Spec_Rules.get
  #> filter (Spec_Rules.is_unknown o #rough_classification)
  #> filter (null o #terms)
  #> maps #rules
  #> filter_out (is_builtin_theory o Thm.theory_id)
  #> map Thm.prop_of;

fun keys_of _ (ITVal (T, _)) = [key_of_typ T]
  | keys_of _ (ITypedef {abs_typ, ...}) = [key_of_typ abs_typ]
  | keys_of _ (IQuotient {abs_typ, ...}) = [key_of_typ abs_typ]
  | keys_of _ (ICoData (_, specs)) = map (key_of_typ o #typ) specs
  | keys_of ctxt (IVal const) = [key_of_const ctxt const]
  | keys_of ctxt (ICoPred (_, _, specs)) = map (key_of_const ctxt o #const) specs
  | keys_of ctxt (IRec specs) = map (key_of_const ctxt o #const) specs
  | keys_of ctxt (ISpec {consts, ...}) = map (key_of_const ctxt) consts
  | keys_of _ (IAxiom _) = []
  | keys_of _ (IGoal _) = []
  | keys_of _ (IEval _) = [];

fun co_data_spec_deps_of ctxt ({ctrs, ...} : isa_co_data_spec) =
  fold (add_keys ctxt) ctrs [];
fun const_spec_deps_of ctxt consts props =
  fold (add_keys ctxt) props [] |> subtract (op =) (map (key_of_const ctxt) consts);
fun consts_spec_deps_of ctxt {consts, props} =
  fold (add_keys ctxt) props [] |> subtract (op =) (map (key_of_const ctxt) consts);

fun deps_of _ (ITVal _) = []
  | deps_of ctxt (ITypedef {wrt, ...}) = add_keys ctxt wrt []
  | deps_of ctxt (IQuotient {wrt, ...}) = add_keys ctxt wrt []
  | deps_of ctxt (ICoData (_, specs)) = maps (co_data_spec_deps_of ctxt) specs
  | deps_of _ (IVal const) = add_type_keys (fastype_of const) []
  | deps_of ctxt (ICoPred (_, _, specs)) =
    maps (const_spec_deps_of ctxt (map #const specs) o #props) specs
  | deps_of ctxt (IRec specs) = maps (const_spec_deps_of ctxt (map #const specs) o #props) specs
  | deps_of ctxt (ISpec spec) = consts_spec_deps_of ctxt spec
  | deps_of ctxt (IAxiom prop) = add_keys ctxt prop []
  | deps_of ctxt (IGoal prop) = add_keys ctxt prop []
  | deps_of ctxt (IEval t) = add_keys ctxt t [];

fun consts_of_rec_or_spec (IRec specs) = map #const specs
  | consts_of_rec_or_spec (ISpec {consts, ...}) = consts;

fun props_of_rec_or_spec (IRec specs) = maps #props specs
  | props_of_rec_or_spec (ISpec {props, ...}) = props;

fun merge_two_rec_or_spec cmd cmd' =
  ISpec {consts = consts_of_rec_or_spec cmd @ consts_of_rec_or_spec cmd',
    props = props_of_rec_or_spec cmd @ props_of_rec_or_spec cmd'};

fun merge_two (ICoData (fp, specs)) (ICoData (fp', specs'), complete) =
    (ICoData (BNF_Util.case_fp fp fp fp', specs @ specs'), complete andalso fp = fp')
  | merge_two (IRec specs) (IRec specs', complete) = (IRec (specs @ specs'), complete)
  | merge_two (cmd as IRec _) (cmd' as ISpec _, complete) =
    (merge_two_rec_or_spec cmd cmd', complete)
  | merge_two (cmd as ISpec _) (cmd' as IRec _, complete) =
    (merge_two_rec_or_spec cmd cmd', complete)
  | merge_two (cmd as ISpec _) (cmd' as ISpec _, complete) =
    (merge_two_rec_or_spec cmd cmd', complete)
  | merge_two _ _ = raise CYCLIC_DEPS ();

fun sort_isa_commands_topologically ctxt cmds =
  let
    fun normal_pairs [] = []
      | normal_pairs (all as normal :: _) = map (rpair normal) all;

    fun add_node [] _ = I
      | add_node (normal :: _) cmd = Graph.new_node (normal, cmd);

    fun merge_scc (cmd :: cmds) complete = fold merge_two cmds (cmd, complete);

    fun sort_problem (cmds, complete) =
      let
        val keyss = map (keys_of ctxt) cmds;
        val normal_keys = Symtab.make (maps normal_pairs keyss);
        val normalize = Symtab.lookup normal_keys;

        fun add_deps [] _ = I
          | add_deps (normal :: _) cmd =
            let
              val deps = deps_of ctxt cmd
                |> map_filter normalize
                |> remove (op =) normal;
            in
              fold (fn dep => Graph.add_edge (dep, normal)) deps
            end;

        val cmd_of_key = the o AList.lookup (op =) (map hd keyss ~~ cmds);

        val G = Graph.empty
          |> fold2 add_node keyss cmds
          |> fold2 add_deps keyss cmds;

        val cmd_sccs = rev (Graph.strong_conn G)
          |> map (map cmd_of_key);
      in
        if exists (can (fn _ :: _ :: _ => ())) cmd_sccs then
          sort_problem (fold_map merge_scc cmd_sccs complete)
        else
          (Graph.schedule (K snd) G, complete)
      end;

    val typedecls = filter (can (fn ITVal _ => ())) cmds;
    val (mixed, complete) =
      (filter (can (fn ITypedef _ => () | IQuotient _ => () | ICoData _ => () | IVal _ => ()
         | ICoPred _ => () | IRec _ => () | ISpec _ => ())) cmds, true)
      |> sort_problem;
    val axioms = filter (can (fn IAxiom _ => ())) cmds;
    val goals = filter (can (fn IGoal _ => ())) cmds;
    val evals = filter (can (fn IEval _ => ())) cmds;
  in
    (typedecls @ mixed @ axioms @ goals @ evals, complete)
  end;

fun group_of (ITVal _) = 1
  | group_of (ITypedef _) = 2
  | group_of (IQuotient _) = 3
  | group_of (ICoData _) = 4
  | group_of (IVal _) = 5
  | group_of (ICoPred _) = 6
  | group_of (IRec _) = 7
  | group_of (ISpec _) = 8
  | group_of (IAxiom _) = 9
  | group_of (IGoal _) = 10
  | group_of (IEval _) = 11;

fun group_isa_commands [] = []
  | group_isa_commands [cmd] = [[cmd]]
  | group_isa_commands (cmd :: cmd' :: cmds) =
    let val (group :: groups) = group_isa_commands (cmd' :: cmds) in
      if group_of cmd = group_of cmd' then
        (cmd :: group) :: groups
      else
        [cmd] :: (group :: groups)
    end;

fun defined_by \<^Const_>\<open>All _ for t\<close> = defined_by t
  | defined_by (Abs (_, _, t)) = defined_by t
  | defined_by \<^Const_>\<open>implies for _ u\<close> = defined_by u
  | defined_by \<^Const_>\<open>HOL.eq _ for t _\<close> = head_of t
  | defined_by t = head_of t;

fun partition_props [_] props = SOME [props]
  | partition_props consts props =
    let
      val propss = map (fn const => filter (fn prop => defined_by prop aconv const) props) consts;
    in
      if eq_set (op aconv) (props, flat propss) andalso forall (not o null) propss then SOME propss
      else NONE
    end;

fun hol_concl_head (Const (\<^const_name>\<open>All\<close>, _) $ Abs (_, _, t)) = hol_concl_head t
  | hol_concl_head (Const (\<^const_name>\<open>implies\<close>, _) $ _ $ t) = hol_concl_head t
  | hol_concl_head (t $ _) = hol_concl_head t
  | hol_concl_head t = t;

fun is_inductive_set_intro t =
  (case hol_concl_head t of
    Const (\<^const_name>\<open>rmember\<close>, _) => true
  | _ => false);

exception NO_TRIPLE of unit;

fun triple_for_intro_rule ctxt x rule =
  let
    val (prems, concl) = Logic.strip_horn rule
      |>> map (Object_Logic.atomize_term ctxt)
      ||> Object_Logic.atomize_term ctxt;

    val (mains, sides) = List.partition (exists_Const (curry (op =) x)) prems;

    val is_right_head = curry (op aconv) (Const x) o head_of;
  in
    if forall is_right_head mains then (sides, mains, concl) else raise NO_TRIPLE ()
  end;

val tuple_for_args = HOLogic.mk_tuple o snd o strip_comb;

fun wf_constraint_for rel sides concl mains =
  HOLogic.mk_mem (HOLogic.mk_prod (apply2 tuple_for_args (mains, concl)), Var rel)
  |> fold (curry HOLogic.mk_imp) sides
  |> close_form [rel];

fun wf_constraint_for_triple rel (sides, mains, concl) =
  map (wf_constraint_for rel sides concl) mains
  |> foldr1 HOLogic.mk_conj;

fun terminates_by ctxt timeout goal tac =
  can (SINGLE (Classical.safe_tac ctxt) #> the
    #> SINGLE (DETERM_TIMEOUT timeout (tac ctxt (auto_tac ctxt))) #> the
    #> Goal.finish ctxt) goal;

val max_cached_wfs = 50;
val cached_timeout = Synchronized.var "Nunchaku_Collect.cached_timeout" Time.zeroTime;
val cached_wf_props = Synchronized.var "Nunchaku_Collect.cached_wf_props" ([] : (term * bool) list);

val termination_tacs = [Lexicographic_Order.lex_order_tac true, ScnpReconstruct.sizechange_tac];

fun is_wellfounded_inductive_predicate ctxt wfs debug wf_timeout const intros =
  let
    val thy = Proof_Context.theory_of ctxt;

    val Const (x as (_, T)) = head_of (HOLogic.dest_Trueprop (Logic.strip_imp_concl (hd intros)));
  in
    (case triple_lookup (const_match thy o swap) wfs (dest_Const const) of
      SOME (SOME wf) => wf
    | _ =>
      (case map (triple_for_intro_rule ctxt x) intros |> filter_out (null o #2) of
        [] => true
      | triples =>
        let
          val binders_T = HOLogic.mk_tupleT (binder_types T);
          val rel_T = HOLogic.mk_setT (HOLogic.mk_prodT (binders_T, binders_T));
          val j = fold (Integer.max o maxidx_of_term) intros 0 + 1;
          val rel = (("R", j), rel_T);
          val prop =
            Const (\<^const_name>\<open>wf\<close>, rel_T --> HOLogic.boolT) $ Var rel ::
            map (wf_constraint_for_triple rel) triples
            |> foldr1 HOLogic.mk_conj
            |> HOLogic.mk_Trueprop;
        in
          if debug then writeln ("Wellfoundedness goal: " ^ Syntax.string_of_term ctxt prop)
          else ();
          if wf_timeout = Synchronized.value cached_timeout andalso
             length (Synchronized.value cached_wf_props) < max_cached_wfs then
            ()
          else
            (Synchronized.change cached_wf_props (K []);
             Synchronized.change cached_timeout (K wf_timeout));
          (case AList.lookup (op =) (Synchronized.value cached_wf_props) prop of
            SOME wf => wf
          | NONE =>
            let
              val goal = Goal.init (Thm.cterm_of ctxt prop);
              val wf = exists (terminates_by ctxt wf_timeout goal) termination_tacs;
            in
              Synchronized.change cached_wf_props (cons (prop, wf)); wf
            end)
        end)
      handle
        List.Empty => false
      | NO_TRIPLE () => false)
  end;

datatype lhs_pat =
  Only_Vars
| Prim_Pattern of string
| Any_Pattern;

fun is_apparently_pat_complete ctxt props =
  let
    val is_Var_or_Bound = is_Var orf is_Bound;

    fun lhs_pat_of t =
      (case t of
        Const (\<^const_name>\<open>All\<close>, _) $ Abs (_, _, t) => lhs_pat_of t
      | Const (\<^const_name>\<open>HOL.eq\<close>, _) $ u $ _ =>
        (case filter_out is_Var_or_Bound (snd (strip_comb u)) of
          [] => Only_Vars
        | [v] =>
          (case strip_comb v of
            (cst as Const (_, T), args) =>
            (case body_type T of
              Type (T_name, _) =>
              if can (Ctr_Sugar.dest_ctr ctxt T_name) cst andalso forall is_Var_or_Bound args then
                Prim_Pattern T_name
              else
                Any_Pattern
            | _ => Any_Pattern)
          | _ => Any_Pattern)
        | _ => Any_Pattern)
      | _ => Any_Pattern);
  in
    (case map lhs_pat_of props of
      [] => false
    | pats as Prim_Pattern T_name :: _ =>
      forall (can (fn Prim_Pattern _ => ())) pats andalso
      length pats = length (#ctrs (the (Ctr_Sugar.ctr_sugar_of ctxt T_name)))
    | pats => forall (curry (op =) Only_Vars) pats)
  end;

(* Prevents divergence in case of cyclic or infinite axiom dependencies. *)
val axioms_max_depth = 255

fun isa_problem_of_subgoal ctxt falsify wfs whacks cards debug wf_timeout evals0 some_assms0
    subgoal0 =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun card_of T =
      (case triple_lookup (typ_match thy o swap) cards T of
        NONE => (NONE, NONE)
      | SOME (c1, c2) => (if c1 = SOME 1 then NONE else c1, c2));

    fun axioms_of_class class =
      #axioms (Axclass.get_info thy class)
      handle ERROR _ => [];

    fun monomorphize_class_axiom T t =
      (case Term.add_tvars t [] of
        [] => t
      | [(x, S)] => Envir.subst_term_types (Vartab.make [(x, (S, T))]) t);

    fun consider_sort depth T S (seens as (seenS, seenT, seen), problem) =
      if member (op =) seenS S then
        (seens, problem)
      else if depth > axioms_max_depth then
        raise TOO_DEEP_DEPS ()
      else
        let
          val seenS = S :: seenS;
          val seens = (seenS, seenT, seen);

          val supers = Sign.complete_sort thy S;
          val axioms0 = maps (map Thm.prop_of o axioms_of_class) supers;
          val axioms = map (preprocess_prop false ctxt whacks o monomorphize_class_axiom T) axioms0;
        in
          (seens, map IAxiom axioms @ problem)
          |> fold (consider_term (depth + 1)) axioms
        end
    and consider_type depth T =
      (case T of
        Type (s, Ts) =>
        if is_type_builtin s then fold (consider_type depth) Ts
        else consider_non_builtin_type depth T
      | _ => consider_non_builtin_type depth T)
    and consider_non_builtin_type depth T (seens as (seenS, seenT, seen), problem) =
      if member (op =) seenT T then
        (seens, problem)
      else
        let
          val seenT = T :: seenT;
          val seens = (seenS, seenT, seen);

          fun consider_typedef_or_quotient itypedef_or_quotient tuple_of s =
            let
              val (T0, repT0, wrt0, abs0, rep0) = tuple_of ctxt s;
              val tyenv = Sign.typ_match thy (T0, T) Vartab.empty;
              val substT = Envir.subst_type tyenv;
              val subst = Envir.subst_term_types tyenv;
              val repT = substT repT0;
              val wrt = preprocess_prop false ctxt whacks (subst wrt0);
              val abs = subst abs0;
              val rep = subst rep0;
            in
              apsnd (cons (itypedef_or_quotient {abs_typ = T, rep_typ = repT, wrt = wrt, abs = abs,
                rep = rep}))
              #> consider_term (depth + 1) wrt
            end;
        in
          (seens, problem)
          |> (case T of
               TFree (_, S) =>
               apsnd (cons (ITVal (T, card_of T)))
               #> consider_sort depth T S
             | TVar (_, S) => consider_sort depth T S
             | Type (s, Ts) =>
               fold (consider_type depth) Ts
               #> (case classify_type_name ctxt s of
                    Co_Datatype =>
                    let
                      val (fp, fpTs, ctrss) = mutual_co_datatypes_of ctxt (s, Ts);
                      val specs = map2 (fn T => fn ctrs => {typ = T, ctrs = ctrs}) fpTs ctrss;
                    in
                      (fn ((seenS, seenT, seen), problem) =>
                          ((seenS, union (op =) fpTs seenT, seen), ICoData (fp, specs) :: problem))
                      #> fold (fold (consider_type (depth + 1) o fastype_of)) ctrss
                    end
                  | Typedef => consider_typedef_or_quotient ITypedef typedef_of s
                  | Quotient => consider_typedef_or_quotient IQuotient quotient_of s
                  | TVal => apsnd (cons (ITVal (T, card_of T)))))
        end
    and consider_term depth t =
      (case t of
        t1 $ t2 => fold (consider_term depth) [t1, t2]
      | Var (_, T) => consider_type depth T
      | Bound _ => I
      | Abs (_, T, t') =>
        consider_term depth t'
        #> consider_type depth T
      | _ => (fn (seens as (seenS, seenT, seen), problem) =>
          if member (op aconv) seen t then
            (seens, problem)
          else if depth > axioms_max_depth then
            raise TOO_DEEP_DEPS ()
          else
            let
              val seen = t :: seen;
              val seens = (seenS, seenT, seen);
            in
              (case t of
                Const (x as (s, T)) =>
                (if is_const_builtin s orelse is_co_datatype_ctr ctxt x orelse
                    is_co_datatype_case ctxt x orelse is_quotient_abs ctxt x orelse
                    is_quotient_rep ctxt x orelse is_typedef_abs ctxt x orelse
                    is_typedef_rep ctxt x then
                   (seens, problem)
                 else if is_stale_typedef_abs ctxt x orelse is_stale_typedef_rep ctxt x then
                   raise UNSUPPORTED_FUNC t
                 else
                   (case spec_rules_of ctxt x of
                     SOME (classif, consts, props0, poly_props) =>
                     let
                       val props = map (preprocess_prop false ctxt whacks) props0;

                       fun def_or_spec () =
                         (case definition_of thy x of
                           SOME eq0 =>
                           let val eq = preprocess_prop false ctxt whacks eq0 in
                             ([eq], [IRec [{const = t, props = [eq], pat_complete = true}]])
                           end
                         | NONE => (props, [ISpec {consts = consts, props = props}]));

                       val (props', cmds) =
                         if null props then
                           ([], map IVal consts)
                         else if Spec_Rules.is_equational classif then
                           (case partition_props consts props of
                             SOME propss =>
                             (props,
                              [IRec (map2 (fn const => fn props =>
                                   {const = const, props = props,
                                    pat_complete = is_apparently_pat_complete ctxt props})
                                 consts propss)])
                           | NONE => def_or_spec ())
                         else if Spec_Rules.is_relational classif
                         then
                           if is_inductive_set_intro (hd props) then
                             def_or_spec ()
                           else
                             (case partition_props consts props of
                               SOME propss =>
                               (props,
                                [ICoPred (if Spec_Rules.is_inductive classif then BNF_Util.Least_FP
                                   else BNF_Util.Greatest_FP,
                                 length consts = 1 andalso
                                 is_wellfounded_inductive_predicate ctxt wfs debug wf_timeout
                                   (the_single consts) poly_props,
                                 map2 (fn const => fn props => {const = const, props = props})
                                   consts propss)])
                             | NONE => def_or_spec ())
                         else
                           def_or_spec ();
                     in
                       ((seenS, seenT, union (op aconv) consts seen), cmds @ problem)
                       |> fold (consider_term (depth + 1)) props'
                     end
                   | NONE =>
                     (case definition_of thy x of
                       SOME eq0 =>
                       let val eq = preprocess_prop false ctxt whacks eq0 in
                         (seens, IRec [{const = t, props = [eq], pat_complete = true}] :: problem)
                         |> consider_term (depth + 1) eq
                       end
                     | NONE => (seens, IVal t :: problem))))
                |> consider_type depth T
              | Free (_, T) =>
                (seens, IVal t :: problem)
                |> consider_type depth T)
            end));

    val (poly_axioms, mono_axioms0) = orphan_axioms_of ctxt
      |> List.partition has_polymorphism;

    fun implicit_evals_of pol \<^Const_>\<open>Not for t\<close> = implicit_evals_of (not pol) t
      | implicit_evals_of pol \<^Const_>\<open>implies for t u\<close> =
        (case implicit_evals_of pol u of
          [] => implicit_evals_of (not pol) t
        | ts => ts)
      | implicit_evals_of pol \<^Const_>\<open>conj for t u\<close> =
        union (op aconv) (implicit_evals_of pol t) (implicit_evals_of pol u)
      | implicit_evals_of pol \<^Const_>\<open>disj for t u\<close> =
        union (op aconv) (implicit_evals_of pol t) (implicit_evals_of pol u)
      | implicit_evals_of false (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t $ u) =
        distinct (op aconv) [t, u]
      | implicit_evals_of true (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t $ _) = [t]
      | implicit_evals_of _ _ = [];

    val mono_axioms_and_some_assms =
      map (preprocess_prop false ctxt whacks) (mono_axioms0 @ some_assms0);
    val subgoal = preprocess_prop falsify ctxt whacks subgoal0;
    val implicit_evals = implicit_evals_of true subgoal;
    val evals = map (preprocess_closed_term ctxt whacks) evals0;
    val seens = ([], [], []);

    val (commandss, complete) =
      (seens,
       map IAxiom mono_axioms_and_some_assms @ [IGoal subgoal] @ map IEval (implicit_evals @ evals))
      |> fold (consider_term 0) (subgoal :: evals @ mono_axioms_and_some_assms)
      |> snd
      |> rev (* prettier *)
      |> sort_isa_commands_topologically ctxt
      |>> group_isa_commands;
  in
    (poly_axioms, {commandss = commandss, sound = true, complete = complete})
  end;

fun add_pat_complete_of_command cmd =
  (case cmd of
    ICoPred (_, _, specs) => union (op =) (map #const specs)
  | IRec specs =>
    union (op =) (map_filter (try (fn {const, pat_complete = true, ...} => const)) specs)
  | _ => I);

fun pat_completes_of_isa_problem {commandss, ...} =
  fold (fold add_pat_complete_of_command) commandss [];

fun str_of_isa_term_with_type ctxt t =
  Syntax.string_of_term ctxt t ^ " : " ^ Syntax.string_of_typ ctxt (fastype_of t);

fun is_triv_wrt (Abs (_, _, body)) = is_triv_wrt body
  | is_triv_wrt \<^Const>\<open>True\<close> = true
  | is_triv_wrt _ = false;

fun str_of_isa_type_spec ctxt {abs_typ, rep_typ, wrt, abs, rep} =
  Syntax.string_of_typ ctxt abs_typ ^ " := " ^ Syntax.string_of_typ ctxt rep_typ ^
  (if is_triv_wrt wrt then "" else "\n  wrt " ^ Syntax.string_of_term ctxt wrt) ^
  "\n  abstract " ^ Syntax.string_of_term ctxt abs ^
  "\n  concrete " ^ Syntax.string_of_term ctxt rep;

fun str_of_isa_co_data_spec ctxt {typ, ctrs} =
  Syntax.string_of_typ ctxt typ ^ " :=\n  " ^
  space_implode "\n| " (map (str_of_isa_term_with_type ctxt) ctrs);

fun str_of_isa_const_spec ctxt {const, props} =
  str_of_isa_term_with_type ctxt const ^ " :=\n  " ^
  space_implode ";\n  " (map (Syntax.string_of_term ctxt) props);

fun str_of_isa_rec_spec ctxt {const, props, pat_complete} =
  str_of_isa_term_with_type ctxt const ^ (if pat_complete then " [pat_complete]" else "") ^
  " :=\n  " ^ space_implode ";\n  " (map (Syntax.string_of_term ctxt) props);

fun str_of_isa_consts_spec ctxt {consts, props} =
  space_implode " and\n     " (map (str_of_isa_term_with_type ctxt) consts) ^ " :=\n  " ^
  space_implode ";\n  " (map (Syntax.string_of_term ctxt) props);

fun str_of_isa_card NONE = ""
  | str_of_isa_card (SOME k) = signed_string_of_int k;

fun str_of_isa_cards_suffix (NONE, NONE) = ""
  | str_of_isa_cards_suffix (c1, c2) = " " ^ str_of_isa_card c1 ^ "-" ^ str_of_isa_card c2;

fun str_of_isa_command ctxt (ITVal (T, cards)) =
    "type " ^ Syntax.string_of_typ ctxt T ^ str_of_isa_cards_suffix cards
  | str_of_isa_command ctxt (ITypedef spec) = "typedef " ^ str_of_isa_type_spec ctxt spec
  | str_of_isa_command ctxt (IQuotient spec) = "quotient " ^ str_of_isa_type_spec ctxt spec
  | str_of_isa_command ctxt (ICoData (fp, specs)) =
    BNF_Util.case_fp fp "data" "codata" ^ " " ^ str_of_and_list (str_of_isa_co_data_spec ctxt) specs
  | str_of_isa_command ctxt (IVal t) = "val " ^ str_of_isa_term_with_type ctxt t
  | str_of_isa_command ctxt (ICoPred (fp, wf, specs)) =
    BNF_Util.case_fp fp "pred" "copred" ^ " " ^ (if wf then "[wf] " else "") ^
    str_of_and_list (str_of_isa_const_spec ctxt) specs
  | str_of_isa_command ctxt (IRec specs) = "rec " ^ str_of_and_list (str_of_isa_rec_spec ctxt) specs
  | str_of_isa_command ctxt (ISpec spec) = "spec " ^ str_of_isa_consts_spec ctxt spec
  | str_of_isa_command ctxt (IAxiom prop) = "axiom " ^ Syntax.string_of_term ctxt prop
  | str_of_isa_command ctxt (IGoal prop) = "goal " ^ Syntax.string_of_term ctxt prop
  | str_of_isa_command ctxt (IEval t) = "eval " ^ Syntax.string_of_term ctxt t;

fun str_of_isa_problem ctxt {commandss, sound, complete} =
  map (cat_lines o map (suffix "." o str_of_isa_command ctxt)) commandss
  |> space_implode "\n\n" |> suffix "\n"
  |> prefix ("# " ^ (if sound then "sound" else "unsound") ^ "\n")
  |> prefix ("# " ^ (if complete then "complete" else "incomplete") ^ "\n");

end;
