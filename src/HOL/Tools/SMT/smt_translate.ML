(*  Title:      HOL/Tools/SMT/smt_translate.ML
    Author:     Sascha Boehme, TU Muenchen

Translate theorems into an SMT intermediate format and serialize them.
*)

signature SMT_TRANSLATE =
sig
  (*intermediate term structure*)
  datatype squant = SForall | SExists
  datatype 'a spattern = SPat of 'a list | SNoPat of 'a list
  datatype sterm =
    SVar of int * sterm list |
    SConst of string * sterm list |
    SQua of squant * string list * sterm spattern list * sterm

  (*translation configuration*)
  type sign = {
    logic: string,
    sorts: string list,
    dtyps: (BNF_Util.fp_kind * (string * (string * (string * string) list) list)) list,
    funcs: (string * (string list * string)) list }
  type config = {
    order: SMT_Util.order,
    logic: term list -> string,
    fp_kinds: BNF_Util.fp_kind list,
    serialize: (string * string) list -> string list -> sign -> sterm list -> string }
  type replay_data = {
    context: Proof.context,
    typs: typ Symtab.table,
    terms: term Symtab.table,
    ll_defs: term list,
    rewrite_rules: thm list,
    assms: (int * thm) list }

  (*translation*)
  val add_config: SMT_Util.class * (Proof.context -> config) -> Context.generic -> Context.generic
  val translate: Proof.context -> (string * string) list -> string list -> (int * thm) list ->
    string * replay_data
end;

structure SMT_Translate: SMT_TRANSLATE =
struct


(* intermediate term structure *)

datatype squant = SForall | SExists

datatype 'a spattern =
  SPat of 'a list | SNoPat of 'a list

datatype sterm =
  SVar of int * sterm list |
  SConst of string * sterm list |
  SQua of squant * string list * sterm spattern list * sterm


(* translation configuration *)

type sign = {
  logic: string,
  sorts: string list,
  dtyps: (BNF_Util.fp_kind * (string * (string * (string * string) list) list)) list,
  funcs: (string * (string list * string)) list }

type config = {
  order: SMT_Util.order,
  logic: term list -> string,
  fp_kinds: BNF_Util.fp_kind list,
  serialize: (string * string) list -> string list -> sign -> sterm list -> string }

type replay_data = {
  context: Proof.context,
  typs: typ Symtab.table,
  terms: term Symtab.table,
  ll_defs: term list,
  rewrite_rules: thm list,
  assms: (int * thm) list }


(* translation context *)

fun add_components_of_typ (Type (s, Ts)) =
    cons (Long_Name.base_name s) #> fold_rev add_components_of_typ Ts
  | add_components_of_typ (TFree (s, _)) = cons (perhaps (try (unprefix "'")) s)
  | add_components_of_typ _ = I;

fun suggested_name_of_typ T = space_implode "_" (add_components_of_typ T []);

fun suggested_name_of_term (Const (s, _)) = Long_Name.base_name s
  | suggested_name_of_term (Free (s, _)) = s
  | suggested_name_of_term _ = Name.uu

val empty_tr_context = (Name.context, Typtab.empty, Termtab.empty)
val safe_suffix = "$"

fun add_typ T proper (cx as (names, typs, terms)) =
  (case Typtab.lookup typs T of
    SOME (name, _) => (name, cx)
  | NONE =>
      let
        val sugg = Name.desymbolize (SOME true) (suggested_name_of_typ T) ^ safe_suffix
        val (name, names') = Name.variant sugg names
        val typs' = Typtab.update (T, (name, proper)) typs
      in (name, (names', typs', terms)) end)

fun add_fun t sort (cx as (names, typs, terms)) =
  (case Termtab.lookup terms t of
    SOME (name, _) => (name, cx)
  | NONE =>
      let
        val sugg = Name.desymbolize (SOME false) (suggested_name_of_term t) ^ safe_suffix
        val (name, names') = Name.variant sugg names
        val terms' = Termtab.update (t, (name, sort)) terms
      in (name, (names', typs, terms')) end)

fun sign_of logic dtyps (_, typs, terms) = {
  logic = logic,
  sorts = Typtab.fold (fn (_, (n, true)) => cons n | _ => I) typs [],
  dtyps = dtyps,
  funcs = Termtab.fold (fn (_, (n, SOME ss)) => cons (n,ss) | _ => I) terms []}

fun replay_data_of ctxt ll_defs rules assms (_, typs, terms) =
  let
    fun add_typ (T, (n, _)) = Symtab.update (n, T)
    val typs' = Typtab.fold add_typ typs Symtab.empty

    fun add_fun (t, (n, _)) = Symtab.update (n, t)
    val terms' = Termtab.fold add_fun terms Symtab.empty
  in
    {context = ctxt, typs = typs', terms = terms', ll_defs = ll_defs, rewrite_rules = rules,
     assms = assms}
  end


(* preprocessing *)

(** (co)datatype declarations **)

fun collect_co_datatypes fp_kinds (tr_context, ctxt) ts =
  let
    val (fp_decls, ctxt') =
      ([], ctxt)
      |> fold (Term.fold_types (SMT_Datatypes.add_decls fp_kinds)) ts
      |>> flat

    fun is_decl_typ T = exists (equal T o fst o snd) fp_decls

    fun add_typ' T proper =
      (case SMT_Builtin.dest_builtin_typ ctxt' T of
        SOME (n, Ts) => pair n (* FIXME HO: Consider Ts *)
      | NONE => add_typ T proper)

    fun tr_select sel =
      let val T = Term.range_type (Term.fastype_of sel)
      in add_fun sel NONE ##>> add_typ' T (not (is_decl_typ T)) end
    fun tr_constr (constr, selects) =
      add_fun constr NONE ##>> fold_map tr_select selects
    fun tr_typ (fp, (T, cases)) =
      add_typ' T false ##>> fold_map tr_constr cases #>> pair fp

    val (fp_decls', tr_context') = fold_map tr_typ fp_decls tr_context

    fun add (constr, selects) =
      Termtab.update (constr, length selects) #>
      fold (Termtab.update o rpair 1) selects

    val funcs = fold (fold add o snd o snd) fp_decls Termtab.empty

  in ((funcs, fp_decls', tr_context', ctxt'), ts) end
    (* FIXME: also return necessary (co)datatype theorems *)


(** eta-expand quantifiers, let expressions and built-ins *)

local
  fun eta f T t = Abs (Name.uu, T, f (Term.incr_boundvars 1 t $ Bound 0))

  fun exp f T = eta f (Term.domain_type (Term.domain_type T))

  fun exp2 T q =
    let val U = Term.domain_type T
    in Abs (Name.uu, U, q $ eta I (Term.domain_type U) (Bound 0)) end

  fun expf k i T t =
    let val Ts = drop i (fst (SMT_Util.dest_funT k T))
    in
      Term.incr_boundvars (length Ts) t
      |> fold_rev (fn i => fn u => u $ Bound i) (0 upto length Ts - 1)
      |> fold_rev (fn T => fn u => Abs (Name.uu, T, u)) Ts
    end
in

fun eta_expand ctxt funcs =
  let
    fun exp_func t T ts =
      (case Termtab.lookup funcs t of
        SOME k => Term.list_comb (t, ts) |> k <> length ts ? expf k (length ts) T
      | NONE => Term.list_comb (t, ts))

    fun expand ((q as Const (\<^const_name>\<open>All\<close>, _)) $ Abs a) = q $ abs_expand a
      | expand ((q as Const (\<^const_name>\<open>All\<close>, T)) $ t) = q $ exp expand T t
      | expand (q as Const (\<^const_name>\<open>All\<close>, T)) = exp2 T q
      | expand ((q as Const (\<^const_name>\<open>Ex\<close>, _)) $ Abs a) = q $ abs_expand a
      | expand ((q as Const (\<^const_name>\<open>Ex\<close>, T)) $ t) = q $ exp expand T t
      | expand (q as Const (\<^const_name>\<open>Ex\<close>, T)) = exp2 T q
      | expand (Const (\<^const_name>\<open>Let\<close>, T) $ t) =
          let val U = Term.domain_type (Term.range_type T)
          in Abs (Name.uu, U, Bound 0 $ Term.incr_boundvars 1 t) end
      | expand (Const (\<^const_name>\<open>Let\<close>, T)) =
          let val U = Term.domain_type (Term.range_type T)
          in Abs (Name.uu, Term.domain_type T, Abs (Name.uu, U, Bound 0 $ Bound 1)) end
      | expand t =
          (case Term.strip_comb t of
            (Const (\<^const_name>\<open>Let\<close>, _), t1 :: t2 :: ts) =>
            Term.betapplys (Term.betapply (expand t2, expand t1), map expand ts)
          | (u as Const (c as (_, T)), ts) =>
              (case SMT_Builtin.dest_builtin ctxt c ts of
                SOME (_, k, us, mk) =>
                  if k = length us then mk (map expand us)
                  else if k < length us then chop k (map expand us) |>> mk |> Term.list_comb
                  else expf k (length ts) T (mk (map expand us))
              | NONE => exp_func u T (map expand ts))
          | (u as Free (_, T), ts) => exp_func u T (map expand ts)
          | (Abs a, ts) => Term.list_comb (abs_expand a, map expand ts)
          | (u, ts) => Term.list_comb (u, map expand ts))

    and abs_expand (n, T, t) = Abs (n, T, expand t)

  in map expand end

end


(** introduce explicit applications **)

local
  (*
    Make application explicit for functions with varying number of arguments.
  *)

  fun add t i = apfst (Termtab.map_default (t, i) (Integer.min i))
  fun add_type T = apsnd (Typtab.update (T, ()))

  fun min_arities t =
    (case Term.strip_comb t of
      (u as Const _, ts) => add u (length ts) #> fold min_arities ts
    | (u as Free _, ts) => add u (length ts) #> fold min_arities ts
    | (Abs (_, T, u), ts) => (can dest_funT T ? add_type T) #> min_arities u #> fold min_arities ts
    | (_, ts) => fold min_arities ts)

  fun take_vars_into_account types t i =
    let
      fun find_min j (T as Type (\<^type_name>\<open>fun\<close>, [_, T'])) =
          if j = i orelse Typtab.defined types T then j else find_min (j + 1) T'
        | find_min j _ = j
    in find_min 0 (Term.type_of t) end

  fun app u (t, T) = (Const (\<^const_name>\<open>fun_app\<close>, T --> T) $ t $ u, Term.range_type T)

  fun apply i t T ts =
    let
      val (ts1, ts2) = chop i ts
      val (_, U) = SMT_Util.dest_funT i T
    in fst (fold app ts2 (Term.list_comb (t, ts1), U)) end
in

fun intro_explicit_application ctxt funcs ts =
  let
    val explicit_application = Config.get ctxt SMT_Config.explicit_application
    val get_arities =
      (case explicit_application of
        0 => min_arities
      | 1 => min_arities
      | 2 => K I
      | n => error ("Illegal value for " ^ quote (Config.name_of SMT_Config.explicit_application) ^
          ": " ^ string_of_int n))

    val (arities, types) = fold get_arities ts (Termtab.empty, Typtab.empty)
    val arities' = arities |> explicit_application = 1 ? Termtab.map (take_vars_into_account types)

    fun app_func t T ts =
      if is_some (Termtab.lookup funcs t) then Term.list_comb (t, ts)
      else apply (the_default 0 (Termtab.lookup arities' t)) t T ts

    fun in_list T f t = SMT_Util.mk_symb_list T (map f (SMT_Util.dest_symb_list t))

    fun traverse Ts t =
      (case Term.strip_comb t of
        (q as Const (\<^const_name>\<open>All\<close>, _), [Abs (x, T, u)]) =>
          q $ Abs (x, T, in_trigger (T :: Ts) u)
      | (q as Const (\<^const_name>\<open>Ex\<close>, _), [Abs (x, T, u)]) =>
          q $ Abs (x, T, in_trigger (T :: Ts) u)
      | (q as Const (\<^const_name>\<open>Let\<close>, _), [u1, u2 as Abs _]) =>
          q $ traverse Ts u1 $ traverse Ts u2
      | (u as Const (c as (_, T)), ts) =>
          (case SMT_Builtin.dest_builtin ctxt c ts of
            SOME (_, k, us, mk) =>
              let
                val (ts1, ts2) = chop k (map (traverse Ts) us)
                val U = Term.strip_type T |>> snd o chop k |> (op --->)
              in apply 0 (mk ts1) U ts2 end
          | NONE => app_func u T (map (traverse Ts) ts))
      | (u as Free (_, T), ts) => app_func u T (map (traverse Ts) ts)
      | (u as Bound i, ts) => apply 0 u (nth Ts i) (map (traverse Ts) ts)
      | (Abs (n, T, u), ts) => traverses Ts (Abs (n, T, traverse (T::Ts) u)) ts
      | (u, ts) => traverses Ts u ts)
    and in_trigger Ts ((c as \<^Const_>\<open>trigger\<close>) $ p $ t) = c $ in_pats Ts p $ traverse Ts t
      | in_trigger Ts t = traverse Ts t
    and in_pats Ts ps =
      in_list \<^typ>\<open>pattern symb_list\<close> (in_list \<^typ>\<open>pattern\<close> (in_pat Ts)) ps
    and in_pat Ts ((p as \<^Const_>\<open>pat _\<close>) $ t) = p $ traverse Ts t
      | in_pat Ts ((p as \<^Const_>\<open>nopat _\<close>) $ t) = p $ traverse Ts t
      | in_pat _ t = raise TERM ("bad pattern", [t])
    and traverses Ts t ts = Term.list_comb (t, map (traverse Ts) ts)
  in map (traverse []) ts end

val fun_app_eq = mk_meta_eq @{thm fun_app_def}

end


(** map HOL formulas to FOL formulas (i.e., separate formulas froms terms) **)

local
  val is_quant = member (op =) [\<^const_name>\<open>All\<close>, \<^const_name>\<open>Ex\<close>]

  val fol_rules = [
    Let_def,
    @{lemma "P = True == P" by (rule eq_reflection) simp}]

  exception BAD_PATTERN of unit

  fun is_builtin_conn_or_pred ctxt c ts =
    is_some (SMT_Builtin.dest_builtin_conn ctxt c ts) orelse
    is_some (SMT_Builtin.dest_builtin_pred ctxt c ts)
in

fun folify ctxt =
  let
    fun in_list T f t = SMT_Util.mk_symb_list T (map_filter f (SMT_Util.dest_symb_list t))

    fun in_term pat t =
      (case Term.strip_comb t of
        (\<^Const_>\<open>True\<close>, []) => t
      | (\<^Const_>\<open>False\<close>, []) => t
      | (u as \<^Const_>\<open>If _\<close>, [t1, t2, t3]) =>
          if pat then raise BAD_PATTERN () else u $ in_form t1 $ in_term pat t2 $ in_term pat t3
      | (Const (c as (n, _)), ts) =>
          if is_builtin_conn_or_pred ctxt c ts orelse is_quant n then
            if pat then raise BAD_PATTERN () else in_form t
          else
            Term.list_comb (Const c, map (in_term pat) ts)
      | (Free c, ts) => Term.list_comb (Free c, map (in_term pat) ts)
      | _ => t)

    and in_pat ((p as Const (\<^const_name>\<open>pat\<close>, _)) $ t) =
          p $ in_term true t
      | in_pat ((p as Const (\<^const_name>\<open>nopat\<close>, _)) $ t) =
          p $ in_term true t
      | in_pat t = raise TERM ("bad pattern", [t])

    and in_pats ps =
      in_list \<^typ>\<open>pattern symb_list\<close> (SOME o in_list \<^typ>\<open>pattern\<close> (try in_pat)) ps

    and in_trigger ((c as \<^Const_>\<open>trigger\<close>) $ p $ t) = c $ in_pats p $ in_form t
      | in_trigger t = in_form t

    and in_form t =
      (case Term.strip_comb t of
        (q as Const (qn, _), [Abs (n, T, u)]) =>
          if is_quant qn then q $ Abs (n, T, in_trigger u)
          else in_term false t
      | (Const c, ts) =>
          (case SMT_Builtin.dest_builtin_conn ctxt c ts of
            SOME (_, _, us, mk) => mk (map in_form us)
          | NONE =>
              (case SMT_Builtin.dest_builtin_pred ctxt c ts of
                SOME (_, _, us, mk) => mk (map (in_term false) us)
              | NONE => in_term false t))
      | _ => in_term false t)
  in
    map in_form #>
    pair (fol_rules, I)
  end

end


(* translation into intermediate format *)

(** utility functions **)

val quantifier = (fn
    \<^const_name>\<open>All\<close> => SOME SForall
  | \<^const_name>\<open>Ex\<close> => SOME SExists
  | _ => NONE)

fun group_quant qname Ts (t as Const (q, _) $ Abs (_, T, u)) =
      if q = qname then group_quant qname (T :: Ts) u else (Ts, t)
  | group_quant _ Ts t = (Ts, t)

fun dest_pat (Const (\<^const_name>\<open>pat\<close>, _) $ t) = (t, true)
  | dest_pat (Const (\<^const_name>\<open>nopat\<close>, _) $ t) = (t, false)
  | dest_pat t = raise TERM ("bad pattern", [t])

fun dest_pats [] = I
  | dest_pats ts =
      (case map dest_pat ts |> split_list ||> distinct (op =) of
        (ps, [true]) => cons (SPat ps)
      | (ps, [false]) => cons (SNoPat ps)
      | _ => raise TERM ("bad multi-pattern", ts))

fun dest_trigger \<^Const_>\<open>trigger for tl t\<close> =
      (rev (fold (dest_pats o SMT_Util.dest_symb_list) (SMT_Util.dest_symb_list tl) []), t)
  | dest_trigger t = ([], t)

fun dest_quant qn T t = quantifier qn |> Option.map (fn q =>
  let
    val (Ts, u) = group_quant qn [T] t
    val (ps, p) = dest_trigger u
  in (q, rev Ts, ps, p) end)

fun fold_map_pat f (SPat ts) = fold_map f ts #>> SPat
  | fold_map_pat f (SNoPat ts) = fold_map f ts #>> SNoPat


(** translation from Isabelle terms into SMT intermediate terms **)

fun intermediate logic dtyps builtin ctxt ts trx =
  let
    fun transT (T as TFree _) = add_typ T true
      | transT (T as TVar _) = (fn _ => raise TYPE ("bad SMT type", [T], []))
      | transT (T as Type _) =
          (case SMT_Builtin.dest_builtin_typ ctxt T of
            SOME (n, []) => pair n
          | SOME (n, Ts) =>
            fold_map transT Ts
            #>> (fn ns => enclose "(" ")" (space_implode " " (n :: ns)))
          | NONE => add_typ T true)

    fun trans t =
      (case Term.strip_comb t of
        (Const (qn, _), [Abs (_, T, t1)]) =>
          (case dest_quant qn T t1 of
            SOME (q, Ts, ps, b) =>
              fold_map transT Ts ##>> fold_map (fold_map_pat trans) ps ##>>
              trans b #>> (fn ((Ts', ps'), b') => SQua (q, Ts', ps', b'))
          | NONE => raise TERM ("unsupported quantifier", [t]))
      | (u as Const (c as (_, T)), ts) =>
          (case builtin ctxt c ts of
            SOME (n, _, us, _) => fold_map trans us #>> curry SConst n
          | NONE => trans_applied_fun u T ts)
      | (u as Free (_, T), ts) => trans_applied_fun u T ts
      | (Bound i, ts) => pair i ##>> fold_map trans ts #>> SVar
      | _ => raise TERM ("bad SMT term", [t]))

    and trans_applied_fun t T ts =
      let val (Us, U) = SMT_Util.dest_funT (length ts) T
      in
        fold_map transT Us ##>> transT U #-> (fn Up =>
          add_fun t (SOME Up) ##>> fold_map trans ts #>> SConst)
      end

    val (us, trx') = fold_map trans ts trx
  in ((sign_of (logic ts) dtyps trx', us), trx') end


(* translation *)

structure Configs = Generic_Data
(
  type T = (Proof.context -> config) SMT_Util.dict
  val empty = []
  val extend = I
  fun merge data = SMT_Util.dict_merge fst data
)

fun add_config (cs, cfg) = Configs.map (SMT_Util.dict_update (cs, cfg))

fun get_config ctxt =
  let val cs = SMT_Config.solver_class_of ctxt
  in
    (case SMT_Util.dict_get (Configs.get (Context.Proof ctxt)) cs of
      SOME cfg => cfg ctxt
    | NONE => error ("SMT: no translation configuration found " ^
        "for solver class " ^ quote (SMT_Util.string_of_class cs)))
  end

fun translate ctxt smt_options comments ithms =
  let
    val {order, logic, fp_kinds, serialize} = get_config ctxt

    fun no_dtyps (tr_context, ctxt) ts =
      ((Termtab.empty, [], tr_context, ctxt), ts)

    val ts1 = map (Envir.beta_eta_contract o SMT_Util.prop_of o snd) ithms

    val ((funcs, dtyps, tr_context, ctxt1), ts2) =
      ((empty_tr_context, ctxt), ts1)
      |-> (if null fp_kinds then no_dtyps else collect_co_datatypes fp_kinds)

    fun is_binder (Const (\<^const_name>\<open>Let\<close>, _) $ _) = true
      | is_binder t = Lambda_Lifting.is_quantifier t

    fun mk_trigger ((q as Const (\<^const_name>\<open>All\<close>, _)) $ Abs (n, T, t)) =
          q $ Abs (n, T, mk_trigger t)
      | mk_trigger (eq as (Const (\<^const_name>\<open>HOL.eq\<close>, T) $ lhs $ _)) =
          Term.domain_type T --> \<^typ>\<open>pattern\<close>
          |> (fn T => Const (\<^const_name>\<open>pat\<close>, T) $ lhs)
          |> SMT_Util.mk_symb_list \<^typ>\<open>pattern\<close> o single
          |> SMT_Util.mk_symb_list \<^typ>\<open>pattern symb_list\<close> o single
          |> (fn t => \<^Const>\<open>trigger for t eq\<close>)
      | mk_trigger t = t

    val (ctxt2, (ts3, ll_defs)) =
      ts2
      |> eta_expand ctxt1 funcs
      |> rpair ctxt1
      |-> Lambda_Lifting.lift_lambdas NONE is_binder
      |-> (fn (ts', ll_defs) => fn ctxt' =>
        let
          val ts'' = map mk_trigger ll_defs @ ts'
            |> order = SMT_Util.First_Order ? intro_explicit_application ctxt' funcs
        in
          (ctxt', (ts'', ll_defs))
        end)
    val ((rewrite_rules, builtin), ts4) = folify ctxt2 ts3
      |>> order = SMT_Util.First_Order ? apfst (cons fun_app_eq)
  in
    (ts4, tr_context)
    |-> intermediate logic dtyps (builtin SMT_Builtin.dest_builtin) ctxt2
    |>> uncurry (serialize smt_options comments)
    ||> replay_data_of ctxt2 ll_defs rewrite_rules ithms
  end

end;
