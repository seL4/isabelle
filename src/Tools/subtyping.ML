(*  Title:      Tools/subtyping.ML
    Author:     Dmitriy Traytel, TU Muenchen

Coercive subtyping via subtype constraints.
*)

signature SUBTYPING =
sig
  val coercion_enabled: bool Config.T
  val add_type_map: term -> Context.generic -> Context.generic
  val add_coercion: term -> Context.generic -> Context.generic
  val print_coercions: Proof.context -> unit
  val print_coercion_maps: Proof.context -> unit
  val setup: theory -> theory
end;

structure Subtyping: SUBTYPING =
struct

(** coercions data **)

datatype variance = COVARIANT | CONTRAVARIANT | INVARIANT | INVARIANT_TO of typ;

datatype data = Data of
  {coes: (term * ((typ list * typ list) * term list)) Symreltab.table,  (*coercions table*)
   (*full coercions graph - only used at coercion declaration/deletion*)
   full_graph: int Graph.T,
   (*coercions graph restricted to base types - for efficiency reasons strored in the context*)
   coes_graph: int Graph.T,
   tmaps: (term * variance list) Symtab.table};  (*map functions*)

fun make_data (coes, full_graph, coes_graph, tmaps) =
  Data {coes = coes, full_graph = full_graph, coes_graph = coes_graph, tmaps = tmaps};

fun merge_error_coes (a, b) =
  error ("Cannot merge coercion tables.\nConflicting declarations for coercions from " ^
    quote a ^ " to " ^ quote b ^ ".");

fun merge_error_tmaps C =
  error ("Cannot merge coercion map tables.\nConflicting declarations for the constructor " ^
    quote C ^ ".");

structure Data = Generic_Data
(
  type T = data;
  val empty = make_data (Symreltab.empty, Graph.empty, Graph.empty, Symtab.empty);
  val extend = I;
  fun merge
    (Data {coes = coes1, full_graph = full_graph1, coes_graph = coes_graph1, tmaps = tmaps1},
      Data {coes = coes2, full_graph = full_graph2, coes_graph = coes_graph2, tmaps = tmaps2}) =
    make_data (Symreltab.merge (eq_pair (op aconv)
        (eq_pair (eq_pair (eq_list (op =)) (eq_list (op =))) (eq_list (op aconv))))
        (coes1, coes2) handle Symreltab.DUP key => merge_error_coes key,
      Graph.merge (op =) (full_graph1, full_graph2),
      Graph.merge (op =) (coes_graph1, coes_graph2),
      Symtab.merge (eq_pair (op aconv) (op =)) (tmaps1, tmaps2)
        handle Symtab.DUP key => merge_error_tmaps key);
);

fun map_data f =
  Data.map (fn Data {coes, full_graph, coes_graph, tmaps} =>
    make_data (f (coes, full_graph, coes_graph, tmaps)));

fun map_coes f =
  map_data (fn (coes, full_graph, coes_graph, tmaps) =>
    (f coes, full_graph, coes_graph, tmaps));

fun map_coes_graph f =
  map_data (fn (coes, full_graph, coes_graph, tmaps) =>
    (coes, full_graph, f coes_graph, tmaps));

fun map_coes_and_graphs f =
  map_data (fn (coes, full_graph, coes_graph, tmaps) =>
    let val (coes', full_graph', coes_graph') = f (coes, full_graph, coes_graph);
    in (coes', full_graph', coes_graph', tmaps) end);

fun map_tmaps f =
  map_data (fn (coes, full_graph, coes_graph, tmaps) =>
    (coes, full_graph, coes_graph, f tmaps));

val rep_data = (fn Data args => args) o Data.get o Context.Proof;

val coes_of = #coes o rep_data;
val coes_graph_of = #coes_graph o rep_data;
val tmaps_of = #tmaps o rep_data;



(** utils **)

fun restrict_graph G = Graph.restrict (fn x => Graph.get_node G x = 0) G;

fun nameT (Type (s, [])) = s;
fun t_of s = Type (s, []);

fun sort_of (TFree (_, S)) = SOME S
  | sort_of (TVar (_, S)) = SOME S
  | sort_of _ = NONE;

val is_typeT = fn (Type _) => true | _ => false;
val is_stypeT = fn (Type (_, [])) => true | _ => false;
val is_compT = fn (Type (_, _ :: _)) => true | _ => false;
val is_freeT = fn (TFree _) => true | _ => false;
val is_fixedvarT = fn (TVar (xi, _)) => not (Type_Infer.is_param xi) | _ => false;
val is_funtype = fn (Type ("fun", [_, _])) => true | _ => false;
val is_identity = fn (Abs (_, _, Bound 0)) => true | _ => false;

fun instantiate t Ts = Term.subst_TVars
  ((Term.add_tvar_namesT (fastype_of t) []) ~~ rev Ts) t;

exception COERCION_GEN_ERROR of unit -> string;

fun inst_collect tye err T U =
  (case (T, Type_Infer.deref tye U) of
    (TVar (xi, S), U) => [(xi, U)]
  | (Type (a, Ts), Type (b, Us)) =>
      if a <> b then raise error (err ()) else inst_collects tye err Ts Us
  | (_, U') => if T <> U' then error (err ()) else [])
and inst_collects tye err Ts Us =
  fold2 (fn T => fn U => fn is => inst_collect tye err T U @ is) Ts Us [];


(* unification *)

exception NO_UNIFIER of string * typ Vartab.table;

fun unify weak ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val arity_sorts = Type.arity_sorts (Context.pretty ctxt) (Sign.tsig_of thy);


    (* adjust sorts of parameters *)

    fun not_of_sort x S' S =
      "Variable " ^ x ^ "::" ^ Syntax.string_of_sort ctxt S' ^ " not of sort " ^
        Syntax.string_of_sort ctxt S;

    fun meet (_, []) tye_idx = tye_idx
      | meet (Type (a, Ts), S) (tye_idx as (tye, _)) =
          meets (Ts, arity_sorts a S handle ERROR msg => raise NO_UNIFIER (msg, tye)) tye_idx
      | meet (TFree (x, S'), S) (tye_idx as (tye, _)) =
          if Sign.subsort thy (S', S) then tye_idx
          else raise NO_UNIFIER (not_of_sort x S' S, tye)
      | meet (TVar (xi, S'), S) (tye_idx as (tye, idx)) =
          if Sign.subsort thy (S', S) then tye_idx
          else if Type_Infer.is_param xi then
            (Vartab.update_new
              (xi, Type_Infer.mk_param idx (Sign.inter_sort thy (S', S))) tye, idx + 1)
          else raise NO_UNIFIER (not_of_sort (Term.string_of_vname xi) S' S, tye)
    and meets (T :: Ts, S :: Ss) (tye_idx as (tye, _)) =
          meets (Ts, Ss) (meet (Type_Infer.deref tye T, S) tye_idx)
      | meets _ tye_idx = tye_idx;

    val weak_meet = if weak then fn _ => I else meet


    (* occurs check and assignment *)

    fun occurs_check tye xi (TVar (xi', _)) =
          if xi = xi' then raise NO_UNIFIER ("Occurs check!", tye)
          else
            (case Vartab.lookup tye xi' of
              NONE => ()
            | SOME T => occurs_check tye xi T)
      | occurs_check tye xi (Type (_, Ts)) = List.app (occurs_check tye xi) Ts
      | occurs_check _ _ _ = ();

    fun assign xi (T as TVar (xi', _)) S env =
          if xi = xi' then env
          else env |> weak_meet (T, S) |>> Vartab.update_new (xi, T)
      | assign xi T S (env as (tye, _)) =
          (occurs_check tye xi T; env |> weak_meet (T, S) |>> Vartab.update_new (xi, T));


    (* unification *)

    fun show_tycon (a, Ts) =
      quote (Syntax.string_of_typ ctxt (Type (a, replicate (length Ts) dummyT)));

    fun unif (T1, T2) (env as (tye, _)) =
      (case pairself (`Type_Infer.is_paramT o Type_Infer.deref tye) (T1, T2) of
        ((true, TVar (xi, S)), (_, T)) => assign xi T S env
      | ((_, T), (true, TVar (xi, S))) => assign xi T S env
      | ((_, Type (a, Ts)), (_, Type (b, Us))) =>
          if weak andalso null Ts andalso null Us then env
          else if a <> b then
            raise NO_UNIFIER
              ("Clash of types " ^ show_tycon (a, Ts) ^ " and " ^ show_tycon (b, Us), tye)
          else fold unif (Ts ~~ Us) env
      | ((_, T), (_, U)) => if T = U then env else raise NO_UNIFIER ("", tye));

  in unif end;

val weak_unify = unify true;
val strong_unify = unify false;


(* Typ_Graph shortcuts *)

fun get_preds G T = Typ_Graph.all_preds G [T];
fun get_succs G T = Typ_Graph.all_succs G [T];
fun maybe_new_typnode T G = perhaps (try (Typ_Graph.new_node (T, ()))) G;
fun maybe_new_typnodes Ts G = fold maybe_new_typnode Ts G;
fun new_imm_preds G Ts =  (* FIXME inefficient *)
  subtract (op =) Ts (distinct (op =) (maps (Typ_Graph.immediate_preds G) Ts));
fun new_imm_succs G Ts =  (* FIXME inefficient *)
  subtract (op =) Ts (distinct (op =) (maps (Typ_Graph.immediate_succs G) Ts));


(* Graph shortcuts *)

fun maybe_new_node s G = perhaps (try (Graph.new_node s)) G
fun maybe_new_nodes ss G = fold maybe_new_node ss G



(** error messages **)

infixr ++> (* lazy error msg composition *)

fun err ++> str = err #> suffix str

fun gen_msg err msg =
  err () ^ "\nNow trying to infer coercions globally.\n\nCoercion inference failed" ^
  (if msg = "" then "" else ":\n" ^ msg) ^ "\n";

fun prep_output ctxt tye bs ts Ts =
  let
    val (Ts_bTs', ts') = Type_Infer.finish ctxt tye (Ts @ map snd bs, ts);
    val (Ts', Ts'') = chop (length Ts) Ts_bTs';
    fun prep t =
      let val xs = rev (Term.variant_frees t (rev (map fst bs ~~ Ts'')))
      in Term.subst_bounds (map Syntax_Trans.mark_boundT xs, t) end;
  in (map prep ts', Ts') end;

fun err_loose i = error ("Loose bound variable: B." ^ string_of_int i);

fun unif_failed msg =
  "Type unification failed" ^ (if msg = "" then "" else ": " ^ msg) ^ "\n\n";

fun err_appl_msg ctxt msg tye bs t T u U () =
  let val ([t', u'], [T', U']) = prep_output ctxt tye bs [t, u] [T, U]
  in unif_failed msg ^ Type.appl_error ctxt t' T' u' U' ^ "\n" end;

fun err_list ctxt msg tye Ts =
  let
    val (_, Ts') = prep_output ctxt tye [] [] Ts;
    val text =
      msg ^ "\nCannot unify a list of types that should be the same:\n" ^
        Pretty.string_of (Pretty.list "[" "]" (map (Syntax.pretty_typ ctxt) Ts'));
  in
    error text
  end;

fun err_bound ctxt msg tye packs =
  let
    val (ts, Ts) = fold
      (fn (bs, t $ u, U, _, U') => fn (ts, Ts) =>
        let val (t', T') = prep_output ctxt tye bs [t, u] [U', U]
        in (t' :: ts, T' :: Ts) end)
      packs ([], []);
    val text = msg ^ "\n" ^ Pretty.string_of (
        Pretty.big_list "Cannot fulfil subtype constraints:"
        (map2 (fn [t, u] => fn [T, U] =>
          Pretty.block [
            Syntax.pretty_typ ctxt T, Pretty.brk 2, Pretty.str "<:", Pretty.brk 2,
            Syntax.pretty_typ ctxt U, Pretty.brk 3,
            Pretty.str "from function application", Pretty.brk 2,
            Pretty.block [Syntax.pretty_term ctxt (t $ u)]])
        ts Ts))
  in
    error text
  end;



(** constraint generation **)

fun generate_constraints ctxt err =
  let
    fun gen cs _ (Const (_, T)) tye_idx = (T, tye_idx, cs)
      | gen cs _ (Free (_, T)) tye_idx = (T, tye_idx, cs)
      | gen cs _ (Var (_, T)) tye_idx = (T, tye_idx, cs)
      | gen cs bs (Bound i) tye_idx =
          (snd (nth bs i handle General.Subscript => err_loose i), tye_idx, cs)
      | gen cs bs (Abs (x, T, t)) tye_idx =
          let val (U, tye_idx', cs') = gen cs ((x, T) :: bs) t tye_idx
          in (T --> U, tye_idx', cs') end
      | gen cs bs (t $ u) tye_idx =
          let
            val (T, tye_idx', cs') = gen cs bs t tye_idx;
            val (U', (tye, idx), cs'') = gen cs' bs u tye_idx';
            val U = Type_Infer.mk_param idx [];
            val V = Type_Infer.mk_param (idx + 1) [];
            val tye_idx'' = strong_unify ctxt (U --> V, T) (tye, idx + 2)
              handle NO_UNIFIER (msg, _) => error (gen_msg err msg);
            val error_pack = (bs, t $ u, U, V, U');
          in (V, (tye_idx''),
            ((U', U), error_pack) :: cs'') end;
  in
    gen [] []
  end;



(** constraint resolution **)

exception BOUND_ERROR of string;

fun process_constraints ctxt err cs tye_idx =
  let
    val thy = Proof_Context.theory_of ctxt;

    val coes_graph = coes_graph_of ctxt;
    val tmaps = tmaps_of ctxt;
    val arity_sorts = Type.arity_sorts (Context.pretty ctxt) (Sign.tsig_of thy);

    fun split_cs _ [] = ([], [])
      | split_cs f (c :: cs) =
          (case pairself f (fst c) of
            (false, false) => apsnd (cons c) (split_cs f cs)
          | _ => apfst (cons c) (split_cs f cs));

    fun unify_list (T :: Ts) tye_idx =
      fold (fn U => fn tye_idx' => strong_unify ctxt (T, U) tye_idx') Ts tye_idx;


    (* check whether constraint simplification will terminate using weak unification *)

    val _ = fold (fn (TU, _) => fn tye_idx =>
      weak_unify ctxt TU tye_idx handle NO_UNIFIER (msg, _) =>
        error (gen_msg err ("weak unification of subtype constraints fails\n" ^ msg))) cs tye_idx;


    (* simplify constraints *)

    fun simplify_constraints cs tye_idx =
      let
        fun contract a Ts Us error_pack done todo tye idx =
          let
            val arg_var =
              (case Symtab.lookup tmaps a of
                (*everything is invariant for unknown constructors*)
                NONE => replicate (length Ts) INVARIANT
              | SOME av => snd av);
            fun new_constraints (variance, constraint) (cs, tye_idx) =
              (case variance of
                COVARIANT => (constraint :: cs, tye_idx)
              | CONTRAVARIANT => (swap constraint :: cs, tye_idx)
              | INVARIANT_TO T => (cs, unify_list [T, fst constraint, snd constraint] tye_idx
                  handle NO_UNIFIER (msg, _) =>
                    err_list ctxt (gen_msg err
                      "failed to unify invariant arguments w.r.t. to the known map function" ^ msg)
                      (fst tye_idx) (T :: Ts))
              | INVARIANT => (cs, strong_unify ctxt constraint tye_idx
                  handle NO_UNIFIER (msg, _) =>
                    error (gen_msg err ("failed to unify invariant arguments" ^ msg))));
            val (new, (tye', idx')) = apfst (fn cs => (cs ~~ replicate (length cs) error_pack))
              (fold new_constraints (arg_var ~~ (Ts ~~ Us)) ([], (tye, idx)));
            val test_update = is_compT orf is_freeT orf is_fixedvarT;
            val (ch, done') =
              if not (null new) then ([], done)
              else split_cs (test_update o Type_Infer.deref tye') done;
            val todo' = ch @ todo;
          in
            simplify done' (new @ todo') (tye', idx')
          end
        (*xi is definitely a parameter*)
        and expand varleq xi S a Ts error_pack done todo tye idx =
          let
            val n = length Ts;
            val args = map2 Type_Infer.mk_param (idx upto idx + n - 1) (arity_sorts a S);
            val tye' = Vartab.update_new (xi, Type(a, args)) tye;
            val (ch, done') = split_cs (is_compT o Type_Infer.deref tye') done;
            val todo' = ch @ todo;
            val new =
              if varleq then (Type(a, args), Type (a, Ts))
              else (Type (a, Ts), Type (a, args));
          in
            simplify done' ((new, error_pack) :: todo') (tye', idx + n)
          end
        (*TU is a pair of a parameter and a free/fixed variable*)
        and eliminate TU done todo tye idx =
          let
            val [TVar (xi, S)] = filter Type_Infer.is_paramT TU;
            val [T] = filter_out Type_Infer.is_paramT TU;
            val SOME S' = sort_of T;
            val test_update = if is_freeT T then is_freeT else is_fixedvarT;
            val tye' = Vartab.update_new (xi, T) tye;
            val (ch, done') = split_cs (test_update o Type_Infer.deref tye') done;
            val todo' = ch @ todo;
          in
            if Sign.subsort thy (S', S) (*TODO check this*)
            then simplify done' todo' (tye', idx)
            else error (gen_msg err "sort mismatch")
          end
        and simplify done [] tye_idx = (done, tye_idx)
          | simplify done (((T, U), error_pack) :: todo) (tye_idx as (tye, idx)) =
              (case (Type_Infer.deref tye T, Type_Infer.deref tye U) of
                (T1 as Type (a, []), T2 as Type (b, [])) =>
                  if a = b then simplify done todo tye_idx
                  else if Graph.is_edge coes_graph (a, b) then simplify done todo tye_idx
                  else error (gen_msg err (quote (Syntax.string_of_typ ctxt T1) ^
                    " is not a subtype of " ^ quote (Syntax.string_of_typ ctxt T2)))
              | (Type (a, Ts), Type (b, Us)) =>
                  if a <> b then error (gen_msg err "different constructors")
                    (fst tye_idx) error_pack
                  else contract a Ts Us error_pack done todo tye idx
              | (TVar (xi, S), Type (a, Ts as (_ :: _))) =>
                  expand true xi S a Ts error_pack done todo tye idx
              | (Type (a, Ts as (_ :: _)), TVar (xi, S)) =>
                  expand false xi S a Ts error_pack done todo tye idx
              | (T, U) =>
                  if T = U then simplify done todo tye_idx
                  else if exists (is_freeT orf is_fixedvarT) [T, U] andalso
                    exists Type_Infer.is_paramT [T, U]
                  then eliminate [T, U] done todo tye idx
                  else if exists (is_freeT orf is_fixedvarT) [T, U]
                  then error (gen_msg err "not eliminated free/fixed variables")
                  else simplify (((T, U), error_pack) :: done) todo tye_idx);
      in
        simplify [] cs tye_idx
      end;


    (* do simplification *)

    val (cs', tye_idx') = simplify_constraints cs tye_idx;

    fun find_error_pack lower T' = map_filter
      (fn ((T, U), pack) => if if lower then T' = U else T' = T then SOME pack else NONE) cs';

    fun find_cycle_packs nodes =
      let
        val (but_last, last) = split_last nodes
        val pairs = (last, hd nodes) :: (but_last ~~ tl nodes);
      in
        map_filter
          (fn (TU, pack) => if member (op =) pairs TU then SOME pack else NONE)
          cs'
      end;

    (*styps stands either for supertypes or for subtypes of a type T
      in terms of the subtype-relation (excluding T itself)*)
    fun styps super T =
      (if super then Graph.immediate_succs else Graph.immediate_preds) coes_graph T
        handle Graph.UNDEF _ => [];

    fun minmax sup (T :: Ts) =
      let
        fun adjust T U = if sup then (T, U) else (U, T);
        fun extract T [] = T
          | extract T (U :: Us) =
              if Graph.is_edge coes_graph (adjust T U) then extract T Us
              else if Graph.is_edge coes_graph (adjust U T) then extract U Us
              else raise BOUND_ERROR "uncomparable types in type list";
      in
        t_of (extract T Ts)
      end;

    fun ex_styp_of_sort super T styps_and_sorts =
      let
        fun adjust T U = if super then (T, U) else (U, T);
        fun styp_test U Ts = forall
          (fn T => T = U orelse Graph.is_edge coes_graph (adjust U T)) Ts;
        fun fitting Ts S U = Sign.of_sort thy (t_of U, S) andalso styp_test U Ts
      in
        forall (fn (Ts, S) => exists (fitting Ts S) (T :: styps super T)) styps_and_sorts
      end;

    (* computes the tightest possible, correct assignment for 'a::S
       e.g. in the supremum case (sup = true):
               ------- 'a::S---
              /        /    \  \
             /        /      \  \
        'b::C1   'c::C2 ...  T1 T2 ...

       sorts - list of sorts [C1, C2, ...]
       T::Ts - non-empty list of base types [T1, T2, ...]
    *)
    fun tightest sup S styps_and_sorts (T :: Ts) =
      let
        fun restriction T = Sign.of_sort thy (t_of T, S)
          andalso ex_styp_of_sort (not sup) T styps_and_sorts;
        fun candidates T = inter (op =) (filter restriction (T :: styps sup T));
      in
        (case fold candidates Ts (filter restriction (T :: styps sup T)) of
          [] => raise BOUND_ERROR ("no " ^ (if sup then "supremum" else "infimum"))
        | [T] => t_of T
        | Ts => minmax sup Ts)
      end;

    fun build_graph G [] tye_idx = (G, tye_idx)
      | build_graph G ((T, U) :: cs) tye_idx =
        if T = U then build_graph G cs tye_idx
        else
          let
            val G' = maybe_new_typnodes [T, U] G;
            val (G'', tye_idx') = (Typ_Graph.add_edge_acyclic (T, U) G', tye_idx)
              handle Typ_Graph.CYCLES cycles =>
                let
                  val (tye, idx) =
                    fold
                      (fn cycle => fn tye_idx' => (unify_list cycle tye_idx'
                        handle NO_UNIFIER (msg, _) =>
                          err_bound ctxt
                            (gen_msg err ("constraint cycle not unifiable" ^ msg)) (fst tye_idx)
                            (find_cycle_packs cycle)))
                      cycles tye_idx
                in
                  collapse (tye, idx) cycles G
                end
          in
            build_graph G'' cs tye_idx'
          end
    and collapse (tye, idx) cycles G = (*nodes non-empty list*)
      let
        (*all cycles collapse to one node,
          because all of them share at least the nodes x and y*)
        val nodes = (distinct (op =) (flat cycles));
        val T = Type_Infer.deref tye (hd nodes);
        val P = new_imm_preds G nodes;
        val S = new_imm_succs G nodes;
        val G' = fold Typ_Graph.del_node (tl nodes) G;
        fun check_and_gen super T' =
          let val U = Type_Infer.deref tye T';
          in
            if not (is_typeT T) orelse not (is_typeT U) orelse T = U
            then if super then (hd nodes, T') else (T', hd nodes)
            else
              if super andalso
                Graph.is_edge coes_graph (nameT T, nameT U) then (hd nodes, T')
              else if not super andalso
                Graph.is_edge coes_graph (nameT U, nameT T) then (T', hd nodes)
              else err_bound ctxt (gen_msg err "cycle elimination produces inconsistent graph")
                    (fst tye_idx)
                    (maps find_cycle_packs cycles @ find_error_pack super T')
          end;
      in
        build_graph G' (map (check_and_gen false) P @ map (check_and_gen true) S) (tye, idx)
      end;

    fun assign_bound lower G key (tye_idx as (tye, _)) =
      if Type_Infer.is_paramT (Type_Infer.deref tye key) then
        let
          val TVar (xi, S) = Type_Infer.deref tye key;
          val get_bound = if lower then get_preds else get_succs;
          val raw_bound = get_bound G key;
          val bound = map (Type_Infer.deref tye) raw_bound;
          val not_params = filter_out Type_Infer.is_paramT bound;
          fun to_fulfil T =
            (case sort_of T of
              NONE => NONE
            | SOME S =>
                SOME
                  (map nameT
                    (filter_out Type_Infer.is_paramT
                      (map (Type_Infer.deref tye) (get_bound G T))), S));
          val styps_and_sorts = distinct (op =) (map_filter to_fulfil raw_bound);
          val assignment =
            if null bound orelse null not_params then NONE
            else SOME (tightest lower S styps_and_sorts (map nameT not_params)
                handle BOUND_ERROR msg =>
                  err_bound ctxt (gen_msg err msg) tye (find_error_pack lower key))
        in
          (case assignment of
            NONE => tye_idx
          | SOME T =>
              if Type_Infer.is_paramT T then tye_idx
              else if lower then (*upper bound check*)
                let
                  val other_bound = map (Type_Infer.deref tye) (get_succs G key);
                  val s = nameT T;
                in
                  if subset (op = o apfst nameT) (filter is_typeT other_bound, s :: styps true s)
                  then apfst (Vartab.update (xi, T)) tye_idx
                  else err_bound ctxt (gen_msg err ("assigned base type " ^
                    quote (Syntax.string_of_typ ctxt T) ^
                    " clashes with the upper bound of variable " ^
                    Syntax.string_of_typ ctxt (TVar(xi, S)))) tye (find_error_pack (not lower) key)
                end
              else apfst (Vartab.update (xi, T)) tye_idx)
        end
      else tye_idx;

    val assign_lb = assign_bound true;
    val assign_ub = assign_bound false;

    fun assign_alternating ts' ts G tye_idx =
      if ts' = ts then tye_idx
      else
        let
          val (tye_idx' as (tye, _)) = fold (assign_lb G) ts tye_idx
            |> fold (assign_ub G) ts;
        in
          assign_alternating ts
            (filter (Type_Infer.is_paramT o Type_Infer.deref tye) ts) G tye_idx'
        end;

    (*Unify all weakly connected components of the constraint forest,
      that contain only params. These are the only WCCs that contain
      params anyway.*)
    fun unify_params G (tye_idx as (tye, _)) =
      let
        val max_params =
          filter (Type_Infer.is_paramT o Type_Infer.deref tye) (Typ_Graph.maximals G);
        val to_unify = map (fn T => T :: get_preds G T) max_params;
      in
        fold
          (fn Ts => fn tye_idx' => unify_list Ts tye_idx'
            handle NO_UNIFIER (msg, _) => err_list ctxt (gen_msg err msg) (fst tye_idx) Ts)
          to_unify tye_idx
      end;

    fun solve_constraints G tye_idx = tye_idx
      |> assign_alternating [] (Typ_Graph.keys G) G
      |> unify_params G;
  in
    build_graph Typ_Graph.empty (map fst cs') tye_idx'
      |-> solve_constraints
  end;



(** coercion insertion **)

fun gen_coercion ctxt err tye TU =
  let
    fun gen (T1, T2) = (case pairself (Type_Infer.deref tye) (T1, T2) of
        (T1 as (Type (a, [])), T2 as (Type (b, []))) =>
            if a = b
            then Abs (Name.uu, Type (a, []), Bound 0)
            else
              (case Symreltab.lookup (coes_of ctxt) (a, b) of
                NONE => raise COERCION_GEN_ERROR (err ++> quote (Syntax.string_of_typ ctxt T1) ^
                  " is not a subtype of " ^ quote (Syntax.string_of_typ ctxt T2))
              | SOME (co, _) => co)
      | (T1 as Type (a, Ts), T2 as Type (b, Us)) =>
            if a <> b
            then
              (case Symreltab.lookup (coes_of ctxt) (a, b) of
                (*immediate error - cannot fix complex coercion with the global algorithm*)
                NONE => error (err () ^ "No coercion known for type constructors: " ^
                  quote a ^ " and " ^ quote b)
              | SOME (co, ((Ts', Us'), _)) =>
                  let
                    val co_before = gen (T1, Type (a, Ts'));
                    val coT = range_type (fastype_of co_before);
                    val insts = inst_collect tye (err ++> "Could not insert complex coercion")
                      (domain_type (fastype_of co)) coT;
                    val co' = Term.subst_TVars insts co;
                    val co_after = gen (Type (b, (map (typ_subst_TVars insts) Us')), T2);
                  in
                    Abs (Name.uu, T1, Library.foldr (op $)
                      (filter (not o is_identity) [co_after, co', co_before], Bound 0))
                  end)
            else
              let
                fun sub_co (COVARIANT, TU) = SOME (gen TU)
                  | sub_co (CONTRAVARIANT, TU) = SOME (gen (swap TU))
                  | sub_co (INVARIANT_TO _, _) = NONE;
                fun ts_of [] = []
                  | ts_of (Type ("fun", [x1, x2]) :: xs) = x1 :: x2 :: (ts_of xs);
              in
                (case Symtab.lookup (tmaps_of ctxt) a of
                  NONE =>
                    if Type.could_unify (T1, T2)
                    then Abs (Name.uu, T1, Bound 0)
                    else raise COERCION_GEN_ERROR
                      (err ++> "No map function for " ^ quote a ^ " known")
                | SOME tmap =>
                    let
                      val used_coes = map_filter sub_co ((snd tmap) ~~ (Ts ~~ Us));
                    in
                      if null (filter (not o is_identity) used_coes)
                      then Abs (Name.uu, Type (a, Ts), Bound 0)
                      else Term.list_comb
                        (instantiate (fst tmap) (ts_of (map fastype_of used_coes)), used_coes)
                    end)
              end
      | (T, U) =>
            if Type.could_unify (T, U)
            then Abs (Name.uu, T, Bound 0)
            else raise COERCION_GEN_ERROR (err ++> "Cannot generate coercion from " ^
              quote (Syntax.string_of_typ ctxt T) ^ " to " ^
              quote (Syntax.string_of_typ ctxt U)));
  in
    gen TU
  end;

fun function_of ctxt err tye T =
  (case Type_Infer.deref tye T of
    Type (C, Ts) =>
      (case Symreltab.lookup (coes_of ctxt) (C, "fun") of
        NONE => error (err () ^ "No complex coercion from " ^ quote C ^ " to fun")
      | SOME (co, ((Ts', _), _)) =>
        let
          val co_before = gen_coercion ctxt err tye (Type (C, Ts), Type (C, Ts'));
          val coT = range_type (fastype_of co_before);
          val insts = inst_collect tye (err ++> "Could not insert complex coercion")
            (domain_type (fastype_of co)) coT;
          val co' = Term.subst_TVars insts co;
        in
          Abs (Name.uu, Type (C, Ts), Library.foldr (op $)
            (filter (not o is_identity) [co', co_before], Bound 0))
        end)
  | T' => error (err () ^ "No complex coercion from " ^
      quote (Syntax.string_of_typ ctxt T') ^ " to fun"));

fun insert_coercions ctxt (tye, idx) ts =
  let
    fun insert _ (Const (c, T)) = (Const (c, T), T)
      | insert _ (Free (x, T)) = (Free (x, T), T)
      | insert _ (Var (xi, T)) = (Var (xi, T), T)
      | insert bs (Bound i) =
          let val T = nth bs i handle General.Subscript => err_loose i;
          in (Bound i, T) end
      | insert bs (Abs (x, T, t)) =
          let val (t', T') = insert (T :: bs) t;
          in (Abs (x, T, t'), T --> T') end
      | insert bs (t $ u) =
          let
            val (t', Type ("fun", [U, T])) = apsnd (Type_Infer.deref tye) (insert bs t);
            val (u', U') = insert bs u;
          in
            if can (fn TU => strong_unify ctxt TU (tye, 0)) (U, U')
            then (t' $ u', T)
            else (t' $ (gen_coercion ctxt (K "") tye (U', U) $ u'), T)
          end
  in
    map (fst o insert []) ts
  end;



(** assembling the pipeline **)

fun coercion_infer_types ctxt raw_ts =
  let
    val (idx, ts) = Type_Infer_Context.prepare ctxt raw_ts;

    fun inf _ (t as (Const (_, T))) tye_idx = (t, T, tye_idx)
      | inf _ (t as (Free (_, T))) tye_idx = (t, T, tye_idx)
      | inf _ (t as (Var (_, T))) tye_idx = (t, T, tye_idx)
      | inf bs (t as (Bound i)) tye_idx =
          (t, snd (nth bs i handle General.Subscript => err_loose i), tye_idx)
      | inf bs (Abs (x, T, t)) tye_idx =
          let val (t', U, tye_idx') = inf ((x, T) :: bs) t tye_idx
          in (Abs (x, T, t'), T --> U, tye_idx') end
      | inf bs (t $ u) tye_idx =
          let
            val (t', T, tye_idx') = inf bs t tye_idx;
            val (u', U, (tye, idx)) = inf bs u tye_idx';
            val V = Type_Infer.mk_param idx [];
            val (tu, tye_idx'') = (t' $ u', strong_unify ctxt (U --> V, T) (tye, idx + 1))
              handle NO_UNIFIER (msg, tye') =>
                let
                  val err = err_appl_msg ctxt msg tye' bs t T u U;
                  val W = Type_Infer.mk_param (idx + 1) [];
                  val (t'', (tye', idx')) =
                    (t', strong_unify ctxt (W --> V, T) (tye, idx + 2))
                      handle NO_UNIFIER _ =>
                        let
                          val err' =
                            err ++> "\nLocal coercion insertion on the operator failed:\n";
                          val co = function_of ctxt err' tye T;
                          val (t'', T'', tye_idx'') = inf bs (co $ t') (tye, idx + 2);
                        in
                          (t'', strong_unify ctxt (W --> V, T'') tye_idx''
                             handle NO_UNIFIER (msg, _) => error (err' () ^ msg))
                        end;
                  val err' = err ++> (if t' aconv t'' then ""
                    else "\nSuccessfully coerced the operand to a function of type:\n" ^
                      Syntax.string_of_typ ctxt
                        (the_single (snd (prep_output ctxt tye' bs [] [W --> V]))) ^ "\n") ^
                      "\nLocal coercion insertion on the operand failed:\n";
                  val co = gen_coercion ctxt err' tye' (U, W);
                  val (u'', U', tye_idx') =
                    inf bs (if is_identity co then u else co $ u) (tye', idx');
                in
                  (t'' $ u'', strong_unify ctxt (U', W) tye_idx'
                    handle NO_UNIFIER (msg, _) => raise COERCION_GEN_ERROR (err' ++> msg))
                end;
          in (tu, V, tye_idx'') end;

    fun infer_single t tye_idx =
      let val (t, _, tye_idx') = inf [] t tye_idx
      in (t, tye_idx') end;

    val (ts', (tye, _)) = (fold_map infer_single ts (Vartab.empty, idx)
      handle COERCION_GEN_ERROR err =>
        let
          fun gen_single t (tye_idx, constraints) =
            let val (_, tye_idx', constraints') =
              generate_constraints ctxt (err ++> "\n") t tye_idx
            in (tye_idx', constraints' @ constraints) end;

          val (tye_idx, constraints) = fold gen_single ts ((Vartab.empty, idx), []);
          val (tye, idx) = process_constraints ctxt (err ++> "\n") constraints tye_idx;
        in
          (insert_coercions ctxt (tye, idx) ts, (tye, idx))
        end);

    val (_, ts'') = Type_Infer.finish ctxt tye ([], ts');
  in ts'' end;



(** installation **)

(* term check *)

val coercion_enabled = Attrib.setup_config_bool @{binding coercion_enabled} (K false);

val add_term_check =
  Syntax_Phases.term_check ~100 "coercions"
    (fn ctxt => Config.get ctxt coercion_enabled ? coercion_infer_types ctxt);


(* declarations *)

fun add_type_map raw_t context =
  let
    val ctxt = Context.proof_of context;
    val t = singleton (Variable.polymorphic ctxt) raw_t;

    fun err_str t = "\n\nThe provided function has the type:\n" ^
      Syntax.string_of_typ ctxt (fastype_of t) ^
      "\n\nThe general type signature of a map function is:" ^
      "\nf1 => f2 => ... => fn => C [x1, ..., xn] => C [y1, ..., yn]" ^
      "\nwhere C is a constructor and fi is of type (xi => yi) or (yi => xi).";

    val ((fis, T1), T2) = apfst split_last (strip_type (fastype_of t))
      handle Empty => error ("Not a proper map function:" ^ err_str t);

    fun gen_arg_var ([], []) = []
      | gen_arg_var ((T, T') :: Ts, (U, U') :: Us) =
          if U = U' then
            if is_stypeT U then INVARIANT_TO U :: gen_arg_var ((T, T') :: Ts, Us)
            else error ("Invariant xi and yi should be base types:" ^ err_str t)
          else if T = U andalso T' = U' then COVARIANT :: gen_arg_var (Ts, Us)
          else if T = U' andalso T' = U then CONTRAVARIANT :: gen_arg_var (Ts, Us)
          else error ("Functions do not apply to arguments correctly:" ^ err_str t)
      | gen_arg_var (_, Ts) =
          if forall (op = andf is_stypeT o fst) Ts
          then map (INVARIANT_TO o fst) Ts
          else error ("Different numbers of functions and variant arguments\n" ^ err_str t);

    (*retry flag needed to adjust the type lists, when given a map over type constructor fun*)
    fun check_map_fun fis (Type (C1, Ts)) (Type (C2, Us)) retry =
          if C1 = C2 andalso not (null fis) andalso forall is_funtype fis
          then ((map dest_funT fis, Ts ~~ Us), C1)
          else error ("Not a proper map function:" ^ err_str t)
      | check_map_fun fis T1 T2 true =
          let val (fis', T') = split_last fis
          in check_map_fun fis' T' (T1 --> T2) false end
      | check_map_fun _ _ _ _ = error ("Not a proper map function:" ^ err_str t);

    val res = check_map_fun fis T1 T2 true;
    val res_av = gen_arg_var (fst res);
  in
    map_tmaps (Symtab.update (snd res, (t, res_av))) context
  end;

fun transitive_coercion ctxt tab G (a, b) =
  let
    fun safe_app t (Abs (x, T', u)) =
      let
        val t' = map_types Type_Infer.paramify_vars t;
      in
        singleton (coercion_infer_types ctxt) (Abs(x, T', (t' $ u)))
      end;
    val path = hd (Graph.irreducible_paths G (a, b));
    val path' = fst (split_last path) ~~ tl path;
    val coercions = map (fst o the o Symreltab.lookup tab) path';
    val trans_co = singleton (Variable.polymorphic ctxt)
      (fold safe_app coercions (Abs (Name.uu, dummyT, Bound 0)));
    val (Ts, Us) = pairself (snd o Term.dest_Type) (Term.dest_funT (type_of trans_co))
  in
    (trans_co, ((Ts, Us), coercions))
  end;

fun add_coercion raw_t context =
  let
    val ctxt = Context.proof_of context;
    val t = singleton (Variable.polymorphic ctxt) raw_t;

    fun err_coercion () = error ("Bad type for a coercion:\n" ^
        Syntax.string_of_term ctxt t ^ " :: " ^
        Syntax.string_of_typ ctxt (fastype_of t));

    val (T1, T2) = Term.dest_funT (fastype_of t)
      handle TYPE _ => err_coercion ();

    val (a, Ts) = Term.dest_Type T1
      handle TYPE _ => err_coercion ();

    val (b, Us) = Term.dest_Type T2
      handle TYPE _ => err_coercion ();

    fun coercion_data_update (tab, G, _) =
      let
        val G' = maybe_new_nodes [(a, length Ts), (b, length Us)] G
        val G'' = Graph.add_edge_trans_acyclic (a, b) G'
          handle Graph.CYCLES _ => error (
            Syntax.string_of_typ ctxt T2 ^ " is already a subtype of " ^
            Syntax.string_of_typ ctxt T1 ^ "!\n\nCannot add coercion of type: " ^
            Syntax.string_of_typ ctxt (T1 --> T2));
        val new_edges =
          flat (Graph.dest G'' |> map (fn (x, ys) => ys |> map_filter (fn y =>
            if Graph.is_edge G' (x, y) then NONE else SOME (x, y))));
        val G_and_new = Graph.add_edge (a, b) G';

        val tab' = fold
          (fn pair => fn tab =>
            Symreltab.update (pair, transitive_coercion ctxt tab G_and_new pair) tab)
          (filter (fn pair => pair <> (a, b)) new_edges)
          (Symreltab.update ((a, b), (t, ((Ts, Us), []))) tab);
      in
        (tab', G'', restrict_graph G'')
      end;
  in
    map_coes_and_graphs coercion_data_update context
  end;

fun delete_coercion raw_t context =
  let
    val ctxt = Context.proof_of context;
    val t = singleton (Variable.polymorphic ctxt) raw_t;

    fun err_coercion the = error ("Not" ^
        (if the then " the defined " else  " a ") ^ "coercion:\n" ^
        Syntax.string_of_term ctxt t ^ " :: " ^
        Syntax.string_of_typ ctxt (fastype_of t));

    val (T1, T2) = Term.dest_funT (fastype_of t)
      handle TYPE _ => err_coercion false;

    val (a, Ts) = dest_Type T1
      handle TYPE _ => err_coercion false;

    val (b, Us) = dest_Type T2
      handle TYPE _ => err_coercion false;

    fun delete_and_insert tab G =
      let
        val pairs =
          Symreltab.fold (fn ((a, b), (_, (_, ts))) => fn pairs =>
            if member (op aconv) ts t then (a, b) :: pairs else pairs) tab [(a, b)];
        fun delete pair (G, tab) = (Graph.del_edge pair G, Symreltab.delete_safe pair tab);
        val (G', tab') = fold delete pairs (G, tab);
        fun reinsert pair (G, xs) = (case (Graph.irreducible_paths G pair) of
              [] => (G, xs)
            | _ => (Graph.add_edge pair G, (pair, transitive_coercion ctxt tab' G' pair) :: xs));
        val (G'', ins) = fold reinsert pairs (G', []);
      in
        (fold Symreltab.update ins tab', G'', restrict_graph G'')
      end

    fun show_term t = Pretty.block [Syntax.pretty_term ctxt t,
      Pretty.str " :: ", Syntax.pretty_typ ctxt (fastype_of t)]

    fun coercion_data_update (tab, G, _) =
        (case Symreltab.lookup tab (a, b) of
          NONE => err_coercion false
        | SOME (t', (_, [])) => if t aconv t'
            then delete_and_insert tab G
            else err_coercion true
        | SOME (t', (_, ts)) => if t aconv t'
            then error ("Cannot delete the automatically derived coercion:\n" ^
              Syntax.string_of_term ctxt t ^ " :: " ^
              Syntax.string_of_typ ctxt (fastype_of t) ^
              Pretty.string_of (Pretty.big_list "\n\nDeleting one of the coercions:"
                (map show_term ts)) ^
              "\nwill also remove the transitive coercion.")
            else err_coercion true);
  in
    map_coes_and_graphs coercion_data_update context
  end;

fun print_coercions ctxt =
  let
    fun separate _ [] = ([], [])
      | separate P (x::xs) = (if P x then apfst else apsnd) (cons x) (separate P xs);
    val (simple, complex) =
      separate (fn (_, (_, ((Ts, Us), _))) => null Ts andalso null Us)
        (Symreltab.dest (coes_of ctxt));
    fun show_coercion ((a, b), (t, ((Ts, Us), _))) = Pretty.block [
      Syntax.pretty_typ ctxt (Type (a, Ts)),
      Pretty.brk 1, Pretty.str "<:", Pretty.brk 1,
      Syntax.pretty_typ ctxt (Type (b, Us)),
      Pretty.brk 3, Pretty.block [Pretty.str "using", Pretty.brk 1,
      Pretty.quote (Syntax.pretty_term ctxt t)]];
  in
    Pretty.big_list "Coercions:"
    [Pretty.big_list "between base types:" (map show_coercion simple),
     Pretty.big_list "other:" (map show_coercion complex)]
    |> Pretty.writeln
  end;

fun print_coercion_maps ctxt =
  let
    fun show_map (x, (t, _)) = Pretty.block [
      Pretty.str x, Pretty.str ":", Pretty.brk 1,
      Pretty.quote (Syntax.pretty_term ctxt t)];
  in
    Pretty.big_list "Coercion maps:" (map show_map (Symtab.dest (tmaps_of ctxt)))
    |> Pretty.writeln
  end;


(* theory setup *)

val setup =
  Context.theory_map add_term_check #>
  Attrib.setup @{binding coercion}
    (Args.term >> (fn t => Thm.declaration_attribute (K (add_coercion t))))
    "declaration of new coercions" #>
  Attrib.setup @{binding coercion_delete}
    (Args.term >> (fn t => Thm.declaration_attribute (K (delete_coercion t))))
    "deletion of coercions" #>
  Attrib.setup @{binding coercion_map}
    (Args.term >> (fn t => Thm.declaration_attribute (K (add_type_map t))))
    "declaration of new map functions";


(* outer syntax commands *)

val _ =
  Outer_Syntax.improper_command @{command_spec "print_coercions"} "print all coercions"
    (Scan.succeed (Toplevel.keep (print_coercions o Toplevel.context_of)))
val _ =
  Outer_Syntax.improper_command @{command_spec "print_coercion_maps"} "print all coercion maps"
    (Scan.succeed (Toplevel.keep (print_coercion_maps o Toplevel.context_of)))

end;
