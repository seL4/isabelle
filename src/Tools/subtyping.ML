(*  Title:      Tools/subtyping.ML
    Author:     Dmitriy Traytel, TU Muenchen

Coercive subtyping via subtype constraints.
*)

signature SUBTYPING =
sig
  datatype variance = COVARIANT | CONTRAVARIANT | INVARIANT
  val infer_types: Proof.context -> (string -> typ option) -> (indexname -> typ option) ->
    term list -> term list
  val add_type_map: term -> Context.generic -> Context.generic
  val add_coercion: term -> Context.generic -> Context.generic
  val gen_coercion: Proof.context -> typ Vartab.table -> (typ * typ) -> term
  val setup: theory -> theory
end;

structure Subtyping: SUBTYPING =
struct

(** coercions data **)

datatype variance = COVARIANT | CONTRAVARIANT | INVARIANT

datatype data = Data of
  {coes: term Symreltab.table,  (*coercions table*)
   coes_graph: unit Graph.T,  (*coercions graph*)
   tmaps: (term * variance list) Symtab.table};  (*map functions*)

fun make_data (coes, coes_graph, tmaps) =
  Data {coes = coes, coes_graph = coes_graph, tmaps = tmaps};

structure Data = Generic_Data
(
  type T = data;
  val empty = make_data (Symreltab.empty, Graph.empty, Symtab.empty);
  val extend = I;
  fun merge
    (Data {coes = coes1, coes_graph = coes_graph1, tmaps = tmaps1},
      Data {coes = coes2, coes_graph = coes_graph2, tmaps = tmaps2}) =
    make_data (Symreltab.merge (op aconv) (coes1, coes2),
      Graph.merge (op =) (coes_graph1, coes_graph2),
      Symtab.merge (eq_pair (op aconv) (op =)) (tmaps1, tmaps2));
);

fun map_data f =
  Data.map (fn Data {coes, coes_graph, tmaps} =>
    make_data (f (coes, coes_graph, tmaps)));

fun map_coes f =
  map_data (fn (coes, coes_graph, tmaps) =>
    (f coes, coes_graph, tmaps));

fun map_coes_graph f =
  map_data (fn (coes, coes_graph, tmaps) =>
    (coes, f coes_graph, tmaps));

fun map_coes_and_graph f =
  map_data (fn (coes, coes_graph, tmaps) =>
    let val (coes', coes_graph') = f (coes, coes_graph);
    in (coes', coes_graph', tmaps) end);

fun map_tmaps f =
  map_data (fn (coes, coes_graph, tmaps) =>
    (coes, coes_graph, f tmaps));

val rep_data = (fn Data args => args) o Data.get o Context.Proof;

val coes_of = #coes o rep_data;
val coes_graph_of = #coes_graph o rep_data;
val tmaps_of = #tmaps o rep_data;



(** utils **)

fun nameT (Type (s, [])) = s;
fun t_of s = Type (s, []);

fun sort_of (TFree (_, S)) = SOME S
  | sort_of (TVar (_, S)) = SOME S
  | sort_of _ = NONE;

val is_typeT = fn (Type _) => true | _ => false;
val is_compT = fn (Type (_, _ :: _)) => true | _ => false;
val is_freeT = fn (TFree _) => true | _ => false;
val is_fixedvarT = fn (TVar (xi, _)) => not (Type_Infer.is_param xi) | _ => false;


(* unification *)

exception TYPE_INFERENCE_ERROR of unit -> string;
exception NO_UNIFIER of string * typ Vartab.table;

fun unify weak ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val pp = Syntax.pp ctxt;
    val arity_sorts = Type.arity_sorts pp (Sign.tsig_of thy);


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

val add_edge = Typ_Graph.add_edge_acyclic;
fun get_preds G T = Typ_Graph.all_preds G [T];
fun get_succs G T = Typ_Graph.all_succs G [T];
fun maybe_new_typnode T G = perhaps (try (Typ_Graph.new_node (T, ()))) G;
fun maybe_new_typnodes Ts G = fold maybe_new_typnode Ts G;
fun new_imm_preds G Ts =
  subtract (op =) Ts (distinct (op =) (maps (Typ_Graph.imm_preds G) Ts));
fun new_imm_succs G Ts =
  subtract op= Ts (distinct (op =) (maps (Typ_Graph.imm_succs G) Ts));


(* Graph shortcuts *)

fun maybe_new_node s G = perhaps (try (Graph.new_node (s, ()))) G
fun maybe_new_nodes ss G = fold maybe_new_node ss G



(** error messages **)

fun gen_msg err msg = 
  err () ^ "\nNow trying to infer coercions:\n\nCoercion inference failed" ^ 
  (if msg = "" then "" else ": " ^ msg) ^ "\n";

fun prep_output ctxt tye bs ts Ts =
  let
    val (Ts_bTs', ts') = Type_Infer.finish ctxt tye (Ts @ map snd bs, ts);
    val (Ts', Ts'') = chop (length Ts) Ts_bTs';
    fun prep t =
      let val xs = rev (Term.variant_frees t (rev (map fst bs ~~ Ts'')))
      in Term.subst_bounds (map Syntax.mark_boundT xs, t) end;
  in (map prep ts', Ts') end;

fun err_loose i = error ("Loose bound variable: B." ^ string_of_int i);
  
fun unif_failed msg =
  "Type unification failed" ^ (if msg = "" then "" else ": " ^ msg) ^ "\n\n";

fun subtyping_err_appl_msg ctxt msg tye bs t T u U () =
  let val ([t', u'], [T', U']) = prep_output ctxt tye bs [t, u] [T, U]
  in msg ^ Type.appl_error (Syntax.pp ctxt) t' T' u' U' ^ "\n" end;
  
fun err_appl_msg ctxt msg tye bs t T u U () =
  let val ([t', u'], [T', U']) = prep_output ctxt tye bs [t, u] [T, U]
  in unif_failed msg ^ Type.appl_error (Syntax.pp ctxt) t' T' u' U' ^ "\n" end;

fun err_list ctxt msg tye Ts =
  let
    val (_, Ts') = prep_output ctxt tye [] [] Ts;
    val text = cat_lines ([msg,
      "Cannot unify a list of types that should be the same:",
      (Pretty.string_of (Pretty.list "[" "]" (map (Pretty.typ (Syntax.pp ctxt)) Ts')))]);
  in
    error text
  end;

fun err_bound ctxt msg tye packs =
  let
    val pp = Syntax.pp ctxt;
    val (ts, Ts) = fold
      (fn (bs, t $ u, U, _, U') => fn (ts, Ts) =>
        let val (t', T') = prep_output ctxt tye bs [t, u] [U', U]
        in (t' :: ts, T' :: Ts) end)
      packs ([], []);
    val text = cat_lines ([msg, "Cannot fulfil subtype constraints:"] @
        (map2 (fn [t, u] => fn [T, U] => Pretty.string_of (
          Pretty.block [
            Pretty.typ pp T, Pretty.brk 2, Pretty.str "<:", Pretty.brk 2, Pretty.typ pp U,
            Pretty.brk 3, Pretty.str "from function application", Pretty.brk 2,
            Pretty.block [Pretty.term pp (t $ u)]]))
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
          (snd (nth bs i handle Subscript => err_loose i), tye_idx, cs)
      | gen cs bs (Abs (x, T, t)) tye_idx =
          let val (U, tye_idx', cs') = gen cs ((x, T) :: bs) t tye_idx
          in (T --> U, tye_idx', cs') end
      | gen cs bs (t $ u) tye_idx =
          let
            val (T, tye_idx', cs') = gen cs bs t tye_idx;
            val (U', (tye, idx), cs'') = gen cs' bs u tye_idx';
            val U = Type_Infer.mk_param idx [];
            val V = Type_Infer.mk_param (idx + 1) [];
            val tye_idx''= strong_unify ctxt (U --> V, T) (tye, idx + 2)
              handle NO_UNIFIER (msg, tye') => error (gen_msg err msg);
            val error_pack = (bs, t $ u, U, V, U');
          in (V, tye_idx'', ((U', U), error_pack) :: cs'') end;
  in
    gen [] []
  end;



(** constraint resolution **)

exception BOUND_ERROR of string;

fun process_constraints ctxt err cs tye_idx =
  let
    val coes_graph = coes_graph_of ctxt;
    val tmaps = tmaps_of ctxt;
    val tsig = Sign.tsig_of (ProofContext.theory_of ctxt);
    val pp = Syntax.pp ctxt;
    val arity_sorts = Type.arity_sorts pp tsig;
    val subsort = Type.subsort tsig;

    fun split_cs _ [] = ([], [])
      | split_cs f (c :: cs) =
          (case pairself f (fst c) of
            (false, false) => apsnd (cons c) (split_cs f cs)
          | _ => apfst (cons c) (split_cs f cs));


    (* check whether constraint simplification will terminate using weak unification *)

    val _ = fold (fn (TU, error_pack) => fn tye_idx =>
      weak_unify ctxt TU tye_idx handle NO_UNIFIER (msg, tye) =>
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
              | INVARIANT => (cs, strong_unify ctxt constraint tye_idx
                  handle NO_UNIFIER (msg, tye) => 
                    error (gen_msg err ("failed to unify invariant arguments\n" ^ msg))));
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
        and eliminate TU error_pack done todo tye idx =
          let
            val [TVar (xi, S)] = filter Type_Infer.is_paramT TU;
            val [T] = filter_out Type_Infer.is_paramT TU;
            val SOME S' = sort_of T;
            val test_update = if is_freeT T then is_freeT else is_fixedvarT;
            val tye' = Vartab.update_new (xi, T) tye;
            val (ch, done') = split_cs (test_update o Type_Infer.deref tye') done;
            val todo' = ch @ todo;
          in
            if subsort (S', S) (*TODO check this*)
            then simplify done' todo' (tye', idx)
            else error (gen_msg err "sort mismatch")
          end
        and simplify done [] tye_idx = (done, tye_idx)
          | simplify done (((T, U), error_pack) :: todo) (tye_idx as (tye, idx)) =
              (case (Type_Infer.deref tye T, Type_Infer.deref tye U) of
                (Type (a, []), Type (b, [])) =>
                  if a = b then simplify done todo tye_idx
                  else if Graph.is_edge coes_graph (a, b) then simplify done todo tye_idx
                  else error (gen_msg err (a ^ " is not a subtype of " ^ b))
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
                  then eliminate [T, U] error_pack done todo tye idx
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

    fun unify_list (T :: Ts) tye_idx =
      fold (fn U => fn tye_idx' => strong_unify ctxt (T, U) tye_idx') Ts tye_idx;

    (*styps stands either for supertypes or for subtypes of a type T
      in terms of the subtype-relation (excluding T itself)*)
    fun styps super T =
      (if super then Graph.imm_succs else Graph.imm_preds) coes_graph T
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
        fun fitting Ts S U = Type.of_sort tsig (t_of U, S) andalso styp_test U Ts
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
        fun restriction T = Type.of_sort tsig (t_of T, S)
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
            val (G'', tye_idx') = (add_edge (T, U) G', tye_idx)
              handle Typ_Graph.CYCLES cycles =>
                let
                  val (tye, idx) = 
                    fold 
                      (fn cycle => fn tye_idx' => (unify_list cycle tye_idx'
                        handle NO_UNIFIER (msg, tye) => 
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
        val G' = Typ_Graph.del_nodes (tl nodes) G;
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
                    (filter_out Type_Infer.is_paramT (map (Type_Infer.deref tye) (get_bound G T))),
                      S));
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
                  else err_bound ctxt (gen_msg err ("assigned simple type " ^ s ^
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
            handle NO_UNIFIER (msg, tye) => err_list ctxt (gen_msg err msg) (fst tye_idx) Ts)
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

fun gen_coercion ctxt tye (T1, T2) =
  (case pairself (Type_Infer.deref tye) (T1, T2) of
    ((Type (a, [])), (Type (b, []))) =>
        if a = b
        then Abs (Name.uu, Type (a, []), Bound 0)
        else
          (case Symreltab.lookup (coes_of ctxt) (a, b) of
            NONE => raise Fail (a ^ " is not a subtype of " ^ b)
          | SOME co => co)
  | ((Type (a, Ts)), (Type (b, Us))) =>
        if a <> b
        then raise Fail ("Different constructors: " ^ a ^ " and " ^ b)
        else
          let
            fun inst t Ts =
              Term.subst_vars
                (((Term.add_tvar_namesT (fastype_of t) []) ~~ rev Ts), []) t;
            fun sub_co (COVARIANT, TU) = gen_coercion ctxt tye TU
              | sub_co (CONTRAVARIANT, TU) = gen_coercion ctxt tye (swap TU);
            fun ts_of [] = []
              | ts_of (Type ("fun", [x1, x2]) :: xs) = x1 :: x2 :: (ts_of xs);
          in
            (case Symtab.lookup (tmaps_of ctxt) a of
              NONE => raise Fail ("No map function for " ^ a ^ " known")
            | SOME tmap =>
                let
                  val used_coes = map sub_co ((snd tmap) ~~ (Ts ~~ Us));
                in
                  Term.list_comb
                    (inst (fst tmap) (ts_of (map fastype_of used_coes)), used_coes)
                end)
          end
  | (T, U) =>
        if Type.could_unify (T, U)
        then Abs (Name.uu, T, Bound 0)
        else raise Fail ("Cannot generate coercion from "
          ^ Syntax.string_of_typ ctxt T ^ " to " ^ Syntax.string_of_typ ctxt U));

fun insert_coercions ctxt tye ts =
  let
    fun insert _ (Const (c, T)) =
          let val T' = T;
          in (Const (c, T'), T') end
      | insert _ (Free (x, T)) =
          let val T' = T;
          in (Free (x, T'), T') end
      | insert _ (Var (xi, T)) =
          let val T' = T;
          in (Var (xi, T'), T') end
      | insert bs (Bound i) =
          let val T = nth bs i handle Subscript => err_loose i;
          in (Bound i, T) end
      | insert bs (Abs (x, T, t)) =
          let
            val T' = T;
            val (t', T'') = insert (T' :: bs) t;
          in
            (Abs (x, T', t'), T' --> T'')
          end
      | insert bs (t $ u) =
          let
            val (t', Type ("fun", [U, T])) = apsnd (Type_Infer.deref tye) (insert bs t);
            val (u', U') = insert bs u;
          in
            if can (fn TU => strong_unify ctxt TU (tye, 0)) (U, U')
            then (t' $ u', T)
            else (t' $ (gen_coercion ctxt tye (U', U) $ u'), T)
          end
  in
    map (fst o insert []) ts
  end;



(** assembling the pipeline **)

fun infer_types ctxt const_type var_type raw_ts =
  let
    val (idx, ts) = Type_Infer.prepare ctxt const_type var_type raw_ts;

    fun inf _ (t as (Const (_, T))) tye_idx = (t, T, tye_idx)
      | inf _ (t as (Free (_, T))) tye_idx = (t, T, tye_idx)
      | inf _ (t as (Var (_, T))) tye_idx = (t, T, tye_idx)
      | inf bs (t as (Bound i)) tye_idx =
          (t, snd (nth bs i handle Subscript => err_loose i), tye_idx)
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
                raise TYPE_INFERENCE_ERROR (err_appl_msg ctxt msg tye' bs t T u U);
          in (tu, V, tye_idx'') end;

    fun infer_single t tye_idx = 
      let val (t, _, tye_idx') = inf [] t tye_idx;
      in (t, tye_idx') end;
      
    val (ts', (tye, _)) = (fold_map infer_single ts (Vartab.empty, idx)
      handle TYPE_INFERENCE_ERROR err =>     
        let
          fun gen_single t (tye_idx, constraints) =
            let val (_, tye_idx', constraints') = generate_constraints ctxt err t tye_idx
            in (tye_idx', constraints' @ constraints) end;
      
          val (tye_idx, constraints) = fold gen_single ts ((Vartab.empty, idx), []);
          val (tye, idx) = process_constraints ctxt err constraints tye_idx;
        in 
          (insert_coercions ctxt tye ts, (tye, idx))
        end);

    val (_, ts'') = Type_Infer.finish ctxt tye ([], ts');
  in ts'' end;



(** installation **)

(* term check *)

fun coercion_infer_types ctxt =
  infer_types ctxt
    (try (Consts.the_constraint (ProofContext.consts_of ctxt)))
    (ProofContext.def_type ctxt);

val add_term_check =
  Syntax.add_term_check ~100 "coercions"
    (fn xs => fn ctxt =>
      let val xs' = coercion_infer_types ctxt xs
      in if eq_list (op aconv) (xs, xs') then NONE else SOME (xs', ctxt) end);


(* declarations *)

fun add_type_map raw_t context =
  let
    val ctxt = Context.proof_of context;
    val t = singleton (Variable.polymorphic ctxt) raw_t;

    fun err_str () = "\n\nthe general type signature for a map function is" ^
      "\nf1 => f2 => ... => fn => C [x1, ..., xn] => C [x1, ..., xn]" ^
      "\nwhere C is a constructor and fi is of type (xi => yi) or (yi => xi)";

    fun gen_arg_var ([], []) = []
      | gen_arg_var ((T, T') :: Ts, (U, U') :: Us) =
          if T = U andalso T' = U' then COVARIANT :: gen_arg_var (Ts, Us)
          else if T = U' andalso T' = U then CONTRAVARIANT :: gen_arg_var (Ts, Us)
          else error ("Functions do not apply to arguments correctly:" ^ err_str ())
      | gen_arg_var (_, _) =
          error ("Different numbers of functions and arguments\n" ^ err_str ());

    (* TODO: This function is only needed to introde the fun type map
      function: "% f g h . g o h o f". There must be a better solution. *)
    fun balanced (Type (_, [])) (Type (_, [])) = true
      | balanced (Type (a, Ts)) (Type (b, Us)) =
          a = b andalso forall I (map2 balanced Ts Us)
      | balanced (TFree _) (TFree _) = true
      | balanced (TVar _) (TVar _) = true
      | balanced _ _ = false;

    fun check_map_fun (pairs, []) (Type ("fun", [T as Type (C, Ts), U as Type (_, Us)])) =
          if balanced T U
          then ((pairs, Ts ~~ Us), C)
          else if C = "fun"
            then check_map_fun (pairs @ [(hd Ts, hd (tl Ts))], []) U
            else error ("Not a proper map function:" ^ err_str ())
      | check_map_fun _ _ = error ("Not a proper map function:" ^ err_str ());

    val res = check_map_fun ([], []) (fastype_of t);
    val res_av = gen_arg_var (fst res);
  in
    map_tmaps (Symtab.update (snd res, (t, res_av))) context
  end;

fun add_coercion raw_t context =
  let
    val ctxt = Context.proof_of context;
    val t = singleton (Variable.polymorphic ctxt) raw_t;

    fun err_coercion () = error ("Bad type for coercion " ^
        Syntax.string_of_term ctxt t ^ ":\n" ^
        Syntax.string_of_typ ctxt (fastype_of t));

    val (T1, T2) = Term.dest_funT (fastype_of t)
      handle TYPE _ => err_coercion ();

    val a =
      (case T1 of
        Type (x, []) => x
      | _ => err_coercion ());

    val b =
      (case T2 of
        Type (x, []) => x
      | _ => err_coercion ());

    fun coercion_data_update (tab, G) =
      let
        val G' = maybe_new_nodes [a, b] G
        val G'' = Graph.add_edge_trans_acyclic (a, b) G'
          handle Graph.CYCLES _ => error (a ^ " is already a subtype of " ^ b ^
            "!\n\nCannot add coercion of type: " ^ a ^ " => " ^ b);
        val new_edges =
          flat (Graph.dest G'' |> map (fn (x, ys) => ys |> map_filter (fn y =>
            if Graph.is_edge G' (x, y) then NONE else SOME (x, y))));
        val G_and_new = Graph.add_edge (a, b) G';

        fun complex_coercion tab G (a, b) =
          let
            val path = hd (Graph.irreducible_paths G (a, b))
            val path' = fst (split_last path) ~~ tl path
          in Abs (Name.uu, Type (a, []),
              fold (fn t => fn u => t $ u) (map (the o Symreltab.lookup tab) path') (Bound 0))
          end;

        val tab' = fold
          (fn pair => fn tab => Symreltab.update (pair, complex_coercion tab G_and_new pair) tab)
          (filter (fn pair => pair <> (a, b)) new_edges)
          (Symreltab.update ((a, b), t) tab);
      in
        (tab', G'')
      end;
  in
    map_coes_and_graph coercion_data_update context
  end;


(* theory setup *)

val setup =
  Context.theory_map add_term_check #>
  Attrib.setup @{binding coercion}
    (Args.term >> (fn t => Thm.declaration_attribute (K (add_coercion t))))
    "declaration of new coercions" #>
  Attrib.setup @{binding coercion_map}
    (Args.term >> (fn t => Thm.declaration_attribute (K (add_type_map t))))
    "declaration of new map functions";

end;
