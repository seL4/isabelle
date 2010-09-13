(*  Title:      Pure/type_infer.ML
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen

Simple type inference.
*)

signature TYPE_INFER =
sig
  val anyT: sort -> typ
  val is_param: indexname -> bool
  val is_paramT: typ -> bool
  val param: int -> string * sort -> typ
  val paramify_vars: typ -> typ
  val paramify_dummies: typ -> int -> typ * int
  val fixate_params: Name.context -> term list -> term list
  val infer_types: Proof.context -> (string -> typ option) -> (indexname -> typ option) ->
    term list -> term list
end;

structure Type_Infer: TYPE_INFER =
struct


(** type parameters and constraints **)

fun anyT S = TFree ("'_dummy_", S);


(* type inference parameters -- may get instantiated *)

fun is_param (x, _: int) = String.isPrefix "?" x;

fun is_paramT (TVar (xi, _)) = is_param xi
  | is_paramT _ = false;

fun param i (x, S) = TVar (("?" ^ x, i), S);

fun mk_param i S = TVar (("?'a", i), S);

val paramify_vars =
  Same.commit
    (Term_Subst.map_atypsT_same
      (fn TVar ((x, i), S) => (param i (x, S)) | _ => raise Same.SAME));

val paramify_dummies =
  let
    fun dummy S maxidx = (param (maxidx + 1) ("'dummy", S), maxidx + 1);

    fun paramify (TFree ("'_dummy_", S)) maxidx = dummy S maxidx
      | paramify (Type ("dummy", _)) maxidx = dummy [] maxidx
      | paramify (Type (a, Ts)) maxidx =
          let val (Ts', maxidx') = fold_map paramify Ts maxidx
          in (Type (a, Ts'), maxidx') end
      | paramify T maxidx = (T, maxidx);
  in paramify end;

fun fixate_params name_context ts =
  let
    fun subst_param (xi, S) (inst, used) =
      if is_param xi then
        let
          val [a] = Name.invents used Name.aT 1;
          val used' = Name.declare a used;
        in (((xi, S), TFree (a, S)) :: inst, used') end
      else (inst, used);
    val name_context' = (fold o fold_types) Term.declare_typ_names ts name_context;
    val (inst, _) = fold_rev subst_param (fold Term.add_tvars ts []) ([], name_context');
  in (map o map_types) (Term_Subst.instantiateT inst) ts end;



(** prepare types/terms: create inference parameters **)

(* prepare_typ *)

fun prepare_typ typ params_idx =
  let
    val (params', idx) = fold_atyps
      (fn TVar (xi as (x, _), S) =>
          (fn ps_idx as (ps, idx) =>
            if is_param xi andalso not (Vartab.defined ps xi)
            then (Vartab.update (xi, mk_param idx S) ps, idx + 1) else ps_idx)
        | _ => I) typ params_idx;

    fun prepare (T as Type (a, Ts)) idx =
          if T = dummyT then (mk_param idx [], idx + 1)
          else
            let val (Ts', idx') = fold_map prepare Ts idx
            in (Type (a, Ts'), idx') end
      | prepare (T as TVar (xi, _)) idx =
          (case Vartab.lookup params' xi of
            NONE => T
          | SOME p => p, idx)
      | prepare (TFree ("'_dummy_", S)) idx = (mk_param idx S, idx + 1)
      | prepare (T as TFree _) idx = (T, idx);

    val (typ', idx') = prepare typ idx;
  in (typ', (params', idx')) end;


(* prepare_term *)

fun prepare_term const_type tm (vparams, params, idx) =
  let
    fun add_vparm xi (ps_idx as (ps, idx)) =
      if not (Vartab.defined ps xi) then
        (Vartab.update (xi, mk_param idx []) ps, idx + 1)
      else ps_idx;

    val (vparams', idx') = fold_aterms
      (fn Var (_, Type ("_polymorphic_", _)) => I
        | Var (xi, _) => add_vparm xi
        | Free (x, _) => add_vparm (x, ~1)
        | _ => I)
      tm (vparams, idx);
    fun var_param xi = the (Vartab.lookup vparams' xi);

    fun polyT_of T idx = apsnd snd (prepare_typ (paramify_vars T) (Vartab.empty, idx));

    fun constraint T t ps =
      if T = dummyT then (t, ps)
      else
        let val (T', ps') = prepare_typ T ps
        in (Type.constraint T' t, ps') end;

    fun prepare (Const ("_type_constraint_", T) $ t) ps_idx =
          let
            val (T', ps_idx') = prepare_typ T ps_idx;
            val (t', ps_idx'') = prepare t ps_idx';
          in (Const ("_type_constraint_", T') $ t', ps_idx'') end
      | prepare (Const (c, T)) (ps, idx) =
          (case const_type c of
            SOME U =>
              let val (U', idx') = polyT_of U idx
              in constraint T (Const (c, U')) (ps, idx') end
          | NONE => error ("Undeclared constant: " ^ quote c))
      | prepare (Var (xi, Type ("_polymorphic_", [T]))) (ps, idx) =
          let val (T', idx') = polyT_of T idx
          in (Var (xi, T'), (ps, idx')) end
      | prepare (Var (xi, T)) ps_idx = constraint T (Var (xi, var_param xi)) ps_idx
      | prepare (Free (x, T)) ps_idx = constraint T (Free (x, var_param (x, ~1))) ps_idx
      | prepare (Bound i) ps_idx = (Bound i, ps_idx)
      | prepare (Abs (x, T, t)) ps_idx =
          let
            val (T', ps_idx') = prepare_typ T ps_idx;
            val (t', ps_idx'') = prepare t ps_idx';
          in (Abs (x, T', t'), ps_idx'') end
      | prepare (t $ u) ps_idx =
          let
            val (t', ps_idx') = prepare t ps_idx;
            val (u', ps_idx'') = prepare u ps_idx';
          in (t' $ u', ps_idx'') end;

    val (tm', (params', idx'')) = prepare tm (params, idx');
  in (tm', (vparams', params', idx'')) end;



(** finish types/terms: standardize remaining parameters **)

(* dereferenced views *)

fun deref tye (T as TVar (xi, _)) =
      (case Vartab.lookup tye xi of
        NONE => T
      | SOME U => deref tye U)
  | deref tye T = T;

fun add_parms tye T =
  (case deref tye T of
    Type (_, Ts) => fold (add_parms tye) Ts
  | TVar (xi, _) => if is_param xi then insert (op =) xi else I
  | _ => I);

fun add_names tye T =
  (case deref tye T of
    Type (_, Ts) => fold (add_names tye) Ts
  | TFree (x, _) => Name.declare x
  | TVar ((x, i), _) => if is_param (x, i) then I else Name.declare x);


(* finish *)

fun finish ctxt tye (Ts, ts) =
  let
    val used =
      (fold o fold_types) (add_names tye) ts (fold (add_names tye) Ts (Variable.names_of ctxt));
    val parms = rev ((fold o fold_types) (add_parms tye) ts (fold (add_parms tye) Ts []));
    val names = Name.invents used ("?" ^ Name.aT) (length parms);
    val tab = Vartab.make (parms ~~ names);
    val idx = Variable.maxidx_of ctxt + 1;

    fun finish_typ T =
      (case deref tye T of
        Type (a, Ts) => Type (a, map finish_typ Ts)
      | U as TFree _ => U
      | U as TVar (xi, S) =>
          (case Vartab.lookup tab xi of
            NONE => U
          | SOME a => TVar ((a, idx), S)));
  in (map finish_typ Ts, map (Type.strip_constraints o Term.map_types finish_typ) ts) end;



(** order-sorted unification of types **)

exception NO_UNIFIER of string * typ Vartab.table;

fun unify ctxt pp =
  let
    val thy = ProofContext.theory_of ctxt;
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
          else if is_param xi then
            (Vartab.update_new (xi, mk_param idx (Sign.inter_sort thy (S', S))) tye, idx + 1)
          else raise NO_UNIFIER (not_of_sort (Term.string_of_vname xi) S' S, tye)
    and meets (T :: Ts, S :: Ss) (tye_idx as (tye, _)) =
          meets (Ts, Ss) (meet (deref tye T, S) tye_idx)
      | meets _ tye_idx = tye_idx;


    (* occurs check and assignment *)

    fun occurs_check tye xi (TVar (xi', S)) =
          if xi = xi' then raise NO_UNIFIER ("Occurs check!", tye)
          else
            (case Vartab.lookup tye xi' of
              NONE => ()
            | SOME T => occurs_check tye xi T)
      | occurs_check tye xi (Type (_, Ts)) = List.app (occurs_check tye xi) Ts
      | occurs_check _ _ _ = ();

    fun assign xi (T as TVar (xi', _)) S env =
          if xi = xi' then env
          else env |> meet (T, S) |>> Vartab.update_new (xi, T)
      | assign xi T S (env as (tye, _)) =
          (occurs_check tye xi T; env |> meet (T, S) |>> Vartab.update_new (xi, T));


    (* unification *)

    fun show_tycon (a, Ts) =
      quote (Syntax.string_of_typ ctxt (Type (a, replicate (length Ts) dummyT)));

    fun unif (T1, T2) (env as (tye, _)) =
      (case pairself (`is_paramT o deref tye) (T1, T2) of
        ((true, TVar (xi, S)), (_, T)) => assign xi T S env
      | ((_, T), (true, TVar (xi, S))) => assign xi T S env
      | ((_, Type (a, Ts)), (_, Type (b, Us))) =>
          if a <> b then
            raise NO_UNIFIER
              ("Clash of types " ^ show_tycon (a, Ts) ^ " and " ^ show_tycon (b, Us), tye)
          else fold unif (Ts ~~ Us) env
      | ((_, T), (_, U)) => if T = U then env else raise NO_UNIFIER ("", tye));

  in unif end;



(** type inference **)

(* infer *)

fun infer ctxt =
  let
    val pp = Syntax.pp ctxt;


    (* errors *)

    fun prep_output tye bs ts Ts =
      let
        val (Ts_bTs', ts') = finish ctxt tye (Ts @ map snd bs, ts);
        val (Ts', Ts'') = chop (length Ts) Ts_bTs';
        fun prep t =
          let val xs = rev (Term.variant_frees t (rev (map fst bs ~~ Ts'')))
          in Term.subst_bounds (map Syntax.mark_boundT xs, t) end;
      in (map prep ts', Ts') end;

    fun err_loose i = error ("Loose bound variable: B." ^ string_of_int i);

    fun unif_failed msg =
      "Type unification failed" ^ (if msg = "" then "" else ": " ^ msg) ^ "\n\n";

    fun err_appl msg tye bs t T u U =
      let val ([t', u'], [T', U']) = prep_output tye bs [t, u] [T, U]
      in error (unif_failed msg ^ Type.appl_error pp t' T' u' U' ^ "\n") end;


    (* main *)

    fun inf _ (Const (_, T)) tye_idx = (T, tye_idx)
      | inf _ (Free (_, T)) tye_idx = (T, tye_idx)
      | inf _ (Var (_, T)) tye_idx = (T, tye_idx)
      | inf bs (Bound i) tye_idx =
          (snd (nth bs i handle Subscript => err_loose i), tye_idx)
      | inf bs (Abs (x, T, t)) tye_idx =
          let val (U, tye_idx') = inf ((x, T) :: bs) t tye_idx
          in (T --> U, tye_idx') end
      | inf bs (t $ u) tye_idx =
          let
            val (T, tye_idx') = inf bs t tye_idx;
            val (U, (tye, idx)) = inf bs u tye_idx';
            val V = mk_param idx [];
            val tye_idx'' = unify ctxt pp (U --> V, T) (tye, idx + 1)
              handle NO_UNIFIER (msg, tye') => err_appl msg tye' bs t T u U;
          in (V, tye_idx'') end;

  in inf [] end;


(* infer_types *)

fun infer_types ctxt const_type var_type raw_ts =
  let
    (*constrain vars*)
    val get_type = the_default dummyT o var_type;
    val constrain_vars = Term.map_aterms
      (fn Free (x, T) => Type.constraint T (Free (x, get_type (x, ~1)))
        | Var (xi, T) => Type.constraint T (Var (xi, get_type xi))
        | t => t);

    (*convert to preterms*)
    val ts = burrow_types (Syntax.check_typs ctxt) raw_ts;
    val (ts', (_, _, idx)) =
      fold_map (prepare_term const_type o constrain_vars) ts
      (Vartab.empty, Vartab.empty, 0);

    (*do type inference*)
    val (tye, _) = fold (snd oo infer ctxt) ts' (Vartab.empty, idx);
  in #2 (finish ctxt tye ([], ts')) end;

end;
