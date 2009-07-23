(*  Title:      Pure/type_infer.ML
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen

Simple type inference.
*)

signature TYPE_INFER =
sig
  val anyT: sort -> typ
  val polymorphicT: typ -> typ
  val constrain: typ -> term -> term
  val is_param: indexname -> bool
  val param: int -> string * sort -> typ
  val paramify_vars: typ -> typ
  val paramify_dummies: typ -> int -> typ * int
  val fixate_params: Name.context -> term list -> term list
  val appl_error: Pretty.pp -> string -> term -> typ -> term -> typ -> string list
  val infer_types: Pretty.pp -> Type.tsig -> (typ list -> typ list) ->
    (string -> typ option) -> (indexname -> typ option) -> Name.context -> int ->
    term list -> term list
end;

structure TypeInfer: TYPE_INFER =
struct


(** type parameters and constraints **)

fun anyT S = TFree ("'_dummy_", S);

(*indicate polymorphic Vars*)
fun polymorphicT T = Type ("_polymorphic_", [T]);

val constrain = Syntax.type_constraint;


(* user parameters *)

fun is_param (x, _: int) = String.isPrefix "?" x;
fun param i (x, S) = TVar (("?" ^ x, i), S);

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



(** pretyps and preterms **)

(*parameters may get instantiated, anything else is rigid*)
datatype pretyp =
  PType of string * pretyp list |
  PTFree of string * sort |
  PTVar of indexname * sort |
  Param of int * sort;

datatype preterm =
  PConst of string * pretyp |
  PFree of string * pretyp |
  PVar of indexname * pretyp |
  PBound of int |
  PAbs of string * pretyp * preterm |
  PAppl of preterm * preterm |
  Constraint of preterm * pretyp;


(* utils *)

fun deref tye (T as Param (i, S)) =
      (case Inttab.lookup tye i of
        NONE => T
      | SOME U => deref tye U)
  | deref tye T = T;

fun fold_pretyps f (PConst (_, T)) x = f T x
  | fold_pretyps f (PFree (_, T)) x = f T x
  | fold_pretyps f (PVar (_, T)) x = f T x
  | fold_pretyps _ (PBound _) x = x
  | fold_pretyps f (PAbs (_, T, t)) x = fold_pretyps f t (f T x)
  | fold_pretyps f (PAppl (t, u)) x = fold_pretyps f u (fold_pretyps f t x)
  | fold_pretyps f (Constraint (t, T)) x = f T (fold_pretyps f t x);



(** raw typs/terms to pretyps/preterms **)

(* pretyp_of *)

fun pretyp_of is_para typ params_idx =
  let
    val (params', idx) = fold_atyps
      (fn TVar (xi as (x, _), S) =>
          (fn ps_idx as (ps, idx) =>
            if is_para xi andalso not (Vartab.defined ps xi)
            then (Vartab.update (xi, Param (idx, S)) ps, idx + 1) else ps_idx)
        | _ => I) typ params_idx;

    fun pre_of (TVar (v as (xi, _))) idx =
          (case Vartab.lookup params' xi of
            NONE => PTVar v
          | SOME p => p, idx)
      | pre_of (TFree ("'_dummy_", S)) idx = (Param (idx, S), idx + 1)
      | pre_of (TFree v) idx = (PTFree v, idx)
      | pre_of (T as Type (a, Ts)) idx =
          if T = dummyT then (Param (idx, []), idx + 1)
          else
            let val (Ts', idx') = fold_map pre_of Ts idx
            in (PType (a, Ts'), idx') end;

    val (ptyp, idx') = pre_of typ idx;
  in (ptyp, (params', idx')) end;


(* preterm_of *)

fun preterm_of const_type is_para tm (vparams, params, idx) =
  let
    fun add_vparm xi (ps_idx as (ps, idx)) =
      if not (Vartab.defined ps xi) then
        (Vartab.update (xi, Param (idx, [])) ps, idx + 1)
      else ps_idx;

    val (vparams', idx') = fold_aterms
      (fn Var (_, Type ("_polymorphic_", _)) => I
        | Var (xi, _) => add_vparm xi
        | Free (x, _) => add_vparm (x, ~1)
        | _ => I)
      tm (vparams, idx);
    fun var_param xi = the (Vartab.lookup vparams' xi);

    val preT_of = pretyp_of is_para;
    fun polyT_of T idx = apsnd snd (pretyp_of (K true) T (Vartab.empty, idx));

    fun constraint T t ps =
      if T = dummyT then (t, ps)
      else
        let val (T', ps') = preT_of T ps
        in (Constraint (t, T'), ps') end;

    fun pre_of (Const (c, T)) (ps, idx) =
          (case const_type c of
            SOME U =>
              let val (pU, idx') = polyT_of U idx
              in constraint T (PConst (c, pU)) (ps, idx') end
          | NONE => raise TYPE ("No such constant: " ^ quote c, [], []))
      | pre_of (Var (xi, Type ("_polymorphic_", [T]))) (ps, idx) =
          let val (pT, idx') = polyT_of T idx
          in (PVar (xi, pT), (ps, idx')) end
      | pre_of (Var (xi, T)) ps_idx = constraint T (PVar (xi, var_param xi)) ps_idx
      | pre_of (Free (x, T)) ps_idx = constraint T (PFree (x, var_param (x, ~1))) ps_idx
      | pre_of (Const ("_type_constraint_", Type ("fun", [T, _])) $ t) ps_idx =
          pre_of t ps_idx |-> constraint T
      | pre_of (Bound i) ps_idx = (PBound i, ps_idx)
      | pre_of (Abs (x, T, t)) ps_idx =
          let
            val (T', ps_idx') = preT_of T ps_idx;
            val (t', ps_idx'') = pre_of t ps_idx';
          in (PAbs (x, T', t'), ps_idx'') end
      | pre_of (t $ u) ps_idx =
          let
            val (t', ps_idx') = pre_of t ps_idx;
            val (u', ps_idx'') = pre_of u ps_idx';
          in (PAppl (t', u'), ps_idx'') end;

    val (tm', (params', idx'')) = pre_of tm (params, idx');
  in (tm', (vparams', params', idx'')) end;



(** pretyps/terms to typs/terms **)

(* add_parms *)

fun add_parmsT tye T =
  (case deref tye T of
    PType (_, Ts) => fold (add_parmsT tye) Ts
  | Param (i, _) => insert (op =) i
  | _ => I);

fun add_parms tye = fold_pretyps (add_parmsT tye);


(* add_names *)

fun add_namesT tye T =
  (case deref tye T of
    PType (_, Ts) => fold (add_namesT tye) Ts
  | PTFree (x, _) => Name.declare x
  | PTVar ((x, _), _) => Name.declare x
  | Param _ => I);

fun add_names tye = fold_pretyps (add_namesT tye);


(* simple_typ/term_of *)

fun simple_typ_of tye f T =
  (case deref tye T of
    PType (a, Ts) => Type (a, map (simple_typ_of tye f) Ts)
  | PTFree v => TFree v
  | PTVar v => TVar v
  | Param (i, S) => TVar (f i, S));

(*convert types, drop constraints*)
fun simple_term_of tye f (PConst (c, T)) = Const (c, simple_typ_of tye f T)
  | simple_term_of tye f (PFree (x, T)) = Free (x, simple_typ_of tye f T)
  | simple_term_of tye f (PVar (xi, T)) = Var (xi, simple_typ_of tye f T)
  | simple_term_of tye f (PBound i) = Bound i
  | simple_term_of tye f (PAbs (x, T, t)) =
      Abs (x, simple_typ_of tye f T, simple_term_of tye f t)
  | simple_term_of tye f (PAppl (t, u)) =
      simple_term_of tye f t $ simple_term_of tye f u
  | simple_term_of tye f (Constraint (t, _)) = simple_term_of tye f t;


(* typs_terms_of *)

fun typs_terms_of tye used maxidx (Ts, ts) =
  let
    val used' = fold (add_names tye) ts (fold (add_namesT tye) Ts used);
    val parms = rev (fold (add_parms tye) ts (fold (add_parmsT tye) Ts []));
    val names = Name.invents used' ("?" ^ Name.aT) (length parms);
    val tab = Inttab.make (parms ~~ names);
    fun f i = (the (Inttab.lookup tab i), maxidx + 1);
  in (map (simple_typ_of tye f) Ts, map (simple_term_of tye f) ts) end;



(** order-sorted unification of types **)

exception NO_UNIFIER of string * pretyp Inttab.table;

fun unify pp tsig =
  let

    (* adjust sorts of parameters *)

    fun not_of_sort x S' S =
      "Variable " ^ x ^ "::" ^ Pretty.string_of_sort pp S' ^ " not of sort " ^
        Pretty.string_of_sort pp S;

    fun meet (_, []) tye_idx = tye_idx
      | meet (Param (i, S'), S) (tye_idx as (tye, idx)) =
          if Type.subsort tsig (S', S) then tye_idx
          else (Inttab.update_new (i,
            Param (idx, Type.inter_sort tsig (S', S))) tye, idx + 1)
      | meet (PType (a, Ts), S) (tye_idx as (tye, _)) =
          meets (Ts, Type.arity_sorts pp tsig a S
            handle ERROR msg => raise NO_UNIFIER (msg, tye)) tye_idx
      | meet (PTFree (x, S'), S) (tye_idx as (tye, _)) =
          if Type.subsort tsig (S', S) then tye_idx
          else raise NO_UNIFIER (not_of_sort x S' S, tye)
      | meet (PTVar (xi, S'), S) (tye_idx as (tye, _)) =
          if Type.subsort tsig (S', S) then tye_idx
          else raise NO_UNIFIER (not_of_sort (Term.string_of_vname xi) S' S, tye)
    and meets (T :: Ts, S :: Ss) (tye_idx as (tye, _)) =
          meets (Ts, Ss) (meet (deref tye T, S) tye_idx)
      | meets _ tye_idx = tye_idx;


    (* occurs check and assigment *)

    fun occurs_check tye i (Param (i', S)) =
          if i = i' then raise NO_UNIFIER ("Occurs check!", tye)
          else
            (case Inttab.lookup tye i' of
              NONE => ()
            | SOME T => occurs_check tye i T)
      | occurs_check tye i (PType (_, Ts)) = List.app (occurs_check tye i) Ts
      | occurs_check _ _ _ = ();

    fun assign i (T as Param (i', _)) S (tye_idx as (tye, idx)) =
          if i = i' then tye_idx
          else meet (T, S) (Inttab.update_new (i, T) tye, idx)
      | assign i T S (tye, idx) =
          (occurs_check tye i T; meet (T, S) (Inttab.update_new (i, T) tye, idx));


    (* unification *)

    fun unif (T1, T2) (tye_idx as (tye, idx)) =
      (case (deref tye T1, deref tye T2) of
        (Param (i, S), T) => assign i T S tye_idx
      | (T, Param (i, S)) => assign i T S tye_idx
      | (PType (a, Ts), PType (b, Us)) =>
          if a <> b then
            raise NO_UNIFIER ("Clash of types " ^ quote a ^ " and " ^ quote b, tye)
          else fold unif (Ts ~~ Us) tye_idx
      | (T, U) => if T = U then tye_idx else raise NO_UNIFIER ("", tye));

  in unif end;



(** type inference **)

(* appl_error *)

fun appl_error pp why t T u U =
 ["Type error in application: " ^ why,
  "",
  Pretty.string_of (Pretty.block
    [Pretty.str "Operator:", Pretty.brk 2, Pretty.term pp t,
      Pretty.str " ::", Pretty.brk 1, Pretty.typ pp T]),
  Pretty.string_of (Pretty.block
    [Pretty.str "Operand:", Pretty.brk 3, Pretty.term pp u,
      Pretty.str " ::", Pretty.brk 1, Pretty.typ pp U]),
  ""];


(* infer *)

fun infer pp tsig =
  let
    (* errors *)

    fun unif_failed msg =
      "Type unification failed" ^ (if msg = "" then "" else ": " ^ msg) ^ "\n";

    fun prep_output tye bs ts Ts =
      let
        val (Ts_bTs', ts') = typs_terms_of tye Name.context ~1 (Ts @ map snd bs, ts);
        val (Ts', Ts'') = chop (length Ts) Ts_bTs';
        fun prep t =
          let val xs = rev (Term.variant_frees t (rev (map fst bs ~~ Ts'')))
          in Term.subst_bounds (map Syntax.mark_boundT xs, t) end;
      in (map prep ts', Ts') end;

    fun err_loose i =
      raise TYPE ("Loose bound variable: B." ^ string_of_int i, [], []);

    fun err_appl msg tye bs t T u U =
      let
        val ([t', u'], [T', U']) = prep_output tye bs [t, u] [T, U];
        val why =
          (case T' of
            Type ("fun", _) => "Incompatible operand type"
          | _ => "Operator not of function type");
        val text = unif_failed msg ^ cat_lines (appl_error pp why t' T' u' U');
      in raise TYPE (text, [T', U'], [t', u']) end;

    fun err_constraint msg tye bs t T U =
      let
        val ([t'], [T', U']) = prep_output tye bs [t] [T, U];
        val text = cat_lines
         [unif_failed msg,
          "Cannot meet type constraint:", "",
          Pretty.string_of (Pretty.block
           [Pretty.str "Term:", Pretty.brk 2, Pretty.term pp t',
            Pretty.str " ::", Pretty.brk 1, Pretty.typ pp T']),
          Pretty.string_of (Pretty.block
           [Pretty.str "Type:", Pretty.brk 2, Pretty.typ pp U']), ""];
      in raise TYPE (text, [T', U'], [t']) end;


    (* main *)

    val unif = unify pp tsig;

    fun inf _ (PConst (_, T)) tye_idx = (T, tye_idx)
      | inf _ (PFree (_, T)) tye_idx = (T, tye_idx)
      | inf _ (PVar (_, T)) tye_idx = (T, tye_idx)
      | inf bs (PBound i) tye_idx =
          (snd (nth bs i handle Subscript => err_loose i), tye_idx)
      | inf bs (PAbs (x, T, t)) tye_idx =
          let val (U, tye_idx') = inf ((x, T) :: bs) t tye_idx
          in (PType ("fun", [T, U]), tye_idx') end
      | inf bs (PAppl (t, u)) tye_idx =
          let
            val (T, tye_idx') = inf bs t tye_idx;
            val (U, (tye, idx)) = inf bs u tye_idx';
            val V = Param (idx, []);
            val U_to_V = PType ("fun", [U, V]);
            val tye_idx'' = unif (U_to_V, T) (tye, idx + 1)
              handle NO_UNIFIER (msg, tye') => err_appl msg tye' bs t T u U;
          in (V, tye_idx'') end
      | inf bs (Constraint (t, U)) tye_idx =
          let val (T, tye_idx') = inf bs t tye_idx in
            (T,
             unif (T, U) tye_idx'
               handle NO_UNIFIER (msg, tye) => err_constraint msg tye bs t T U)
          end;

  in inf [] end;


(* infer_types *)

fun infer_types pp tsig check_typs const_type var_type used maxidx raw_ts =
  let
    (*constrain vars*)
    val get_type = the_default dummyT o var_type;
    val constrain_vars = Term.map_aterms
      (fn Free (x, T) => constrain T (Free (x, get_type (x, ~1)))
        | Var (xi, T) => constrain T (Var (xi, get_type xi))
        | t => t);

    (*convert to preterms*)
    val ts = burrow_types check_typs raw_ts;
    val (ts', (_, _, idx)) =
      fold_map (preterm_of const_type is_param o constrain_vars) ts
      (Vartab.empty, Vartab.empty, 0);

    (*do type inference*)
    val (tye, _) = fold (snd oo infer pp tsig) ts' (Inttab.empty, idx);
  in #2 (typs_terms_of tye used maxidx ([], ts')) end;

end;
